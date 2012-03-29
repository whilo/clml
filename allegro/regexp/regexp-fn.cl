;; -*- mode: common-lisp; package: regexp -*-
;;
;;
;; copyright (c) 2003-2007 Franz Inc, Oakland, CA - All rights reserved.
;;
;; The software, data and information contained herein are proprietary
;; to, and comprise valuable trade secrets of, Franz, Inc.  They are
;; given in confidence by Franz, Inc. pursuant to a written license
;; agreement, and may be stored and used only in accordance with the terms
;; of such license.
;;
;; Restricted Rights Legend
;; ------------------------
;; Use, duplication, and disclosure of the software, data and information
;; contained herein by any agency, department or entity of the U.S.
;; Government are subject to restrictions of Restricted Rights for
;; Commercial Software developed at private expense as specified in
;; DOD FAR Supplement 52.227-7013 (c) (1) (ii), as applicable.
;;

(in-package :regexp)

;;; Debugging variables, not for use in prduction.
(defvar *debug-regexp-function* nil)	; Print the regexp function at cmopile time.
(defvar *trace-regexp-backup* nil)	; Caution, this has effect at both compile time
					; and run time.  In particular, it enables
					; generation of debugging code in the regexp
					; function.
(defvar *interpret-regexp-function* nil) ; Prevent compilation of the regexp function.
;; Allow compiler optimization fo teh generated regexp function.
(defparameter *regexp-optimize* '(optimize #+notyet speed #+notyet (safety 0)))
(defvar .backup-vec-used.)		; Set true if any operator actually
                                        ; uses the backup vec, allowing simple
                                        ; regexps to avoid the allocation
                                        ; overhead.

(defvar .set-label-used.)		; Set true if any set-label instructions are
					; encountered, meaning that a computed jump table
					; needs to be included.  If true, this is a list
					; of all the go tags seen.

(defvar .fails.)
(defvar .fail-dispatch.)
(defvar .fail-cleanups.)

(defvar *regexp-code-gen-hashtable* (make-hash-table :test #'eq))

(excl::defresource backup-vector
  :constructor (lambda () (declare (optimize (speed 3) (safety 0))) (make-array 255))
  ;; The initialization and reinitialization needs to be done by the inline code.
  )

(defmacro vec-push (new)
  `(let ((val ,new))
     ,@(and *trace-regexp-backup*
	    `((let ((low (max 0 (- pos 5)))
		    (hih (min len (+ pos 5))))
		(format *trace-output* "~a_~a~15t"
			(subseq sstring low pos) (subseq sstring pos hih)))
	      (format *trace-output* "push @~d ~a=~s~%" backup-index ',new val)
	      (force-output *trace-output*)))
     (when (>= backup-index backup-vec-length)
       (let ((nvec (make-array (setf backup-vec-length (ash backup-vec-length 2)))))
	 (loop for i below backup-index do (setf (svref nvec i) (svref backup-vec i)))
	 (excl::deallocate-resource 'backup-vector backup-vec)
	 (setf backup-vec nvec)))
     (prog1 (setf (svref backup-vec backup-index) val)
       (incf backup-index))))

(defmacro vec-pop (var)
  ;; For simplicity, vec must be a variable to preserve semantics.
  `(progn
     ,@(and *trace-regexp-backup*
	    `((when (<= backup-index 0)
		(error "Over popping stack."))
	      (let ((low (max 0 (- pos 5)))
		    (hih (min len (+ pos 5))))
		(format *trace-output* "~a_~a~15t"
			(subseq sstring low pos) (subseq sstring pos hih)))
	      (format *trace-output* "pop @~d ~a <= ~s~%"
		      backup-index ',var (svref backup-vec (1- backup-index)))
	      (force-output *trace-output*)))
     (setf ,var
       (svref backup-vec (decf backup-index)))))

(defmacro regexp-gogo (tag)
  (if *trace-regexp-backup*
      `(progn (let ((low (max 0 (- pos 5)))
		    (hih (min len (+ pos 5))))
		(format *trace-output* "~a_~a~15t"
			(subseq sstring low pos) (subseq sstring pos hih)))
	      (format *trace-output* "pos=~d (go ~a)~%" pos ',tag)
	      (force-output *trace-output*)
	      (if (and limit (<= (decf limit) 0))
		  (return-from result :limit-failure))
	      (go ,tag))
    `(go ,tag)))

(defun regexp-function (fe-code minlen &key original-regexp (return :unknown))
  (let* ((comp::*warn-about-unused-tags* nil) ; Shut up the damn unused tag warnings!
	 (excl:*record-xref-info* nil)	; Costs compile time!
	 (*gensym-counter* 100)
	 (lambda-exp (regexp-lambda fe-code minlen
				    :original-regexp original-regexp :return return)))
    (when *debug-regexp-function*
      (format *debug-io* "~s~%" lambda-exp))
    (if *interpret-regexp-function*
	(coerce lambda-exp 'function)
      (compile nil lambda-exp))))

(defun regexp-lambda (fe-code min-length &key original-regexp (return :unknown))
  (let* ((.backup-vec-used. nil)
	 (.set-label-used. nil)
	 (.fail-dispatch. 0)
	 (.fails. '((0 . match-failure)))
	 (.fail-cleanups. nil)
	 reps subs code)
    (loop for (nil . args) in fe-code
	do (loop for arg in args
	       when (and (consp arg) (eq (car arg) 'rep))
	       do (pushnew (cadr arg) reps)
	       when (and (not (eq return nil))
			 (consp arg)
			 (eq (car arg) 'sub))
	       do (pushnew (cadr arg) subs)))
    (setf reps
      (mapcar (lambda (n) (cons n (make-symbol (format nil "rep~2,'0d" n))))
	      reps))
    (unless (null return)
      (setf subs
	(sort (mapcar (lambda (n) (list* n
					 (make-symbol (format nil "subhi~2,'0d" n))
					 (make-symbol (format nil "sublo~2,'0d" n))))
		      subs)
	      #'< :key #'car)))
    (format t "~&reps: ~s~%subs: ~s~%" reps subs)
    (setf code
      (loop for instr in fe-code
	  appending (compile-regexp-code instr reps subs)))
    (setf code
      `(loop named result
	   for begin of-type regexp-dim from ipos
	   to ,(if min-length `(- len ,min-length) 'len)
	   as pos of-type regexp-dim = begin
	   do ,@(when .backup-vec-used.
		  `((setf backup-index 1 (svref backup-vec 0) 0)))
	      ,@(when *trace-regexp-backup*
		  `((format *trace-output* "Starting match at offset ~d.~%" begin)))
	      (tagbody ,@code
		(return-from result
		  ,(ecase return
		     ((nil) 't)
		     (:index `(values ,@(loop for (nil hi . lo) in subs
					    collect `(when ,lo (cons ,lo ,hi)))))
		     (:string `(values ,@(loop for (nil hi . lo) in subs
					     collect `(when ,lo (subseq string ,lo ,hi)))))
		     (:unknown `(ecase return
				  ((nil) t)
				  (:index
				   (values
				    ,@(loop for (nil hi . lo) in subs
					  collect `(when ,lo (cons ,lo ,hi)))))
				  (:string
				   (values
				    ,@(loop for (nil hi . lo) in subs
					  collect `(when ,lo (subseq string ,lo ,hi)))))))))
		,@(when .set-label-used.
		    `(label-gogo
		      (case gogo
			,@(loop for label in .set-label-used.
			      collect `(,label (regexp-gogo ,label))))))
	       fail
		,@(when .backup-vec-used.
		    `((case (let (x) (vec-pop x) x)
			,@(loop for (n . try-cleanup-label) in .fails.
			      collect `(,n (regexp-gogo ,try-cleanup-label))))))
		,@.fail-cleanups.
	       match-failure)))
    ;; Add keywords: starr, end, case-fuld, newlines-special shortest etc.
    `(lambda (string &key ,@(when (eq return :unknown)
			      `((return :string)))
			  ,@(and *trace-regexp-backup* '(limit)))
       (declare ,*regexp-optimize*)
       ;;(declare (:explain :calls))
       ,(format nil ".ignore-case. ~s~@[ ~a~]" .ignore-case. original-regexp)
       (let (,@(loop for (nil lo . hi) in subs collect lo collect hi)
	     ,@(loop for (nil . rep) in reps collect rep)
	     ,@(when .set-label-used. `(gogo)))
	 (excl::with-underlying-simple-vector (string sstring ipos len)
	   (declare (type simple-string sstring) (type regexp-dim ipos len))
	   ,(if .backup-vec-used.
		`(excl::with-resource (backup-vec backup-vector)
		   (declare (simple-vector backup-vec))
		   (let ((backup-index 0)
			 (backup-vec-length (length backup-vec)))
		     (declare (type regexp-dim backup-index bacup-vec-length)
			      (ignorable backup-index))
		     ,code))
	      code))))))

(defmacro def-regexp-code-gen (name lambda-list &body body)
  `(setf (gethash ',name *regexp-code-gen-hashtable*)
     (excl:named-function (regexp-code-gen ,name)
       (lambda (reps subs ,@lambda-list)
	 (declare (ignorable reps subs))
	 ,@body))))

(defmacro reg (reg)
  `(reg1 ,reg reps subs))

(defun reg1 (reg reps subs)
  (case (car reg)
    (rep (cdr (assoc (cadr reg) reps :test #'eql)))
    (sub (cdr (assoc (cadr reg) subs :test #'eql)))))

(defmacro regexp-nextchar ()
  `(and (< pos len)
	(prog1 (schar sstring pos)
	  (incf pos))))

(defmacro regexp-peekchar (&optional (offset 0))
  ;; Warning -- type not evident to the compiler.
  `(let ((i ,(if (= offset 0) 'pos `(+ pos ,offset))))
     (and (< i len) ,@(and (< offset 0) `((>= i 0)))
	  (schar sstring i))))

(defun compile-regexp-code (code reps subs)
  (let ((handler (gethash (car code) *regexp-code-gen-hashtable*)))
    (unless handler
      (error "Unknown regexp intermediate instruction: ~s" code))
    (apply handler reps subs (cdr code))))

(def-regexp-code-gen label (tag)
  ;; tag is an integer.  It would be more hygienic to generate a symbol, but regexp
  ;; functions don'contain only code generated here so there is no chance of collision
  ;; with other use of integers as tags.
  `(,tag))

(def-regexp-code-gen jump (tag)
  ;; tag is an integer.  It would be more hygienic to generate a symbol, but regexp
  ;; functions don'contain only code generated here so there is no chance of collision
  ;; with other use of integers as tags.
  `((regexp-gogo ,tag)))

(def-regexp-code-gen set-label (reg label)
  (pushnew label .set-label-used.)
  `((setf gogo ,(reg reg))
    (regexp-gogo label-gogo)))

(def-regexp-code-gen jump-reg (reg)
  `((setf gogo ,(reg reg))
    (regexp-gogo label-gogo)))

(def-regexp-code-gen save-ip (reg)
  `((setf ,(reg reg) pos)))

(def-regexp-code-gen save-sp (reg)
  `((setf ,(reg reg) backup-index)))

(def-regexp-code-gen load-ip (reg)
  `((setf pos ,(reg reg))))

(def-regexp-code-gen load-sp (reg)
  `((setf backup-index ,(reg reg))))

(def-regexp-code-gen pop (&rest regs)
  `((vec-pop pos)
    ,@(loop for reg in regs collect `(vec-pop ,reg))))

(def-regexp-code-gen try (tag &rest regs)
  (setf .backup-vec-used. t)
  (flet ((regs (reg)
	   (ecase (car reg)
	     (rep (list (reg reg)))
	     (sub (let ((sub (reg reg)))
		    (list (car sub) (cdr sub)))))))
    (let ((fail-label (cons (incf .fail-dispatch.) (gensym))))
      (push fail-label .fails.)
      (setf .fail-cleanups.
	(append `(,(cdr fail-label)
		  ,@(nreverse (loop for reg in regs
				  append (loop for r in (regs reg)
					     collect `(vec-pop ,r))))
		  (vec-pop pos)
		  (regexp-gogo ,tag))
		.fail-cleanups.))
      `((vec-push pos)
	,@(loop for reg in regs
	      append (loop for r in (regs reg)
			 collect `(vec-push ,r)))
	(vec-push ,(car fail-label))))))

(defmacro fail (fail)
  (cond ((eq fail 't)
	 `(go match-failure))
	((null fail)
	 `(regexp-gogo fail))
	;; assert nonnegative integer
	(t `(progn (decf backup-index)
		   (regexp-gogo ,fail)))))

(def-regexp-code-gen reset (reg)
  `((setf ,(reg reg) 0)))

(def-regexp-code-gen set (reg val)
  `((setf ,(reg reg) ,val)))

(def-regexp-code-gen invalidate (&rest subs)
  (loop for sub in subs collect `(setf ,(cdr (reg sub)) nil)))

(def-regexp-code-gen char (char fail)
  `((unless (char= ,char (regexp-nextchar)) (fail ,fail))))

(def-regexp-code-gen char-ci (char fail)
  `((unless (char-equal ,char (regexp-nextchar)) (fail ,fail))))

;; string will always be a simple-string
(def-regexp-code-gen string (string fail)
  `((unless ,(let ((len (length string)))
	       (if (< len 5)
		   `(and ,@(loop for c across string
			       collect `(char= ,c (regexp-nextchar))))
		 `(loop with s = ,string for i below ,len
		      unless `(char= (schar s i) (regexp-nextchar))
		      return nil)))
      (fail ,fail))))

(def-regexp-code-gen string-ci (string fail)
  `((unless ,(let ((len (length string)))
	       (if (< len 5)
		   `(and ,@(loop for c across string
			       collect `(char-equal ,c (regexp-nextchar))))
		 `(loop with s = ,string for i below ,len
		      unless `(char-equal (schar s i) (regexp-nextchar))
		      return nil)))
      (fail ,fail))))

(def-regexp-code-gen any (fail)
  `((unless (regexp-nextchar) (fail ,fail))))

(def-regexp-code-gen any-except-newline (fail)
  `((let ((c (regexp-nextchar))))
     (unless (or (null c) (eql #\newline c)) (fail ,fail))))

;;;    (char-set <char-set>), (char-set-ci <char-set>)
;;;
;;;        Match to a char-set, case sensitive/insensitive.
;;;        Tentative <char-set> format: (<complement> <spec>)
;;;
;;;    (word-boundary), (not-word-boudary)

#+notyet
(def-regexp-code-gen char-set (arg fail)
  (destructuring-bind (complementp &rest members) arg
    (multiple-value-bind (chars tests upper-limit classes)
	(normalize-class-stuff members)

      )))

(def-regexp-code-gen bos (fail)
  `((unless (= pos ipos) (fail ,fail))))

(def-regexp-code-gen bol (fail)
  `((unless (or (= pos ipos)
		(char= #\newline (schar string (1- pos))))
      (fail ,fail))))

(def-regexp-code-gen eos (fail)
  `((unless (= pos len) (fail ,fail))))

(def-regexp-code-gen eos-newline (fail)
  `((unless (or (= pos len)
		(and (= pos (1- len))
		     (char= #\newline (schar string pos))))
      (fail ,fail))))

(def-regexp-code-gen eol (fail)
  `((unless (or (= pos len)
		(char= #\newline (schar string pos)))
      (fail ,fail))))

(def-regexp-code-gen reference (sub fail)
  (let* ((reg (reg `(sub ,sub)))
	 (lo (cdr reg))
	 (hi (car reg)))
    `((unless ,hi (fail ,fail))
      (loop for p from ,lo below ,hi
	  unless (eql (schar string p) (regexp-nextchar)) do (fail ,fail)))))

(def-regexp-code-gen reference-ci (sub fail)
  (let* ((reg (reg `(sub ,sub)))
	 (lo (cdr reg))
	 (hi (car reg)))
    `((unless ,hi (fail ,fail))
      (loop for p from ,lo below ,hi
	  unless (char-equal (schar string p) (regexp-nextchar)) do (fail)))))

(def-regexp-code-gen submatch-start (sub)
  (let* ((reg (reg sub))
	 (lo (cdr reg))
	 (hi (car reg)))
    (and reg
	 `((setf ,lo pos ,hi nil)))))

(def-regexp-code-gen submatch-end (sub)
  (let* ((reg (reg sub))
	 (hi (car reg)))
    (and reg
	 `((setf ,hi pos)))))

;;;    (increment-branch< (rep N) <integer> <label-number>)
;;;
;;;        Increment the specified counter.  If the counter value
;;;        is smaller than <integer>, branch to the
;;;        specified label.

(def-regexp-code-gen increment-branch< (reg lim label)
  `((when (< (incf ,(reg reg)) ,lim) (regexp-gogo ,label))))

(def-regexp-code-gen fail (target)
  `((regexp-gogo ,(if (eq target 't) 'match-failure target))))

(defun fun (regexp)
  (multiple-value-bind (code nsubs nreps minlen)
      (fe-compile-regexp (parse-re regexp) nil)
    nsubs nreps minlen
    (print-fe t code)
    (pprint (regexp-lambda code minlen))))

(defun fu (regexp &key (return :string returnp))
  (multiple-value-bind (code nsubs nreps minlen)
      (fe-compile-regexp (parse-re regexp) nil)
    nsubs nreps minlen
    (print-fe t code)
    (let ((*debug-regexp-function* t))
      (if returnp
	  (regexp-function code minlen :return return)
	(regexp-function code minlen)))))

(defun fur (regexp string &key (return :string))
  (funcall (fu regexp :return return) string))
