;; -*- mode: common-lisp; package: yacc -*-
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

;;; See the accompanying file yacc.cl

;;(provide :yacc-runtime)

;; (eval-when (compile load eval)
;;   (require :yacc-defs (merge-pathnames "yacc-defs.fasl" *load-pathname*)))
;; (eval-when (compile)
;;   (require :yacc-defs (merge-pathnames "yacc-defs.fasl" *compile-file-pathname*)))

(in-package :yacc)

(defvar *yacc-trace* nil
  "When non-NIL the parser state machine reports its actions for debugging.")

;;; Interface to main LALR parser stack machine.

;;; Easy user-callable interface to invoke a grammar by name or by class.
(defmethod parse ((grammar symbol) &key (state-machine 'state-machine))
  (funcall state-machine (make-instance grammar)))

(defmethod parse ((grammar grammar-class) &key (state-machine 'state-machine))
  (funcall state-machine (make-instance grammar)))

(defmethod parse ((grammar grammar) &key (state-machine 'state-machine))
  (funcall state-machine grammar))

;;; This is called to clear the error state inside the machine.
(defun error-resynchronized (grammar)
  (setf (grammar-error grammar) nil))

;; This is used as the default action code when there is none specified in the production.
(defun $$ (grammar &optional $1 &rest rest)
  (declare (ignore grammar rest))
  $1)

;;;
;;; These are necessary if we turn on *yacc-trace*.
;;;

(defmethod print-object ((terminal terminal) stream)
  (let ((x (terminal-terminal terminal)))
    (format stream #-never "{~s}" #+never "~s"
	    (if (integerp x) (code-char x) x))))

(defun print-term (s term)
  (cond ((numberp term)
	 (let* ((char (code-char term))
		(char-name (char-name char)))
	   (if char-name
	       (princ char-name s)
	     (prin1 char-name s))))
	;; ((consp term) (prin1 (car term) s)) ; nonterminal -- entry on nonterminal-alist
	(t (prin1 term s)))
  #+nomore (write-char #\space s))

(defun print-term-1 (s code grammar)
  (let* ((terminal (find code (grammar-terminals grammar) :key #'terminal-code))
	 (term (terminal-terminal terminal)))
    (if (numberp term)
	(let* ((char (code-char term))
	       (char-name (char-name char)))
	  (if char-name
	      (format s "~a" char-name)
	    (format s "~c" char)))
      (format s "~a" term))))

(defmethod print-object ((nonterminal nonterminal) stream)
  (format stream "[~s]" (nonterminal-symbol nonterminal)))

(defmethod print-object ((prod production) stream)
  (print-production-1 (production-lhs prod) (production-rhs prod) stream))

(defun print-production-1 (lhs rhs stream)
  (pprint-logical-block (stream nil :prefix "[" :suffix "]")
    (princ lhs stream)
    (write-char #\space stream)
    (pprint-newline :miser stream)
    (pprint-indent :block 2 stream)
    (write-string "->" stream)
    (do ((rhs rhs (cdr rhs)))
	((not (consp rhs)))
      (write-char #\space stream)
      (pprint-newline :fill stream)
      ;; The rhs symbol is changed to a cons (symbol . lookaheadv) during grammar build.
      (print-term stream (if (consp (car rhs)) (caar rhs) (car rhs))))))

(defun print-action (stream action)
  (let ((type (car action))
	(arg (cdr action)))
    (case type
      (shift (format stream "Shift ~D" arg))
      (reduce (format stream "Reduce ~S" arg))
      (t (format stream "~a~@[ ~s~]" type arg)))))

#+unused
(defun print-prod (p s d)
  (declare (ignore d))
  (format s "#s(~s :lhs ~s :number ~s"
	  'production (production-lhs p) (production-number p))
  (when (production-plist p)
    (format s " :plist ~s" (production-plist p)))
  (when (consp (production-rhs p))
    (format s " :rhs (")
    (do ((rhs (production-rhs p) (cdr rhs)))
	((not (consp rhs)) (format s ")"))
      (format s "~s " (car rhs))))
  (when (production-action-code p)
    (format s " :action-code ~s" (production-action-code p)))
  (format s ")"))

;;;
;;;
;;;

(defmacro array-dispatch (dispatch symbol index)
  `(let ((v (svref ,dispatch ,symbol)))
     (or (and v (svref v ,index))
	 '(error))))

(defun state-machine (grammar)
  (declare (optimize (speed 3) (safety 0)))
  (or (grammar-goto-table grammar) (construct-grammar-tables grammar))
  (or (grammar-state-stack grammar)
      (setf (grammar-state-stack grammar) (make-array (grammar-initial-stack-size grammar))
	    (grammar-value-stack grammar) (make-array (grammar-initial-stack-size grammar))))
  (setf (grammar-sp grammar) 1)
  (setf (grammar-error grammar) nil)
  (let* ((lexer (or (grammar-lexer grammar) (error "No lexer for ~S" grammar)))
	 (state 0)
	 (state-stack (grammar-state-stack grammar))
	 (value-stack (grammar-value-stack grammar))
	 (stack-len (length state-stack))
	 (sp 1)
	 (action-table (grammar-action-table grammar))
	 (goto-table (grammar-goto-table grammar))
	 (defaults (grammar-defaults grammar))
	 (reduction-args
	  (do ((target (make-sequence 'list (grammar-longest-rhs grammar))
		       (cdr target))
	       (result))
	      ((null target) (cons nil result))
	    (push target result)))
	 token token-type type value action where)
    (setf (svref state-stack 0) 0)
    (setf (svref value-stack 0) nil)
    ;; The theory of error handling inside the parser state machine: If there is a
    ;; grammar-parse-error, just resignal it and let any outer handler deal with it, or
    ;; else enter the debugger.  If some action or IO code signals any other kind of
    ;; error, first resignal it silently and give any outer handler a chance to deal with
    ;; it, or else resignal it noisily using error, allowing entry to the debugger.  This
    ;; annotation makes it easiler for programmers to diagnose exceptions inside the
    ;; state-machine, while not interfering with regular silent condition handling.
    (handler-bind
	((grammar-parse-error (lambda (c) (error c)))) ; Grammar didn't do error recovery.
      (handler-bind
	  ((error (lambda (c)		; Some non-parse error occurred.
		    (setf (grammar-sp grammar) sp)
		    (signal c)		; Give outer handlers a chance to handle.
		    (signal-grammar-error grammar :state state :token token :enclosed-error c))))
	(macrolet ((vcheck ()
		     `(when (= sp stack-len)
			(let* ((new-len (+ sp (ash sp -1)))
			       (new-state-stack (make-array new-len))
			       (new-value-stack (make-array new-len)))
			  (setf (grammar-state-stack grammar) new-state-stack
				(grammar-value-stack grammar) new-value-stack)
			  (loop for i below sp
			      do (setf (svref new-state-stack i) (svref state-stack i)
				       (svref new-value-stack i) (svref value-stack i)))
			  (setf stack-len new-len
				state-stack new-state-stack
				value-stack new-value-stack)))))
	  (loop
	    (unless token
	      (or (setq token-type (and (svref defaults state)
					0))
		  (multiple-value-setq (token-type token where)
		    (funcall lexer grammar))))
	    (setq action
	      (array-dispatch action-table token-type state))
	    (setq type (car action))
	    (setq value (cdr action))
	    (when *yacc-trace*
	      (let* ((*print-length* 2) (*print-level* 2)
		     (term (find token-type (grammar-terminals grammar) :key #'terminal-code))
		     (type (and term (terminal-terminal term))))
		(format t "~&~3d~@[ ~s~]~@[ ~s~]: "
			state
			(unless (numberp type) type)
			token))
	      (print-action t action)
	      (format t "~%"))
	    (case type
	      (accept (return (svref value-stack (decf sp))))
	      (shift (vcheck)
		     (setf (svref value-stack sp) token
			   (svref state-stack sp) value)
		     (incf sp)
		     (setq state value token nil))
	      (reduce
	       (do ((tokens (production-rhs value) (cdr tokens))
		    (args reduction-args)
		    (function (production-action-code value)))
		   ((not (consp tokens))
		    (setq state
		      (array-dispatch goto-table
				      (production-lhs-goto-index value)
				      (svref state-stack (1- sp))))
		    (vcheck)
		    (setf (svref value-stack sp)
		      (if function
			  (apply function grammar (car args))
			(caar args)))
		    (setf (svref state-stack sp) state)
		    (incf sp))
		 (setq args (cdr args))
		 (rplaca (car args) (svref value-stack (decf sp)))))
	      (ireduce
	       (do ((n (production-rhs value) (1- n))
		    (args reduction-args)
		    (function (production-action-code value)))
		   ((= n 0)
		    (setq state
		      (array-dispatch goto-table
				      (production-lhs-goto-index value)
				      (svref state-stack (1- sp))))
		    (vcheck)
		    (setf (svref value-stack sp)
		      (if function
			  (apply function grammar (car args))
			(caar args)))
		    (setf (svref state-stack sp) state)
		    (incf sp))
		 (setq args (cdr args))
		 (rplaca (car args) (svref value-stack (- sp n)))))
	      (error
	       (cond
		((null (grammar-error grammar)) ;Initial entry to error.
		 (when *yacc-trace*
		   (format t "~^syntax error with token ~s in state ~s~%" token state))
		 ;;Search the stack for a state where it is legal to shift an error.
		 (loop with saved-state = state and
		       saved-sp = sp and
		       disp = (svref action-table (grammar-error-code grammar))
		     until (and disp (eq (car (svref disp state)) 'shift))
		     do (when (eql sp 1)
			  ;; Error recovery failed -- restore the machine state at time of error.
			  (setf sp saved-sp
				(grammar-sp grammar) saved-sp
				state saved-state)
			  (signal-grammar-error grammar :token token :state state :where where))
			(decf sp)
			(when *yacc-trace*
			  (format t "~^error recovery discards state ~s uncovering state ~s~%"
				  state (svref state-stack (1- sp))))
			(setq state (svref state-stack (1- sp))))
		 (setq token token-type	;Just to remember the bad token.
		       ;; error pseudo-token becomes input.
		       token-type (grammar-error-code grammar))
		 (when *yacc-trace*
		   (format t "~^continuing error recovery state ~s token ~s token-type ~s~%"
			   state token token-type))
		 (setf (grammar-error grammar) 'discarding))
		(t
		 (when *yacc-trace*
		   (format t "~&error recovery discards token ~s ~s~%" token-type token))
		 (when (eq token 'eof)	; Give up if eof doesn't lead to accept!
		   (setf (grammar-sp grammar) sp)
		   (signal-grammar-error grammar :token token :state state :where where))
		 (setq token nil))))
	      ((nil)
	       (setf (grammar-sp grammar) sp)
	       (signal-grammar-error grammar :token token :state state :where where)
	       (error "the lexer for grammar ~s in state ~s returned an illegal token: ~s ~s~%"
		      grammar state token token-type)
	       ))))))))

(defun state-machine-for-debugging (grammar)
  (or (grammar-goto-table grammar) (construct-grammar-tables grammar))
  (or (grammar-state-stack grammar)
      (setf (grammar-state-stack grammar) (make-array (grammar-initial-stack-size grammar))
	    (grammar-value-stack grammar) (make-array (grammar-initial-stack-size grammar))))
  (setf (grammar-sp grammar) 1)
  (setf (grammar-error grammar) nil)
  (let* ((lexer (or (grammar-lexer grammar) (error "No lexer for ~S" grammar)))
	 (known-lexemes (grammar-known-lexemes grammar))
	 (lexeme-limit (length known-lexemes))
	 (state 0)
	 (state-stack (grammar-state-stack grammar))
	 (value-stack (grammar-value-stack grammar))
	 (stack-len (length state-stack))
	 (sp 1)
	 (action-table (grammar-action-table grammar))
	 (goto-table (grammar-goto-table grammar))
	 (defaults (grammar-defaults grammar))
	 (reduction-args
	  (do ((target (make-sequence 'list (grammar-longest-rhs grammar))
		       (cdr target))
	       (result))
	      ((null target) (cons nil result))
	    (push target result)))
	 token token-type type value action where)
    (setf (svref state-stack 0) 0)
    (setf (svref value-stack 0) nil)
    ;; The theory of error handling inside the parser state machine: If there is a
    ;; grammar-parse-error, just resignal it and let any outer handler deal with it,
    ;; or else enter the debugger.  If some action or IO code signals any other kind
    ;; of error, first resignal it silently and give any outer handler a chance to
    ;; deal with it, or else resignal it noisily using error, allowing entry to the
    ;; debugger.  This annotation makes it easiler for programmers to diagnose
    ;; exceptions inside the state-machine, while not interfering with regular silent
    ;; condition handling.
    (handler-bind
	((grammar-parse-error (lambda (c) (error c)))) ; Grammar didn't do error recovery.
      (handler-bind
	  ((error (lambda (c)		; Some non-parse error occurred.
		    (setf (grammar-sp grammar) sp)
		    (signal c)		; Give outer handlers a chance to handle.
		    (signal-grammar-error grammar :state state :token token :enclosed-error c))))
	(macrolet ((vcheck ()
		     `(when (= sp stack-len)
			(let* ((new-len (+ sp (ash sp -1)))
			       (new-state-stack (make-array new-len))
			       (new-value-stack (make-array new-len)))
			  (setf (grammar-state-stack grammar) new-state-stack
				(grammar-value-stack grammar) new-value-stack)
			  (loop for i below sp
			      do (setf (svref new-state-stack i) (svref state-stack i)
				       (svref new-value-stack i) (svref value-stack i)))
			  (setf stack-len new-len
				state-stack new-state-stack
				value-stack new-value-stack)))))
	  (loop
	    (unless token
	      (or (setq token-type (and (svref defaults state)
					0))
		  (multiple-value-setq (token-type token where)
		    (funcall lexer grammar))
		  (unless (and (integerp token-type)
			       (>= token-type 0)
			       (< token-type lexeme-limit)
			       (sbit known-lexemes token-type))
		    (error "lexer for ~s returned an unknown token: ~s" token-type token))))
	    (setq action
	      (array-dispatch action-table token-type state))
	    (setq type (car action))
	    (setq value (cdr action))
	    (when *yacc-trace*
	      (let* ((*print-length* 2) (*print-level* 2)
		     (term (find token-type (grammar-terminals grammar) :key #'terminal-code))
		     (type (and term (terminal-terminal term))))
		(format t "~&~3d~@[ ~s~]~@[ ~s~]: "
			state
			(unless (numberp type) type)
			token))
	      (print-action t action)
	      (format t "~%"))
	    (case type
	      (accept (return (svref value-stack (decf sp))))
	      (shift (vcheck)
		     (setf (svref value-stack sp) token
			   (svref state-stack sp) value)
		     (incf sp)
		     (setq state value token nil))
	      (reduce
	       (do ((tokens (production-rhs value) (cdr tokens))
		    (args reduction-args)
		    (function (production-action-code value)))
		   ((not (consp tokens))
		    (setq state
		      (array-dispatch goto-table
				      (production-lhs-goto-index value)
				      (svref state-stack (1- sp))))
		    (vcheck)
		    (setf (svref value-stack sp)
		      (if function
			  (apply function grammar (car args))
			(caar args)))
		    (setf (svref state-stack sp) state)
		    (incf sp))
		 (setq args (cdr args))
		 (rplaca (car args) (svref value-stack (decf sp)))))
	      (ireduce
	       (do ((n (production-rhs value) (1- n))
		    (args reduction-args)
		    (function (production-action-code value)))
		   ((= n 0)
		    (setq state
		      (array-dispatch goto-table
				      (production-lhs-goto-index value)
				      (svref state-stack (1- sp))))
		    (vcheck)
		    (setf (svref value-stack sp)
		      (if function
			  (apply function grammar (car args))
			(caar args)))
		    (setf (svref state-stack sp) state)
		    (incf sp))
		 (setq args (cdr args))
		 (rplaca (car args) (svref value-stack (- sp n)))))
	      (error
	       (cond
		((null (grammar-error grammar)) ;Initial entry to error.
		 (when *yacc-trace*
		   (format t "~^syntax error with token ~s in state ~s~%" token state))
		 ;;Search the stack for a state where it is legal to shift an error.
		 (loop with saved-state = state and
		       saved-sp = sp and
		       disp = (svref action-table (grammar-error-code grammar))
		     until (and disp (eq (car (svref disp state)) 'shift))
		     do (when (eql sp 1)
			  ;; Error recovery failed -- restore the machine state at time of error.
			  (setf sp saved-sp
				(grammar-sp grammar) saved-sp
				state saved-state)
			  (signal-grammar-error grammar :token token :state state :where where))
			(decf sp)
			(when *yacc-trace*
			  (format t "~^error recovery discards state ~s uncovering state ~s~%"
				  state (svref state-stack (1- sp))))
			(setq state (svref state-stack (1- sp))))
		 (setq token token-type	;Just to remember the bad token.
		       ;; error pseudo-token becomes input.
		       token-type (grammar-error-code grammar))
		 (when *yacc-trace*
		   (format t "~^continuing error recovery state ~s token ~s token-type ~s~%"
			   state token token-type))
		 (setf (grammar-error grammar) 'discarding))
		(t
		 (when *yacc-trace*
		   (format t "~&error recovery discards token ~s ~s~%" token-type token))
		 (when (eq token 'eof)	; Give up if eof doesn't lead to accept!
		   (setf (grammar-sp grammar) sp)
		   (signal-grammar-error grammar :token token :state state :where where))
		 (setq token nil))))
	      ((nil)
	       (setf (grammar-sp grammar) sp)
	       (signal-grammar-error grammar :token token :state state :where where)
	       (error "the lexer for grammar ~s in state ~s returned an illegal token: ~s ~s~%"
		      grammar state token token-type)
	       ))))))))

(define-condition grammar-parse-error (parse-error simple-error)
  ((grammar        :accessor grammar-parse-error-grammar        :initarg :grammar)
   (source         :accessor grammar-parse-error-source         :initarg :source)
   (state          :accessor grammar-parse-error-state          :initarg :state)
   (token          :accessor grammar-parse-error-token          :initarg :token)
   (position       :accessor grammar-parse-error-position       :initarg :position)
   (enclosed-error :accessor grammar-parse-error-enclosed-error :initarg :enclosed-error))
  (:report grammar-parse-error-printer))

;; This can be invoked by call-next-method from a more-specialized method.
(defun grammar-parse-error-printer (x stream)
  (with-slots (grammar state token position enclosed-error)
      x
    (with-slots (state-stack value-stack sp)
	(grammar-parse-error-grammar x)
      (or
       (ignore-errors
	(when enclosed-error
	  (format stream
		  "grammar ~s signalled an unhandled error~@[ at source position ~d~]:~%   ~a~%"
		  grammar position enclosed-error)
	  t))
       (format
	stream
	"grammar ~a~@[ in state ~s~] detected error~@[ on token ~s~]~@[ at source position ~d~]"
	grammar state token position))
      (when (and *yacc-trace* state-stack)
	(format stream "~& State/Value Stack~%")
	(loop for i downfrom (1- sp) to 0
	    do (format stream "~5d   ~s~%" (aref state-stack i) (aref value-stack i))))
      )))

(defmethod signal-grammar-error ((grammar grammar) &key token where state enclosed-error)
  (error 'grammar-parse-error
	 :grammar grammar
	 :state state
	 :token token
	 :position (or where
		       (funcall (grammar-lexer grammar) grammar
				:report-location))
	 :enclosed-error enclosed-error))
