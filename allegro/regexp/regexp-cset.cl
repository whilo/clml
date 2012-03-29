;; -*- mode: common-lisp; package: regexp -*-
;;
;; regexp-cset.cl - Character-set implementation
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
;; $Id: regexp-cset.cl,v 1.11 2007/04/17 21:51:47 layer Exp $

(in-package :regexp)

;;;
;;; Character set library
;;;

;; The char-set is represented by a list of ranges.
;; It also has slots for bitvector, but that's merely a cache.
;; The bitvector part should be updated explicitly by
;; char-set-update-bitvector if ranges is modified.

;; Moved to regexp2-s in 8.1:
(defstruct (char-set (:print-function char-set-print))
  ranges                                ; list of (lo . hi), inclusive
  bitvector                             ; bitmap for char-set; see below.
  bitvector-type                        ; type of bitmap vector.  can be:
                                        ;   cs7  - 128 bits
                                        ;   cs7+ - 128 bits
                                        ;   cs8  - 256 bits
                                        ;   cs8+ - 256 bits inverted
                                        ;   cs16 - 65536 bits
                                        ; for cs7+ and cs8+, chars outside
                                        ; the bitvector is included in the
                                        ; char-set.
  )

;; Moved to regexp2-s in 8.1:
(defun char-set-print (cset port indent)
  (declare (ignore indent))
  (format port "#S(char-set :ranges ~a)"
          (char-set-ranges cset)))

(defmethod make-load-form ((x char-set) &optional e) ;bug14767
  (make-load-form-saving-slots x :environment e))

(defun char-set-num-ranges (cset)
  (length (char-set-ranges cset)))

;; Are there system-provided constant for this?
(defconstant +char-code-max+ 65535)

;; internal routines
(defun %char-set-add-ranges (range ranges)
  (cond ((null ranges) (list range))
        ((< (1+ (cdr range)) (caar ranges))
         ;; <--range-->
         ;;              <--(car ranges)--> ...
         (cons range ranges))
        ((< (1+ (cdar ranges)) (car range))
         ;;                    <--range-->
         ;; <--(car ranges)-->   ....
         (cons (car ranges) (%char-set-add-ranges range (cdr ranges))))
        ((< (caar ranges) (car range))
         (if (< (cdar ranges) (cdr range))
             ;;       <-----range----->
             ;; <--(car ranges)-->
             (%char-set-add-ranges (cons (caar ranges) (cdr range))
                        (cdr ranges))
           ;;    <--range-->
           ;; <--(car ranges)-->
           ranges))
        (t
         (if (< (cdr range) (cdar ranges))
             ;; <---range--->
             ;;   <--(car ranges)-->
             (cons (cons (car range) (cdar ranges))
                   (cdr ranges))
           ;; <------range-------->
           ;;   <--(car ranges)->
           (%char-set-add-ranges range (cdr ranges))))))

(defun %char-set-sub-ranges (range ranges)
  (cond ((null ranges) nil)
        ((< (cdr range) (caar ranges))
         ;; <--range-->
         ;;              <--(car ranges)--> ...
         ranges)
        ((< (cdar ranges) (car range))
         ;;                    <--range-->
         ;; <--(car ranges)-->   ....
         (cons (car ranges) (%char-set-sub-ranges range (cdr ranges))))
        ((< (caar ranges) (car range))
         (if (<= (cdar ranges) (cdr range))
             ;;       <-----range----->
             ;; <--(car ranges)-->
             (cons (cons (caar ranges) (1- (car range)))
                   (%char-set-sub-ranges range (cdr ranges)))
           ;;    <--range-->
           ;; <--(car ranges)-->
           (list* (cons (caar ranges) (1- (car range)))
                  (cons (1+ (cdr range)) (cdar ranges))
                  (cdr ranges))))
        (t
         (if (< (cdr range) (cdar ranges))
             ;; <---range--->
             ;;   <--(car ranges)-->
             (cons (cons (1+ (cdr range)) (cdar ranges))
                   (cdr ranges))
           ;; <------range-------->
           ;;   <--(car ranges)->
           (%char-set-sub-ranges range (cdr ranges))))))

(defun %char-set-range-op (cset op objs)
  (labels ((rec (objs r)
             (if (null objs)
                 r
               (etypecase (car objs)
                 (character
                  (let ((code (char-code (car objs))))
                    (rec (cdr objs) (funcall op (cons code code) r))))
                 (char-set
                  (rec (cdr objs)
                       (rec (char-set-ranges (car objs)) r)))
                 (cons
                  (let ((lo (ccode (caar objs)))
                        (hi (ccode (cdar objs))))
                    (when (> lo hi)
                      (error "In regexp range low limit ~a higher than ~a."
                             lo hi))
                    (rec (cdr objs)
                         (funcall op (cons lo hi) r)))))))
           (ccode (c)
             (etypecase c
               (character (char-code c))
               (integer c))))
    (setf (char-set-ranges cset) (rec objs (char-set-ranges cset)))
    cset))

;; Constructor
(defun char-set (&rest objs)
  (let ((cset (make-char-set)))
    (apply #'char-set-add! cset objs)
    cset))

(defun char-set-copy (cset)
  (let ((cset2 (make-char-set)))
    (setf (char-set-ranges cset2)
      (copy-list (char-set-ranges cset)))
    cset2))

(defun char-set-add! (cset &rest objs)
  (%char-set-range-op cset #'%char-set-add-ranges objs))

(defun char-set-add (cset &rest objs)
  (apply #'char-set-add! (char-set-copy cset) objs))

(defun char-set-subtract! (cset &rest objs)
  (%char-set-range-op cset #'%char-set-sub-ranges objs))

(defun char-set-subtract (cset &rest objs)
  (apply #'char-set-subtract! (char-set-copy cset) objs))

(defun char-set-complement! (cset)
  (labels ((rec (prev ranges)
             (cond ((null ranges)
                    (if (>= prev +char-code-max+)
                        nil
                      (list (cons prev +char-code-max+))))
                   ((< prev (caar ranges))
                    (cons (cons prev (1- (caar ranges)))
                          (rec (1+ (cdar ranges)) (cdr ranges))))
                   (t
                    (rec (1+ (cdar ranges)) (cdr ranges))))))
    (setf (char-set-ranges cset)
      (rec 0 (char-set-ranges cset))))
  cset)

(defun char-set-complement (cset)
  (char-set-complement! (char-set-copy cset)))

(defun char-set-has-char-p (cset char)
  (loop with cc = (char-code char)
      for r in (char-set-ranges cset)
      if (<= (car r) cc (cdr r)) do (return t)))

;; calculate bitvector for the char-set.
(defun char-set-update-bitvector (cset)
  (let* ((ranges (char-set-ranges cset))
         (erange (car (last ranges))))
    (if (null ranges)
        (progn
          (setf (char-set-bitvector cset) nil)
          (setf (char-set-bitvector-type cset) nil))
      (labels ((fill-bits (bv limit)
                 (loop for (lo . hi) in ranges
                     while (< lo limit)
                     do (loop for k from lo to hi
                            while (< k limit)
                            do (setf (sbit bv k) 1))))
               (make-bitx (size)
                 (let ((bv (make-array (list size)
                                       :element-type 'bit
                                       :initial-element 0)))
                   (fill-bits bv size)
                   bv)))
        (cond
         ((< (cdr erange) 128)
          (setf (char-set-bitvector-type cset) 'cs7)
          (setf (char-set-bitvector cset) (make-bitx 128)))
         ((< (cdr erange) 256)
          (setf (char-set-bitvector-type cset) 'cs8)
          (setf (char-set-bitvector cset) (make-bitx 256)))
         ((and (= (cdr erange) +char-code-max+)
               (<= (car erange) 256))
          (cond ((<= (car erange) 128)
                 (setf (char-set-bitvector-type cset) 'cs7+)
                 (setf (char-set-bitvector cset) (make-bitx 128)))
                (t
                 (setf (char-set-bitvector-type cset) 'cs8+)
                 (setf (char-set-bitvector cset) (make-bitx 256)))))
         (t
          (setf (char-set-bitvector-type cset) 'cs16)
          (setf (char-set-bitvector cset) (make-bitx 65536)))))
      ))
  cset)

(defun char-set-ensure-bitvector (cset)
  (when (null (char-set-bitvector cset))
    (char-set-update-bitvector cset))
  (when (null (char-set-bitvector cset))
    (error "encountered an empty character set: ~s~%" cset))
  cset)

;; pre-defined character sets.  should be created at compile time.
;; also need to consider Unicode.

(defparameter *char-set-alpha*
    (char-set-update-bitvector
     (char-set '(#\A . #\Z) '(#\a . #\z) `(128 . ,+char-code-max+))))

(defparameter *char-set-digit*
    (char-set-update-bitvector
     (char-set '(#\0 . #\9))))

(defparameter *char-set-xdigit*
    (char-set-update-bitvector
     (char-set '(#\0 . #\9) '(#\A . #\F) '(#\a . #\f))))

(defparameter *char-set-alnum*
    (char-set-update-bitvector
     (char-set-add *char-set-alpha* *char-set-digit*)))

(defparameter *char-set-ascii*
    (char-set-update-bitvector
     (char-set '(0 . 127))))

(defparameter *char-set-blank*
    (char-set-update-bitvector
     (char-set #\Space #\Tab)))

(defparameter *char-set-cntrl*
    (char-set-update-bitvector
     (char-set '(0 . 31) #\Delete)))

(defparameter *char-set-space*
    (char-set-update-bitvector
     (char-set #\Space #\Tab #\Newline #\Return #\Page #\Vt)))

(defparameter *char-set-graph*
    (char-set-update-bitvector
     (char-set '(32 . 126))))

(defparameter *char-set-punct*
    (char-set-update-bitvector
     (char-set-subtract *char-set-graph* *char-set-alnum*)))

(defparameter *char-set-print*
    (char-set-update-bitvector
     (char-set-add *char-set-graph* *char-set-space*)))

(defparameter *char-set-upper*
    (char-set-update-bitvector
     (char-set '(#\A . #\Z))))

(defparameter *char-set-lower*
    (char-set-update-bitvector
     (char-set '(#\a . #\z))))

(defparameter *char-set-word*
    (char-set-update-bitvector
     (char-set-add *char-set-alnum* #\_)))

(defparameter *char-set-word-complement*
    (char-set-update-bitvector
     (char-set-complement *char-set-word*)))

(defparameter *char-set-digit-complement*
    (char-set-update-bitvector
     (char-set-complement *char-set-digit*)))

(defparameter *char-set-space-complement*
    (char-set-update-bitvector
     (char-set-complement *char-set-space*)))

(defparameter *char-set-except-newline*
    (char-set-update-bitvector
     (char-set-complement! (char-set #\Newline))))

;; make given cset case-insensitive
;; TODO: unicode.  efficiency.
(defun char-set-uncase! (cset)
  (let* ((filter-lower (char-set-complement! (char-set '(#\a . #\z))))
         (filter-upper (char-set-complement! (char-set '(#\A . #\Z))))
         (lower (char-set-subtract cset filter-lower))
         (upper (char-set-subtract cset filter-upper))
         (lower* (mapcar #'(lambda (c) (cons (- (car c) 32) (- (cdr c) 32)))
                         (char-set-ranges lower)))
         (upper* (mapcar #'(lambda (c) (cons (+ (car c) 32) (+ (cdr c) 32)))
                         (char-set-ranges upper)))
         )
    (apply #'char-set-add! cset lower*)
    (apply #'char-set-add! cset upper*)))

(defun char-set-uncase (cset)
  (char-set-uncase! (char-set-copy cset)))

;; returns t if given character sets or characters doesn't overlap.
;; each 'cs' may be a char-set, a character, nil, 'any, 'any-except-newline.
(defun char-set-exclusive-p (cs1 cs2 &rest more-cs)
  (labels ((cs-vs-cs (cs1 cs2)
             (loop with r0 = (char-set-ranges cs1)
                 with r1 = (char-set-ranges cs2)
                 unless (and r0 r1) do (return t) end
                 if      (< (cdar r0) (caar r1)) do (pop r0)
                 else if (< (cdar r1) (caar r0)) do (pop r1)
                 else do (return nil)))
           (cs-vs-char (cs1 ch)
             (loop with cc = (char-code ch)
                 with r0 = (char-set-ranges cs1)
                 unless r0 do (return t) end
                 when (<= (caar r0) cc (cdar r0)) do (return nil) end
                 do (pop r0)))
           (exclusivep (c1 c2)
             (or
              (null c1)
              (null c2)
              (typecase c1
                (character
                 (typecase c2
                   (character (not (char= c1 c2)))
                   (char-set  (cs-vs-char c2 c1))
                   (symbol    (if (eq c2 'any) nil
                                (cs-vs-char *char-set-except-newline* c1)))))
                (char-set
                 (typecase c2
                   (character (cs-vs-char c1 c2))
                   (char-set  (cs-vs-cs c1 c2))
                   (symbol    (if (eq c2 'any) nil
                                (cs-vs-cs c1 *char-set-except-newline*)))))
                (symbol
                 (if (eq c1 'any) nil
                   (exclusivep *char-set-except-newline* c2))))))
           )
    (if (null more-cs)
        (exclusivep cs1 cs2)
      (and (exclusivep cs1 cs2)
           (every (lambda (x) (exclusivep cs1 x)) more-cs)
           (apply #'char-set-exclusive-p cs2 more-cs)))))


;; convert AST char representation to char-set
(defun char-class->char-set (class)
  (ecase class
    (:word-char-class           *char-set-word*)
    (:digit-class               *char-set-digit*)
    (:whitespace-char-class     *char-set-space*)
    (:non-word-char-class       *char-set-word-complement*)
    (:non-digit-class           *char-set-digit-complement*)
    (:non-whitespace-char-class *char-set-space-complement*)))

(defun char-range->char-set (complement ci members)
  (loop with cs = (char-set)
      for m in members
      do
        (etypecase m
	  (character
	   (char-set-add! cs m))
          (integer
           (char-set-add! cs (code-char m)))
          (cons
	   (unless (and (eq (car m) :range)
			(consp (cdr m))
			(consp (cddr m))
			(null (cdddr m)))
	     (error "A :char-class has incorrect syntax: " m))
	   (pop m)
	   (char-set-add! cs (cons (if (characterp (car  m)) (char-code (car  m)) (car  m))
				   (if (characterp (cadr m)) (char-code (cadr m)) (cadr m)))))
	  (symbol
	   (char-set-add! cs (char-class->char-set m))))
      finally (let ((cs (if ci (char-set-uncase! cs) cs)))
                (return (if complement
                            (char-set-complement! cs)
                          cs)))))

;;;
;;; Steve's original code follows.
;;;

(deftype regexp-dim () #+excl 'excl::adim #-excl 'fixnum)

(eval-when (compile load eval)

(defun normalize-class-stuff (members ignore-case)
  (let ((upper-limit 0)
	tests)
    (multiple-value-bind (chars classes)
	(loop for item in members
	    do (when (characterp item) (setq item (char-code item)))
	    when (consp item)
	    do (setq item
		 (cons (if (characterp (car item)) (char-code (car item)))
		       (if (characterp (cdr item)) (char-code (cdr item)))))
	    and
	    if (numberp (car item))
	    collect (if (<= (car item) (cdr item))
			item
		      (error "In regexp range low limit ~d higher than high ~d"
			     (car item) (cdr item)))
	    into chars
	    else collect item into classes
	    else collect (cons item item) into chars
	    finally (return (values chars classes)))
      ;; Ignore-case explosion.  We try to do this efficiently, although the later merge
      ;; phase will catch adjacencies missed here.  The theory is that nearly all discrete
      ;; character ranges of case-discriminable chars translate to a similarly discrete
      ;; range.
      (when ignore-case
	(loop for (nlow . nhih) in chars as low = (code-char nlow) and hih = (code-char nhih)
	    if (eql low hih)
	    do (if (lower-case-p low)
		   (push (let ((x (char-code (char-upcase   low)))) (cons x x)) chars))
	       (if (upper-case-p low)
		   (push (let ((x (char-code (char-downcase low)))) (cons x x)) chars))
	    else
	      ;; Here is a simple, unreliable version.  It assumes that every range of
	      ;; case-sensitive characters translates to an equivelent range of characters
	      ;; bounded by the translated end points.  This assumption is known not to be
	      ;; true for certain weird character ranges, and is certainly true for ranges
	      ;; that aren't entirely within a single range of upper- or lower-case chars.
	    do (if (lower-case-p low)
		   (if (lower-case-p hih)
		       (push (cons (char-code (char-upcase low))
				   (char-code (char-upcase hih)))
			     chars)
		     (warn "weird case in char range [~c-~c]" low hih))
		 (if (upper-case-p low)
		     (if (upper-case-p hih)
			 (push (cons (char-code (char-downcase low))
				     (char-code (char-downcase hih)))
			       chars)
		       (warn "weird case in char range [~c-~c]" low hih))))))
      ;; Sort on initial char code.
      (setf chars (sort chars #'< :key #'car))
      ;; Now merge entries that can be merged.
      (setf chars
	(loop for (elt1 elt2) on chars
	    if (and elt2 (>= (1+ (cdr elt1)) (car elt2)))
	    do (setf (car elt2) (car elt1))
	    else collect elt1
	    and do (setf upper-limit (cdr elt1))))
      ;; chars is now a sorted merged list of conses of (low . hih) char codes.
      ;; Determine how many discrete tests would be necessary to discriminate.
      (setf tests (loop for item in chars
		      sum (if (eql (car item) (cdr item)) 1 2)))
      (values chars tests upper-limit classes))))

)

(eval-when (compile load eval)

(defun prebuild-class-bitmap (size items)
  (declare (optimize (speed 3) (safety 0)))
  (let ((bitmap (make-array size :element-type 'bit :initial-element 0)))
    (declare (type simple-bit-vector bitmap))
    (loop for (low . hih) in items
	do (loop for i from low to hih
	       do (setf (aref bitmap i) 1)))
    bitmap))

)

(eval-when (compile)
  (compile 'normalize-class-stuff)
  (compile 'prebuild-class-bitmap))

(defparameter .whitespace-char.
    (destructuring-bind (op &rest stuff) (parse-re "[ \\n\\r\\t\\f]")
      (declare (ignore op))
      (multiple-value-bind (stuff tests upper-limit classes)
	  (normalize-class-stuff stuff nil)
	(declare (ignore tests classes))
	(prebuild-class-bitmap (1+ upper-limit) stuff))))

(defparameter .digit-class.
    (destructuring-bind (op &rest stuff) (parse-re "[0-9]")
      (declare (ignore op))
      (multiple-value-bind (stuff tests upper-limit classes)
	  (normalize-class-stuff stuff nil)
	(declare (ignore tests classes))
	(prebuild-class-bitmap (1+ upper-limit) stuff))))

(defparameter .word-class.
    (destructuring-bind (op &rest stuff) (parse-re "[a-zA-Z0-9_]")
      (declare (ignore op))
      (multiple-value-bind (stuff tests upper-limit classes)
	  (normalize-class-stuff stuff nil)
	(declare (ignore tests classes))
	(prebuild-class-bitmap (1+ upper-limit) stuff))))

(defun expand-class-ref (char bitmap complement end-ok)
  `(,@(if end-ok `(or (null ,char)) `(and ,char))
      (let ((cc (char-code ,char))
	    (bitmap ,bitmap))
	(declare (type regexp-dim cc) (simple-bit-vector bitmap))
	,(if complement
	     `(or (not (<= cc ,(length bitmap)))
		  (not (eql 1 (aref bitmap cc))))
	   `(and (<= cc ,(length bitmap))
		 (eql 1 (aref bitmap cc)))))))

(defun make-class-bitmap (size items)
  (declare (optimize (speed 3) (safety 0)))
  (let ((bitmap (make-array size :element-type 'bit :initial-element 0)))
    (declare (type simple-bit-vector bitmap))
    (loop for (low . hih) in items
	do (loop for i from low to hih
	       do (setf (aref bitmap i) 1)))
    bitmap))


