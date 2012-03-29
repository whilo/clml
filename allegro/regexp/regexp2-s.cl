;; -*- mode: common-lisp; package: regexp -*-
;;
;; regexp.cl - regexp package definition
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
;; $Id: regexp2-s.cl,v 2.2 2007/04/17 21:27:39 layer Exp $

(in-package :common-lisp-user)

(defpackage :regexp ;;NOTE: package name hardwired in regexp-vm.cl
  (:use #:cl #:yacc)
  #+ignore
  (:import-from #:excl
		#:match-re #:compile-re #:replace-re #:split-re
		#:re-submatch #:re-lambda #:re-let #:re-case #:parse-re
		#:quote-re)
  (:export #:match-re
           #:compile-re
           #:replace-re
           #:split-re
	   #:quote-re
           #:re-submatch
           #:re-lambda
           #:re-let
           #:re-case
	   #:parse-re
           #:native
	   #:vm))

(provide :regexp2-s)

(in-package :regexp)

(eval-when (compile load eval)
  (declaim (special *regexp-back-end*))
  (setq *regexp-back-end* 'vm)
  )

;; The char-set is represented by a list of ranges.
;; It also has slots for bitvector, but that's merely a cache.
;; The bitvector part should be updated explicitly by
;; char-set-update-bitvector if ranges is modified.

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

(defun char-set-print (cset port indent)
  (declare (ignore indent))
  (format port "#S(char-set :ranges ~a)"
          (char-set-ranges cset)))

;; Represents compiled regular expression
(defstruct (regular-expression
            (:constructor make-regular-expression (matcher
                                                   source
                                                   return-type
                                                   num-submatches
                                                   named-submatches)))
  matcher               ;; closure of compiled regexp
  source                ;; the original regexp string
  return-type           ;; return type given at the compilation time
  num-submatches        ;; number of submatches
  named-submatches      ;; list of (<name> <submatch#> ...)
  )

;; Packs regexp match information.  Returned by match-re with
;; :return :match argument.
(defstruct (regular-expression-match
            (:constructor make-regular-expression-match (indexes
                                                         input
                                                         num-submatches
                                                         named-submatches)))
  indexes              ;; mached indexes
  input                ;; input string
  num-submatches       ;; number of submatches
  named-submatches     ;; list of (<name> <submatch#> ...)
  )

#+allegro
(define-compiler-macro match-re (regexp input
				 &whole form
				 &rest args
				 &key (return :string)
				      case-fold
				      single-line
				      multiple-lines
				      ignore-whitespace
				      start
				      end
				      (back-end *regexp-back-end*)
				 &environment e)
  (let ((args (list return case-fold single-line multiple-lines ignore-whitespace)))
    (cond
     ((and (constantp regexp e)
	   (progn (setf regexp (excl::constant-value regexp e))
		  (or (stringp regexp)
		      (characterp regexp)
		      (consp regexp)))
	   (every (lambda (v) (constantp v e)) args))
      (let ((make-re-args (apply #'compile-re regexp
				 :for-load-time t
				 :back-end back-end
				 (mapcan #'list
					 '(:return :case-fold :single-line
					   :multiple-lines :ignore-whitespace)
					 (mapcar (lambda (arg) (excl::constant-value arg e))
						 args)))))
	`(funcall (load-time-value
		   (regular-expression-matcher
		    (apply 'make-vm-closure
			   ',make-re-args)))
		  ,input ,start ,end ,return)))
     (t form))))
