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
;; $Id: package.cl,v 1.19 2007/04/17 21:51:47 layer Exp $

(eval-when (compile eval load)
  (require :regexp2-s)
  (require :yacc))

(in-package :common-lisp-user)

(defpackage :regexp ;;NOTE: package name hardwired in regexp-vm.cl
  (:use #:cl #:yacc #:excl)
  #+allegro
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

(provide :regexp2)
