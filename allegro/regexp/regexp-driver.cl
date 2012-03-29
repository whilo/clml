;; -*- mode: common-lisp; package: regexp -*-
;;
;; regexp-driver.cl - high-level regexp APIs
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
;; $Id: regexp-driver.cl,v 1.35 2007/04/17 21:51:47 layer Exp $

(defpackage :regexp ;;NOTE: package name hardwired in regexp-vm.cl
  (:use #:cl)
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

(in-package :regexp)

(eval-when (compile eval load)
  (defvar *regexp-back-end* 'vm)
  (defvar *test-log-output* nil)
  )


;;; This file defines the high-level API that user sees.
;;;    compile-re
;;;    match-re
;;;    replace-re
;;;    split-re
;;;    quote-re
;;;    re-submatch
;;;    re-lambda
;;;    re-let
;;;    re-case

;;; Back-end API:
;;;
;;;   A new back-end compiler has to define a property function
;;;   'regexp-back-end to the symbol that designates the back-end
;;;   implementation, e.g. for 'vm' back-end, it defines the function
;;;   (:property regexp-back-end vm).
;;;
;;;   The compiler function is called with the following signature.
;;;
;;;      (code
;;;       &key num-submatches
;;;            num-repetitions
;;;            minimum-length
;;;            lookahead-set
;;;            return-type)
;;;
;;;   CODE is a list of pseudo insturctions; see regexp-fe.cl for the
;;;   specification.
;;;   NUM-SUBMATCHES and NUM-REPETITIONS are the number of submatch registers
;;;   and the number of repetition registers, respectively.
;;;   RETURN-TYPE is the requested return type (nil, :string, or :index).
;;;   It may be :unknown, which indicates the compiled regexp should accept
;;;   return keyword arguments at matching time.
;;;
;;;   What the compiler returns is a closure that takes four fixed
;;;   arguments, INPUT, START, END, and RETURN-TYPE.
;;;
;;;   INPUT is a input string to match, and START and END are the indexes
;;;   into INPUT to specify the range of input.   NIL as START means the
;;;   beginning of INPUT, and NIL as END means the end of the INPUT.
;;;   The closure must check the validity of those arguments.
;;;   RETURN-TYPE may be nil, :string or :index.  It only matters when
;;;   the :return keyword argument isn't given at the compilation time.
;;;   If the compiled regexp already "knows" the return type, it can
;;;   just ignore RETURN-TYPE argument.

;;=================================================================
;; regexp structure
;;

(eval-when (compile eval load)

;; Represents compiled regular expression
;; moved to cl/src/code/regexp2-s.cl in 8.1:
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
;; moved to cl/src/code/regexp2-s.cl in 8.1:
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

(eval-when (compile load eval)

(defun make-vm-closure (code string-or-tree return nsubs names back-end args)
  (let ((be (get 'regexp-back-end back-end)))
    (unless be
      (error "unknown back-end type: ~s" back-end))
    (make-regular-expression (apply be code args)
			     string-or-tree return nsubs names)))
  
)

;;=================================================================
;; compile & match basic API
;;

(defun compile-re (string-or-tree
		   &key case-fold
			ignore-whitespace
			multiple-lines
			single-line
			(return :unknown)
			(back-end *regexp-back-end*)
			for-load-time)
  "Given a STRING or regexp tree that describes a regular expression,
creates a closure that works as a regexp matcher.

The keyword argument CASE-FOLD controls whether the result matcher becomes
case-sensitive or not by default.  (The 'i' flag of Perl RE).

If the keyword argument IGNORE-WHITESPACE is given and true, whitespace
characters within STRING are ignored as regexp spec.  (The 'x' flag of Perl
RE).

If the keyword argument MULTIPLE-LINES is given and true, the created
matcher recognizes multiple lines, i.e. ^ and $ matches beginning and end
of individual lines.  Without this argument, ^ and $ matches only beginning
and end of the input string. (The 'm' flag of Perl RE).

If the keyword argument SINGLE-LINE is given and true, '.' will match any
character including newline.  Without SINGLE-LINE, '.' matches any
character except newline.  (The 's' flag of Perl RE).

The keyword argument BACK-END can be either regexp:native or regexp:vm.
If it is regexp:native, the compiled regexp code is a native code;
which runs fast, but it takes more time to compile.  If it is regexp:vm,
the compiled regexp code is a instruction sequence of a virtual machine to
match the input string.

The keyword argument RETURN specifies how the created matcher returns the
result. If it is NIL, the matcher will return only a boolean value
indicates whether the input string matches the regexp or not.  If it is
:string, it also returns the substrings of matched region and all
submatches of the input string.  If it is :index, the matcher returns pairs
of start and end index of matched region and all submatches.  If the
keyword argument isn't given at compile time, the matcher is created so
that it will accept :return keyword argument at the matching time;
however, compile-re will generate more efficient code if it knows the
return type at the compile time.

Returns a compiled regexp object.
 "
  (let ((.ignore-case. case-fold)
        (.single-line. single-line)
        (.multiple-lines. multiple-lines)
        (.ignore-whitespace. ignore-whitespace))
    (multiple-value-bind (code nsubs nreps stackp minlen fixed laset names)
        (fe-compile-regexp (if (stringp string-or-tree)
			       (parse-re string-or-tree :extended-mode ignore-whitespace)
			     string-or-tree)
                           return)
      (declare (ignore fixed))
      (when *test-log-output*
        (format *test-log-output*
                "Regexp /~a/  minlen ~s%~
                 code: ~/regexp:print-fe/~%"
                string-or-tree minlen code))
      ;; The for-load-time boolean is for use by the compiler macro, to defer creation of
      ;; the vm closure until load time.  This will have to be reworked if we even
      ;; implement the compiled back end.  bug14767
      (if for-load-time
	  (list code string-or-tree return nsubs names back-end
		(list :num-submatches     nsubs
		      :num-repetitions    nreps
		      :use-stack          stackp
		      :minimum-length     minlen
		      :lookahead-set      laset
		      :return-type        return
		      :named-submatches   names
		      ))
	(make-vm-closure code string-or-tree return nsubs names back-end
			 (list :num-submatches     nsubs
			       :num-repetitions    nreps
			       :use-stack          stackp
			       :minimum-length     minlen
			       :lookahead-set      laset
			       :return-type        return
			       :named-submatches   names
			       ))))))

) ;; eval-when (compile eval)

(defun match-re (regexp input
		 &rest args
		 &key (return :string)
		      case-fold
		      single-line
		      multiple-lines
		      ignore-whitespace
		      start
		      end
		      (back-end *regexp-back-end*))
  "REGEXP must be a string specifying a regular expression, aa regexp tree,
or a compiled regular expression returned by compile-re.  This function
tries to match the string INPUT with the REGEXP.  If they don't match, NIL
is returned.  If they matches, T is returned as a first value, and the
match result of the whole, submatch 1, submatch 2, ... are returned as the
other values.

The way of returning match result can be specified by the RETURN keyword
argument.  If it is :string (default), substrings of INPUT are returned.
If it is :index, a cons of start and end index within INPUT is returned for
each match.

The keyword argument START and END limits the region of INPUT.

The keyword argument CASE-FOLD and BACK-END are passed to the compile-re
function, when a string is given to REGEXP.  They are ignored when REGEXP
is a compiled regulare expression."
  (declare (optimize (speed 3)))
  (when (not (stringp input))
    (error "Second argument must be a string: ~s." input))
  (cond ((regular-expression-p regexp)
         (funcall (regular-expression-matcher regexp) input start end return))
        ((or (stringp regexp)
	     (consp regexp)
	     (characterp regexp))
         (funcall (regular-expression-matcher
                   (compile-re regexp
                               :case-fold case-fold
                               :single-line single-line
                               :multiple-lines multiple-lines
                               :ignore-whitespace ignore-whitespace
                               :back-end back-end
                               :return return))
                  input start end return))
        (t (error
	    "match-re requires a string, regexp tree expr, or a compiled regexp, but got ~s"
		  regexp))))

;;================================================================= re-submatch
;;

(defun re-submatch (regexp string indexes selector
                    &key (type :string))
  "A convenience funtion to extract a specified submatch information from
the value returned by match-re.

REGEXP is a compiled regexp, and INDEXES is a list of (START . END)
index pairs returned by match-re.  SELECTOR should be an integer
that specifies a captured submatch (or 0 for the whole match),
or a string or a symbol that names a named submatch.

Alternatively, you can pass the opaque 'match' object returned by
match-re with :return :match argument, as REGEXP.  The match object
knows the information about the match results, so you don't need STRING
and INDEXES; just pass NIL to them.

TYPE argument may be :string, :after, :before or :index,
specifies the return value.  If it is :string (default), the substring
of the specified submatch is returned.  If it is :after or
:before, the substring after or before the specified submatch
is returned, respectively.  If it is :index, a pair of (START . END)
indexes are returned.

If the specified submatch isn't included in indexes, NIL is returned.

A typical usage pattern of this function is like this:

  (let ((r (multiple-value-list (match-re regexp string :return :index))))
    (re-submatch regexp string (cdr r) 3))

Or, if you use the match object, like this:

  (let ((match (match-re regexp string :return :match)))
    (re-submatch match nil nil 3))
"
  (multiple-value-bind (num-subs named-subs input indexes)
      (cond
       ((regular-expression-match-p regexp)
        (values (regular-expression-match-num-submatches regexp)
                (regular-expression-match-named-submatches regexp)
                (regular-expression-match-input regexp)
                (regular-expression-match-indexes regexp)))
       ((and (regular-expression-p regexp)
             (stringp string)
             (listp indexes))
        (values (regular-expression-num-submatches regexp)
                (regular-expression-named-submatches regexp)
                string
                indexes))
       ((not (regular-expression-p regexp))
        (error "bad type of argument: compiled regexp or regexp match object required, but got ~s" regexp))
       ((not (stringp string))
        (error "bad type of argument: string required, but got ~s" string))
       (t
        (error "bad type of argument: list of indexes required, but got ~s" indexes)))
    (labels ((return-it (ind)
               (and ind
                    (case type
                      ((:string) (subseq input (car ind) (cdr ind)))
                      ((:after)  (subseq input (cdr ind) (length input)))
                      ((:before) (subseq input 0 (car ind)))
                      ((:index)  ind)
                      (t (error "type must be one of :string, :after, :before or :index, but got ~s" type)))))
             (get-submatch (num)
               (and (<= 0 num num-subs) (nth num indexes)))
             (get-named (name)
               (let ((n (assoc name named-subs :test #'equal)))
                 (some #'get-submatch (cdr n))))
             )
      (cond
       ((integerp selector)
        (return-it (get-submatch selector)))
       ((symbolp selector)
        (return-it (get-named (symbol-name selector))))
       ((stringp selector)
        (return-it (get-named selector)))
       (t
        (error "selector must be either an integer, a symbol, or a string, but got ~s" selector)))
      )))

;;=================================================================
;; replace-re
;;

(defun replace-re (string regexp substitution
		   &key count (start 0) end
                        case-fold
                        single-line
                        multiple-lines
                        ignore-whitespace)
  "Replaces substring(s) in STRING that matches REGEXP for SUBSTITUTION,
and returns the replaced strings.

REGEXP can be a string that specifies a regular expression, a regexp tree,
or an already-compiled regular expression (by compile-re).  REGEXP should
match non-zero length string, or an error is signalled.

SUBSTITUTION can be a string, or a procedure that takes one argument, a list
match substrings returned by regexp matcher.
The procedure must return a string, which is then used as a substitution
string.

The keyword argument COUNT limits the maximum number of substitutions.
If it is NIL, all occurrence of REGEXP in STRING is replaced.

The keyword argument START and END limits the region in STRING where
match occurs.

Other keyword arguments are passed to compile-re to compile REGEXP.
"
  (cond
   ((or (stringp regexp)
	(consp regexp)
	(characterp regexp))
    (setf regexp (compile-re regexp :return :index
                             :case-fold case-fold
                             :single-line single-line
                             :multiple-lines multiple-lines
                             :ignore-whitespace ignore-whitespace)))
   ((not (regular-expression-p regexp))
    (error "regular expression or string is required: ~s" regexp)))
  (when (or (< start 0) (> start (length string)))
    (error "start argument is out of range: ~s" start))
  (cond
   ((not end) (setf end (length string)))
   ((<= end start) (return-from replace-re string)) ;; special case
   ((> end (length string))
    (error "end argument is out of range: ~s" end)))
  (setf substitution (parse-substitution substitution))
  (loop with i = 0
      and start = start
      and pre = (if (> start 0) (subseq string 0 start) "")
      for (next . fragments) = (replace-1 string regexp start end substitution)
      nconc fragments into results
      do (incf i)
         (setf start next)
      until (or (>= next end)
                (and count (>= i count)))
      finally (let ((r (if (< next (length string))
                           (nconc results (list (subseq string next)))
                         results)))
                (return (apply #'concatenate 'string pre r))))
  )

;; start scanning STRING from START, and returns
;; (BEFORE-STRING SUBSTITUTED) and the next index.
(defun replace-1 (string re start end substitution)
  (let ((m (multiple-value-list
            (match-re re string :start start :end end :return :index))))
    (cond
     ((not (car m)) ;; no match
      (list (length string) (subseq string start)))
     ((= (caadr m) (cdadr m)) ;; matched to null str
      (error "regexp for replace-re should match non-zero length string: ~s"
             (regular-expression-source re)))
     (t
      (let ((match-start (caadr m))
            (match-end   (cdadr m)))
        (list
	 match-end
	 (subseq string start match-start)
	 (if (functionp substitution)
	     (funcall
	      substitution
	      (mapcar
	       (lambda (ind)
		 ;; `ind' might be nil when an alternate regexp is used.
		 ;; For example: "(a)|(b)", when one side matches.
		 (when ind
		   (subseq string (car ind) (cdr ind))))
	       (cdr m)))
	   (substitute-1 string re (cdr m) substitution))))))))

;; create substitution string according to substitution spec
(defun substitute-1 (string re indexes substitution)
  (loop for fragment in substitution
      if (stringp fragment)
      collect fragment into r
      else if (or (numberp fragment) (keywordp fragment))
      collect (or (re-submatch re string indexes fragment) "") into r
      finally (return (apply #'concatenate 'string r))))


(eval-when (compile eval load)
  (defvar *parse-substitution-re*
      (compile-re "\\\\(?:(\\d+)|k<(\\w+)>|\\\\)" :return :index))
  )

;; "abc\\1de\\3ef\\k<foo>gh" => '("abc" 1 "de" 3 "ef" :foo "gh")
(defun parse-substitution (sub)
  (cond
   ((stringp sub)
    (loop with len = (length sub)
        and results = ()
        and i = 0
        while (< i len)
        do (multiple-value-bind (match? m0 m1 m2)
               (match-re *parse-substitution-re* sub :start i)
             (cond
              ((not match?)
               (push (subseq sub i) results)
               (setf i len)) ;; end
              (m1 ;; numbered back-reference
               (unless (= i (car m0))
                 (push (subseq sub i (car m0)) results))
               (push (read-from-string (subseq sub (car m1) (cdr m1)))
                     results)
               (setf i (cdr m0)))
              (m2 ;; named back-reference
               (unless (= i (car m0))
                 (push (subseq sub i (car m0)) results))
               (push (intern (subseq sub (car m2) (cdr m2)) :keyword)
                     results)
               (setf i (cdr m0)))
              (t  ;; \\
               (unless (= i (car m0))
                 (push (subseq sub i (car m0)) results))
               (push "\\" results)
               (setf i (cdr m0)))))
        finally (return (nreverse results))))
   ((functionp sub) sub)
   (t (error "string or procedure required, but got: ~s" sub))))

;;=================================================================
;; split-re
;;

(defun split-re (regexp string
                 &key count (start 0) end
		      (return :string)
                      case-fold
                      single-line
                      multiple-lines
                      ignore-whitespace)
  "Scan STRING for a delimiter given by REGEXP and return a list of
substrings.  If COUNT is given, then split into no more than COUNT
substrings, in which case the last substring will contain the rest of
the STRING.

REGEXP should match non-zero length string, or an error is signalled."
  (cond
   ((or (stringp regexp)
	(consp regexp)
	(characterp regexp))
    (setf regexp (compile-re regexp :return :index
                             :case-fold case-fold
                             :single-line single-line
                             :multiple-lines multiple-lines
                             :ignore-whitespace ignore-whitespace)))
   ((not (regular-expression-p regexp))
    (error "regular expression or string is required: ~s" regexp)))
  (when (or (< start 0) (> start (length string)))
    (error "start argument is out of range: ~s" start))
  (cond
   ((not end) (setf end (length string)))
   ((<= end start) (return-from split-re ; special case
		     (if (eq return :index)
			 (cons 0 (length string))
		       string)))
   ((> end (length string))
    (error "end argument is out of range: ~s" end)))
  (loop with i = 0
      and origin = 0
      for (match? . indexes) =
        (multiple-value-list
         (match-re regexp string :start start :end end :return :index))
      until (not match?)
      when (= (caar indexes) (cdar indexes)) ;; zero-length match
      do (error "regexp ~s matched zero-length string in split-re"
                (regular-expression-source regexp))
      end
      collect (if (eq return :index)
		  (cons origin (caar indexes))
		(subseq string origin (caar indexes)))
      into results
      do (incf i)
         (setf origin (setf start (cdar indexes)))
      until (and count (>= i count))
      finally (return (append results
			      (list
			       (if (eq return :index)
				   (cons start (length string))
				 (subseq string start))))))
  )

;;=================================================================
;; quote-re
;;

(defun quote-re (string)
  "Rewrite STRING, which must be a string, as a regexp in which all
characters are literal and have no special meaning.  The
implementation is simply <string> => (:SEQUENCE <string>)."
  `(:sequence ,string)
  )

;;=================================================================
;; re-lambda, re-let and re-case
;;

(defmacro re-lambda (regexp
                     bindings
                     &body body)
  "REGEXP must be a string that specifies a regular expression (string-re),
or a list of (string-re options ...), or an expression evaluates to a
compiled regular expression.

This form returns a closure which takes the following arguments:
  (string &key if-does-not-match)

When the closure is called, it scans the given string with REGEXP,
and if it matches, evaluates BODY with the environment where the
variables in BINDINGS are bound to the substrings of the match(es).
The closure returns the result(s) of the last expression of BODY.

BINDINGS is like the binding form of let.  Each element of BINDINGS
must be either one of the following:

  (VAR INTEGER)       ;; VAR binds to INTEGER-th submatch (0 for whole)
  (VAR STRING/SYMBOL) ;; VAR binds to the submatch named by STRING/SYMBOL
  VAR                 ;; VAR binds to the submatch named by VAR

If the specified match doesn't have a value, VAR is bound to nil.
You can also bind a substring before or after the specified submatch,
by giving modifier like (VAR INTEGER :before) or (VAR INTEGER :after).

If STRING doesn't match REGEXP, BODY is not evaluated, and the value
given to the keyword argument IF-DOES-NOT-MATCH is returned.

If REGEXP is the form of (string-re options ...), then options are passed
to compile-re to create a compiled regular expression.  It takes place
at macro-expansion time, so options must only contain constant literals.
"
  (let* ((match (gensym))
         (input (gensym))
         (if-does-not-match (gensym))
         (matcher-form (if (stringp regexp)
                           `(match-re ,regexp ,input :return :match)
                         (if (consp regexp)
                             (if (stringp (car regexp))
                                 `(match-re ,(car regexp) ,input
                                            :return :match
                                            ,@(cdr regexp))
                               `(match-re ,regexp ,input :return :match))
                           `(match-re ,regexp ,input :return :match))))
         )
    (labels ((gen-bind-form (bind)
               (cond
                ((symbolp bind)
                 `(,bind (re-submatch ,match nil nil ',bind)))
                ((or (not (consp bind))
                     (not (symbolp (car bind)))
                     (not (or (integerp (cadr bind))
                              (stringp (cadr bind))
                              (symbolp (cadr bind)))))
                 (error "bad binding form in re-lambda: ~s" bind))
                (t
                 `(,(car bind)
                   (re-submatch ,match nil nil
                                ',(cadr bind)
                                ,@(and (member (caddr bind) '(:before :after)
                                               :test #'eq)
                                       (list :type (caddr bind))))))))
             )
      `(lambda (,input &key ((:if-does-not-match ,if-does-not-match) nil))
         (let ((,match ,matcher-form))
           (if ,match
               (let (,@(mapcar #'gen-bind-form bindings))
                 ,@body)
             ,if-does-not-match)))
      )))

(defmacro re-let (regexp string bindings &body body)
  "REGEXP and BINDINGS are the same as of re-lambda.  STRING must be an
expression that evaluates to a string.  This macro evaluates STRING,
matches it with REGEXP, and if it matches, bind variables with (sub)matches
according to BINDINGS, then evaluates BODY.  If STRING doesn't match
REGEXP, BODY is not evaluated and nil is returned."
  `(funcall (re-lambda ,regexp ,bindings ,@body) ,string))

(defmacro re-case (string &rest clauses)
  "STRING must be an expression that evaluates to a string.  The
clauses are then examined one by one, checking whether it matches string or
not.  CLAUSES must be one of the following form.

 (REGEXP BINDINGS EXPR ...)
    If STRING matches REGEXP, (sub)matches are bound to the variables
    according to BINDIGNS, then EXPR ... are evaluated.  See the documentation
    of re-lambda about the specifiction of REGEXP and BINDINGS.

 (:test PROC EXPR ...)
    PROC must be an expression that evaluates to a procedure that takes
    single argument.   PROC is called with STRING, and if it returns a
    true value, evaluates EXPR ....

 (:testlet PROC VAR EXPR ...)
    Like :test above, but binds the result of PROC to VAR while evaluating
    EXPR....

 (t EXPR ...)
    Always match and evaluates EXPR ....    This can be used to describe
    the fallback case.

If no clause match, NIL is returned."
  (let ((string-var (gensym))
        (unique-var (gensym)))
    (labels ((genclause (clauses)
               (if (null clauses)
                   nil
                 (case (caar clauses)
                   ((t) `(progn ,@(cdar clauses)))
                   ((:test)
                    (destructuring-bind ((_ proc . exprs) . rest) clauses
                      (declare (ignore _))
                      `(if (funcall ,proc ,string-var)
                           (progn ,@exprs)
                         ,(genclause rest))))
                   ((:testlet)
                    (destructuring-bind ((_ proc var . exprs) . rest) clauses
                      (declare (ignore _))
                      `(let ((,var (funcall ,proc ,string-var)))
                         (if ,var
                             (progn ,@exprs)
                           ,(genclause rest)))))
                   (t
                    (destructuring-bind ((rx bindings . exprs) . rest) clauses
                      (let ((matcher (gensym))
                            (tmp (gensym)))
                        `(let* ((,matcher (re-lambda ,rx ,bindings ,@exprs))
                                (,tmp (funcall ,matcher ,string-var
                                               :if-does-not-match ,unique-var)))
                           (if (not (eq ,tmp ,unique-var))
                               ,tmp
                             ,(genclause rest))))))
                   ))))
      `(let ((,string-var ,string)
             (,unique-var (cons nil nil)))
         (declare (ignorable ,string-var ,unique-var))
         ,(genclause clauses))))
  )

;;=================================================================
;; parse-re defined in regexp-parser.cl
;;
