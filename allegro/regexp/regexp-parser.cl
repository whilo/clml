;; -*- mode: common-lisp; package: regexp -*-
;;
;; regexp-parser.cl - Regular Expression Parser
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
;; $Id: regexp-parser.cl,v 1.19 2007/04/17 21:51:47 layer Exp $

(in-package :regexp)

;;; The parser converts perl regexp string syntax to the equivalent parse tree Other
;;; exported regexp functions such as match-re accept either forms, but a complex parse
;;; tree may be easier to read and is certainly easier to construct for regexps generated
;;; by an application at run time. intention was to implement the same parse-tree.  The
;;; intention was to implement the same tree syntax implemented by cl-ppcre.  The follwing
;;; description is clipped with only a few modifications from the cl-ppcre documentation.

#|

This is similar to CREATE-SCANNER above but accepts a parse tree as
its first argument. A parse tree is an S-expression conforming to the
following syntax:

* Every string and character is a parse tree and is treated literally
  as a part of the regular expression, i.e. parentheses, brackets,
  asterisks and such aren't special.

* The symbol :VOID is equivalent to the empty string.

* The symbol :EVERYTHING is equivalent to Perl's dot, i.e it matches
  everything (except maybe a newline character depending on the mode).

* The symbols :WORD-BOUNDARY and :NON-WORD-BOUNDARY are equivalent to
  Perl's "\b" and "\B".

* The symbols :DIGIT-CLASS, :NON-DIGIT-CLASS, :WORD-CHAR-CLASS,
  :NON-WORD-CHAR-CLASS, :WHITESPACE-CHAR-CLASS, and
  :NON-WHITESPACE-CHAR-CLASS are equivalent to Perl's special
  character classes "\d", "\D", "\w", "\W", "\s", and "\S"
  respectively.

* The symbols :START-ANCHOR, :END-ANCHOR, :MODELESS-START-ANCHOR,
  :MODELESS-END-ANCHOR, and :MODELESS-END-ANCHOR-NO-NEWLINE are
  equivalent to Perl's "^", "$", "\A", "\Z", and "\z" respectively.

* The symbols :CASE-INSENSITIVE-P, :CASE-SENSITIVE-P,
  :MULTI-LINE-MODE-P, :NOT-MULTI-LINE-MODE-P, :SINGLE-LINE-MODE-P, and
  :NOT-SINGLE-LINE-MODE-P are equivalent to Perl's embedded modifiers
  "(?i)", "(?-i)", "(?m)", "(?-m)", "(?s)", and "(?-s)". As usual,
  changes applied to modes are kept local to the innermost enclosing
  grouping or clustering construct.

* (:FLAGS {<modifier>}*) where <modifier> is one of the modifier
  symbols from above is used to group modifier symbols. The modifiers
  are applied from left to right. (This construct is obviously
  redundant. It is only there because it's used by the parser.)

* (:SEQUENCE {<parse-tree>}*) means a sequence of parse trees,
  i.e. the parse trees must match one after another. Example:
  (:SEQUENCE #\f #\o #\o) is equivalent to the parse tree "foo".

* (:GROUP {<parse-tree>}*) is like :SEQUENCE but changes applied to
  modifier flags (see above) are kept local to the parse trees
  enclosed by this construct. Think of it as the S-expression variant
  of Perl's "(?:<pattern>)" construct.

* (:ALTERNATION {<parse-tree>}*) means an alternation of parse trees,
  i.e. one of the parse trees must match. Example: (:ALTERNATION #\b
  #\a #\z) is equivalent to the Perl regex string "b|a|z".

* (:BRANCH <test> <parse-tree>) is for conditional regular
  expressions. <test> is either a number which stands for a register
  or a parse tree which is a look-ahead or look-behind assertion. See
  the entry for (?(<condition>)<yes-pattern>|<no-pattern>) in man
  perlre for the semantics of this construct. If <parse-tree> is an
  alternation is must enclose exactly one or two parse trees where the
  second one (if present) will be treated as the "no-pattern" - in all
  other cases <parse-tree> will be treated as the "yes-pattern".

* (:POSITIVE-LOOKAHEAD|:NEGATIVE-LOOKAHEAD|:POSITIVE-LOOKBEHIND|:NEGATIVE-LOOKBEHIND
  <parse-tree>) should be pretty obvious...

* (:GREEDY-REPETITION|:NON-GREEDY-REPETITION <min> <max> <parse-tree>)
  where <min> is a non-negative integer and <max> is either a
  non-negative integer not smaller than <min> or NIL will result in a
  regular expression which tries to match <parse-tree> at least <min>
  times and at most <max> times (or as often as possible if <max> is
  NIL). So, e.g., (:NON-GREEDY-REPETITION 0 1 "ab") is equivalent to
  the Perl regex string "(?:ab)??".

* (:STANDALONE <parse-tree>) is an "independent" subexpression,
  i.e. (:STANDALONE "bar") is equivalent to the Perl regex string
  "(?>bar)".

* (:REGISTER <parse-tree>) is a capturing register group. As usual,
  registers are counted from left to right beginning with 1.

* (:BACK-REFERENCE <number>) where <number> is a positive integer is a
  back-reference to a register group.

* (:CHAR-CLASS|:INVERTED-CHAR-CLASS {<item>}*) where <item> is either
  a character, a character range, or a symbol for a special character
  class (see above) will be translated into a (one character wide)
  character class. A character range looks like (:RANGE <char1>
  <char2>) where <char1> and <char2> are characters such that (CHAR<=
  <char1> <char2>) is true. Example: (:INVERTED-CHAR-CLASS #\a (:RANGE
  #\D #\G) :DIGIT-CLASS) is equivalent to the Perl regex string
  "[^aD-G\d]".

Because CREATE-SCANNER is defined as a generic function which
dispatches on its first argument there's a certain ambiguity: Although
strings are valid parse trees they will be interpreted as Perl regex
strings when given to CREATE-SCANNER. To circumvent this you can
always use the equivalent parse tree (:GROUP <string>) instead.

|#

;;;
;;;
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)

(defgrammar regexp (string-grammar-mixin grammar)
  ((lexer-mode :accessor lexer-mode :initform 0))
  ;;(:non-associative lowest)
  (:non-associative low #\,)
  (:non-associative low1)
  (:non-associative low2)
  (:left-associative #\|)
  (:left-associative seqprec1)
  (:non-associative #\( #\) #\[ #\] )
  ;;(:non-associative #\- #\])
  (:left-associative seqprec2)
  (:left-associative seqprec3)
  (:non-associative char class-ref anchor back-reference group-name #\^ #\$ #\.)
  (:non-associative #\* #\+ #\? #\{ #\- #\})
  (:left-associative non-greedy)
  (:default-initargs :lexer 'regexp-lexer)
  (:lexemes int)
  )

)

;; The parser must be aware of 'x' modifier, which has lexical scope.

(defvar .extended-mode. nil)  ; 'x' modifier - ignore whitespace and allow
                              ; Perl-style commends.
(defvar .group-stack. nil)    ; stack to save parser mode - currently
                              ; only for .extended-mode.
(defvar .num-groups. 0)       ; # of submatch groups already seen.
                              ; we need to count it to resolve ambiguity
                              ; between back-reference and octal char code.

(defun save-modes    () (push .extended-mode. .group-stack.))
(defun restore-modes () (setf .extended-mode. (pop .group-stack.)))
(defun sticky-modes ()
  ;; used for sticky switches like (?x).  Need to copy the current switch
  ;; to the stack top.
  (pop .group-stack.)
  (push .extended-mode. .group-stack.))

(defmacro p (lhs rhs &rest options)
  `(defproduction (,lhs regexp) ,rhs ,@options))

;; An xexp is a possibly-empty regexp.  An exp is a non-empty regexp.

(p regexp (xexp) ($1))

(p xexp () (':void) (:precedence low1))
(p xexp (seq1) ($1) (:precedence low2))

;; cl-ppcre prefers to present adjacent characters as strings, so we do the same in order
;; to be compatible.
(p seq1 (seq) ((if (and (consp $1) (eq (car $1) :sequence))
		   (let ((s (loop with x = (cdr $1)
				while x
				when (and (characterp (car x)) (characterp (cadr x)))
				collect (loop collect (pop x) into chars
					    count 1 into len
					    while (characterp (car x))
					    finally
					      (return (make-array len
								  :element-type 'character
								  :initial-contents chars)))
				else collect (pop x))))
		     (if (null (cdr s)) (car s) `(:sequence ,@s)))
		 $1))
   (:precedence low2))

(p seq (exp) ($1) (:precedence low2))
(p seq (seq exp) ((cond ((and (consp $1) (eq (car $1) ':sequence))
			 (append $1 (list $2)))
			(t `(:sequence ,$1 ,$2))))
   (:precedence seqprec3))

;;(p exp (seq) (`(seq ,@$1)) (:precedence low))
(p exp (alt) ($1)          (:precedence low))
(p exp (class) ($1)        (:precedence low))

;; (p seq (exp exp) ((list $1 $2)) (:precedence seqprec1))
;; (p seq (seq exp) ((append $1 (list $2))) (:precedence seqprec1))
;; (p seq () ('empty) (:precedence seqprec2))

(p alt (xexp #\| xexp) (`(:alternation ,$1 ,$3)))
(p alt (alt #\| xexp) ((append $1 (list $3))))

(p exp (char) ($1))
(p exp (class-ref) (#+nomore `(:class-ref ,$1) #-nomore $1))
(p exp (anchor) (#+nomore `(:anchor ,@$1) #-nomore $1))
(p exp (back-reference) (`(:back-reference ,$1)))
(p exp ( #\. ) (':everything))
(p exp ( #\^ ) (':start-anchor) (:precedence seqprec2))
(p exp ( #\$ ) (':end-anchor) (:precedence seqprec2))
(p exp ( repeat )     ($1) (:precedence seqprec3))
(p exp ( repeat #\? ) (`(:non-greedy-repetition ,@(cdr $1))) (:precedence non-greedy))

(p repeat ( exp #\* )     (`(:greedy-repetition 0 nil ,$1)))
(p repeat ( exp #\+ )     (`(:greedy-repetition 1 nil ,$1)))
(p repeat ( exp #\? )     (`(:greedy-repetition 0   1 ,$1)))

(p repeat ( exp #\{ repeat-begin oint omax #\} )
   ((setf (lexer-mode grammar) 0)
    (unless $4 (setf $4 1))
    (if (eq $5 t)
	(setf $5 $4)
      (when $5 (unless (>= $5 $4) (signal-grammar-error grammar))))
    `(:greedy-repetition ,$4 ,$5 ,$1)))
(p omax () (t))	; exactly -- duplicate low range
(p omax ( #\, oint ) ($2))

(p repeat-begin () ((setf (lexer-mode grammar) 1)))

(p class ( #\[ class-begin ocaret obraket ohyphen class-list #\] )
   ((setf (lexer-mode grammar) 0)
    (let ((stuff (append $4 $5 $6)))
      #+never
      (if (and (null (cdr stuff)) (null $3))
	  (car stuff)
	`(,(if $3 :inverted-char-class :char-class) ,@(parse-class-exp stuff)))
      #-never
      `(,(if $3 :inverted-char-class :char-class) ,@(parse-class-exp stuff))))
   (:precedence low))

(p class-begin () ((setf (lexer-mode grammar) 2) nil))

(p ocaret () (nil) (:precedence seqprec1))
(p ocaret (#\^) (t))
(p ohyphen () () (:precedence seqprec1))
(p ohyphen (#\-) ((list #\-)))
(p obraket () () (:precedence seqprec1))
(p obraket (#\]) ((list #\])) (:precedence seqprec2))

(p class-list () (nil))	     ; This allows null class content, but we'll detect
                             ; that during later processing and signal error.
(p class-list (class-list class-list-item) ((append $1 $2)))

(p class-list-item (char) ((list $1)))
(p class-list-item (#\^)  ((list $1)))
(p class-list-item (#\-)  ((list $1)))
(p class-list-item (class-ref)  ((list $1)))

(p oint () ('nil))
(p oint (int) ($1))

(p exp ( #\( group-begin submatch-begin xexp group-end #\) )
   (`(:register ,$4)))
(p group-begin  () ((save-modes)))
(p group-end    () ((restore-modes)))
(p group-sticky () ((sticky-modes)))  ;; used for sticky switches

(p submatch-begin () ((incf .num-groups.)))

(p exp ( #\( group-begin #\? question-begin question group-end #\) )
   ((setf (lexer-mode grammar) 0)
    $5))

(p question-begin () ((setf (lexer-mode grammar) 3) nil))
(p question-end ()   ((setf (lexer-mode grammar) 0) nil))

(p question ( oqflags ocqflags #\: question-end xexp )
   ;; It would be nice to eliminate option parens that only affect grouping, which would
   ;; be done by the following line, but this causes incorrect associatiative grouping
   ;; of other operators.  See if this can be fixed, even though it only imposes a trivial
   ;; cost at compile time.
   ;;((if (or $1 $2) `(options ,$1 ,$2 ,$5) $5))
   ((setf $1 (delete :extended-mode-p $1))
    (setf $2 (delete :not-extended-mode-p $2))
    `(:group ,@$1 ,@$2 ,$5)))

(p question ( oqflags ocqflags question-end group-sticky )
   ((setf $1 (delete :extended-mode-p $1))
    (setf $2 (delete :not-extended-mode-p $2))
      (if (and (null $1) (null $2))
	  :void
	`(:flags ,@$1 ,@$2))))

(p question ( #\= question-end xexp )
   (`(:positive-lookahead ,$3)))

(p question ( #\! question-end xexp )
   (`(:negative-lookahead ,$3)))

;; "(?<" may be a beginning of lookbehind assertion or named capture.
;; we need to switch the lexer mode to parse it.
(p question ( #\< qlt-begin qlt )
   ($3))

(p qlt-begin () ((setf (lexer-mode grammar) 4) nil))
(p qlt ( question-end )  ;; "(?<)" - perl accepts it
   (:void))
(p qlt ( #\= question-end xexp )
   (`(:positive-lookbehind ,$3)))
(p qlt ( #\! question-end xexp )
   (`(:negative-lookbehind ,$3)))
(p qlt ( group-name #\> question-end submatch-begin xexp )
   (`(:register ,$5 ,$1)))

(p question ( #\> question-end xexp )
   (`(:standalone ,$3)))

(p question ( #\( #\? #\= question-end xexp #\) xexp )
   (`(:branch (:positive-lookahead ,$5) ,$7 )))

(p question ( #\( #\? #\! question-end xexp #\) xexp )
   (`(:branch (:negative-lookahead ,$5) ,$7 )))

(p question ( #\( #\? #\< #\= question-end xexp #\) xexp )
   (`(:branch (:positive-lookbehind ,$6) ,$8 )))

(p question ( #\( #\? #\< #\! question-end xexp #\) xexp )
   (`(:branch (:negative-lookbehind ,$6) ,$8 )))

(p question ( #\( qdigits #\) question-end xexp )
   (`(:branch ,(read-from-string (coerce (reverse $2) 'string)) ,$5 )))
(p qdigits ( qdigit ) (`(,$1)))
(p qdigits ( qdigits qdigit ) ((cons $2 $1)))
(p qdigit  ( #\0 ) ($1))
(p qdigit  ( #\1 ) ($1))
(p qdigit  ( #\2 ) ($1))
(p qdigit  ( #\3 ) ($1))
(p qdigit  ( #\4 ) ($1))
(p qdigit  ( #\5 ) ($1))
(p qdigit  ( #\6 ) ($1))
(p qdigit  ( #\7 ) ($1))
(p qdigit  ( #\8 ) ($1))
(p qdigit  ( #\9 ) ($1))

(p oqflags (qflags) ((setf $1 (mapcar #'car $1))
		     (when (member :extended-mode-p $1)
		       (setf .extended-mode. t))
                     $1))
(p ocqflags () (nil))
(p ocqflags (#\- qflags) ((setf $2 (mapcar #'cdr $2))
			  (when (member :not-extended-mode-p $2)
			    (setf .extended-mode. nil))
                          $2))

(p qflags () (nil))
(p qflags (qflags qflag) ((cons $2 $1)))
(p qflag (#\i) ('(:case-insensitive-p . :case-sensitive-p)))
(p qflag (#\m) ('(:multi-line-mode-p  . :not-multi-line-mode-p)))
(p qflag (#\s) ('(:single-line-mode-p . :not-single-line-mode-p)))
(p qflag (#\x) ('(:extended-mode-p    . :not-extended-mode-p)))

;;;;;;;;;;
;;;;;;;;;;
;;;;;;;;;;

(define-condition regexp-parse-error (grammar-parse-error)
  ()
  (:report (lambda (x stream)
	     (format stream "regexp ~s is unsyntactic~@[ at position ~d~]"
		     (string-grammar-string (grammar-parse-error-grammar x))
		     (grammar-parse-error-position x)))))

(defmethod signal-grammar-error ((grammar regexp) &key token where state)
  (error 'regexp-parse-error
	 :grammar grammar
	 :state state
	 :token token
	 :position (or where
		       (funcall (grammar-lexer grammar) grammar
				:report-location))))

(build-grammar regexp nil)

;;;;;;;;;;
;;;;;;;;;;
;;;;;;;;;;

(defun regexp-lexer (grammar &optional op)
  (when op
    (return-from regexp-lexer
      (case op
	(:report-location (ignore-errors (string-grammar-index grammar)))
	)))
  (macrolet ((nextchar ()
	       `(when (< n string-length)
		  (prog1 (char s n)
		    (setf n (setf (string-grammar-index grammar) (1+ n))))))
	     (peekchar (&optional (o 0))
	       `(let ((x (+ n ,o)))
		  (when (< x string-length)
		    (char s x))))
	     (putback ()
	       `(setf n (setf (string-grammar-index grammar) (1- n))))
             (advance (k)
               `(setf n (setf (string-grammar-index grammar)
                          (min (+ n ,k) string-length))))
             (word-char-p (c) ; used for named capture
               `(and ,c (or (alphanumericp ,c) (eql ,c #\_))))
	     )
    (with-terminal-codes (regexp)
      (tagbody				; for comments
       comment
	(let* ((s (string-grammar-string grammar))
	       (n (string-grammar-index grammar))
	       (string-length (string-grammar-length grammar))
	       (c (nextchar))
	       token value xlate)
	  (unless c
	    (return-from regexp-lexer (values (tcode eof) 'eof)))
	  (ecase (lexer-mode grammar)
            ;;;------------------------------------------------
            ;;; Normal case
            ;;;
	    (0
	     (when .extended-mode.
	       (loop
		   if (member c '(#\Space #\Tab #\Newline #\Page #\Return))
		   do (setf c (nextchar))
		   else if (eql #\# c)
		   do (loop until (or (not c) (eql #\Newline c))
			  do (setf c (nextchar)))
		   else return nil)
	       (unless c (go comment)))
	     ;; We need to treat comments specially, since they can't be seen
             ;; by the grammar without huge complications.
	     (if (eql #\( c)
		 (if (eql #\? (peekchar))
		     (if (eql #\# (peekchar 1))
			 (loop as c = (nextchar)
			     unless c do (error "unterminated (?# comment")
			     until (eql #\) c) finally (go comment)))))
	     (cond
	      ((eql c #\\)
	       (let ((c (nextchar)))
		 (unless c (error "Trailing backslash in regexp."))
		 (cond
                  ((eql c #\0)
                   ;; Octal digits.
                   (setf token (tcode char)
                         value (parse-octal-char 0
                                                 (lambda () (peekchar))
                                                 (lambda () (nextchar)))))
                  ((eql c #\x)
                   ;; Hex digits.  It may be \xN, \xNN, \x{N...}
                   (setq token (tcode char)
                         value (parse-hex-char (lambda () (peekchar))
                                               (lambda () (nextchar)))))
                  ((eql c #\c)
                   ;; control char
                   (setq xlate (nextchar))
                   (unless xlate (error "Trailing \\c in regexp."))
                   (setq token (tcode char)
                         value (code-char (logxor (char-code (char-upcase xlate))
                                                  #x40))))
                  ((digit-char-p c 10)
                   ;; This may be a back-reference _or_ octal digits.
                   ;; *ALERT* Ugly code follows.  Blame Perl spec.
                   (let* ((c1 (peekchar))
                          (c2 (peekchar 1))
                          (d0 (digit-char-p c 10))
                          (d1 (and c1 (digit-char-p c1 10)))
                          (d2 (and c2 (digit-char-p c2 10))))
                     (cond ((not d1)
                            ;; one digit is always a back reference (except \0,
                            ;; but we already ruled it out.
                            (setq token (tcode back-reference) value d0))
                           ((>= d0 8)
                            (cond (d2
                                   ;; we have \8NN or \9NN.  This can't be
                                   ;; back ref, but rather interpreted as
                                   ;; \0 + "8NN" or \0 + "9NN"
                                   (putback)
                                   (setq token (tcode char) value #\null))
                                  (t
                                   ;; we have \8N or \9N.  This is back ref
                                   ;; iff we've seen that many groups.
                                   ;; otherwise, it is interpreted as
                                   ;; \0 + "8N" or \0 + "9N"
                                   (let ((cnt (+ (* d0 10) d1)))
                                     (cond ((<= cnt .num-groups.)
                                            (advance 1)
                                            (setq token (tcode back-reference)
                                                  value cnt))
                                           (t
                                            (putback)
                                            (setq token (tcode char)
                                                  value #\null)))))))
                           ((>= d1 8)
                            ;; two digits; either back-reference or
                            ;; octal char + digit char
                            (let ((cnt (+ (* d0 10) d1)))
                              (cond ((<= cnt .num-groups.)
                                     (advance 1)
                                     (setq token (tcode back-reference)
                                           value cnt))
                                    (t
                                     (setq token (tcode char)
                                           value (code-char d0))))))
                           ((not d2)
                            ;; two digits; either back-reference or
                            ;; octal char.
                            (let ((cnt  (+ (* d0 10) d1))
                                  (cnt8 (+ (* d0 8) d1)))
                              (advance 1)
                              (cond ((<= cnt .num-groups.)
                                     (setq token (tcode back-reference)
                                           value cnt))
                                    (t
                                     (setq token (tcode char)
                                           value (code-char cnt8))))))
                           ((>= d2 8)
                            ;; more than three digits, but the first two
                            ;; digits forms an octal number.  this is always
                            ;; an octal char + digit char
                            (advance 1)
                            (setq token (tcode char)
                                  value (code-char (+ (* d0 8) d1))))
                           (t
                            ;; three octal digits; this is always an octal char
                            ;; mod 256 is for Perl compatibility
                            (advance 2)
                            (setq token (tcode char)
                                  value (code-char (mod (+ (* d0 64)
                                                           (* d1 8)
                                                           d2)
                                                        256)))))))
                  ((setq xlate (cdr (assoc c '((#\w . :word-char-class)
                                               (#\W . :non-word-char-class)
                                               (#\d . :digit-class)
                                               (#\D . :non-digit-class)
                                               (#\s . :whitespace-char-class)
                                               (#\S . :non-whitespace-char-class)
                                               )
                                           :test #'eql)))
                   (setq token (tcode class-ref) value xlate))
                  ((setq xlate (cdr (assoc c '((#\t . #\tab)
                                               (#\n . #\linefeed)
                                               (#\r . #\return)
                                               (#\f . #\form)
                                               (#\a . #\bell)
                                               (#\e . #\esc)
                                               )
                                           :test #'eql)))
                   (setq token (tcode char) value xlate))
                  ((setq xlate (cdr (assoc c '((#\A . :modeless-start-anchor)
                                               (#\z . :modeless-end-anchor-no-newline)
                                               (#\Z . :modeless-end-anchor)
                                               (#\b . :word-boundary)
                                               (#\B . :non-word-boundary)
                                               )
                                           :test #'eql)))
                   (setq token (tcode anchor) value xlate))
                  ((eql c #\k)
                   ;; named back-reference \k<name> (a la Ruby)
                   ;; 'name' is a sequence of word-constituting chars.
                   ;; we just grab through the terminating #\>.
                   (unless (eql #\< (setq c (nextchar)))
                     (error "badly formed named capture \\k<name>"))
                   (loop
                       for c = (nextchar) ;; we use nextchar since we consume
                       until (eql c #\>)  ;; closing #\>.
                       unless (word-char-p c)
                       do (error "missing name terminator (#\\>) in the named capture \\k<name>")
                       end
                       collect c into name
                       finally (setq token (tcode back-reference)
                                     value (coerce name 'string))))
                  (t (setq token (tcode char) value c)))))
	      #+notyet
	      ((and (member c '(#\+ #\* #\?) :test #'eql)
		    (eql (peekchar) #\?))
	       (nextchar)

	       )
	      ((member c '(#\( #\) #\| #\+ #\* #\? #\. #\[ #\{ #\} #\^ #\$)
		       :test #'eql)
	       (setq token (char-code c) value c))
	      (t (setq token (tcode char) value c))))
            ;;;------------------------------------------------
            ;;; Repeat range
            ;;;
	    (1
	     ;; Parse a decimal integer, return anything else as literal
	     ;; character.  Need to do numeric escapes here?
	     (loop with int = nil
		 as x = (digit-char-p c)
		 while x
		 do (setf int (+ (* (or int 0) 10) x)
			  c (nextchar))
		 finally (if int
			     (progn (putback)
				    (setf token (tcode int) value int))
			   ;; Return #\, and #\} as themselves, otherwise this will be an
			   ;; error so we return a generic `char' to avoid giving the
			   ;; state machine an our-of-range code.
			   (setf token (if (member c '(#\} #\,))
					   (char-code c)
					 (tcode char))
				 value c))))
            ;;;------------------------------------------------
            ;;; [char class] right after #\[
            ;;;
	    (2
	     (cond
               ((eql c #\\)
                (let ((c (nextchar)))
                  (unless c (error "Trailing backslash in regexp."))
                  (cond
                   ((eql c #\x)
                    (setq token (tcode char)
                          value (parse-hex-char (lambda () (peekchar))
                                                (lambda () (nextchar)))))
                   ((digit-char-p c 8)
                    (setq token (tcode char)
                          value (parse-octal-char (digit-char-p c 8)
                                                  (lambda () (peekchar))
                                                  (lambda () (nextchar)))))
                   ((eql c #\c)
                    ;; control char
                    (setq xlate (nextchar))
                    (unless xlate (error "Trailing \\c in regexp."))
                    (setq token (tcode char)
                          value (code-char (logxor (char-code (char-upcase xlate))
                                                   #x40))))
                   ((eql c #\b)
                    ;; NB: \b in character class becomes ^H (backslash).
                    ;; This is not documented in man perlre, but perl 5.8
                    ;; works so.
                    (setq token (tcode char) value #\Backspace))
                   ((setq xlate (cdr (assoc c '((#\d . :digit-class)
                                                (#\D . :non-digit-class)
                                                (#\e . #\esc)
                                                (#\f . #\form)
                                                (#\a . #\bell)
                                                (#\n . #\linefeed)
                                                (#\r . #\return)
                                                (#\s . :whitespace-char-class)
                                                (#\S . :non-whitespace-char-class)
                                                (#\t . #\tab)
                                                (#\w . :word-char-class)
                                                (#\W . :non-word-char-class))
                                            :test #'eql)))
                    (if (characterp xlate)
                        (setq token (tcode char) value xlate)
                      (setq token (tcode class-ref) value xlate)))
                   (t
                    (setq token (tcode char) value c)))))
	       ((member c '(#\^ #\- #\]) :test #'eql)
                (setq token (char-code c) value (char-code c)))
               (t
                (setf token (tcode char) value c))))
            ;;;------------------------------------------------
            ;;; after (?
            ;;;
	    (3
             (cond
              ((member c '(#\= #\! #\< #\> #\( #\? #\) #\:
                           #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                           #\i #\m #\s #\x #\-))
               (setf token (char-code c) value c))
              (t
               (setf token (tcode char) value c)))
	     )
            ;;;------------------------------------------------
            ;;; after (?<
            ;;;
            (4
             (cond
              ((member c '(#\= #\! #\> #\)))
               (setf token (char-code c) value c))
              ((word-char-p c)
               ;; Named capture.
               (loop with word = (list c)
                   for c = (peekchar)
                   while (word-char-p c)
                   do (push (nextchar) word)
                   finally (setf token (tcode group-name)
                                 value (coerce (reverse word) 'string))))
              (t
               ;; Error.  Let state machine support it.
               (setf token (tcode char) value c))))
	    )
	  (return-from regexp-lexer
	    (values token value #+notyet pos)))))))

;; Parse hex charcode notation.
;; Perl behavior:
;;  \x{N...}  : Hex N....  When the parser encounters non-hexdigit char,
;;              it skips to the closing '}'.   It is an error if the closing
;;              brace is missing.
;;  \xNN      : Hex NN.
;;  \xN       ; Hex 0N.
;;  \x        ; if \x is followed by non-hexdigit char, it is #\null.
(defun parse-hex-char (peek next)
  (let ((num 0)
        (nc (funcall peek)))
    (cond ((eql nc #\{)
           (funcall next)
           (loop with valid = t and chars = nil and k = 0
               as nc = (funcall peek)
               until (eql nc #\})
               do (cond ((not nc)
                         (error "unterminated hex escape: \"\x{~a\"~%"
                                (coerce (nreverse chars) 'string)))
                        ((not valid))
                        ((setf k (digit-char-p nc 16))
                         (setf num (+ (* num 16) k)))
                        (t (setf valid nil)))
                  (push nc chars)
                  (funcall next)
               finally (funcall next)
                       (return (code-char num))))
          ((and nc (setf num (digit-char-p nc 16)))
           (funcall next)
           (let* ((nc   (funcall peek))
                  (num2 (and nc (digit-char-p (funcall peek) 16))))
             (if num2
                 (progn (funcall next)
                        (code-char (+ (* 16 num) num2)))
               (code-char num))))
          (t (code-char 0)))))

;; \NNN, \NN or \N, where N is an octal digit.
;; (mod num 256) for Perl compatibility, although it is not documented.
(defun parse-octal-char (n peek next)
  (loop with num = n
      and count = 1
      as nc = (funcall peek)
      while (and nc (digit-char-p nc 8) (< count 3))
      do (setf num (+ (* 8 num) (digit-char-p nc 8)))
         (funcall next)
         (incf count)
      finally (return (code-char (mod num 256)))))

;; The argument is an uninterpreted list of characters appearing
;; inside [...].  The lexically significant characters #\^ and #\- appear
;; as char-code  All other characters, and escaped characters, appear as
;; themselves.
(defun parse-class-exp (content)
  (loop with p = content
      while p
      as pp = (car p)
      as ppn = (typecase pp (character pp) (integer (code-char pp)))
      if (not ppn)
      collect (pop p)
      else if (and (eql (cadr p) (char-code #\-))
                   (cddr p)
                   (or (characterp (caddr p)) (integerp (caddr p))))
      collect `(:range ,ppn
		       ,(if (characterp (caddr p))
			    (caddr p)
			  (code-char (caddr p))))
      and do (setf p (cdddr p))
      else collect ppn and do (pop p)))

(defun parse-re (string &key extended-mode)
  (let ((.extended-mode. extended-mode)
        (.num-groups. 0))
    (let ((ret (parse (make-instance 'regexp :string string))))
      ;; Never return a bare string, since that looks like something that will need
      ;; parsing again.
      (if (stringp ret) `(:sequence ,ret) ret))))

