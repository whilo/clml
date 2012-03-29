;; -*- mode: common-lisp; package: regexp -*-
;;
;; regexp-fe.cl - Regular Expression Front-end Compiler
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
;; $Id: regexp-fe.cl,v 1.47 2007/04/17 21:51:47 layer Exp $

(in-package :regexp)

;;;
;;; [COMPILER FRONT-END]
;;;
;;;  Regexp operator generates the intermediate code of matcher procedure,
;;;  which is then compiled into either a Lisp function or a code vector.
;;;
;;;  The intermediate code assumes an abstract architecture, which has
;;;  the following components:
;;;
;;;  * Start index and end index.  The input string between these indexes
;;;    (from start-index below end-index) are the target of the match.
;;;
;;;  * Maximum start index.  At the beginning of match it should be set
;;;    to the (- end-index minimum-length).  The value of this register
;;;    is used in the instructions such as check-input-length.
;;;
;;;  * Input pointer (ip).  At the beginning of the match, it is initialized
;;;    by start-index.  As match proceeds, it is updated to point the
;;;    'current character' in the input string.
;;;
;;;  * Tail string position:  If the regexp has a fixed tail string, these
;;;    registers are used to limit the region of search.  See
;;;    floating-tail-string instructions below.
;;;
;;;  * Submatch registers, which keep start and end positions (indexes) of
;;;    submatches.  The number of registers are determined at the
;;;    compile time.  In instruction's operand, it is noted as
;;;    (sub N).
;;;    *NOTE*: the code to set 0-th submatch (entire match) is no longer
;;;    generated.  Whenever the back-end executes 'success' instruction,
;;;    the input range between start-index and ip is the entire match.
;;;
;;;  * Repetition registers, which keep the count of repetition, but are
;;;    also used as general purpose registers.
;;;    In instraction's operand, it is noted as (rep N).
;;;
;;;  * A stack, which keeps some of the values of the registers, in case
;;;    backtrack is needed.
;;;
;;;  * A stack pointer, (sp), pointing the current top of the stack.
;;;
;;;  I take CISC approach (lots of high-function instructions) than RISC
;;;  approach (small set of orthogonal instructions); because it is easier
;;;  to do peeohole optimization in back-end, and also it is faster for VM.
;;;
;;;  The intermediate language instructions:
;;;
;;;
;;;  START/END POINTERS
;;;  ..................
;;;
;;;    These instructions controls "outer loop" of the match.
;;;
;;;    (check-input-length)
;;;
;;;        If (> START-INDEX MAXIMUM-START-INDEX), the input never matches,
;;;        so the matcher just returns false.
;;;
;;;    (increment-start-index <num>)
;;;
;;;        Increment START-INDEX by <num>.   It doens't need to check the
;;;        validity of START-INDEX; there should always be either
;;;        check-input-length or advance-start-index instruction following.
;;;
;;;    (advance-start-index <condition>)
;;;
;;;        Advance START-INDEX until <condition> meets.  <condition> may
;;;        be a character, a char-set, or 'bol.
;;;
;;;        If <condition> is a character or a char-set, the matcher can
;;;        advance START-INDEX until (schar INPUT START-INDEX) equals to or
;;;        is contained by the <condition>.   (You can use char=, since
;;;        case-insensitivity is reflected in char-set.)
;;;
;;;        If <condition> is a symbol 'bol, the matcher can advance
;;;        START-INDEX until it gets the next point of a newline character.
;;;        (As a special case, the first execution of advance-start-index
;;;        for 'bol should keep START-INDEX as is, for the beginning of
;;;        input also matches beginning-of-line anchor).
;;;
;;;        If START-INDEX gets bigger than MAXIMUM-START-INDEX during
;;;        advancing, the matcher can just return false.
;;;
;;;    (floating-tail-string <string>)
;;;    (floating-tail-string-ci <string>)
;;;
;;;        This instruction appears when the regexp has a fixed tail
;;;        string that is not anchored at the end of input.  We can
;;;        quickly filter out the input that can never match.
;;;
;;;        Let prelen be the minimum length of the matching string of
;;;        regexp before <string>.  It can be pre-calculated as
;;;          (- minimum-length (length <string>)).
;;;
;;;        First, this instruction checks TAIL-STRING-POSITION register.
;;;
;;;        a. If it has never been set, it looks for <string> in input
;;;           starting from
;;;            (+ START-INDEX prelen)
;;;           until the end of <string> reaches END-INDEX.
;;;
;;;        b. If TAIL-STRING-POSITION is set, then:
;;;         b1. If (> (+ START-INDEX prelen) TAIL-STRING-POSITION),
;;;             start searching from (+ START-INDEX prelen)
;;;         b2. Otherwise, skip searching at all without touching
;;;             neither START-INDEX nor TAIL-STRING-POSITION.
;;;
;;;        If the string isn't found, the matcher returns false.
;;;
;;;        If it matches, the matcher has to set TAIL-STRING-POSITION
;;;        register to the position of input that matches the beginning
;;;        of <string>.
;;;
;;;    (anchored-tail-string <string> <anchor>)
;;;    (anchored-tail-string-ci <string> <anchor>)
;;;
;;;        ****NOT USED YET****
;;;        This instruction appears near the beginning of the instruction
;;;        stream if the regexp has a fixed tail string that is anchored
;;;        at the end of string (modulo newline).
;;;        <anchor> may be 'eos or 'eos-newline.
;;;
;;;        The matcher has to peek the end of the input to see if it matches
;;;        <string>.  If <anchor> is 'eos-newline, an optional newline before
;;;        the end of string is allowed.
;;;
;;;        If it doesn't match, the matcher returns false.
;;;
;;;        If it matches, the matcher moves END-INDEX to the beginning of
;;;        matching string, and sets the length of matching string to
;;;        TAIL-STRING-LENGTH register (since it may or may not include
;;;        the last newline, we need to remeber this number).
;;;
;;;
;;;    (initialize-inner-loop)
;;;    (reset-inner-loop)
;;;
;;;        This instruction sets up the internal state of the registers
;;;        that are used in the inner loop.  Specifically,
;;;
;;;          * All submatch-start registers are invalidated.
;;;          * IP is set to START-INDEX.
;;;          * SP is set to the bottom of the stack.
;;;
;;;        Front-end output guarantees that initialize-inner-loop
;;;        is called before the first try of inner loop, and
;;;        reset-inner-loop is used for subsequent calls of inner loop.
;;;        The back-end can use this fact to do some extra initialization
;;;        work in initialize-inner-loop.
;;;
;;;    (start-from-tail-string <length>)
;;;
;;;        Sets START-INDEX to TAIL-STRING-POSITION, and IP to
;;;        (+ TAIL-STRING-POSITION <length>).
;;;
;;;
;;;  CONTROL FLOW
;;;  ............
;;;
;;;    (label <label-number>)
;;;
;;;        A label.
;;;
;;;    (jump <label-number>)
;;;
;;;        Simple jump to the specified label.
;;;
;;;    (decrement-branch>=0 (rep N) <label>)
;;;
;;;        Decrements (rep N).  If it is greater than or equal to zero,
;;;        branch to <label>.
;;;
;;;    (increment-branch< (rep N) <num> <label>)
;;;
;;;        Increments (rep N).  If it is less than <num>, branch to <label>.
;;;
;;;    (branch-if-ip<= <reg> <label-numer>)
;;;
;;;        Compares the current IP to the value of <reg>, and if IP is
;;;        smaller than or equal to <reg>, jump to <label-number>.
;;;        This instruction is used to check an empty match within
;;;        greedy unbound repetition.  Without this check, the match like
;;;        the following example would repeat infinitely within the first
;;;        alternative.
;;;
;;;            "a--" =~ /^((a?b?)*|a--)$/
;;;
;;;    (branch-if-void <submatch-number> <label-number>)
;;;
;;;        If the <submatch-number> submatch doesn't have a value (i.e.
;;;        it has never been matched), jump to <label-number>.
;;;
;;;    (jump-reg (rep N))
;;;
;;;        Jumps to the label whose number is the value of (rep N).
;;;        The actual number stored may differ from the label number.
;;;        It is guaranteed that the register is set by set-label below.
;;;
;;;    (success)
;;;
;;;        Match succeeds unconditionally.  The input string between
;;;        start-index (inclusive) and ip (exclusive) is the entire match.
;;;
;;;
;;;  STACK OPERATIONS
;;;  ................
;;;
;;;    The following operations manipulates the stack.
;;;    (The stack is also changed when matching instructions fail.  See
;;;    MATCHING section below.)
;;;
;;;    (try <fail-label> <register> ...)
;;;
;;;        Saves a failure continuation to the stack and continues
;;;        the match.  <fail-label> is a label the matcher jumps to
;;;        when the following code fails.
;;;
;;;        The back-end VM can choose representation of the stack frame,
;;;        except that <fail-label> must be pushed last (i.e. it should
;;;        be on the top).  One possible stack frame structure is as follows:
;;;
;;;         * value of <register> ....
;;;         * value of (ip)
;;;         * <fail-label>
;;;               |
;;;               v  stack grows this way
;;;
;;;        <fail-label> will be popped whenever match fails.
;;;
;;;    (push-fc <fail-label>)
;;;
;;;        Like try, pushes <fail-label> to the stack, except it doesn't
;;;        save IP.  This is used to adjust failure continuation.
;;;        Only appears when *optimize-stack* is t.
;;;
;;;    (pop <register> ...)
;;;
;;;        Recovers the contents of IP and <register>s from the stack, i.e.
;;;
;;;         * pops (ip)
;;;         * pops values of <register> ...
;;;
;;;        Note that the <fail-label> at the stack top that 'try' instruction
;;;        pushed is already popped.
;;;
;;;        The order of <register>... here is reversed from the
;;;        corresponding 'try' instruction.
;;;
;;;
;;;  REGISTER OPERATIONS
;;;  ...................
;;;
;;;    (save-ip (rep N))
;;;    (save-sp (rep N))
;;;
;;;        Saves current value of ip/sp to the register (rep N).
;;;
;;;    (load-ip (rep N))
;;;    (load-sp (rep N))
;;;
;;;        Sets the value of (rep N) to ip/sp.
;;;
;;;    (submatch-start (sub N))
;;;
;;;        Save the current input pointer as the beginning of the
;;;        specified submatch, and nullify the end point of the submatch
;;;        to indicate the submatch is 'open'.
;;;
;;;    (submatch-end (sub N))
;;;
;;;        Save the current input index as the end of the
;;;        specified submatch.
;;;
;;;    (submatch-set (sub N) <length>)
;;;
;;;        This appears in optimized code.  Sets the start and end submatch
;;;        to (- (ip) <length>) and (ip), respectively.
;;;
;;;    (submatch-save (sub N) (rep I) (rep J))
;;;
;;;        Saves start and end value of (sub N) to two registers, (rep I)
;;;        and (rep J), respectively.
;;;
;;;    (submatch-load (sub N) (rep I) (rep J))
;;;
;;;        Sets start and end value of (sub N) from two registers, (rep I)
;;;        and (rep J).
;;;
;;;    (submatch-load-or-set (sub N) (rep K) (rep I) (rep J) <length>)
;;;
;;;        This appears in optimized code.   IF (rep K) is less than or
;;;        equal to 0, loads the start and end value of (sub N) from
;;;        (rep I) and (rep J).  Othwerise, sets the start and end
;;;        of (sub N) as (- (ip) <length) and (ip).
;;;
;;;    (invalidate (sub N) ...)
;;;
;;;        Invalidate the submatch registers (sub N) ....
;;;
;;;    (set (rep N) <value>)
;;;
;;;        Sets <value> to register (rep N).
;;;
;;;    (inc (rep N))
;;;    (dec (rep N))
;;;
;;;        Increments/decrements register (rep N).
;;;
;;;    (set-label (rep N) <label-number>)
;;;
;;;        Sets <label-number> to register N.  The actual number to be set
;;;        to the register may differ from <label-number>, depending on
;;;        the back-end.  It is guaranteed that the content of the register
;;;        is only used by jump-reg.
;;;
;;;   MATCHING INSTRUCTIONS
;;;   .....................
;;;
;;;   The instructions below are matching instructions.  It performs some
;;;   test against the input string pointed by (ip).  If the test succeeds,
;;;   the matcher proceeds to the next instruction.  If the test fails,
;;;   the matcher pops a label number from the stack top, and jumps
;;;   to it.  In some context, the jump destination can be statically
;;;   determined, and in such case non-negative label number is put
;;;   at <fail> position.  The back-end can generate a code which directly
;;;   jumps to the given label on failure (however, the code should still pop
;;;   one integer from the stack).  If <fail> is t, failure causes the
;;;   whole match to fail.  If <fail> is nil, the jump destination should be
;;;   dynamically determined according to the stack top.
;;;
;;;   If *optimize-stack* is t, <fail> may be a list of single integer.
;;;   Failure causes the VM to jump to the label indicated by the integer.
;;;   The difference from (non-list) integer is that such failure does not
;;;   requires popping the stack.
;;;
;;;   NB: it is guaranteed that if <fail> is integer, it always matches the
;;;   stack top.  If they don't match, it is a bug of the front-end compiler.
;;;   If the matcher has "debug mode", it may check the stack top whenever
;;;   it jumps to the label <fail>.
;;;
;;;    (char <char> <fail>)
;;;    (char-ci <char> <fail>)
;;;
;;;        Match to a single char, case sensitive/insensitive.
;;;        *If it fails, it shouldn't move the input pointer.*
;;;
;;;    (char-set <char-set> <fail>)
;;;    (char-set-ci <char-set> <fail>)
;;;
;;;        Match to a char-set, case sensitive/insensitive.
;;;        *If it fails, it shouldn't move the input pointer.*
;;;
;;;    (string <string> <fail>)
;;;    (string-ci <string> <fail>)
;;;
;;;        Match to a string, case sensitive/insensitive.
;;;        *If it fails, it shouldn't move the input pointer.*
;;;
;;;    (tail-string <string> <fail>)
;;;    (tail-string-ci <string> <fail>)
;;;
;;;        If IP < TSP, fail.
;;;        If IP = TSP, we match.  IP <- IP + length(<string>), and
;;;           proceed.   We don't need to check <string> matches, since
;;;           we already know it does.
;;;        If IP > TSP, we checks like normal <string>/<string-ci>.
;;;
;;;    (reference (sub N) <fail>)
;;;    (reference-ci (sub N) <fail>)
;;;
;;;        Match to the string currently in the specified submatch.
;;;        NB: reference-ci is required to handle regexps like
;;;        /(\w+):(?i:\1)/.
;;;        *If it fails, it shouldn't move the input pointer.*
;;;
;;;    (peek-char <char> <fail>) (peek-char-ci <char> <fail>)
;;;    (peek-char-set <char-set> <fail>) (peek-char-set-ci <char-set> <fail>)
;;;    (peek-string <string> <fail>) (peek-string-ci <string> <fail>)
;;;    (peek-reference (sub N) <fail>) (peek-reference-ci (sub N) <fail>)
;;;
;;;        Like char, char-ci, etc., except they don't increment input
;;;        pointer.  Appears in the optimized code that does lookahead
;;;        dispatch.
;;;
;;;    (any <fail>), (any-except-newline <fail>)
;;;
;;;        Matches any character (including, and except, a newline).
;;;        *If it fails, it shouldn't move the input pointer.*
;;;
;;;    (bol <fail>), (eol <fail>), (bos <fail>),
;;;    (eos <fail>), (eos-newline <fail>),
;;;    (word-boundary <fail>), (not-word-boudary <fail>)
;;;
;;;        Assertions.
;;;
;;;    (fail <fail>)
;;;
;;;        Fails unconditionally.
;;;
;;;    (sub-ip <num> <fail>)
;;;
;;;        Subtract an integer value <num> from the current IP value.
;;;        Fails if IP becomes less than 0.
;;;
;;;    (tail-condition <num> <fail>)
;;;
;;;        ***NOT USED YET***
;;;        This instruction appears when anchored tail string is used.
;;;        If IP equals END-INDEX, add <num> to IP and proceed.
;;;        (<num> is the length of pre-matched tail string).
;;;        Otherwise fail.
;;;
;;;
;;;   The followings are specialized matching instructions.  They capture
;;;   the common pattern, allowing the back-end to do special optimization.
;;;
;;;    (repeat-char <char> [(sub N)])
;;;    (repeat-char-ci <char> [(sub N)])
;;;    (repeat-char-set <char-set> [(sub N)])
;;;    (repeat-char-set-ci <char-set> [(sub N)])
;;;    (repeat-string <string> [(sub N)])
;;;    (repeat-string-ci <string> [(sub N)])
;;;    (repeat-any [(sub N)])
;;;    (repeat-any-except-newline [(sub N)])
;;;
;;;        Matches repetition of the item as many times as possible.
;;;        No backtrack is required.   It must leave the input pointer
;;;        just after the last successful match of the item.
;;;        (If the input doesn't match the item at all, it doesn't move
;;;        the input pointer at all).   If an optional submatch register
;;;        is given, it must be set for the last successful match of
;;;        the item.  If the input doesn't match the item at all, it
;;;        shouldn't touch the submatch register.
;;;
;;;    (repeat-until/push <member> <limit> <label>)
;;;
;;;        <member> is a char-set or a symbol 'any or 'any-except-newline.
;;;        <limit> is a character, a char-set, or one of symbols 'bol, 'eol,
;;;        'bos, 'eos, 'eos-newline, 'word-boundary or 'not-word-boundary,
;;;        specifying the anchor.
;;;
;;;        This code matches as many characters as ones that match <member>,
;;;        and stops just before the furthest point where <limit> is
;;;        satisfied.  (If <limit> is a character or a char-set, the point
;;;        is where the character is a member of <limit>; if <limit> is
;;;        a symbol, the point is where the anchor condition meets.)
;;;
;;;        Besides that, for every point that satisfies <limit> except the
;;;        last one, it pushes the input pointer and the given <label> into
;;;        the stack, for later retries.
;;;
;;;        Example: suppose we have (repeat-until/push [\w] [\d] 9 nil)
;;;        matching the input "abc0defg1hij..2".
;;;        After the match, the input pointer must be on the character '1',
;;;        and the stack must contain 3 as a input pointer of the character
;;;        '0' in the input and the given label 9.
;;;
;;;        If the input is "abc**0" instead, then this instruction doesn't
;;;        match, and it should leave the input pointer at the initial
;;;        position.
;;;
;;;
;;;  OBSOLETED INSTRUCTIOS
;;;  .....................
;;;
;;;    The following instructions are no longer generated by the front-end.
;;;
;;;    (cut)
;;;    (reset (rep N))
;;;

;; Dynamic state variables used by the compiler front-end.

;; Regexp switches, a.k.a. imsx.  These only have effects at compile time.
(defvar .ignore-case. nil)              ; a flag bound by (?:...) and friends.
(defvar .multiple-lines. nil)           ; ditto
(defvar .single-line. nil)              ; ditto
(defvar .ignore-whitespace. nil)        ; ditto

;; Counters - for generating labels and registers.
(defvar .label-counter. 0)
(defvar .submatch-counter. 0)
(defvar .repetition-counter. 0)

;; States for bookkeeping
(defvar .submatch-nodes. '())           ; list of ast-submatch nodes.
                                        ; set up by pass 1.

(defvar .submatch-names. '())           ; alist of (name number ...)
                                        ; for named submatches.  set up and
                                        ; used within pass 1.

(defvar .failure-continuation. t)       ; current failure continuation, used
                                        ; as <fail> label.  't' means no
                                        ; backtrack, integer means backtrack
                                        ; to a known label, and 'nil' means
                                        ; backtrack should be determined at
                                        ; runtime.

(defvar .reentrant. nil)                ; True while we're compiling an AST
                                        ; which can be re-entered by backtrack.

(defvar .peek-match. nil)               ; True while compiling a specific
                                        ; lookahead asserting sequence.
                                        ; It only matters for :item and
                                        ; :back-reference node.

;; Controls various optimization stages.
(defvar *optimize-stack* t)             ; Try to minimize usage of stack.

(defvar *use-lookahead* t)              ; Use lookahead information

(defvar *loop-unroll-limit* 4)          ; Required repetition less than this
                                        ; count will be open looped.
(defvar *simple-loop-unroll-limit* 16)  ; Ditto, but applied if the body
                                        ; of the loop is a simple item.

;; TEMPORARY: Controls whether it uses char-set structure
;;  - Eventually it will be the default, but for the time being
;;    I keep the backward compatibility.
(defvar *use-char-set* t)

;;;==============================================================
;;; Front-end compiler entry point
;;;
;;;   Returns
;;;    * Instruction list
;;;    * # of submatch registers
;;;    * # of repetition registers
;;;    * flag of whether run-time stack is used or not.
;;;    * minimum match string length
;;;    * whether matching length is fixed or not
;;;    * lookahead set of the matcher.  it constrains the beginning
;;;      of the input string that can match.
;;;    * list of (submatch-name submatch-number ...) for named submatches
;;;      (NB: more than one submatch may have the same name).

(defun fe-compile-regexp (ast return-type &key pass)
  (declare (ignore return-type))
  (let ((.label-counter.      0)
        (.submatch-counter.   1)
        (.repetition-counter. 0)
        (.submatch-nodes.     ())
        (.submatch-names.     ())
        (.failure-continuation. t)
        (.reentrant.          nil)
        (.peek-match.         nil)
        (.ignore-case.        .ignore-case.)
        (.multiple-lines.     .multiple-lines.)
        (.single-line.        .single-line.)
        (.ignore-whitespace.  .ignore-whitespace.)
        )
    (let ((aast (fe-compile-pass1 ast)))
      (when (eql pass 1) (return-from fe-compile-regexp aast))
      (fe-compile-pass2 aast t)
      (when (eql pass 2) (return-from fe-compile-regexp aast))
      (let* ((code (fe-compile-pass3 aast))
             (minlen (ast-minlen aast))
             (fixed  (ast-fixed aast)))
        (values
         code
         .submatch-counter.
         .repetition-counter.
         (fe-stack-needed-p code)
         minlen
         fixed
         (ast-laset aast)
         .submatch-names.
         )))
    ))

(defun new-label ()
  (prog1 .label-counter. (incf .label-counter.)))

(defun new-submatch ()
  (prog1 .submatch-counter. (incf .submatch-counter.)))

(defun new-repetition ()
  (prog1 .repetition-counter. (incf .repetition-counter.)))

(defun num-submatches () ;; you know number of submatches after pass1.
  .submatch-counter.)

;; Compile body with delimiting the effect of mode switches (imsx).
;; These switches are resolved in Pass 1.
(defmacro protecting-mode-scope (&body body)
  `(let ((.ignore-case.       .ignore-case.)
         (.multiple-lines.    .multiple-lines.)
         (.single-line.       .single-line.)
         (.ignore-whitespace. .ignore-whitespace.))
     ,@body))

;; returns t if the code requires stack to be used or not
;; NB: Don't forget to update the list of instructions that needs stack op
;; if a new instruction is added.
(defun fe-stack-needed-p (code)
  (not (loop for c in code
           never (or (member (car c) '(try push-fc repeat-until/push))))))

;;;----------------------------------------------------
;;;  Pass 1.
;;;
;;;  This pass transforms the input parse tree (S-expression) into
;;;  AST suitable for later processing.
;;;  The 'subs' and 'used' slots of AST are also filled in this pass.
;;;

;; Base AST classes
(defclass ast ()
  ((laset     :documentation "lookahead set"
              :initarg :laset
              :initform ()
              :accessor ast-laset)
   (subs      :documentation "List of submatches within the tree"
              :initarg :subs
              :initform ()
              :accessor ast-subs)
   (used      :documentation "list of used registers within the tree"
              :initarg :used
              :initform ()
              :accessor ast-used)
   (minlen    :documentation "minimum input length that matches this aast."
              :initarg :minlen
              :initform 0
              :accessor ast-minlen)
   (fixed     :documentation "whether this aast matches fixed length of input."
              :initarg :fixed
              :initform t
              :accessor ast-fixed)
   (visited   :documentation "a marker used internally in pass 2."
              :initarg :visited
              :initform nil))
  )

(defclass ast-multi-container (ast)
  ((clauses   :documentation "list of asts"
              :accessor ast-clauses
              :initarg :clauses
              :initform nil))
  (:documentation "Abstract class for AST that has multiple clauses"))

(defclass ast-single-container (ast)
  ((clause    :documentation "child ast"
              :accessor ast-clause
              :initarg :clause))
  (:documentation "Abstract class for AST that has a single clause"))

(defclass ast-dual-container (ast)
  ((yes       :documentation "A clause taken if condition satisfies"
              :accessor branch-yes-clause
              :initarg :yes)
   (no        :documentation "A clause taken if condition doesn't satisfy"
              :accessor branch-no-clause
              :initarg :no))
  (:documentation "Abstract class for AST that has two children, yes-clause and no-clause"))

;; Concrete AST classes
(defclass ast-void (ast)
  ()
  (:documentation "empty RE"))

(defclass ast-item (ast)
  ((item      :documentation "character, char-set, string, or 'any"
              :initarg :item
              :accessor item-item)
   (flag      :documentation "case-fold flag, or whether any matches newline"
              :initarg :flag
              :accessor item-flag))
  (:documentation "Atomic item"))

(defclass ast-anchor (ast)
  ((type      :documentation "Anchor type"
              :initarg :type
              :accessor anchor-type))
  (:documentation "Anchor"))

(defclass ast-sequence (ast-multi-container)
  ()
  (:documentation "Sequence"))

(defclass ast-alternation (ast-multi-container)
  ((deterministic :documentation "true if we can determine which clause to take by using one-character lookahead"
                  :accessor ast-deterministic
                  :initform nil))
  (:documentation "Alternation"))

(defclass ast-required-repetition (ast-single-container)
  ((count     :documentation "# of repetition"
              :accessor repetition-count
              :initarg :count))
  (:documentation "Exactly COUNT times of repetition"))

(defclass ast-greedy-optional-repetition (ast-single-container)
  ((deterministic :documentation "true if we don't need backtrack"
                  :accessor ast-deterministic
                  :initform nil))
  (:documentation "Zero or more repetition of CLAUSE"))

(defclass ast-greedy-bound-repetition (ast-single-container)
  ((max       :documentation "Maximum count of repetition"
              :accessor repetition-max
              :initarg :max)
   (deterministic :documentation "true if we don't need backtrack"
                  :accessor ast-deterministic
                  :initform nil))
  (:documentation "Zero or more repetition of CLAUSE"))

(defclass ast-non-greedy-optional-repetition (ast-single-container)
  ((deterministic :documentation "true if we don't need backtrack"
                  :accessor ast-deterministic
                  :initform nil))
  (:documentation "Zero or more repetition of CLAUSE"))

(defclass ast-non-greedy-bound-repetition (ast-single-container)
  ((max       :documentation "Maximum count of repetition"
              :accessor repetition-max
              :initarg :max)
   (deterministic :documentation "true if we don't need backtrack"
                  :accessor ast-deterministic
                  :initform nil))
  (:documentation "Zero or more repetition of CLAUSE"))

(defclass ast-submatch (ast-single-container)
  ((number    :documentation "Submatch number, beginning with 1"
              :accessor submatch-number
              :initarg :number)
   (name      :documentation "Named of the sucmatch, if it has one."
              :accessor submatch-name
              :initarg :name)
   )
  (:documentation "Registering submatch"))

(defclass ast-reference (ast)
  ((number    :documentation "Submatch number"
              :accessor reference-number
              :initarg :number)
   (case-fold :documentation "Case fold flag"
              :initarg :case-fold)
   )
  (:documentation "Reference to the submatch"))

(defclass ast-lookahead (ast-single-container)
  ((negate    :documentation "Negated condition"
              :initarg :negate))
  (:documentation "lookahead and negative-lookahead assertion"))

(defclass ast-lookbehind (ast-single-container)
  ((negate    :documentation "Negated condition"
              :initarg :negate))
  (:documentation "lookbehind and negative-lookbehind assertion"))

(defclass ast-branch-submatch (ast-dual-container)
  ((number    :documentation "Submatch number"
              :initarg :number))
  (:documentation "(?(N)yes|no) - type conditional branch"))

(defclass ast-branch-lookahead (ast-dual-container)
  ((negate    :documentation "Negated condition"
              :initarg :negate)
   (condition :documentation "Condition expr"
              :accessor branch-condition
              :initarg :condition))
  (:documentation "(?(=cond)yes|no) and (?(!cond)yes|no)"))

(defclass ast-branch-lookbehind (ast-dual-container)
  ((negate    :documentation "Negated condition"
              :initarg :negate)
   (condition :documentation "Condition expr"
              :accessor branch-condition
              :initarg :condition))
  (:documentation "(?(<=cond)yes|no) and (?(<!cond)yes|no)"))

(defclass ast-standalone (ast-single-container)
  ()
  (:documentation "(?>foo)"))

(defclass ast-tail-string (ast)
  ((string    :documentation "String to match"
              :initarg :string)
   (anchor    :documentation "Optional anchor after the string"
              :initarg :anchor
              :initform nil)
   (case-fold :initarg :case-fold
              :initform nil)
   )
  (:documentation "A string that should match whenever regexp matches"))

;; Entry point of AST transformation.
;; S-expression AST is converted to a tree of ast-* objects.
;; The mode switches (?imsx-imsx:...) are resolved at this stage.
;; Repetition constructs are broken down to simpler constructs.

(defun fe-compile-pass1 (ast)
  ;; first, set up the named submatch alist.  this also assigns
  ;; submatch numbers to (:register <ast>) form.
  (scan-submatches ast)
  ;; second, creates a tree of AST objects.
  (fe-compile-pass1-rec ast)
  )

;; Preprocess function of pass 1 to pick out submatches.
;; we need this pass, since we have to know all the submatches in order to
;; fill the 'used' slot of AST instance, which is used within pass 1.
(defun scan-submatches (ast)
  (let ((counter 0)
        (names   ()))
    (labels ((rec (ast)
               (when (consp ast)
                 (cond ((eq (car ast) :register)
                        (let ((num (incf counter)))
                          (when (consp (cddr ast))
                            (register-name num (caddr ast)))
                          (rec (cadr ast))))
                       ((symbolp (car ast))
                        (dolist (elt (cdr ast)) (rec elt))))))
             (register-name (count name)
               (let ((p (assoc name names :test #'equal)))
                 (if p
                     (push count (cdr p))
                   (push (list name count) names)))))
      (rec ast)
      (setf .submatch-names. names))))

;; Main recursive function of pass 1.
(defun fe-compile-pass1-rec (ast)
  (labels ((get-safe (sym)
             (or (get sym 'regexp-fe-pass1)
                 (error "~s is not a known regexp operator." sym))))
    (etypecase ast
      (character (make-item ast .ignore-case.))
      (char-set  (make-item (if .ignore-case. (char-set-uncase ast) ast)
                            .ignore-case.))
      (string    (if (equal ast "")
                     (make-void)
                   (make-item ast .ignore-case.)))
      (null      (make-void))
      (symbol    (funcall (get-safe ast)))
      (cons      (destructuring-bind (op &rest args) ast
                   (apply (get-safe op) args))))
    ))

(defun make-item (item flag)
  (let ((len (if (stringp item) (length item) 1))
        (laset (etypecase item
                 (symbol
                  (if flag 'any 'any-except-newline))
                 (character
                  (if flag (char-set-uncase! (char-set item)) item))
                 (string
                  (let ((c (schar item 0)))
                    (if flag (char-set-uncase! (char-set c)) (schar item 0))))
                 (char-set item))))
    (make-instance 'ast-item
      :item item :flag flag :minlen len :laset (list laset) :visited t)))

(defun make-void ()
  (make-instance 'ast-void))

;;; Per-node pass1 handlers -------------------------------
(defmacro def-regexp-fe1 (name lambda-list &body body)
  (let ((function (intern (format nil "~A ~A ~A" :property name 'regexp-fe-pass1))))
    `(progn
       (defun ,function (,@lambda-list)
         ,@body)
       (setf (get ,name 'regexp-fe-pass1)
         (function ,function)))))

(def-regexp-fe1 :sequence (&rest clauses)
  ;; coerces subsequent characters into a string.  also splices
  ;; nested :sequences.
  ;; NB: the sequence may be flattened again in later pass, since
  ;; tree transformation may introduce nested sequences again.  Yet
  ;; performing pre-flattening here reduces # of nodes to process.
  (let ((chars ())
        (asts  ())
        (subs  ())
        (used  ()))
    (labels ((push-chars ()
               (when chars
                 (let ((item (if (null (cdr chars))
                                 (car chars)
                               (coerce (nreverse chars) 'string))))
                   (push (make-item item .ignore-case.) asts))
                 (setf chars nil)))
             (rec (clauses)
               (unless (null clauses)
                 (loop for cl in clauses
                     if (characterp cl) do (push cl chars)
                     else if (and (consp cl) (eq (car cl) :sequence))
                     do (rec (cdr cl))
                     else
                     do (progn
			  ;; need push-chars before compiling cl
			  ;; to get .ignore-case. right.
                          (push-chars)
                          (let ((z (fe-compile-pass1-rec cl)))
                            (unless (typep z 'ast-void)
                              (push z asts)
                              (setf used (union (ast-used z) used))
                              (setf subs (union (ast-subs z) subs))))))))
             )
      (rec clauses)
      (push-chars)
      (let ((asts (remove nil (nreverse asts))))
	(if (null asts)
	    (make-void)
	  (if (null (cdr asts))
	      (car asts)
	    (make-instance 'ast-sequence :clauses asts :subs subs :used used))))
      )))

(def-regexp-fe1 :alternation (&rest clauses)
  (let* ((cls  (mapcar #'fe-compile-pass1-rec clauses))
         (used (reduce #'union cls :key #'ast-used :initial-value nil))
         (subs (reduce #'union cls :key #'ast-subs :initial-value nil)))
    (make-instance 'ast-alternation
      :clauses cls :subs subs :used used)))

(def-regexp-fe1 :void ()
  (make-void))

(def-regexp-fe1 :everything ()    ; #\.
  (make-item 'any .single-line.))

(def-regexp-fe1 :start-anchor ()  ; #\^
  (make-instance 'ast-anchor :type (if .multiple-lines. 'bol 'bos)))

(def-regexp-fe1 :end-anchor ()    ; #\$
  (make-instance 'ast-anchor :type (if .multiple-lines. 'eol 'eos-newline)))

(def-regexp-fe1 :modeless-start-anchor () ; #\A
  (make-instance 'ast-anchor :type 'bos))

(def-regexp-fe1 :modeless-end-anchor-no-newline () ; #\z
  (make-instance 'ast-anchor :type 'eos))

(def-regexp-fe1 :modeless-end-anchor () ; #\Z
  (make-instance 'ast-anchor :type 'eos-newline))

(def-regexp-fe1 :word-boundary ()
  (make-instance 'ast-anchor :type 'word-boundary))

(def-regexp-fe1 :non-word-boundary ()
  (make-instance 'ast-anchor :type 'not-word-boundary))

#+nomore
(def-regexp-fe1 :anchor (op &rest args)
  (make-instance 'ast-anchor
    :type (ecase op
            (:modeless-start-anchor 'bos) ; #\A
            (:modeless-end-anchor-no-newline 'eos) ; #\z
            (:modeless-end-anchor 'eos-newline) ; #\Z
            (:word-boundary
             (let ((complement (car args)))
               (if complement 'not-word-boundary 'word-boundary)))
            )))

(def-regexp-fe1 :greedy-repetition (min max ast)
  (let* ((body (fe-compile-pass1-rec ast))
         (subs (ast-subs body))
         (used (ast-used body)))
    (cond
     ((null body) (make-void)) ;; edge case
     ((and (eql min 0) (eql max 0)) (make-void)) ;; edge case
     ((and (eql min 0) (eql max 1))
      (make-instance 'ast-alternation
        :subs subs :used used :clauses (list body (make-void))))
     ((and (eql min 0) (not max))
      (make-instance 'ast-greedy-optional-repetition
        :subs subs :used used :clause body))
     ((and (eql min 1) (not max))
      (make-instance 'ast-sequence
        :subs subs :used used
        :clauses (list body
                       (make-instance 'ast-greedy-optional-repetition
                         :subs subs :used used :clause body))))
     ((not max)
      (make-instance 'ast-sequence
        :subs subs :used used
        :clauses (list
                  (make-required-repetition subs used min body)
                  (make-instance 'ast-greedy-optional-repetition
                    :subs subs :used used :clause body))))
     ((eql min max)
      (make-required-repetition subs used min body))
     ((eql min 0)
      (make-instance 'ast-greedy-bound-repetition
        :subs subs :used used :max max :clause body))
     (t
      (make-instance 'ast-sequence
        :subs subs :used used
        :clauses (list
                  (make-required-repetition subs used min body)
                  (make-instance 'ast-greedy-bound-repetition
                    :subs subs :used used :max (- max min) :clause body))))
     )))

(def-regexp-fe1 :non-greedy-repetition (min max ast)
  (let* ((body (fe-compile-pass1-rec ast))
         (subs (ast-subs body))
         (used (ast-used body)))
    (cond
     ((null body) (make-void)) ;; edge case
     ((and (eql min 0) (eql max 0)) (make-void)) ;; edge case
     ((and (eql min 0) (eql max 1))
      (make-instance 'ast-alternation
        :subs subs :used used :clauses (list (make-void) body)))
     ((and (eql min 0) (not max))
      (make-instance 'ast-non-greedy-optional-repetition
        :subs subs :used used :clause body))
     ((and (eql min 1) (not max))
      (make-instance 'ast-sequence
        :subs subs :used used
        :clauses (list body
                       (make-instance 'ast-non-greedy-optional-repetition
                         :subs subs :used used :clause body))))
     ((not max)
      (make-instance 'ast-sequence
        :subs subs :used used
        :clauses (list
                  (make-required-repetition subs used min body)
                  (make-instance 'ast-non-greedy-optional-repetition
                    :subs subs :used used :clause body))))
     ((eql min max)
      (make-required-repetition subs used min body))
     ((eql min 0)
      (make-instance 'ast-non-greedy-bound-repetition
        :subs subs :used used :max max :clause body))
     (t
      (make-instance 'ast-sequence
        :subs subs :used used
        :clauses (list
                  (make-required-repetition subs used min body)
                  (make-instance 'ast-non-greedy-bound-repetition
                    :subs subs :used used :max (- max min) :clause body))))
     )))

(defun make-required-repetition (subs used count body)
  (if (or (and (or (typep body 'ast-item)
                   (and (typep body 'ast-submatch)
                        (typep (ast-clause body) 'ast-item)))
               (< count *simple-loop-unroll-limit*))
          (< count *loop-unroll-limit*))
      (let ((stripped (strip-submatches body used)))
        (make-instance 'ast-sequence
          :subs subs :used used
          :clauses (append (loop repeat (1- count) collect stripped)
                           (list body))))
    (make-instance 'ast-required-repetition
      :subs subs :used used :count count :clause body)))

(def-regexp-fe1 :register (ast &optional name)
  (let* ((num (new-submatch))
         (body (protecting-mode-scope (fe-compile-pass1-rec ast)))
         (node (make-instance 'ast-submatch
                 :number num :name name :clause body
                 :subs (cons num (ast-subs body)) :used (ast-used body))))
    (push node .submatch-nodes.)
    node))

(def-regexp-fe1 :back-reference (ref)
  (etypecase ref
    (integer
     (make-instance 'ast-reference
       :used (list ref) :number ref :laset t :case-fold .ignore-case.))
    (string
     ;; named reference.  beware the case that there are more than one
     ;; submatches with the name.
     (let ((subnums (cdr (assoc ref .submatch-names. :test #'equal))))
       (cond
        ((null subnums) (error "reference to unknown name: ~a" ref))
        ((null (cdr subnums))
         (make-instance 'ast-reference
           :used subnums :number (car subnums)
           :laset t :case-fold .ignore-case.))
        (t
         (make-instance 'ast-alternation
           :used subnums
           :clauses (mapcar (lambda (num)
                              (make-instance 'ast-reference
                                :used (list num) :number num :laset t
                                :case-fold .ignore-case.))
                            (sort subnums #'>)))))))
    ))

(def-regexp-fe1 :class-ref (item)
  (let ((cset (char-class->char-set item)))
    (make-item cset .ignore-case.)))

(def-regexp-fe1 :char-class (&rest members)
  (let ((cset (char-range->char-set nil .ignore-case. members)))
    (make-item cset .ignore-case.)))

(def-regexp-fe1 :inverted-char-class (&rest members)
  (let ((cset (char-range->char-set t .ignore-case. members)))
    (make-item cset .ignore-case.)))

(def-regexp-fe1 :group (&rest exps)
  #+nomore (let ((inter (intersection turn-on turn-off)))
	     (when inter
	       (error "regexp simultaneously turns on and off option~{ ~a~^,~}." inter)))
  (if exps
      (protecting-mode-scope
       (if (cdr exps)
	   (fe-compile-pass1-rec `(:sequence ,@exps))
	 (fe-compile-pass1-rec (car exps))))
    (fe-compile-pass1-rec :void)))

(def-regexp-fe1 :flags (&rest exps)
  (if exps
      (if (cdr exps)
	  (fe-compile-pass1-rec `(:sequence ,@exps))
	(fe-compile-pass1-rec (car exps)))
    (fe-compile-pass1-rec :void)))

(def-regexp-fe1 :case-insensitive-p ()
  (setf .ignore-case. t)
  (fe-compile-pass1-rec :void))
(def-regexp-fe1 :case-sensitive-p ()
  (setf .ignore-case. nil)
  (fe-compile-pass1-rec :void))

(def-regexp-fe1 :multi-line-mode-p ()
  (setf .multiple-lines. t)
  (fe-compile-pass1-rec :void))
(def-regexp-fe1 :not-multi-line-mode-p ()
  (setf .multiple-lines. nil)
  (fe-compile-pass1-rec :void))

(def-regexp-fe1 :single-line-mode-p ()
  (setf .single-line. t)
  (fe-compile-pass1-rec :void))
(def-regexp-fe1 :not-single-line-mode-p ()
  (setf .single-line. nil)
  (fe-compile-pass1-rec :void))

(def-regexp-fe1 :extended-mode-p ()
  (setf .ignore-whitespace. t)
  (fe-compile-pass1-rec :void))
(def-regexp-fe1 :not-extended-mode-p ()
  (setf .ignore-whitespace. nil)
  (fe-compile-pass1-rec :void))


(def-regexp-fe1 :positive-lookahead (clause)
  (let* ((body (protecting-mode-scope (fe-compile-pass1-rec clause)))
         (subs (ast-subs body))
         (used (ast-used body)))
    (make-instance 'ast-lookahead
      :subs subs :used used :negate nil :clause body)))

(def-regexp-fe1 :negative-lookahead (clause)
  (let* ((body (protecting-mode-scope (fe-compile-pass1-rec clause)))
         (subs (ast-subs body))
         (used (ast-used body)))
    (make-instance 'ast-lookahead
      :subs subs :used used :negate t :clause body)))

(def-regexp-fe1 :positive-lookbehind (clause)
  (let* ((body (protecting-mode-scope (fe-compile-pass1-rec clause)))
         (subs (ast-subs body))
         (used (ast-used body)))
    (make-instance 'ast-lookbehind
      :subs subs :used used :negate nil :clause body)))

(def-regexp-fe1 :negative-lookbehind (clause)
  (let* ((body (protecting-mode-scope (fe-compile-pass1-rec clause)))
         (subs (ast-subs body))
         (used (ast-used body)))
    (make-instance 'ast-lookbehind
      :subs subs :used used :negate t :clause body)))

(def-regexp-fe1 :branch (condition exp)
  (protecting-mode-scope
   (let ((yes-clause nil)
         (no-clause nil))
     (cond
      ((and (consp exp) (eq (car exp) :alternation))
       (when (> (length (cdr exp)) 2)
         (error "Bad :branch node - alternation has more than two ~
                     branches: ~S" exp))
       (setf yes-clause (cadr exp))
       (setf no-clause (caddr exp)))
      (t (setf yes-clause exp)
         (setf no-clause nil)))

     (let* ((yes-clause (fe-compile-pass1-rec yes-clause))
            (no-clause  (fe-compile-pass1-rec no-clause))
            (subs (union (ast-subs yes-clause) (ast-subs no-clause)))
            (used (union (ast-used yes-clause) (ast-used no-clause))))

       (cond
        ((integerp condition)
         (make-instance 'ast-branch-submatch
           :subs subs :used (union used `(,condition))
           :number condition :yes yes-clause :no no-clause))
        ((or (not (consp condition))
             (not (member (car condition) '(:positive-lookahead :negative-lookahead
                                            :positive-lookbehind :negative-lookbehind))))
         (error "Bad :branch condition - ~s" condition))
        (t
         (let* ((cond-node (protecting-mode-scope
                            (fe-compile-pass1-rec condition)))
                (cond-exp  (slot-value cond-node 'clause)))
           (let ((subs (union subs (ast-subs cond-exp)))
                 (used (union used (ast-used cond-exp))))
             (make-instance (etypecase cond-node
                              (ast-lookahead  'ast-branch-lookahead)
                              (ast-lookbehind 'ast-branch-lookbehind))
               :subs subs :used used :negate (slot-value cond-node 'negate)
               :condition cond-exp :yes yes-clause :no no-clause))))))
     )))

(def-regexp-fe1 :standalone (exp)  ;; (?>...)
  (let* ((body (protecting-mode-scope (fe-compile-pass1-rec exp)))
         (subs (ast-subs body))
         (used (ast-used body)))
    (make-instance 'ast-standalone :subs subs :used used :clause body)))

(macrolet ((char-class (sym)
	     `(def-regexp-fe1 ,sym ()
		(let ((cset (char-class->char-set ',sym)))
		  (make-item cset .ignore-case.)))))
  (char-class :word-char-class)
  (char-class :non-word-char-class)
  (char-class :digit-class)
  (char-class :non-digit-class)
  (char-class :whitespace-char-class)
  (char-class :non-whitespace-char-class)
  )

;; "simple" ast is an ast that doesn't need backtrack.
(defmethod simple-ast-p ((ast ast)) t) ;; fallback

(defmethod simple-ast-p ((ast ast-sequence))
  (every #'simple-ast-p (ast-clauses ast)))

(defmethod simple-ast-p ((ast ast-alternation))
  (slot-value ast 'deterministic))

(defmethod simple-ast-p ((ast ast-required-repetition))
  (simple-ast-p (ast-clause ast)))

(defmethod simple-ast-p ((ast ast-greedy-optional-repetition))     nil)
(defmethod simple-ast-p ((ast ast-greedy-bound-repetition))        nil)
(defmethod simple-ast-p ((ast ast-non-greedy-optional-repetition)) nil)
(defmethod simple-ast-p ((ast ast-non-greedy-bound-repetition))    nil)

(defmethod simple-ast-p ((ast ast-submatch))
  (simple-ast-p (ast-clause ast)))

(defmethod simple-ast-p ((ast ast-dual-container))
  (and (simple-ast-p (branch-yes-clause ast))
       (simple-ast-p (branch-no-clause ast))))

;; true if matching AST doesn't move input pointer if it fails.  that is,
;; the ASTs that we can try without worrying about saving input pointers.
(defmethod atomic-ast-p ((ast ast)) nil) ;; fallback

(defmethod atomic-ast-p ((ast ast-void)) t)
(defmethod atomic-ast-p ((ast ast-anchor)) t)
(defmethod atomic-ast-p ((ast ast-item)) t)

(defmethod atomic-ast-p ((ast ast-sequence))
  (and (= (length (ast-clauses ast)) 1)
       (atomic-ast-p (car (ast-clauses ast)))))
(defmethod atomic-ast-p ((ast ast-alternation))
  (every #'atomic-ast-p (ast-clauses ast)))

(defmethod atomic-ast-p ((ast ast-submatch))
  (atomic-ast-p (ast-clause ast)))
(defmethod atomic-ast-p ((ast ast-standalone))
  (atomic-ast-p (ast-clause ast)))

;; strip submatch registers except the ones listed in 'used' list
(defmethod strip-submatches ((ast ast) used)    ;; fallback
  (declare (ignore used))
  ast)

(defmethod strip-submatches ((ast ast-multi-container) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used
    :clauses (mapcar (lambda (c) (strip-submatches c used))
                     (ast-clauses ast))))

(defmethod strip-submatches ((ast ast-single-container) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used
    :clause (strip-submatches (ast-clause ast) used)))

(defmethod strip-submatches ((ast ast-required-repetition) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used :count (repetition-count ast)
    :clause (strip-submatches (ast-clause ast) used)))

(defmethod strip-submatches ((ast ast-greedy-bound-repetition) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used :max (repetition-max ast)
    :clause (strip-submatches (ast-clause ast) used)))

(defmethod strip-submatches ((ast ast-non-greedy-bound-repetition) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used :max (repetition-max ast)
    :clause (strip-submatches (ast-clause ast) used)))

(defmethod strip-submatches ((ast ast-submatch) used)
  (if (member (submatch-number ast) used)
      ast
    (ast-clause ast)))

(defmethod strip-submatches ((ast ast-lookahead) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used :negate (slot-value ast 'negate)
    :clause (strip-submatches (ast-clause ast) used)))

(defmethod strip-submatches ((ast ast-lookbehind) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used :negate (slot-value ast 'negate)
    :clause (strip-submatches (ast-clause ast) used)))

(defmethod strip-submatches ((ast ast-branch-submatch) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used :number (slot-value ast 'number)
    :yes (strip-submatches (branch-yes-clause ast) used)
    :no  (strip-submatches (branch-no-clause ast) used)))

(defmethod strip-submatches ((ast ast-branch-lookahead) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used
    :negate (slot-value ast 'negate)
    :condition (strip-submatches (branch-condition ast) used)
    :yes (strip-submatches (branch-yes-clause ast) used)
    :no  (strip-submatches (branch-no-clause ast) used)))

(defmethod strip-submatches ((ast ast-branch-lookbehind) used)
  (make-instance (class-of ast)
    :subs (ast-subs ast) :used used
    :negate (slot-value ast 'negate)
    :condition (strip-submatches (branch-condition ast) used)
    :yes (strip-submatches (branch-yes-clause ast) used)
    :no  (strip-submatches (branch-no-clause ast) used)))

;;;----------------------------------------------------
;;;  Pass 2.
;;;
;;; Traverses AST in reverse order and filling node attributes.
;;; This is basically a side-effecting operation.
;;;
;;; Each node receives lookahead set (laset) of its continuation.
;;;
;;;  <laset> : t    ;; anything is possible
;;;          | nil  ;; unknown
;;;          | (<chars> <assertion> ...)
;;;
;;;  <chars> : a character, a char-set, 'any, 'any-except-newline
;;;  <assertion> : a symbol appears in ast-anchor types.
;;;
;;; Used, minlen, fixed, and laset slots of each AST node are filled.
;;;

(defun merge-laset (laset1 laset2)
  (cond
   ((or (eq laset1 t) (eq laset2 t)) t)
   ((not laset1) laset2)
   ((not laset2) laset1)
   (t
    (let* ((c1 (car laset1))
           (c2 (car laset2))
           (assertions (union (cdr laset1) (cdr laset2)))
           (cs
            (etypecase c1
              (null c2)
              (symbol
               (if (eq c1 'any) 'any
                 (etypecase c2
                   (null    c1)
                   (symbol    (if (eq c2 'any) 'any 'any-except-newline))
                   (character (if (eql c2 #\Newline) 'any 'any-except-newline))
                   (char-set (char-set-add c2 *char-set-except-newline*)))))
              (character
               (etypecase c2
                 (null c1)
                 (symbol
                  (if (eq c2 'any) 'any
                    (if (eql c1 #\Newline) 'any 'any-except-newline)))
                 (character (if (eql c1 c2) c1 (char-set c1 c2)))
                 (char-set  (char-set-add c2 c1))))
              (char-set
               (etypecase c2
                 (null c1)
                 (symbol
                  (if (eq c2 'any) 'any
                    (char-set (char-set-add c1 *char-set-except-newline*))))
                 (character (char-set-add c1 c2))
                 (char-set  (char-set-add c1 c2))
                 )))))
      (if (and (eq cs 'any) (null assertions))
          t
        (cons cs assertions))))))

;; See if two lookahead set is exclusive or not.
;; It gets complicated if either of them has an anchor.  For now we only
;; check trivial cases.
(defun laset-char-exclusive-p (laset1 laset2)
  (labels ((vs-eos (laset)
             (and (car laset) (not (cdr laset))))
           (vs-eos-newline (laset)
             (and (not (cdr laset))
                  (char-set-exclusive-p (car laset) #\newline)))
           )
    (cond
     ((or (not (consp laset1)) (not (consp laset2))) nil)
     ;; If either of lasets have more than one anchors, just give up.
     ((or (cddr laset1) (cddr laset2)) nil)
     ;; Check for simple case; both of them are character conditions.
     ((and (not (cdr laset1)) (not (cdr laset2)))
      (char-set-exclusive-p (car laset1) (car laset2)))
     ;; at this point, either of lasets has anchor(s).  We only check
     ;; specific combinations.
     ((and (eq (cadr laset1) 'eos) (not (car laset1)))
      (vs-eos laset2))
     ((and (eq (cadr laset2) 'eos) (not (car laset2)))
      (vs-eos laset1))
     ((and (eq (cadr laset1) 'eos-newline) (not (car laset1)))
      (vs-eos-newline laset2))
     ((and (eq (cadr laset2) 'eos-newline) (not (car laset2)))
      (vs-eos-newline laset1))
     (t nil))))

;; negate the laset if possible.  when laset has anchor conditions, it
;; is not always possible, so we just return t (anything)
;; (strictly speaking, word-boundary anchor can be negated; we don't do it
;; for now).
(defun laset-negate (laset)
  (cond
   ((not (consp laset)) t)
   ((cdr laset) t)
   ((characterp (car laset))
    (list (char-set-complement! (char-set (car laset)))))
   ((char-set-p (car laset))
    (list (char-set-complement (car laset))))
   ((eq (car laset) 'any) (list (char-set)))
   ((eq (car laset) 'any-except-newline) (list #\newline))
   (t (error "regexp internal error: laset negate got weird laset: ~s~%" laset)
      )))

;; flatten nested :sequences, and also coerces subsequent characters
;; and strings into a single string.  NB: this is a side-effecting
;; operation.

(defmethod flatten-sequence ((ast t)) ;;fallback
  ast)

(defmethod flatten-sequence ((ast ast-sequence))
  (let ((fragments ())  ;; (:item char flag) or (:item string flag)
        (casemode nil)
        (asts ()))
    (labels ((flush-fragments ()
               (cond
                ((not fragments))
                ((not (cdr fragments))
                 (push (make-item (car fragments) casemode) asts))
                (t (loop for f in (nreverse fragments)
                       if (stringp f) collect f into ss
                       else collect (string f) into ss
                       finally (push
                                (make-item (apply #'concatenate 'string ss)
                                           casemode)
                                asts))))
               (setf fragments nil))
             (rec (clauses)
               (unless (null clauses)
                 (loop for cl in clauses
                     if (and (typep cl 'ast-item)
                             (or (characterp (item-item cl))
                                 (stringp (item-item cl))))
                     do (unless (eql casemode (item-flag cl))
                          (flush-fragments)
                          (setf casemode (item-flag cl)))
                        (push (item-item cl) fragments)
                     else if (typep cl 'ast-sequence)
                     do (rec (ast-clauses cl))
                     else
                     do (progn (flush-fragments)
                               (push cl asts)))))
             )
      (rec (ast-clauses ast))
      (flush-fragments)
      (let ((asts (remove (make-void) (nreverse asts))))
        (setf (ast-clauses ast) asts))
      ast)))

;;; Per-node pass2 handlers -------------------------------

(defmethod fe-compile-pass2 :around (ast laset)
  (declare (ignore laset))
  (if (slot-value ast 'visited)
      ast
    (prog1 (call-next-method) (setf (slot-value ast 'visited) t))))

(defmethod fe-compile-pass2 ((ast ast-void) laset)
  (setf (ast-laset ast) laset)
  ast)

(defmethod fe-compile-pass2 ((ast ast-item) laset)
  (declare (ignore laset))
  ast)

(defmethod fe-compile-pass2 ((ast ast-anchor) laset)
  (declare (ignore laset))
  (setf (ast-laset ast) (list nil (anchor-type ast)))
  (setf (ast-minlen ast) 0)
  (setf (ast-fixed ast) t)
  ast)

(defmethod fe-compile-pass2 ((ast ast-sequence) laset)
  (loop with minlen-all = 0 and fixed-all = t and laset-all = laset
      for clause in (reverse (ast-clauses ast))
      do (unless (typep clause 'ast-void)
           (with-slots (laset minlen fixed)
               (fe-compile-pass2 clause laset-all)
             (setf laset-all laset)
             (incf minlen-all minlen)
             (setf fixed-all (and fixed-all fixed))))
      finally (progn
                (flatten-sequence ast)
                (setf (ast-laset  ast) laset-all
                      (ast-minlen ast) minlen-all
                      (ast-fixed  ast) fixed-all)))
  ast)

(defmethod fe-compile-pass2 ((ast ast-alternation) laset0)
  (loop with laset-all = nil and minlen-all = nil and fixed-all = t
      for clause in (ast-clauses ast)
      do (with-slots (laset minlen fixed)
             (fe-compile-pass2 clause laset0)
           (setf laset-all (merge-laset laset-all laset))
           (setf fixed-all (and fixed-all fixed
                                (or (not minlen-all)
                                    (eql minlen-all minlen))))
           (setf minlen-all (if (not minlen-all)
                                minlen
                              (min minlen-all minlen))))
      finally (progn
                (setf (ast-laset ast) laset-all)
                (setf (ast-minlen ast) minlen-all)
                (setf (ast-fixed ast)  fixed-all)))
  ast)

(defmethod fe-compile-pass2 ((ast ast-submatch) laset)
  (let ((inner (ast-clause ast)))
    (with-slots (laset minlen fixed)
        (fe-compile-pass2 inner laset)
      (setf (ast-laset ast) laset
            (ast-minlen ast) minlen
            (ast-fixed ast) fixed)
      ast)))

(defmethod fe-compile-pass2 ((ast ast-reference) laset)
  (declare (ignore laset))
  (let* ((sub (find-if (lambda (n) (= (reference-number ast)
                                      (submatch-number n)))
                       .submatch-nodes.)))
    (unless sub
      (error "Reference to nonexistent group \\~a in regexp"
             (reference-number ast)))
    (if (slot-value sub 'visited)
        (setf (ast-minlen ast) (ast-minlen sub)
              (ast-fixed ast)  (ast-fixed sub))
      (setf (ast-fixed ast) nil))
    ast))

(defmethod fe-compile-pass2 ((ast ast-required-repetition) laset)
  (declare (ignore laset))
  (with-slots (count clause) ast
    (with-slots (laset minlen fixed) (fe-compile-pass2 clause nil)
      (setf (ast-laset ast) laset
            (ast-minlen ast) (* minlen count)
            (ast-fixed ast) fixed)
      ast)))

(defmethod fe-compile-pass2 ((ast ast-greedy-optional-repetition) laset)
  (repetition-pass2 ast laset))

(defmethod fe-compile-pass2 ((ast ast-non-greedy-optional-repetition) laset)
  (repetition-pass2 ast laset))

(defmethod fe-compile-pass2 ((ast ast-greedy-bound-repetition) laset)
  (repetition-pass2 ast laset))

(defmethod fe-compile-pass2 ((ast ast-non-greedy-bound-repetition) laset)
  (repetition-pass2 ast laset))

(defun repetition-pass2 (ast laset0)
  (with-slots (laset) (fe-compile-pass2 (ast-clause ast) laset0)
    (setf (ast-laset ast)  (merge-laset laset0 laset)
          (ast-minlen ast) 0
          (ast-fixed ast) nil)
    ast))

(defmethod fe-compile-pass2 ((ast ast-standalone) laset)
  (with-slots (laset minlen fixed)
      (fe-compile-pass2 (ast-clause ast) laset)
    (setf (ast-laset ast) laset
          (ast-minlen ast) minlen
          (ast-fixed ast)  fixed)
    ast))

(defmethod fe-compile-pass2 ((ast ast-lookahead) laset0)
  (with-slots (laset)
      (fe-compile-pass2 (ast-clause ast) nil)
    (setf (ast-laset ast)
      (if (slot-value ast 'negate)
          (let ((nlaset (laset-negate laset)))
            (if (eq nlaset t) laset0 nlaset))
        laset))
    (setf (ast-minlen ast) 0
          (ast-fixed ast) t)
    ast))

(defmethod fe-compile-pass2 ((ast ast-lookbehind) laset)
  (fe-compile-pass2 (ast-clause ast) nil) ;; ignore return values
  (setf (ast-laset ast) laset
        (ast-minlen ast) 0
        (ast-fixed ast) t)
  ast)

(defmethod fe-compile-pass2 ((ast ast-branch-submatch) laset)
  (branch-pass2 ast nil laset))

(defmethod fe-compile-pass2 ((ast ast-branch-lookbehind) laset)
  (branch-pass2 ast (branch-condition ast) laset))

(defmethod fe-compile-pass2 ((ast ast-branch-lookahead) laset)
  (branch-pass2 ast (branch-condition ast) laset))

(defun branch-pass2 (ast cond-exp laset)
  (when cond-exp (fe-compile-pass2 cond-exp nil))
  (with-slots (yes no) ast
    (with-slots ((laset1 laset) (min1 minlen) (fix1 fixed))
        (fe-compile-pass2 yes laset)
      (with-slots ((laset2 laset) (min2 minlen) (fix2 fixed))
          (fe-compile-pass2 no laset)
        (setf (ast-laset ast)  (merge-laset laset1 laset2)
              (ast-minlen ast) (min min1 min2)
              (ast-fixed ast)  (and fix1 fix2))
        ast))))

;;;----------------------------------------------------
;;;  Pass 3.
;;;
;;; Traverses AAST recursively, calling handlers for the AST nodes
;;; to generate a list of instruction stream.
;;;
;;; The 'cont' argument is an AAST node which would match after the
;;; compiling AAST node matches.
;;;
;;; Returns:
;;;   * Instruction list to execute AST.
;;;   * List of registers that are clobbered during executing the AST.
;;;

;; Utilities used within the third pass.
(defun merge-regs (&rest regs)
  (reduce #'(lambda (a b) (union a b :test #'equal)) regs))

(defun difference-regs (regs1 regs2)
  (remove-if (lambda (r1) (member r1 regs2 :test #'equal)) regs1))

;; See if AST doesn't contain a submatch register, or only contains
;; it at the top-level.
(defun register-free-p (ast)
  (or (null (ast-subs ast))
      (and (typep ast 'ast-submatch)
           (null (ast-subs (ast-clause ast))))))

;; If AST has top-level register node, removes the register from
;; the given register list.
(defun remove-toplevel-register (ast regs)
  (if (typep ast 'ast-submatch)
      (let ((num (submatch-number ast)))
        (remove-if (lambda (reg)
                     (and (eq (car reg) 'sub) (= (cadr reg) num)))
                   regs))
    regs))

;; Extract only SUB or REP registers
(defun sub-registers (regs)
  (remove-if (lambda (reg) (eq (car reg) 'rep)) regs))

(defun rep-registers (regs)
  (remove-if (lambda (reg) (eq (car reg) 'sub)) regs))

;; Extract toplevel and non-toplevel SUB registers
(defun toplevel-sub-register (ast)
  (if (typep ast 'ast-submatch)
      `(sub ,(submatch-number ast))))

(defun non-toplevel-sub-registers (ast regs)
  (sub-registers (remove-toplevel-register ast regs)))

;; Allocates REP registers enough to save given SUB registers
(defun new-repetitions-to-save-subs (subs)
  (loop for i below (length subs)
      collect `(rep ,(new-repetition))
      collect `(rep ,(new-repetition))))

;; Generates submatch-save and submatch-load insns for given SUBs and REPs.
(defun generate-submatch-save (subs reps)
  (loop for sub in subs
      for (rep1 rep2) on reps by #'cddr
      collect `(submatch-save ,sub ,rep1 ,rep2)))

(defun generate-submatch-load (subs reps)
  (loop for sub in subs
      for (rep1 rep2) on reps by #'cddr
      collect `(submatch-load ,sub ,rep1 ,rep2)))

;; If the previous match doesn't use stack for failure continuations,
;; but the current match expects it, then pushes the failure continuation.
(defun adjust-fcont (oldfcont)
  (if (consp oldfcont)
      `((push-fc ,(car oldfcont)))
    ()))

;; Partition submatch registers into those which are used within
;; the subtree and those which are not.
(defun used-submatches (ast subs)
  (if *optimize-stack*
      (loop with used = (ast-used ast)
          for sub in subs
          if (member (cadr sub) used)
          collect sub into used-subs
          else
          collect sub into unused-subs
          finally (return (values used-subs unused-subs)))
    (values subs nil) ;; just to keep backward compatibility - to be removed.
    ))

;; Return t if either laset is just a char/char-set condition or
;; assertion, but not both.
(defun simple-laset-p (laset)
  (and (consp laset)
       (or
        ;; laset is either (<char>) or (<char-set>)
        (and (null (cdr laset))
                (or (characterp (car laset))
                    (char-set-p (car laset))))
        ;; laset is (nil <assertion>)
        (and (null (car laset))
             (null (cddr laset))))))

;;; Pass3 toplevel routine ------------------------------

;; fe-compile-pass3 looks the toplevel structure of the regexp
;; and determines the structure of the matcher loop.
;;
;; In the most general case, the matcher needs to be a double
;; loop; the inner loop tries to match from the given point of
;; the input, and the outer loop calls the inner loop for each
;; position from START-INDEX to (- END-INDEX minlen).
;;
;; However, the above general Scheme is very slow if input is long.
;; We use lookahead set and tail-string information to limit
;; the number of possible starting point.  It gives us huge
;; performance boost.

;; Fallback
(defmethod fe-compile-pass3 ((ast ast))
  (let ((hconst (fe-head-constraint ast)))
    (if (eq hconst 'bos)
        (fe-bos-outer-loop (fe-strip-head-bos ast) nil)
      (fe-generic-outer-loop ast hconst 0 nil)))
  )

;; If we have sequence at top, look for tail-string.
(defmethod fe-compile-pass3 ((ast ast-sequence))
  (let* ((clauses (ast-clauses ast))
         (len    (length clauses))
         (first1 (car clauses))
         (last1  (car (last clauses)))
         (hconst (fe-head-constraint ast))
         (preskip 0)
         )
    ;; a special case; if the regexp begins with positive lookbehind,
    ;; we can skip that many characters.
    (if (and (typep first1 'ast-lookbehind)
             (not (slot-value first1 'negate)))
        (setf preskip (ast-minlen (ast-clause first1))))
    (if (and (>= len 2)
             (typep last1 'ast-item)
             (typep (item-item last1) 'string))
        (let* ((v (item-item last1))
               (f (item-flag last1))
               (tail-check `((,(if f
                                   'floating-tail-string-ci
                                 'floating-tail-string)
                                 ,v))))
          (change-class last1 'ast-tail-string)
          (setf (slot-value last1 'string) v)
          (setf (slot-value last1 'case-fold) f)
          (if (eq hconst 'bos)
              (fe-bos-outer-loop (fe-strip-head-bos ast) tail-check)
            (fe-generic-outer-loop ast hconst preskip tail-check)))
      (if (eq hconst 'bos)
          (fe-bos-outer-loop (fe-strip-head-bos ast) nil)
        (fe-generic-outer-loop ast hconst preskip nil))
      )))

;; A special case - all we have is a string.
;; It's awful lot of code just to search a string;
(defmethod fe-compile-pass3 ((ast ast-item))
  (if (not (stringp (item-item ast)))
      (call-next-method)
    (let* ((v (item-item ast))
           (f (item-flag ast)))
      `((,(if f 'floating-tail-string-ci 'floating-tail-string) ,v)
        (initialize-inner-loop)
        (start-from-tail-string ,(length v))
        (success)))))

;; When the beginning of match is anchored, we don't really need
;; the outer "loop".
(defun fe-bos-outer-loop (top-ast tail-check)
  (let ((code (let ((.failure-continuation. t))
                (fe-compile-pass3-rec top-ast nil)))) ;; ignore regs
    `((initialize-inner-loop)
      ,@tail-check
      ,@code
      (success))))

;; The general case.  We loop over input string, possibly using
;; head constraints.
(defun fe-generic-outer-loop (top-ast head-constraint pre-skip tail-check)
  (let* ((outer  (new-label))
         (fail   (new-label))
         (preskip (if (> pre-skip 0) `((increment-start-index ,pre-skip))))
         (hcheck (if head-constraint
                     `(advance-start-index ,head-constraint)
                   '(check-input-length)))
         (code   (let ((.failure-continuation. (list fail)))
                   (fe-compile-pass3-rec top-ast nil)))) ;; ignore regs
    `(;; prologue
      ,@preskip
      ,hcheck
      ,@tail-check
      (initialize-inner-loop)
      (label ,outer)
      ,@code
      (success)
      ;; retry
      (label ,fail)
      (increment-start-index 1)
      ,hcheck
      ,@tail-check
      (reset-inner-loop)
      (jump ,outer))))

;; Returns either character, char-set, or 'bos, according to the
;; head-constraint of top-ast.
(defun fe-head-constraint (top-ast)
  (let ((laset (ast-laset top-ast)))
    (cond
     ((not (consp laset)) nil)
     ((not (cdr laset))
      (and (or (characterp (car laset))
               (char-set-p (car laset)))
           (car laset)))
     ((equal laset '(nil bos))
      'bos)
     (t nil))))

;; strip preceding BOS
(defun fe-strip-head-bos (ast)
  (if (typep ast 'ast-sequence)
      (let ((clauses (ast-clauses ast)))
        (if (and (typep (car clauses) 'ast-anchor)
                 (eq (anchor-type (car clauses)) 'bos))
            (if (null (cddr clauses))
                (cadr clauses)
              (progn (setf (ast-clauses ast) (cdr clauses))
                     ast))
          ast))
    ast))



;;; Pass3 code generators -------------------------------

;; We recursively traverse the AST by method fe-compile-pass3-rec,
;; generating instruction stream.  We also keep track of the list
;; of registers that has to be saved if backtrack occurs.

;;.......................................................
;; Sequence
;;
(defmethod fe-compile-pass3-rec ((ast ast-sequence) cont)
  (loop with code = nil and regs = nil
      for cls on (ast-clauses ast)
      while cls
      do (multiple-value-bind (c r)
             (fe-compile-pass3-rec (car cls) (or (cadr cls) cont))
           (setf code (nconc code c))
           (setf regs (merge-regs r regs)))
      finally (return (values code regs))))

;;.......................................................
;; Alternation
;;
(defmethod fe-compile-pass3-rec ((ast ast-alternation) cont)
  (with-slots (clauses) ast
    (cond
     ((null clauses) (values () ())) ;; edge case
     ((null (cdr clauses)) (fe-compile-pass3-rec (car clauses) cont)) ;;edge case
     ((and *optimize-stack*
           (not cont))
      (alternation-noretry clauses))
     ((and *optimize-stack*
           (not .reentrant.)
           (typep cont 'ast)
           (= (length clauses) 2)
           (simple-ast-p (car clauses))
           (typep (cadr clauses) 'ast-void)
           (laset-char-exclusive-p (ast-laset (car clauses))
                                   (ast-laset cont)))
      ;; This is a pattern like (foo|), which is the same as one-or-zero
      ;; greedy bounded repetition.
      (greedy-bound-noretry-1-or-0 (car clauses)))
     ((and *optimize-stack*
           (not .reentrant.)
           (every #'simple-ast-p clauses))
      (alternation-simple clauses cont))
     (t
      (alternation-general clauses cont)))
    ))

;; Alternation simple case - no need to push registers
(defun alternation-simple (clauses cont)
  (let* ((labelN (new-label))
         (labelF (new-label))
         (ipreg  (new-repetition))
         (labreg (new-repetition))
         (old-fcont .failure-continuation.)
         (labelP (if (integerp old-fcont) nil (new-label)))
         (code   ())
         (regs   ()))
    (loop while (cdr clauses)
        do (let ((clause (pop clauses))
                 (fail (new-label)))
             (setq .failure-continuation. (list fail))
             (multiple-value-bind (c r)
                 (fe-compile-pass3-rec clause cont)
               (setf code
                 (nconc code
                        `((set-label (rep ,labreg) ,fail)
                          ,@c
                          (jump ,labelN)
                          (label ,fail)
                          (invalidate ,@r)
                          (load-ip (rep ,ipreg))
                          )))
               (setf regs (merge-regs regs r)))))
    (setq .failure-continuation.
      (if (integerp old-fcont) old-fcont (list labelP)))
    (multiple-value-bind (codeN regsN)
        (fe-compile-pass3-rec (car clauses) cont)
      (setq .failure-continuation. (list labelF))
      (values `((save-ip (rep ,ipreg))
                ,@code
                (set-label (rep ,labreg)
                           ,(if (integerp old-fcont) old-fcont labelP))
                ,@codeN
                (jump ,labelN)
                (label ,labelF)
                (jump-reg (rep ,labreg))
                ,@(unless (integerp old-fcont)
                    `((label ,labelP)
                      (fail ,old-fcont)))
                (label ,labelN))
              (merge-regs regs regsN)))))

;; Alternation special case - we are at the end of regexp, so we don't
;; need backtrack.  This is a variation of alternation-simple.
(defun alternation-noretry (clauses)
  (let* ((labelN (new-label))
         (save-ip? (not (every #'atomic-ast-p clauses)))
         (ipreg  (and save-ip? (new-repetition)))
         (old-fcont .failure-continuation.)
         (code   ())
         (regs   ()))
    (loop while (cdr clauses)
        do (let ((clause (pop clauses))
                 (fail (new-label)))
             (setq .failure-continuation. (list fail))
             (multiple-value-bind (c r)
                 (fe-compile-pass3-rec clause nil)
               (setf code
                 (nconc code
                        `(,@c
                          (jump ,labelN)
                          (label ,fail)
                          (invalidate ,@r)
                          ,@(if save-ip? `((load-ip (rep ,ipreg))))
                          )))
               (setf regs (merge-regs regs r)))))
    (setf .failure-continuation. old-fcont)
    (multiple-value-bind (codeN regsN)
        (fe-compile-pass3-rec (car clauses) nil)
      (values `(,@(if save-ip? `((save-ip (rep ,ipreg))))
                ,@code
                ,@codeN
                (jump ,labelN)
                (label ,labelN))
              (merge-regs regs regsN)))))

;; Alternation general case
(defun alternation-general (clauses cont)
  (let ((labelN (new-label))
        (oldfcont .failure-continuation.)
        (code   ())
        (regs   ()))
    (loop while (cdr clauses)
        do (let ((clause (pop clauses))
                 (fail (new-label)))
             (setq .failure-continuation. fail)
             (multiple-value-bind (c r) (fe-compile-pass3-rec clause cont)
               (multiple-value-bind (used unused)
                   (if .reentrant. (values r nil)
                     (used-submatches clause r))
                 (setf code
                   (nconc code
                          `((try ,fail ,@used)
                            ,@c
                            ,@(if cont (adjust-fcont .failure-continuation.))
                            (jump ,labelN)
                            (label ,fail)
                            ,@(if unused `((invalidate ,@unused)))
                            (pop ,@(reverse used))
                            )))
                 (setf regs (merge-regs (difference-regs regs used) r))))))
    (setf .failure-continuation. oldfcont)
    (multiple-value-bind (codeN regsN)
        (fe-compile-pass3-rec (car clauses) cont)
      (let ((newfcont .failure-continuation.))
        (setf .failure-continuation. nil)
        (values `(,@(adjust-fcont oldfcont)
                    ,@code
                    ,@codeN
                    ,@(if cont
                          (adjust-fcont newfcont))
                    (label ,labelN))
                (merge-regs regs regsN)
                )))))

;;.......................................................
;; Items, anchors, registers.
;;
(defmethod fe-compile-pass3-rec ((ast ast-item) cont)
  (declare (ignore cont))
  (with-slots (item flag) ast
    (labels ((choose (w/flag no-flag peek-flag peek-no-flag)
               (if .peek-match.
                   (if flag peek-flag peek-no-flag)
                 (if flag w/flag no-flag))))
      (let* ((fcont .failure-continuation.)
             (code
              (etypecase item
                (character
                 `((,(choose 'char-ci 'char 'peek-char-ci 'peek-char)
                    ,item
                    ,fcont)))
                (string
                 `((,(choose 'string-ci 'string 'peek-string 'peek-string-ci)
                    ,item
                    ,fcont)))
                (char-set
                 ;; TEMPORARY: for backward compatibility
                 (unless *use-char-set*
                   (setf item `(nil ,(char-set-ranges item))))
                 `((,(choose 'char-set-ci 'char-set 'peek-char-set-ci 'peek-char-set)
                    ,item
                    ,fcont)))
                (symbol  ;; any
                 (when .peek-match.
                   (error "internal-error: .peek-match. can't be set for any"))
                 `((,(choose 'any 'any-except-newline nil nil)
                    ,fcont))))))
        (values code ())))))

(defmethod fe-compile-pass3-rec ((ast ast-tail-string) cont)
  (declare (ignore cont))
  (values `((,(if (slot-value ast 'case-fold)
                  'tail-string-ci
                'tail-string)
                ,(slot-value ast 'string)
                , .failure-continuation.))
          nil))

(defun item-with-repetition (obj flag maybe-subreg)
  (values (etypecase obj
            (character
             `((,(if flag 'repeat-char-ci 'repeat-char)
                   ,obj ,maybe-subreg)))
            (string
             `((,(if flag 'repeat-string-ci 'repeat-string)
                   ,obj ,maybe-subreg)))
            (char-set
             `((,(if flag 'repeat-char-set-ci 'repeat-char-set)
                   ,obj ,maybe-subreg)))
            (symbol
             `((,(if flag 'repeat-any 'repeat-any-except-newline)
                   ,maybe-subreg))))
          ()))

(defmethod fe-compile-pass3-rec ((ast ast-anchor) cont)
  (declare (ignore cont))
  (with-slots (type) ast
    (values `(,(list type .failure-continuation.)) ())))

(defmethod fe-compile-pass3-rec ((ast ast-submatch) cont)
  (with-slots (clause number) ast
    (multiple-value-bind (code regs) (fe-compile-pass3-rec clause cont)
      (values
       (cond
        ((ast-fixed clause)
         `(,@code
           (submatch-set (sub ,number) ,(ast-minlen clause))))
        (t
         `((submatch-start (sub ,number))
           ,@code
           (submatch-end (sub ,number)))))
       (cons `(sub ,number) regs)))))

(defmethod fe-compile-pass3-rec ((ast ast-reference) cont)
  (declare (ignore cont))
  (with-slots (number case-fold) ast
    (pass3-simple-reference number case-fold)))

(defun pass3-simple-reference (number case-fold)
  (values `(,(list (if .peek-match.
                       (if case-fold
                           'peek-reference-ci
                         'peek-reference)
                     (if case-fold
                         'reference-ci
                       'reference))
                   number
                   .failure-continuation.))
          ()))

(defmethod fe-compile-pass3-rec ((ast ast-void) cont)
  (declare (ignore cont))
  (values () ()))

;;.......................................................
;; Required repetition
;;
(defmethod fe-compile-pass3-rec ((ast ast-required-repetition) cont)
  (declare (ignore cont))
  (with-slots (count fixed minlen clause) ast
    (cond
     ((= count 0) ;; edge case
      (values () ()))
     ((and fixed (= minlen 0))
      ;; special case like (\b){3}.  we need to match it once.
      (fe-compile-pass3-rec clause t))
     ((simple-ast-p clause)
      (required-simple clause count minlen))
     (t
      (required-general clause count minlen)))))

;; simple case - if clause fails, entire repetition just fails.
(defun required-simple (clause count minlen)
  (let* ((label  (new-label))
         (next   (new-label))
         (rep    (new-repetition))
         (ipreg  (and (= minlen 0) (new-repetition))))
    (multiple-value-bind (code regs)
        (let ((.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (values `((set (rep ,rep) ,(1- count))
                (label ,label)
                ,@(and (= minlen 0)
                       `((save-ip (rep ,ipreg))))
                ,@code
                ,@(and (= minlen 0)
                       `((branch-if-ip<= (rep ,ipreg) ,next)))
                (decrement-branch>=0 (rep ,rep) ,label)
                (label ,next))
              ;; no need to save (rep ,rep)
              regs))))

;; General case.  This repetition can be retried arbitrary
;; times, so we have to push states into the stack.
(defun required-general (clause count minlen)
  (let* ((label  (new-label))
         (next   (new-label))
         (succ   (new-label))
         (fail   (new-label))
         (rep    (new-repetition))
         (ipreg  (and (= minlen 0) (new-repetition)))
         (oldfcont .failure-continuation.))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. fail)
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (multiple-value-bind (used unused)
          (if .reentrant. (values regs nil) (used-submatches clause regs))
        (setq .failure-continuation. nil)
        (values `(,@(adjust-fcont oldfcont)
                    (set (rep ,rep) ,(1- count))
                    ;; loop
                    (label ,label)
                    (try ,fail (rep ,rep) ,@used)
                    ,@(and (= minlen 0) `((save-ip (rep ,ipreg))))
                    ,@code
                    ,@(and (= minlen 0)
                           `((branch-if-ip<= (rep ,ipreg) ,next)))
                    (jump ,succ)
                    ;; fail in loop
                    (label ,fail)
                    (pop ,@(reverse used) (rep ,rep))
                    ,@(if unused `((invalidate ,@unused)))
                    (inc (rep ,rep))
                    (fail nil)
                    ;; continue
                    (label ,succ)
                    (decrement-branch>=0 (rep ,rep) ,label)
                    (label ,next))
                (difference-regs regs used))))))

;;.......................................................
;; Greedy optional repetition
;;
(defmethod fe-compile-pass3-rec ((ast ast-greedy-optional-repetition) cont)
  (with-slots (clause) ast
    (when (typep clause 'ast-greedy-optional-repetition)
      (error "nested unbound greedy repetition isn't allowed"))
    (with-slots (minlen fixed) clause
      (cond
       ((and fixed (= minlen 0))
        ;; special case like ()*. It effectively becomes zero-or-one
        ;; alternation.
        (let ((fail (new-label))
              (next (new-label)))
          (multiple-value-bind (code regs)
              (let ((.failure-continuation. (list fail)))
                (fe-compile-pass3-rec clause cont))
            (values `(,@code
                      (jump ,next)
                      (label ,fail)
                      (invalidate ,@(non-toplevel-sub-registers clause regs))
                      (label ,next))
                    regs))))
       ((and *optimize-stack*
             (not cont)
             (simple-ast-p clause))
        ;; The simplest case.  This repetition will never be retried, so
        ;; we only need to save internal submatch registers.
        ;; This case is further broken down to whether the clause has
        ;; only the toplevel submatch (e.g. /(.)*/) or not.
        (let ((topsub (toplevel-sub-register clause)))
          (if (and topsub (register-free-p clause))
              (greedy-optional-noretry-topsub clause topsub minlen)
            (greedy-optional-noretry clause))))
       ((and *use-lookahead*
             (simple-ast-p clause)
             (typep cont 'ast)
             (laset-char-exclusive-p (ast-laset clause) (ast-laset cont)))
        ;; The repetition becomes deterministic by looking ahead one
        ;; character.
        (greedy-deterministic clause (ast-laset cont)))
       ((and *use-lookahead*
             (typep clause 'ast-item)
             (typep cont 'ast)
             (let ((elt (item-item clause)))
               (or (typep elt 'character)
                   (typep elt 'char-set)
                   (typep elt 'symbol)))
             (simple-laset-p (ast-laset cont)))
        ;; We have a single-character repetition, followed by a continuation
        ;; that has a simple head condition.  we can reduce the number of
        ;; backup points significantly by peeking the next character.
        (greedy-optional-lookahead clause (ast-laset cont)))
       ((and *optimize-stack*
             (not .reentrant.)
             fixed
             (simple-ast-p clause)
             (register-free-p clause))
        ;; Internal loop has fixed size, so we can calculate ip and subs values
        ;; when backtrack occurs, instead of using the stack.
        ;; This case is further broken down to the case that the clause has
        ;; the toplevel submatch or not.
        (let ((topsub (toplevel-sub-register clause)))
          (if topsub
              (greedy-optional-fixed-topsub clause topsub minlen)
            (greedy-optional-fixed clause minlen))))
       (t
        (greedy-optional-general clause minlen)))
      )))

;; A common case.  We have fixed-length repetition with
;; toplevel grouping, like /(abc)*/.
;; We can retrocompute the top-level submatch after the loop is exitted,
;; which gives us quite a lot of performance gain.
;; We should distinguish that whether clause does match at least one
;; time or not.
(defun greedy-optional-noretry-topsub (clause topsub minlen)
  (let ((inner (ast-clause clause)))
    (if (typep inner 'ast-item)
        ;; a special shortcut (big win)
        (item-with-repetition (item-item inner) (item-flag inner) topsub)
      (let ((start (new-label))
            (fail1 (new-label))
            (fail2 (new-label))
            (next  (new-label))
            (ipreg (new-repetition))
            (subreg1 (new-repetition))
            (subreg2 (new-repetition)))
        (multiple-value-bind (code1 regs1)
            (let ((.failure-continuation. (list fail1))
                  (.reentrant. t))
              (fe-compile-pass3-rec inner t))
          (multiple-value-bind (code2 regs2)
              (let ((.failure-continuation. (list fail2))
                    (.reentrant. t))
                (fe-compile-pass3-rec inner t))
            (values `(;; initial try to see if we have at least one match
                      (save-ip (rep ,ipreg))
                      (submatch-save ,topsub (rep ,subreg1) (rep ,subreg2))
                      ,@code1
                      ;; then repeat as many times as possible
                      (label ,start)
                      (save-ip (rep ,ipreg))
                      ,@code2
                      ,@(and (= minlen 0)
                             `((branch-if-ip<= (rep ,ipreg) ,fail2)))
                      (jump ,start)
                      ;; we didn't match at all.
                      (label ,fail1)
                      (load-ip (rep ,ipreg))
                      (submatch-load ,topsub (rep ,subreg1) (rep ,subreg2))
                      (jump ,next)
                      ;; we did match at least one time.
                      (label ,fail2)
                      (load-ip (rep ,ipreg))
                      (submatch-set ,topsub ,minlen)
                      (label ,next))
                    (merge-regs regs1 regs2))))))))

;; The special case like /(?:ab(cd)ef)*/.
;; Only need to save previous internal submatches
(defun greedy-optional-noretry (clause)
  (if (typep clause 'ast-item)
      ;; a special shortcut (big win)
      (item-with-repetition (item-item clause) (item-flag clause) nil)
    (let* ((start (new-label))
           (next  (new-label))
           (minlen (ast-minlen clause)))
      (multiple-value-bind (code regs)
          (let ((.failure-continuation. (list next))
                (.reentrant. t))
            (fe-compile-pass3-rec clause t))
        (let* ((ipreg (new-repetition))
               (save-subs (non-toplevel-sub-registers clause regs))
               (save-reps (new-repetitions-to-save-subs save-subs)))
          (values `((label ,start)
                    (save-ip (rep ,ipreg))
                    ,@(generate-submatch-save save-subs save-reps)
                    ,@code
                    ,@(and (= minlen 0)
                           `((branch-if-ip<= (rep ,ipreg) ,next)))
                    (jump ,start)
                    (label ,next)
                    (load-ip (rep ,ipreg))
                    ,@(generate-submatch-load save-subs save-reps))
                  regs))))))

;; Fixed size loop, possible retry.
;; Like /(?:ab|ac)*ad/.
(defun greedy-optional-fixed (clause minlen)
  (let* ((start (new-label))
         (fail  (new-label))
         (next  (new-label))
         (cfail (new-label))
         (retry  (new-label))
         (count (new-repetition))
         (ipreg (new-repetition))
         (atomic? (atomic-ast-p clause))
         (oldfcont .failure-continuation.))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list fail))
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (setf .failure-continuation. (list cfail))
      (values `((set (rep ,count) 0)
                (label ,start)
                ,@(unless atomic? `((save-ip (rep ,ipreg))))
                ,@code
                (inc  (rep ,count))
                (jump ,start)
                ;; failure within the repetition
                (label ,fail)
                ,(if atomic?
                     `(save-ip (rep ,ipreg))
                   `(load-ip (rep ,ipreg)))
                (jump ,next)
                ;; failure from the continuation
                (label ,cfail)
                (load-ip (rep ,ipreg))
                (decrement-branch>=0 (rep ,count) ,retry)
                (fail ,oldfcont)

                (label ,retry)
                (sub-ip ,minlen t)
                (save-ip (rep ,ipreg))
                ;; continuation
                (label ,next))
              (if .reentrant.
                  (cons `(rep ,count) regs)
                regs)))))

;; Fixed size loop, possible retry, toplevel submatch.
;; It's a combination of greedy-optional-noretry-topsub and
;; greedy-optional-fixed.
(defun greedy-optional-fixed-topsub (clause topsub minlen)
  (let* ((inner (ast-clause clause)) ;; strip register node
         (start (new-label))
         (ifail (new-label))
         (next  (new-label))
         (cfail (new-label))
         (retry  (new-label))
         (count (new-repetition))
         (ipreg (new-repetition))
         (subreg1 (new-repetition))
         (subreg2 (new-repetition))
         (atomic? (atomic-ast-p inner))
         (oldfcont .failure-continuation.))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list ifail))
              (.reentrant. t))
          (fe-compile-pass3-rec inner t))
      (setf .failure-continuation. (list cfail))
      (values `(;; preparation
                (submatch-save ,topsub (rep ,subreg1) (rep ,subreg2))
                (set (rep ,count) 0)
                ;; loop
                (label ,start)
                ,@(unless atomic? `((save-ip (rep ,ipreg))))
                ,@code
                (inc  (rep ,count))
                (jump ,start)
                ;; failure within the repetition.  we set the submatch
                ;; to the last successful one.
                (label ,ifail)
                ,(if atomic?
                     `(save-ip (rep ,ipreg))
                   `(load-ip (rep ,ipreg)))
                (submatch-load-or-set ,topsub (rep ,count)
                                      (rep ,subreg1) (rep ,subreg2) ,minlen)
                (jump ,next)
                ;; failure from the continuation.  we need to 'pop' one
                ;; state, which we fake by registers.
                (label ,cfail)
                (load-ip (rep ,ipreg))
                (decrement-branch>=0 (rep ,count) ,retry)
                (submatch-load ,topsub (rep ,subreg1) (rep ,subreg2))
                (fail ,oldfcont)

                (label ,retry)
                (sub-ip ,minlen t)
                (save-ip (rep ,ipreg))
                (submatch-load-or-set ,topsub (rep ,count)
                                      (rep ,subreg1) (rep ,subreg2) ,minlen)
                ;; continuation
                (label ,next))
              (if .reentrant.
                  (cons `(rep ,count) regs)
                regs)))))

;; Simple item repetition followed by something, like /.*a/
;; We can take advantage of lookahead set.
(defun greedy-optional-lookahead (item laset)
  (labels ((err ()
             (error "regexp implementation error: greedy-optional-lookahead")))
    (let* ((oldfcont .failure-continuation.)
           (next  (new-label))
           (retry (new-label))
           (elt   (item-item item))
           (flag  (item-flag item))
           (rep-elt (cond ((characterp elt)
                           (if flag
                               (char-set-uncase! (char-set elt))
                             (char-set elt)))
                          ((and (eq elt 'any) (not flag))
                           'any-except-newline)
                          (t elt)))
           (limit
            (cond ((characterp (car laset)) (car laset))
                  ((char-set-p (car laset)) (car laset))
                  ((member (cadr laset) '(bol eol bos eos eos-newline
                                          word-boundary not-word-boundary))
                   (cadr laset))
                  (t (err))))
           )
      (setf .failure-continuation. nil)
      (values `(,@(adjust-fcont oldfcont)
                (repeat-until/push ,rep-elt ,limit ,retry)
                (jump ,next)
                (label ,retry)
                (pop)
                (label ,next))
              nil))))

;; Deterministic case, like /\s*\d/.  We can match as far as possible
;; without considering backtracking.
(defun greedy-deterministic (clause out-laset)
  (cond
   ;; If repetition is a single item, we can use shortcut instruction.
   ((typep clause 'ast-item)
    (item-with-repetition (item-item clause) (item-flag clause) nil))
   ((and (typep clause 'ast-submatch)
         (typep (ast-clause clause) 'ast-item))
    (item-with-repetition (item-item (ast-clause clause))
                          (item-flag (ast-clause clause))
                          `(sub ,(submatch-number clause))))
   ;; General case.  We peek one item to determine we continue to repeat.
   (t
    (let* ((start (new-label))
           (body (new-label))
           (next (new-label))
           (out-char  (car out-laset))
           (out-char-dispatch
            ;; NB: laset is case-expanded, so we don't need *-ci version.
            (cond
             ((characterp out-char)
              `(peek-char ,out-char (,body)))
             ((char-set-p out-char)
              `(peek-char-set ,out-char (,body)))
             ((eq out-char 'any-except-newline)
              `(peek-char-set ,*char-set-except-newline* (,body)))
             ((and (not out-char)
                   (eq (cadr out-laset) 'eos)
                   (not (cddr out-laset)))
              `(eos (,body)))
             ((and (not out-char)
                   (eq (cadr out-laset) 'eos-newline)
                   (not (cddr out-laset)))
              `(eos-newline (,body)))
             (t
              (error "regexp internal error: greedy-deterministic: impossible out-char")))))
      (multiple-value-bind (code regs)
          (let ((.reentrant. t))
            (fe-compile-pass3-rec clause t))
        (values `((label ,start)
                  ,out-char-dispatch
                  (jump ,next)
                  (label ,body)
                  ,@code
                  (jump ,start)
                  (label ,next))
                regs)))
    )))

;; General case.
(defun greedy-optional-general (clause minlen)
  (let* ((start (new-label))
         (fail  (new-label))
         (next  (new-label))
         (ipreg (if (= minlen 0) (new-repetition) nil))
         (oldfcont .failure-continuation.))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. fail)
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (setf .failure-continuation. nil)
      (values `(,@(adjust-fcont oldfcont)
                  (label ,start)
                  (try ,fail ,@regs)
                  ,@(and (= minlen 0)
                         `((save-ip (rep ,ipreg))))
                  ,@code
                  ,@(and (= minlen 0)
                         `((branch-if-ip<= (rep ,ipreg) ,next)))
                  (jump ,start)
                  (label ,fail)
                  (pop ,@(reverse regs))
                  (label ,next)
                  )
              ;; we saved all regs by ourselves, so no need to pass it up.
              ()))))

;;.......................................................
;; Greedy bound repetition
;;
(defmethod fe-compile-pass3-rec ((ast ast-greedy-bound-repetition) cont)
  (with-slots (clause max) ast
    (with-slots (minlen fixed) clause
      (cond
       ((= max 0) ;; edge case
        (values () ()))
       ((and fixed (= minlen 0))
        ;; Special case.  It effectively becomes zero-or-one alternation.
        (let ((fail (new-label))
              (next (new-label)))
          (multiple-value-bind (code regs)
              (let ((.failure-continuation. (list fail)))
                (fe-compile-pass3-rec clause cont))
            (values `(,@code
                      (jump ,next)
                      (label ,fail)
                      (invalidate ,@(non-toplevel-sub-registers clause regs))
                      (label ,next))
                    regs))))
       ((and *optimize-stack*
             (simple-ast-p clause)
             (or (not cont)
                 (and (not .reentrant.)
                      (typep cont 'ast)
                      (laset-char-exclusive-p (ast-laset clause)
                                              (ast-laset cont)))))
        ;; We don't need to retry the clause.
        (case max
          (1 (greedy-bound-noretry-1-or-0 clause))
          (2 (greedy-bound-noretry-2-or-1-or-0 clause))
          (t (greedy-bound-noretry clause max))))
       ((and *optimize-stack*
             fixed
             (simple-ast-p clause)
             (not (ast-subs clause)))
        ;; The clause may be retried, but we know its length so we can
        ;; rewind the input pointer by subtraction.
        (greedy-bound-fixed clause max))
       (t
        (greedy-bound-general clause max))
       ))))

;; Nothing follows us, so no backtrack.
(defun greedy-bound-noretry (clause max)
  (let* ((start (new-label))
         (fail  (new-label))
         (next  (new-label))
         (rep   (new-repetition))
         (atomic? (atomic-ast-p clause))
         (ipreg (unless atomic? (new-repetition)))
         (atomic? (atomic-ast-p clause))
         (oldfcont .failure-continuation.))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list fail))
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (let* ((save-subs (non-toplevel-sub-registers clause regs))
             (save-reps (new-repetitions-to-save-subs save-subs)))
        (setf .failure-continuation. nil)
        (values `(,@(adjust-fcont oldfcont)
                  (set (rep ,rep) ,(1- max))
                  (label ,start)
                  ,@(unless atomic? `((save-ip (rep ,ipreg))))
                  ,@(generate-submatch-save save-subs save-reps)
                  ,@code
                  (decrement-branch>=0 (rep ,rep) ,start)
                  (jump ,next)
                  (label ,fail)
                  ,@(unless atomic? `((load-ip (rep ,ipreg))))
                  ,@(generate-submatch-load save-subs save-reps)
                  (label ,next))
                regs)))))

;; Special case of greedy-bound-noretry, where we have 1 or 0
(defun greedy-bound-noretry-1-or-0 (clause)
  (let* ((fail  (new-label))
         (next  (new-label))
         (atomic? (atomic-ast-p clause))
         (oldfcont .failure-continuation.)
         (ipreg (unless atomic? (new-repetition))))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list fail))
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (let* ((save-subs (non-toplevel-sub-registers clause regs))
             (save-reps (new-repetitions-to-save-subs save-subs)))
        (setf .failure-continuation. nil)
        (if (or save-subs (not atomic?))
            (values `(,@(adjust-fcont oldfcont)
                      ,@(unless atomic? `((save-ip (rep ,ipreg))))
                      ,@(generate-submatch-save save-subs save-reps)
                      ,@code
                      (jump ,next)
                      (label ,fail)
                      ,@(unless atomic? `((load-ip (rep ,ipreg))))
                      ,@(generate-submatch-load save-subs save-reps)
                      (label ,next))
                    regs)
          (values `(,@(adjust-fcont oldfcont)
                    ,@code
                    (label ,fail)
                    (label ,next))
                  regs))))))

;; Special case of greedy-bound-noretry, where we have 2, 1 or 0
(defun greedy-bound-noretry-2-or-1-or-0 (clause)
  (let* ((fail  (new-label))
         (next  (new-label))
         (oldfcont .failure-continuation.)
         (atomic? (atomic-ast-p clause))
         (ipreg (unless atomic? (new-repetition))))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list fail))
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (let* ((save-subs (non-toplevel-sub-registers clause regs))
             (save-reps (new-repetitions-to-save-subs save-subs)))
        (setf .failure-continuation. nil)
        (values `(,@(adjust-fcont oldfcont)
                  ,@(unless atomic? `((save-ip (rep ,ipreg))))
                  ,@(generate-submatch-save save-subs save-reps)
                  ,@code
                  ,@(unless atomic? `((save-ip (rep ,ipreg))))
                  ,@(generate-submatch-save save-subs save-reps)
                  ,@code
                  (jump ,next)
                  (label ,fail)
                  ,@(unless atomic? `((load-ip (rep ,ipreg))))
                  ,@(generate-submatch-load save-subs save-reps)
                  (label ,next))
                regs)))))

;; Fixed simple bound repetition
(defun greedy-bound-fixed (clause max)
  (let* ((start (new-label))
         (fail  (new-label))
         (next  (new-label))
         (cfail (new-label))
         (retry (new-label))
         (oldfcont .failure-continuation.))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list fail))
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (let* ((atomic? (atomic-ast-p clause))
             (minlen (ast-minlen clause))
             (ipreg  (new-repetition))
             (count (new-repetition)))
        (setf .failure-continuation. (list cfail))
        (values `((set (rep ,count) ,(1- max))
                  (label ,start)
                  ,@(unless atomic? `((save-ip (rep ,ipreg))))
                  ,@code
                  (decrement-branch>=0 (rep ,count) ,start)
                  (save-ip (rep ,ipreg))
                  (jump ,next)
                  ;; failure within the repetition
                  (label ,fail)
                  ,(if atomic?
                       `(save-ip (rep ,ipreg))
                     `(load-ip (rep ,ipreg)))
                  (jump ,next)
                  ;; failure from the continuation
                  (label ,cfail)
                  (load-ip (rep ,ipreg))
                  (increment-branch< (rep ,count) ,max ,retry)
                  (fail ,oldfcont)

                  (label ,retry)
                  (sub-ip ,minlen t)
                  (save-ip (rep ,ipreg))
                  (label ,next))
                (if .reentrant.
                    (cons `(rep ,count) regs)
                  regs))))))

;; General case.
(defun greedy-bound-general (clause max)
  (let* ((start (new-label))
         (end   (new-label))
         (rep   (new-repetition))
         (fail  (new-label))
         (oldfcont .failure-continuation.))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. fail)
              (.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (setf .failure-continuation. nil)
      (values `(,@(adjust-fcont oldfcont)
                (set (rep ,rep) ,(1- max))
                (label ,start)
                (try ,fail (rep ,rep) ,@regs)
                ,@code
                (decrement-branch>=0 (rep ,rep) ,start)
                (jump ,end)
                (label ,fail)
                (pop ,@(reverse regs) (rep ,rep))
                (label ,end))
              ;; we saved all regs by ourselves, so no need to pass it up.
              ()))))

;;.......................................................
;; Non-greedy optional repetition
;;
(defmethod fe-compile-pass3-rec ((ast ast-non-greedy-optional-repetition) cont)
  (declare (ignore cont))
  (with-slots (clause) ast
    (cond
     ((and *optimize-stack*
           (not .reentrant.)
           (simple-ast-p clause))
      (non-greedy-optional-simple clause))
     (t
      (non-greedy-optional-general clause)))))

;; Fixed size clause
(defun non-greedy-optional-simple (clause)
  (let* ((cfail (new-label))
         (next  (new-label))
         (ipreg (new-repetition))
         )
    (multiple-value-bind (code regs)
        (let ((.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (setf .failure-continuation. (list cfail))
      (values `((save-ip (rep ,ipreg))
                (jump ,next)
                ;; when continuation fails
                (label ,cfail)
                (load-ip (rep ,ipreg))
                ,@code
                (save-ip (rep ,ipreg))
                ;; continuation
                (label ,next))
              (if .reentrant.
                  (cons `(rep ,ipreg) regs)
                regs)))))

;; General case
(defun non-greedy-optional-general (clause)
  (let* ((start (new-label))
         (end   (new-label))
         (fail  (new-label))
         (back  (new-label))
         (oldfcont .failure-continuation.))
    (setf .failure-continuation. fail)
    (multiple-value-bind (code regs)
        (let ((.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (let ((newfcont .failure-continuation.))
        (setf .failure-continuation. nil)
        (values `(,@(adjust-fcont oldfcont)
                  (label ,start)
                  (try ,back)  ;; try #1 - first try the continuation.
                  (jump ,end)
                  (label ,back)
                  (pop)        ;; pop #1 - continuation failed.
                  (try ,fail ,@regs) ;; try #2 - try the clause.
                  ,@code
                  ,@(adjust-fcont newfcont)
                  (jump ,start)
                  (label ,fail)
                  (pop ,@(reverse regs)) ;; pop #2 - clause failed.
                  (fail nil)   ;; fail to the previous failure continuation.
                  (label ,end))
                ;; we saved all regs by ourselves, so no need to pass it up.
                ())))))

;;.......................................................
;; Non-greedy bound repetition
;;
(defmethod fe-compile-pass3-rec ((ast ast-non-greedy-bound-repetition) cont)
  (declare (ignore cont))
  (let* ((clause (ast-clause ast))
         (max   (repetition-max ast))
         (start (new-label))
         (end   (new-label))
         (back  (new-label))
         (fail  (new-label))
         (rep   (new-repetition))
         (oldfcont .failure-continuation.))
    (setf .failure-continuation. fail)
    (multiple-value-bind (code regs)
        (let ((.reentrant. t))
          (fe-compile-pass3-rec clause t))
      (let ((newfcont .failure-continuation.))
        (setf .failure-continuation. nil)
        (values `(,@(adjust-fcont oldfcont)
                    (set (rep ,rep) ,(1- max))
                    (label ,start)
                    (try ,back)   ;; try #1 - first try the continuation.
                    (jump ,end)
                    (label ,back)
                    (pop)         ;; pop #1 - continuation failed.
                    (try ,fail (rep ,rep) ,@regs) ;; try #1 - try the clause.
                    ,@code
                    ,@(adjust-fcont newfcont)
                    (decrement-branch>=0 (rep ,rep) ,start)
                    (jump ,end)
                    (label ,fail)
                    (pop ,@(reverse regs) (rep ,rep)) ;; pop #2 - clause failed.
                    (fail nil)    ;; fail to the previous failure cont.
                    (label ,end))
                (if .reentrant.
                    (cons `(rep ,rep) regs)
                  regs))))))

;;.......................................................
;; Standalone
;;
(defmethod fe-compile-pass3-rec ((ast ast-standalone) cont)  ;; (?>...)
  (declare (ignore cont))
  ;; once matches, standalone won't allow backtrack within it.
  (let* ((oldfcont .failure-continuation.)
         (clause  (ast-clause ast))
         (fail (new-label))
         (next (new-label)))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list fail)))
          (fe-compile-pass3-rec clause nil)) ;; pass NIL to fake this is the end.
      (let* ((use-stack? (fe-stack-needed-p code))
             (spreg  (and use-stack? (new-repetition))))
        (values `(,@(adjust-fcont oldfcont)
                    ,@(and use-stack? `((save-sp (rep ,spreg))))
                    ,@code
                    (jump ,next)
                    (label ,fail)
                    ,@(and use-stack? `((load-sp (rep ,spreg))))
                    (fail ,oldfcont)
                    (label ,next)
                    ,@(and use-stack? `((load-sp (rep ,spreg)))))
                regs)))))

;;.......................................................
;; lookahead and lookbehind
;;
(defmethod fe-compile-pass3-rec ((ast ast-lookahead) cont)
  (declare (ignore cont))
  (with-slots (clause negate) ast
    (cond
     ((and *use-lookahead*
           (or (typep clause 'ast-reference)
               (and (typep clause 'ast-item)
                    (or (characterp (item-item clause))
                        (stringp (item-item clause))
                        (char-set-p (item-item clause)))))
           (lookahead-simple negate clause)))
     (t
      (lookahead-general negate clause)))))

;; special peephole optimization - we don't need to save ip's.
(defun lookahead-simple (negate exp)
  (let* ((next (when negate (new-label)))
         (oldfcont .failure-continuation.)
         (code (let ((.failure-continuation.
                      (if negate (list next) oldfcont))
                     (.peek-match. t))
                 (fe-compile-pass3-rec exp nil))))
    (values `(,@code
              ,@(when negate
                  `((fail ,oldfcont)
                    (label ,next))))
            nil)))

;; general case
(defun lookahead-general (negate exp)
  (let ((fail (new-label))
        (next (unless negate (new-label))))
    (multiple-value-bind (code regs)
        (let ((.failure-continuation. (list fail)))
          (fe-compile-pass3-rec exp nil))
      (let* ((use-stack? (fe-stack-needed-p code))
             (ipr  (new-repetition))
             (spr  (and use-stack? (new-repetition))))
        (values `((save-ip (rep ,ipr))
                  ,@(and use-stack? `((save-sp (rep ,spr))))
                  ,@code
                  (load-ip (rep ,ipr))
                  ,@(and use-stack? `((load-sp (rep ,spr))))
                  ,@(if negate
                        `((fail , .failure-continuation.))
                      `((jump ,next)))
                  (label ,fail)
                  (load-ip (rep ,ipr))
                  ,@(and use-stack? `((load-sp (rep ,spr))))
                  ,@(unless negate
                      `((fail , .failure-continuation.)
                        (label ,next))))
                regs)))))

(defmethod fe-compile-pass3-rec ((ast ast-lookbehind) cont)
  (declare (ignore cont))
  (with-slots (clause negate) ast
    (unless (ast-fixed clause)
      (error "lookbehind assertion has to have a fixed length."))
    (let ((fail (new-label))
          (next (unless negate (new-label)))
          (minlen (ast-minlen clause)))
      (multiple-value-bind (code regs)
          (let ((.failure-continuation. (list fail)))
            (fe-compile-pass3-rec clause nil))
        (let* ((use-stack? (fe-stack-needed-p code))
               (ipr  (new-repetition))
               (spr  (and use-stack? (new-repetition))))
          (values `((save-ip (rep ,ipr))
                    ,@(and use-stack? `((save-sp (rep ,spr))))
                    ,@(and (> minlen 0) `((sub-ip ,minlen ,(list fail))))
                    ,@code
                    ,@(and use-stack? `((load-sp (rep ,spr))))
                    ,@(if negate
                          `((fail , .failure-continuation.))
                        `((jump ,next)))
                    (label ,fail)
                    (load-ip (rep ,ipr))
                    ,@(and use-stack? `((load-sp (rep ,spr))))
                    ,@(unless negate
                        `((fail , .failure-continuation.)
                          (label ,next))))
                  regs))))))

;;.......................................................
;; Conditionals
;;
(defmethod fe-compile-pass3-rec ((ast ast-branch-submatch) cont)
  (with-slots (number yes no) ast
    (multiple-value-bind (code1 regs1) (fe-compile-pass3-rec yes cont)
      (multiple-value-bind (code2 regs2) (fe-compile-pass3-rec no cont)
        (cond
         ((>= number (num-submatches)) ;; condition never satisfied
          (values code2 regs2))
         ((null code2)                 ;; only yes-clause
          (let ((next (new-label)))
            (values `((branch-if-void ,number ,next)
                      ,@code1
                      (label ,next))
                    regs1)))
         (t                               ;; general case
          (let ((next (new-label))
                (else (new-label)))
            (values `((branch-if-void ,number ,else)
                      ,@code1
                      (jump ,next)
                      (label ,else)
                      ,@code2
                      (label ,next))
                    (merge-regs regs1 regs2)
                    ))))))))

(defmethod fe-compile-pass3-rec ((ast ast-branch-lookahead) cont)
  (with-slots (negate condition yes no) ast
    (let ((else (new-label))
          (next (new-label)))
      (multiple-value-bind (code1 regs1) (fe-compile-pass3-rec yes cont)
        (multiple-value-bind (code2 regs2) (fe-compile-pass3-rec no cont)
          (multiple-value-bind (code0 regs0)
              (let ((.failure-continuation. else))
                (fe-compile-pass3-rec condition nil))
            (let* ((use-stack? (fe-stack-needed-p code0))
                   (ipreg (new-repetition))
                   (spreg (and use-stack? (new-repetition))))
              (values `((save-ip (rep ,ipreg))
                        ,@(and use-stack? `((save-sp (rep ,spreg))))
                        (try ,else)
                        ,@code0
                        (load-ip (rep ,ipreg))
                        ,@(and use-stack? `((load-sp (rep ,spreg))))
                        ,@(if negate code2 code1)
                        (jump ,next)
                        (label ,else)
                        (load-ip (rep ,ipreg))
                        ,@(and use-stack? `((load-sp (rep ,spreg))))
                        ,@(if negate code1 code2)
                        (label ,next))
                      (merge-regs regs0 regs1 regs2)
                      ))))))))

(defmethod fe-compile-pass3-rec ((ast ast-branch-lookbehind) cont)
  (with-slots (negate condition yes no) ast
    (let ((else (new-label))
          (next (new-label)))
      (multiple-value-bind (code1 regs1) (fe-compile-pass3-rec yes cont)
        (multiple-value-bind (code2 regs2) (fe-compile-pass3-rec no cont)
          (multiple-value-bind (code0 regs0)
              (let ((.failure-continuation. else))
                (fe-compile-pass3-rec condition nil))
            (unless (ast-fixed condition)
              (error "negative-lookbehind assertion has to have a fixed length."))
            (let* ((minlen0 (ast-minlen condition))
                   (use-stack? (fe-stack-needed-p code0))
                   (ipreg (new-repetition))
                   (spreg (and use-stack? (new-repetition))))
              (values `((save-ip (rep ,ipreg))
                        ,@(and use-stack? `((save-sp (rep ,spreg))))
                        ,@(and (> minlen0 0) `((sub-ip ,minlen0 ,else)))
                        (try ,else)
                        ,@code0
                        (load-ip (rep ,ipreg))
                        ,@(and use-stack? `((load-sp (rep ,spreg))))
                        ,@(if negate code2 code1)
                        (jump ,next)
                        (label ,else)
                        (load-ip (rep ,ipreg))
                        ,@(and use-stack? `((load-sp (rep ,spreg))))
                        ,@(if negate code1 code2)
                        (label ,next))
                      (merge-regs regs0 regs1 regs2)
                      ))))))))

;;;----------------------------------------------------
;;;  Development tools
;;;

;; A development tool for printing fe output more readably.
(defun print-fe (stm fe &rest ignore)
  (declare (ignore ignore))
  (pprint-logical-block (stm fe)
    (loop with e = fe while e
	if (and (consp (car e)) (eq (caar e) 'label))
	do (format stm "~2d " (cadar e))
	   (pop e)
	else do
	     (format stm "   ")
	if (and (consp (car e)) (eq (caar e) 'label))
	do (pprint-newline :linear stm)
	else do
	     (write (car e) :stream stm)
	     (pop e)
	     (when e (pprint-newline :linear stm))))
  (values))

;; Test routine for development
(defun hack-fe (string &key pass ignore-whitespace case-fold
                            single-line multiple-lines)
  (let ((.ignore-case. case-fold)
        (.single-line. single-line)
        (.multiple-lines. multiple-lines)
        (.ignore-whitespace. ignore-whitespace))
    (multiple-value-bind (code nsubs nreps use-stack minlen fixed laset)
        (fe-compile-regexp (parse-re string :extended-mode ignore-whitespace)
                           nil :pass pass)
      (case pass
        ((1 2) code)
        (t
         (format t "nsubs=~d nreps=~d stack=~a minlen=~d fixed=~a~%~
               laset=~s~%~
               code: ~/regexp:print-fe/~%"
                 nsubs nreps use-stack minlen fixed laset code)
         (values))))))


