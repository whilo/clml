;;
;; regexp-vm.cl - Back-end implementation based on VM.
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

;; (excl::defresource backup-vector
;;   :constructor (lambda () (declare (optimize (speed 3) (safety 0))) (make-array 255))
;;   ;; The initialization and reinitialization needs to be done by the inline code.
;;   )

;; Note for submatch register:
;;
;;  Perl allows a submatch to be used before its contents is determined.
;;  If such a submatch hasn't yet have a value, it always fails.
;;     "x" =~ /(a)|\1/   ;; failure
;;  However, if a submatch has matched before, the previous value is used.
;;     "aaaaaa" =~ /^(a\1?){3}$/   ;; success
;;  In the above case, the first repetition matches 'a', the second
;;  matches 'aa' (since \1 contains 'a'), and the third matches 'aaa'
;;  (since \1 contains 'aa).
;;  The submatch registers are canceled, however, if the subtree that includes
;;  the submaches fails.
;;     "aaaaaa" =~ /^(a\1?){3}$|\1/   ;; fails
;;  (When the first alternative fails, the value of \1 is canceled, thus
;;  the next alternative \1 won't match any part of "aaaaaa".)
;;
;;  This behavior can be achieved by using three registers per submatch,
;;  [mark, start, end].  They are all initialized by -1.
;;  When submatch begins, the index is saved in the mark register.  When
;;  submatch ends, the value of the mark register is moved to the start
;;  register, and the input index is saved to the end register.
;;  If the register is referenced, the substring specified by the start
;;  and end register is used (if either of them is -1, the submatch doesn't
;;  have a value).  The "canceling" behavior is automatically handled by
;;  register push/pop.

;; Note on register allocation:
;;
;;  Since we don't know the number of regexp registers at the compile
;;  time of the matcher closure, we can't use local stack frame for them
;;  (wish I could use alloca!).  Allocating separate vector will cost
;;  too much, so we use the beginning portion of the VM stack vector,
;;  which is allocated by resource mechanism, to store registers.
;;
;;  At the regexp compilation time we know exact number of registers,
;;  so we assign the offset for rep registers and sub registers at
;;  assembly time.
;;
;;            stack vector
;;          +-------------+    ------
;;          | (rep 0)     |      ^
;;          | (rep 1)     |      | num-repetitions (R+1)
;;          :    :        :      |
;;          | (rep R)     |      v
;;          | (start 0)   |      ^
;;          | (end 0)     |      |
;;          | (mark 0)    |      |
;;          | (start 1)   |      | num-submatches (S+1) * 3
;;          | (end 1)     |      |
;;          | (mark 1)    |      |
;;          :    :        :      |
;;          | (srart S)   |      |
;;          | (end S)     |      |
;;          | (mark S)    |      v
;;          +-------------+
;;          | stack area  |
;;          |      |      |
;;          |      V      |
;;          :             :
;;
;;  For the assemply instructions that touches multiple registers
;;  (mark, start, end) of a specific submatch, the operand usually
;;  points to the first register (start).   For the assembly instructions
;;  that touches only one register, the operand is the direct offset
;;  to the register.

(defvar *vm-show-disassemble* nil)

;;;==============================================================
;;; The entry called from the driver
;;;


(eval-when (compile load eval)
(defun |property regexp-back-end vm| (code
                                       &key num-submatches
                                            num-repetitions
                                            minimum-length
                                            use-stack
                                            lookahead-set
                                            named-submatches
                                            return-type)
  (make-fast-vm code num-submatches num-repetitions
                minimum-length use-stack lookahead-set
                named-submatches return-type))

(setf (get 'regexp-back-end 'vm)
  (function |property regexp-back-end vm|))
)

;; utility
(eval-when (compile load eval)
(defun symbol-append (sym suffix)
  (intern (format nil "~a~a" (symbol-name sym) (symbol-name suffix))
	  (load-time-value (find-package :regexp))))
)

(eval-when (compile)
  (compile 'symbol-append))

;;;==============================================================
;;; Fast string search utilities
;;;

;; We have Boyer-Moore-Horspool and Knuth-Morris-Pratt implemented here.
;; BMH is faster in general, but it needs space in order of the size
;; of alphabet (if we're using UCS2, needs 65536-element vector).
;; KMP, on the other hand, requires space proportional to the length
;; of matching string (if we have matching string of length 10, we only
;; need 10-element vector).

;; To switch the algorithm, change the following two macros.

(defmacro vm-preprocess-fast-search (matchstr ci?)
  `(vm-make-bmh-vec ,matchstr ,ci?))

(defmacro vm-fast-search (matchstr mlen vec input start end ci?)
  `(vm-bmh-search ,matchstr ,mlen ,vec ,input ,start ,end ,ci?))

;(defmacro vm-preprocess-fast-search (matchstr ci?)
;  `(vm-make-kmp-vec ,matchstr ,ci?))

;(defmacro vm-fast-search (matchstr mlen vec input start end ci?)
;  `(vm-kmp-search ,matchstr ,mlen ,vec ,input ,start ,end ,ci?))


;; Knuth-Morris-Pratt
(defun vm-make-kmp-vec (matchstr ci?)
  (let* ((plen (length matchstr))
         (sv   (make-array (list plen)
                           :element-type 'integer :initial-element -1)))
    (declare (optimize speed))
    (loop for i of-type fixnum below (1- plen)
        do (loop for k of-type fixnum = (1+ (svref sv i))
                                      then (1+ (svref sv (1- k)))
               while (and (> k 0)
                          (not (funcall (if ci? #'char-equal #'char=)
                                        (schar matchstr i)
                                        (schar matchstr (1- k)))))
               finally (setf (svref sv (1+ i)) k)))
    sv))

(defmacro vm-kmp-search (matchstr mlen restarts input start end ci)
  (let ((si (gensym "kmp-si"))
        (sj (gensym "kmp-sj"))
        (mi (gensym "kmp-mi"))
        (mj (gensym "kmp-mj"))
        (ms (gensym "kmp-ms"))
        (next (gensym "kmp-next"))
        (gmlen (gensym "kmp-gmlen")))
    (labels ((gen-srch (cmp)
               `(loop with ,gmlen of-type regexp-dim = ,mlen
                    and ,ms of-type simple-string = ,matchstr
                    and ,si of-type regexp-dim = ,start
                    and ,sj of-type regexp-dim = (- ,end ,start)
                    and ,mi of-type regexp-dim = 0
                    and ,mj of-type regexp-dim = ,mlen
                    if (= ,mi ,gmlen) do (return (- ,si ,gmlen))
                    else if (< ,sj ,mj) do (return nil)
                    else if (,cmp (schar ,ms ,mi) (schar ,input ,si))
                    do (incf ,si) (decf ,sj) (incf ,mi) (decf ,mj)
                    else
                    do (let ((,next (the regexp-dim (svref ,restarts ,mi))))
                         (cond
                          ((= ,next -1)
                           (incf ,si) (decf ,sj)
                           (setf ,mi 0 ,mj ,gmlen))
                          (t (setf ,mi ,next) (decf ,mj ,next)))))))
      (if ci (gen-srch 'char-equal) (gen-srch 'char=)))))

(defun vm-test-kmp-search (matchstr inputstr ci?)
  (let* ((mlen (length matchstr))
         (vec  (vm-make-kmp-vec matchstr ci?))
         (end  (length inputstr)))
    (vm-kmp-search matchstr mlen vec inputstr 0 end ci?)))

;; Boyer-Moore-Horspool
(defun vm-make-bmh-vec (matchstr ci?)
  (declare (simple-string matchstr))
  (let* ((plen (length matchstr))
         (sv (make-array (list +char-code-max+)
                         :element-type 'integer
                         :initial-element plen)))
    (declare (optimize speed))
    (loop for i of-type fixnum below (1- plen)
        do (if (not ci?)
               (setf (svref sv (char-code (schar matchstr i)))
                 (1- (- plen i)))
             (let* ((c  (schar matchstr i))
                    (cu (char-upcase c))
                    (cd (char-downcase c)))
               (setf (svref sv (char-code cu)) (1- (- plen i)))
               (setf (svref sv (char-code cd)) (1- (- plen i))))))
    sv))

(defmacro vm-bmh-search (matchstr mlen skip input start end ci)
  (let ((i (gensym "bmh-i"))
        (c (gensym "bmh-c"))
        (j (gensym "bmh-j"))
        (k (gensym "bmh-k"))
        (gmlen (gensym "bmh-gmlen")))
    (labels ((gen-srch (cmp)
               `(loop with ,gmlen of-type regexp-dim = ,mlen
                    and ,c of-type character
                    and ,i of-type regexp-dim = ,start
                    while (<= ,i (- ,end ,gmlen))
                    do (setf ,c (schar ,input (1- (+ ,i ,gmlen))))
                    if (and (,cmp ,c (schar ,matchstr (1- ,gmlen)))
                            (loop
                                for ,j of-type regexp-dim below (1- ,gmlen)
                                for ,k of-type regexp-dim from ,i
                                always (,cmp (schar ,matchstr ,j)
                                             (schar ,input ,k))))
                    do (return ,i)
                    end
                    do (incf ,i (the regexp-dim (svref ,skip (char-code ,c))))
                    finally (return nil))))
      (if ci (gen-srch 'char-equal) (gen-srch 'char=)))))

(defun vm-test-bmh-search (matchstr inputstr ci?)
  (let* ((mlen (length matchstr))
         (vec  (vm-make-bmh-vec matchstr ci?))
         (end  (length inputstr)))
    (vm-bmh-search matchstr mlen vec inputstr 0 end ci?)))

;;;==============================================================
;;;  VM back-end
;;;

;; VM instructions
;;  Back-end VM instructions are encoded in fixnum.
;;  The rule of thumb of efficient VM is (a) to increase functions performed
;;  per instruction, and (b) to reduce the total number of instructions.
;;  That leads to CISC-like instruction set.
;;
;;  The VM has variable length instruction set.  The first word is an
;;  opcode (OPC), that determines how many operands (IMMn) that follow
;;  the opcode.  So far we have 6 types of instructions.
;;
;;    type 0:  OPC only
;;    type 1:  OPC + IMM0
;;    type 2:  OPC + IMM0 + IMM1
;;    type 3:  OPC + IMM0 + IMM1 + IMM2
;;    type 4:  OPC + IMM0 + IMM1 + IMM2 + IMM3
;;    type 5:  OPC + IMM0 + IMM1 + IMM2 + IMM3 + IMM5
;;
;;  Match instructions that may fail have the following variations
;;    */t    - complete failure
;;    */nil  - jump to stack top
;;    */pop  - jump to given address, popping stack top
;;    *      - jump to given address.
;;
;;  Some match instructions also have 'p' prefixed form.  That indicates
;;  the match action doesn't increment input pointer.
;;
;;  Note that VM doesn't use a submatch register 0.  Assembler offsets
;;  submatch register number accordingly.

(eval-when (compile load eval)

;;-----------------------------------------------------------
;; Instruction definitions
;;
(defparameter *vm-insn*
    ;; (OPCODE TYPE [IMM-TYPE])
    ;;    TYPE = 0 | 1 | 2
    ;;    IMM-TYPE = c (char) | v (index to const vector)
    `(;; outer-loop stuff
      (cil          0)   ;; check-input-length
      (iil          0)   ;; initialize-inner-loop
      (cil+iil      0)   ;; combined above two
      (ril          0)   ;; reset-inner-loop
      (isi1         0)   ;; increment-start-index by 1
      (isi          1)   ;; increment-start-index by IMM0
      (isi1+cil     0)   ;; isi1 + cil combined insn
      (isi+cil      1)   ;; isi + cil combined insn
      (asi-char     1 c) ;; advance-start-index
      (asi-cs7      1 v) ;;
      (asi-cs7+     1 v) ;;
      (asi-cs8      1 v) ;;
      (asi-cs8+     1 v) ;;
      (asi-cs16     1 v) ;;
      ;(asi-bol      0)
      (fts          2 v) ;; floating-tail-string IMM0=string IMM1=skip vector
      (fts-ci       2 v)
      (sfts         1)   ;; start-from-tail-string

      ;; unconditional jumps
      (jump         1)   ;; IMM0 is label
      (jump-reg     1)   ;; IMM0 is (rep N)
      (success      0)   ;; match success

      ;; saving and loading.  IMM0 is register number (rep N).
      ;; For combined OP (*-isp), IMM0 is register for ip and IMM1
      ;; is register for sp.
      ;; save-sub and load-sub uses IMM0 for submatch reg, and
      ;; IMM1 and IMM2 for repetition reg.
      (save-ip      1) (save-sp      1) (save-isp     2)
      (load-ip      1) (load-sp      1) (load-isp     2)
      (save-sub     3)
      (load-sub     3)

      ;; push/pop.  IMM0 is the register number for *-rep/sub,
      ;; and label for push-ip.   (NB: pop-ip doesn't care about label).
      ;; The combined instruction push-repip and push-subip
      ;; uses IMM1 for target address.
      (push-rep     1) (push-sub     1)
      (push-repip   2) (push-subip   2)
      (push-ip      1)
      (push-fc      1)
      (pop-rep      1) (pop-sub      1)
      (pop-repip    1) (pop-subip    1)
      (pop-ip       0)

      ;; submatch.  IMM0 is the register number.
      (start-sub    1) (end-sub      1)
      (cancel-sub   1)   ;; invalidate
      (set-sub      2)   ;; IMM0=reg, IMM1=length
      (load/set-sub 5)   ;; IMM0=subreg, IMM1/IMM2/IMM3=regs, IMM4=length


      ;; register operations.  IMM0 is the register.
      ;; IMM1 is immediate value. (set, sub-sub)
      (reset        1)   ;; reset (rep N)
      (dec          1)   ;; decrement (rep N)
      (inc          1)   ;; increment (rep N)
      (inc-jump     2)   ;; combining (inc (rep IMM0)) (jump IMM1)
      (set          2)   ;; set (rep N) value
      (sub-sub      2)   ;; subtract value from (sub N)
      (sub-ipsave   2)   ;; combining (sub-ip/t IMM0) (save-ip (rep IMM1))

      ;; conditional branches.  IMM0 is the register number.
      ;; IMM1 is the target address.
      (dec-bgez     2)   ;; decrement (rep N), branch to IMM1 if >= 0.
      (inc-blt      3)   ;; increment (rep N), branch to IMM2 if < IMM1.
      (biple        2)   ;; if IP <= IMM0, branch to IMM1
      (bv           2)   ;; if (sub N) is void, branch to IMM1.

      ;; Match instructions.
      ;; char - IMM0 is charcode.
      (char/t     1 c) (char/nil     1 c) (char/pop     2 c) (char      2 c)
      (char-ci/t  1 c) (char-ci/nil  1 c) (char-ci/pop  2 c) (char-ci   2 c)
      (pchar/t    1 c) (pchar/nil    1 c) (pchar/pop    2 c) (pchar     2 c)
      (pchar-ci/t 1 c) (pchar-ci/nil 1 c) (pchar-ci/pop 2 c) (pchar-ci  2 c)
      ;; char-set - IMM0 is index to constant vector
      (cs7/t      1 v) (cs7/nil      1 v) (cs7/pop      2 v) (cs7       2 v)
      (cs7+/t     1 v) (cs7+/nil     1 v) (cs7+/pop     2 v) (cs7+      2 v)
      (cs8/t      1 v) (cs8/nil      1 v) (cs8/pop      2 v) (cs8       2 v)
      (cs8+/t     1 v) (cs8+/nil     1 v) (cs8+/pop     2 v) (cs8+      2 v)
      (cs16/t     1 v) (cs16/nil     1 v) (cs16/pop     2 v) (cs16      2 v)
      (pcs7/t     1 v) (pcs7/nil     1 v) (pcs7/pop     2 v) (pcs7      2 v)
      (pcs7+/t    1 v) (pcs7+/nil    1 v) (pcs7+/pop    2 v) (pcs7+     2 v)
      (pcs8/t     1 v) (pcs8/nil     1 v) (pcs8/pop     2 v) (pcs8      2 v)
      (pcs8+/t    1 v) (pcs8+/nil    1 v) (pcs8+/pop    2 v) (pcs8+     2 v)
      (pcs16/t    1 v) (pcs16/nil    1 v) (pcs16/pop    2 v) (pcs16     2 v)
      ;; string -  IMM0 is index to constant vector
      (str/t      1 v) (str/nil      1 v) (str/pop      2 v) (str       2 v)
      (str-ci/t   1 v) (str-ci/nil   1 v) (str-ci/pop   2 v) (str-ci    2 v)
      (pstr/t     1 v) (pstr/nil     1 v) (pstr/pop     2 v) (pstr      2 v)
      (pstr-ci/t  1 v) (pstr-ci/nil  1 v) (pstr-ci/pop  2 v) (pstr-ci   2 v)
      (tstr/t     1 v) (tstr/nil     1 v) (tstr/pop     2 v) (tstr      2 v)
      (tstr-ci/t  1 v) (tstr-ci/nil  1 v) (tstr-ci/pop  2 v) (tstr-ci   2 v)

      ;; reference -  IMM0 is submatch number
      (ref/t        1) (ref/nil      1) (ref/pop      2) (ref          2)
      (ref-ci/t     1) (ref-ci/nil   1) (ref-ci/pop   2) (ref-ci       2)
      (pref/t       1) (pref/nil     1) (pref/pop     2) (pref         2)
      (pref-ci/t    1) (pref-ci/nil  1) (pref-ci/pop  2) (pref-ci      2)
      ;; any and any-except-newline
      (any/t        0) (any/nil      0) (any/pop      1) (any          1)
      (any-nl/t     0) (any-nl/nil   0) (any-nl/pop   1) (any-nl       1)
      ;; assertions
      (bol/t        0) (bol/nil      0) (bol/pop      1) (bol          1)
      (eol/t        0) (eol/nil      0) (eol/pop      1) (eol          1)
      (bos/t        0) (bos/nil      0) (bos/pop      1) (bos          1)
      (eos/t        0) (eos/nil      0) (eos/pop      1) (eos          1)
      (eos-nl/t     0) (eos-nl/nil   0) (eos-nl/pop   1) (eos-nl       1)
      (wb/t         0) (wb/nil       0) (wb/pop       1) (wb           1)
      (nwb/t        0) (nwb/nil      0) (nwb/pop      1) (nwb          1)
      ;; unconditional failure
      (fail/t       0) (fail/nil     0) (fail/pop     1) (fail         1)
      ;; sub-ip - IMM0 is integer value to subtract
      (sub-ip/t     1) (sub-ip/nil   1) (sub-ip/pop   2) (sub-ip       2)

      ;; Specialized matcher  (corresponds to repeat-*)
      ;; Capturing version (char*-sub etc) takes submatch register number.
      (char*      1 c) (char*-sub    2 c)
      (char-ci*   1 c) (char-ci*-sub 2 c)
      (cs7*       1 v) (cs7*-sub     2 v)
      (cs7+*      1 v) (cs7+*-sub    2 v)
      (cs8*       1 v) (cs8*-sub     2 v)
      (cs8+*      1 v) (cs8+*-sub    2 v)
      (cs16*      1 v) (cs16*-sub    2 v)
      (str*       1 v) (str*-sub     2 v)
      (str-ci*    1 v) (str-ci*-sub  2 v)
      (any*       0)   (any*-sub     1)
      (any-nl*    0)   (any-nl*-sub  1)

      ;; repeat-until/push special instruction.
      ;;  IMM0 specifies the type of <char-set-in>; cs7, cs7+, cs8, cs8+, cs16
      ;;  IMM1 is an index to constant vector for <char-set-in>
      ;;  IMM2 is <limit> (char, char-set-vector, or anchor)
      ;;  IMM3 is <label>
      (ruchar     4) (ruanchor   4)
      (rucs7      4) (rucs7+     4)
      (rucs8      4) (rucs8+     4)
      (rucs16     4)

      ;;  IMM0 is <limit>, IMM1 is <label>
      (rauchar    2 c) (rauanchor  2)
      (raucs7     2 v) (raucs7+    2 v)
      (raucs8     2 v) (raucs8+    2 v)
      (raucs16    2 v)
      (rnuchar    2 c) (rnuanchor  2)
      (rnucs7     2 v) (rnucs7+    2 v)
      (rnucs8     2 v) (rnucs8+    2 v)
      (rnucs16    2 v)

      ;; Tail constraint matcher.  IMM0 is string.
      ))

(defparameter *vm-insn-code*
    (loop with code = 0
        for insn in *vm-insn*
        collect (cons (car insn) code)
        do (incf code)))

(defun vm-insn-code (insn) ;; insn symbol -> code number
  (let ((code (cdr (assoc insn *vm-insn-code*))))
    (unless code
      (error "regexp internal error: bad insn ~s" insn))
    code))

(defun vm-insn-type (insn) ;; insn symbol -> type
  (cadr (assoc insn *vm-insn*)))
)

(eval-when (compile)
  (compile 'vm-insn-code))

;;-----------------------------------------------------------
;; Assembler and disassembler
;;
(defun vm-assemble (fe-code nsubs nreps)
  (declare (ignore nsubs))
  (let* ((labelmap ()) ;; assoc list of label# to code-vector address
         (relocmap ()) ;; assoc list of code vector offset and label #
         (codes fe-code)
         (codevec (make-array '(0) :fill-pointer 0 :adjustable t
                              :element-type 'fixnum))
         (constvec (make-array '(0) :fill-pointer 0 :adjustable t))
         (fts-alist ()) ;; assoc list of string and skip vector.
                        ;; used to cache skip vector for fts.
         )
    (labels ((nextcode () (and codes (pop codes)))
             (peekcode () (and codes (car codes)))
             ;; submatch register offset.  subN is the submatch number.
             ;; note that sub0 is treated differently, so we exclude it.
             (sub-start (subN)
               (+ (* (1- subN) 3) nreps))
             (sub-mark (subN)
               (+ (* (1- subN) 3) nreps 2))
             ;; emit instruction
             (emit0 (insn)
               (vector-push-extend (vm-insn-code insn) codevec))
             (emit1 (insn imm0)
               (vector-push-extend (vm-insn-code insn) codevec)
               (vector-push-extend imm0 codevec))
             (emit2 (insn imm0 imm1)
               (vector-push-extend (vm-insn-code insn) codevec)
               (vector-push-extend imm0 codevec)
               (vector-push-extend imm1 codevec))
             (emit3 (insn imm0 imm1 imm2)
               (vector-push-extend (vm-insn-code insn) codevec)
               (vector-push-extend imm0 codevec)
               (vector-push-extend imm1 codevec)
               (vector-push-extend imm2 codevec))
             (emit4 (insn imm0 imm1 imm2 imm3)
               (vector-push-extend (vm-insn-code insn) codevec)
               (vector-push-extend imm0 codevec)
               (vector-push-extend imm1 codevec)
               (vector-push-extend imm2 codevec)
               (vector-push-extend imm3 codevec))
             (emit5 (insn imm0 imm1 imm2 imm3 imm4)
               (vector-push-extend (vm-insn-code insn) codevec)
               (vector-push-extend imm0 codevec)
               (vector-push-extend imm1 codevec)
               (vector-push-extend imm2 codevec)
               (vector-push-extend imm3 codevec)
               (vector-push-extend imm4 codevec))
             (mark-reloc (label)
               (push (cons (1- (fill-pointer codevec)) label) relocmap))
             (emit/fc1 (insn fc)
               (cond
                ((eq fc t)     (emit0 (symbol-append insn '/t)))
                ((not fc)      (emit0 (symbol-append insn '/nil)))
                ((integerp fc) (emit1 (symbol-append insn '/pop) 0)
                               (mark-reloc fc))
                ((consp fc)    (emit1 insn 0)
                               (mark-reloc (car fc)))
                (t (error "emit/fc1: bad failure continuation: ~s" fc))))
             (emit/fc2 (insn fc imm)
               (cond
                ((eq fc t)     (emit1 (symbol-append insn '/t) imm))
                ((not fc)      (emit1 (symbol-append insn '/nil) imm))
                ((integerp fc) (emit2 (symbol-append insn '/pop) imm 0)
                               (mark-reloc fc))
                ((consp fc)    (emit2 insn imm 0)
                               (mark-reloc (car fc)))
                (t (error "emit/fc2: bad failure continuation: ~s" fc))))
;             (emit/fc3 (insn fc imm0 imm1)
;               (cond
;                ((eq fc t)     (emit2 (symbol-append insn '/t) imm0 imm1))
;                ((not fc)      (emit2 (symbol-append insn '/nil) imm0 imm1))
;                ((integerp fc) (emit3 (symbol-append insn '/pop) imm0 imm1 0)
;                               (mark-reloc fc))
;                ((consp fc)    (emit3 insn imm0 imm1 0)
;                               (mark-reloc (car fc)))
;                (t (error "emit/fc3: bad failure continuation: ~s" fc))))
;             (emit/fc4 (insn fc imm0 imm1 imm2)
;               (cond
;                ((eq fc t)     (emit3 (symbol-append insn '/t) imm0 imm1 imm2))
;                ((not fc)      (emit3 (symbol-append insn '/nil) imm0 imm1 imm2))
;                ((integerp fc) (emit4 (symbol-append insn '/pop) imm0 imm1 imm2 0)
;                               (mark-reloc fc))
;                ((consp fc)    (emit4 insn imm0 imm1 imm2 0)
;                               (mark-reloc (car fc)))
;                (t (error "emit/fc4: bad failure continuation: ~s" fc))))
             (emit/r0 (insn sub)
               (if sub
                   (emit1 (symbol-append insn '*-sub) (sub-start (cadr sub)))
                 (emit0 (symbol-append insn '*))))
             (emit/r1 (insn imm sub)
               (if sub
                   (emit2 (symbol-append insn '*-sub) imm (sub-start (cadr sub)))
                 (emit1 (symbol-append insn '*) imm)))
             (emit/ru4 (insn char-set-in arg label)
               (let* ((cs (char-set-ensure-bitvector char-set-in))
                      (bvtype (cstype-index (char-set-bitvector-type cs)))
                      (bvindex (newconst (char-set-bitvector cs))))
                 (ecase insn
                   (ruchar (emit4 insn bvtype bvindex (char-code arg) 0))
                   (rucs7  (emit4 insn bvtype bvindex (newconst arg) 0))
                   (rucs7+ (emit4 insn bvtype bvindex (newconst arg) 0))
                   (rucs8  (emit4 insn bvtype bvindex (newconst arg) 0))
                   (rucs8+ (emit4 insn bvtype bvindex (newconst arg) 0))
                   (rucs16 (emit4 insn bvtype bvindex (newconst arg) 0))
                   (ruanchor (emit4 insn bvtype bvindex (anchor-index arg) 0))
                   )
                 (mark-reloc label)))
             (cstype-index (cstype)
               (or (cdr (assoc cstype '((cs7 . 0) (cs7+ . 1)
                                        (cs8 . 2) (cs8+ . 3) (cs16 . 4))))
                   (error "bad cstype:~s~%" cstype)))
             (anchor-index (anchor)
               (or (cdr (assoc anchor '((bol . 0) (eol . 1) (bos . 2)
                                        (eos . 3) (eos-newline . 4)
                                        (word-boundary . 5)
                                        (not-word-boundary . 6))))
                   (error "bad anchor:~s~%" anchor)))
             (newconst (obj)
               (loop for i below (length constvec)
                   if (equal (aref constvec i) obj)
                   return i
                   finally (return (vector-push-extend obj constvec))))
             )
      ;; Fill in the code vector
      (loop for c = (nextcode)
          while c
          do (ecase (car c)
               ((label)
                (push (cons (cadr c) (fill-pointer codevec)) labelmap))
               ((jump)
                (emit1 'jump 0) (mark-reloc (cadr c)))
               ((jump-reg)
                (emit1 'jump-reg (cadadr c)))
               ((success)
                (emit0 'success))
               ((check-input-length)
                (if (eq (car (peekcode)) 'initialize-inner-loop)
                    (progn
                      (nextcode)
                      (emit0 'cil+iil))
                  (emit0 'cil)))
               ((reset-inner-loop)
                (emit0 'ril))
               ((initialize-inner-loop)
                (emit0 'iil))
               ((increment-start-index)
                (if (eq (car (peekcode)) 'check-input-length)
                    (progn
                      (nextcode)
                      (if (= (cadr c) 1)
                          (emit0 'isi1+cil)
                        (emit1 'isi+cil (cadr c))))
                  (if (= (cadr c) 1)
                          (emit0 'isi1)
                        (emit1 'isi (cadr c)))))
               ((advance-start-index)
                (destructuring-bind (condition) (cdr c)
                  (etypecase condition
                   (character (emit1 'asi-char (char-code condition)))
                   (char-set
                    (let* ((bv (char-set-bitvector
                                (char-set-ensure-bitvector condition)))
                           (bvtype (char-set-bitvector-type condition))
                           (imm0 (newconst bv)))
                      (emit1 (symbol-append 'asi- bvtype) imm0)))
                   )))
               ((floating-tail-string floating-tail-string-ci)
                (let* ((str (cadr c))
                       (ci? (eq (car c) 'floating-tail-string-ci))
                       (strindex (newconst str))
                       (skipvec (let ((p (assoc str fts-alist :test #'equal)))
                                  (if p
                                      (cdr p)
                                    (let ((v (vm-preprocess-fast-search str ci?)))
                                      (push (cons str v) fts-alist)
                                      v))))
                       (vecindex (newconst skipvec))
                       (insn (if ci? 'fts-ci 'fts)))
                  (emit2 insn strindex vecindex)))
               ((start-from-tail-string)
                (emit1 'sfts (cadr c)))
               ((save-ip)
                (if (eq (car (peekcode)) 'save-sp)
                    (emit2 'save-isp (cadadr c) (cadadr (nextcode)))
                  (emit1 'save-ip (cadadr c))))
               ((save-sp)
                (if (eq (car (peekcode)) 'save-ip)
                    (emit2 'save-isp (cadadr (nextcode)) (cadadr c))
                  (emit1 'save-sp (cadadr c))))
               ((submatch-save)
                (destructuring-bind (sub rep1 rep2) (cdr c)
                  (emit3 'save-sub (sub-start (cadr sub))
                         (cadr rep1) (cadr rep2))))
               ((load-ip)
                (if (eq (car (peekcode)) 'load-sp)
                    (emit2 'load-isp (cadadr c) (cadadr (nextcode)))
                  (emit1 'load-ip (cadadr c))))
               ((load-sp)
                (if (eq (car (peekcode)) 'load-ip)
                    (emit2 'load-isp (cadadr (nextcode)) (cadadr c))
                  (emit1 'load-sp (cadadr c))))
               ((submatch-load)
                (destructuring-bind (sub rep1 rep2) (cdr c)
                  (emit3 'load-sub (sub-start (cadr sub))
                         (cadr rep1) (cadr rep2))))
               ((submatch-load-or-set)
                (destructuring-bind (sub repk repi repj len) (cdr c)
                  (emit5 'load/set-sub (sub-start (cadr sub))
                         (cadr repk) (cadr repi) (cadr repj) len)))
               ((try)
                (destructuring-bind (label . regs) (cdr c)
                  (cond
                   ((consp regs)
                    (loop for reg = (pop regs)
                        while reg
                        as (type num) = reg
                        if regs
                        do (ecase type
                             (rep (emit1 'push-rep num))
                             (sub (emit1 'push-sub (sub-start num))))
                        else
                        do (ecase type
                             ((rep) (emit2 'push-repip num 0)
                                    (mark-reloc label))
                             ((sub) (emit2 'push-subip (sub-start num) 0)
                                    (mark-reloc label)))))
                   (t
                    (emit1 'push-ip 0) (mark-reloc (cadr c))))))
               ((push-fc)
                (emit1 'push-fc 0) (mark-reloc (cadr c)))
               ((pop)
                (cond
                 ((consp (cdr c))
                  (destructuring-bind ((type num) . regs) (cdr c)
                    (ecase type
                      (rep (emit1 'pop-repip num))
                      (sub (emit1 'pop-subip (sub-start num))))
                    (loop for reg in regs
                        as (type num) = reg
                        do (ecase type
                             (rep (emit1 'pop-rep num))
                             (sub (emit1 'pop-sub (sub-start num)))))))
                 (t
                  (emit0 'pop-ip))))
               ((submatch-start)
                (let ((n (cadadr c)))
                  (emit1 'start-sub (sub-mark n))))
               ((submatch-end)
                (let ((n (cadadr c)))
                  (emit1 'end-sub (sub-start n))))
               ((submatch-set)
                (destructuring-bind ((_ num) start-off) (cdr c)
                  (declare (ignore _))
                  (emit2 'set-sub (sub-start num) start-off)))
               ((invalidate)
                (loop for (type num) in (cdr c)
                    if (eq type 'sub)
                    do (emit1 'cancel-sub (sub-start num))))
               ((sub-sub)
                (destructuring-bind ((_ num) value) (cdr c)
                  (declare (ignore _))
                  (emit2 'sub-sub (sub-start num) value)))
               ((cut)
                (error "cut is obsoleted."))
               ((dec)
                (emit1 'dec (cadadr c)))
               ((inc)
                (let ((reg (cadadr c)))
                  (if (eq (car (peekcode)) 'jump)
                      ;; Special, but appears frequently in tight loop.
                      ;; so we combine them.
                      (let ((label (cadr (nextcode))))
                        (emit2 'inc-jump reg 0)
                        (mark-reloc label))
                    (emit1 'inc reg))))
               ((set)
                (destructuring-bind ((rep num) value) (cdr c)
                  (declare (ignore rep))
                  (if (= value 0)
                      (emit1 'reset num)
                    (emit2 'set num value))))
               ((set-label)
                (emit2 'set (cadadr c) 0)
                (mark-reloc (caddr c)))
               ((decrement-branch>=0)
                (destructuring-bind ((rep num) label) (cdr c)
                  (declare (ignore rep))
                  (emit2 'dec-bgez num 0)
                  (mark-reloc label)))
               ((increment-branch<)
                (destructuring-bind ((rep num) val label) (cdr c)
                  (declare (ignore rep))
                  (emit3 'inc-blt num val 0)
                  (mark-reloc label)))
               ((branch-if-ip<=)
                (emit2 'biple (cadadr c) 0)
                (mark-reloc (caddr c)))
               ((branch-if-void)
                (emit2 'bv (sub-start (cadr c)) 0)
                (mark-reloc (caddr c)))
               ((char)
                (destructuring-bind (ch fail) (cdr c)
                  (emit/fc2 'char fail (char-code ch))))
               ((char-ci)
                (destructuring-bind (ch fail) (cdr c)
                  (emit/fc2 'char-ci fail (char-code ch))))
               ((peek-char)
                (destructuring-bind (ch fail) (cdr c)
                  (emit/fc2 'pchar fail (char-code ch))))
               ((peek-char-ci)
                (destructuring-bind (ch fail) (cdr c)
                  (emit/fc2 'pchar-ci fail (char-code ch))))
               ((char-set char-set-ci)
                (destructuring-bind (cs fail) (cdr c)
                  (let* ((cs (char-set-ensure-bitvector cs))
                         (bv (char-set-bitvector cs))
                         (type (char-set-bitvector-type cs))
                         (ci (newconst bv)))
                    (ecase type
                      (cs7  (emit/fc2 'cs7  fail ci))
                      (cs7+ (emit/fc2 'cs7+ fail ci))
                      (cs8  (emit/fc2 'cs8  fail ci))
                      (cs8+ (emit/fc2 'cs8+ fail ci))
                      (cs16 (emit/fc2 'cs16 fail ci))))))
               ((peek-char-set peek-char-set-ci)
                (destructuring-bind (cs fail) (cdr c)
                  (let* ((cs (char-set-ensure-bitvector cs))
                         (bv (char-set-bitvector cs))
                         (type (char-set-bitvector-type cs))
                         (ci (newconst bv)))
                    (ecase type
                      (cs7  (emit/fc2 'pcs7  fail ci))
                      (cs7+ (emit/fc2 'pcs7+ fail ci))
                      (cs8  (emit/fc2 'pcs8  fail ci))
                      (cs8+ (emit/fc2 'pcs8+ fail ci))
                      (cs16 (emit/fc2 'pcs16 fail ci))))))
               ((string)
                (destructuring-bind (str fail) (cdr c)
                  (emit/fc2 'str fail (newconst str))))
               ((string-ci)
                (destructuring-bind (str fail) (cdr c)
                  (emit/fc2 'str-ci fail (newconst str))))
               ((peek-string)
                (destructuring-bind (str fail) (cdr c)
                  (emit/fc2 'pstr fail (newconst str))))
               ((peek-string-ci)
                (destructuring-bind (str fail) (cdr c)
                  (emit/fc2 'pstr-ci fail (newconst str))))
               ((tail-string)
                (destructuring-bind (str fail) (cdr c)
                  (emit/fc2 'tstr fail (newconst str))))
               ((tail-string-ci)
                (destructuring-bind (str fail) (cdr c)
                  (emit/fc2 'tstr-ci fail (newconst str))))
               ((reference)
                (destructuring-bind (num fail) (cdr c)
                  (emit/fc2 'ref fail (sub-start num))))
               ((reference-ci)
                (destructuring-bind (num fail) (cdr c)
                  (emit/fc2 'ref-ci fail (sub-start num))))
               ((peek-reference)
                (destructuring-bind (num fail) (cdr c)
                  (emit/fc2 'pref fail (sub-start num))))
               ((peek-reference-ci)
                (destructuring-bind (num fail) (cdr c)
                  (emit/fc2 'pref-ci fail (sub-start num))))
               ((any)
                (emit/fc1 'any (cadr c)))
               ((any-except-newline)
                (emit/fc1 'any-nl (cadr c)))
               ((bol)
                (emit/fc1 'bol (cadr c)))
               ((eol)
                (emit/fc1 'eol (cadr c)))
               ((bos)
                (emit/fc1 'bos (cadr c)))
               ((eos)
                (emit/fc1 'eos (cadr c)))
               ((eos-newline)
                (emit/fc1 'eos-nl (cadr c)))
               ((word-boundary)
                (emit/fc1 'wb  (cadr c)))
               ((not-word-boundary)
                (emit/fc1 'nwb (cadr c)))
               ((fail)
                (emit/fc1 'fail (cadr c)))
               ((sub-ip)
                (destructuring-bind (val fail) (cdr c)
                  (if (and (eq fail t)
                           (eq (car (peekcode)) 'save-ip))
                      ;; special, but frequently used combination
                      (let* ((c (nextcode))
                             (reg (cadadr c)))
                        (emit2 'sub-ipsave val reg))
                    (emit/fc2 'sub-ip fail val))))
               ((repeat-char)
                (destructuring-bind (ch sub) (cdr c)
                  (emit/r1 'char (char-code ch) sub)))
               ((repeat-char-ci)
                (destructuring-bind (ch sub) (cdr c)
                  (emit/r1 'char-ci (char-code ch) sub)))
               ((repeat-char-set repeat-char-set-ci)
                (destructuring-bind (cs sub) (cdr c)
                  (let* ((cs (char-set-ensure-bitvector cs))
                         (bv (char-set-bitvector cs))
                         (type (char-set-bitvector-type cs))
                         (ci (newconst bv)))
                    (ecase type
                      (cs7  (emit/r1 'cs7  ci sub))
                      (cs7+ (emit/r1 'cs7+ ci sub))
                      (cs8  (emit/r1 'cs8  ci sub))
                      (cs8+ (emit/r1 'cs8+ ci sub))
                      (cs16 (emit/r1 'cs16 ci sub))))))
               ((repeat-string)
                (destructuring-bind (str sub) (cdr c)
                  (emit/r1 'str (newconst str) sub)))
               ((repeat-string-ci)
                (destructuring-bind (str sub) (cdr c)
                  (emit/r1 'str-ci (newconst str) sub)))
               ((repeat-any)
                (emit/r0 'any (cadr c)))
               ((repeat-any-except-newline)
                (emit/r0 'any-nl (cadr c)))
               ((repeat-until/push)
                (destructuring-bind (member limit label) (cdr c)
                  (cond
                   ((char-set-p member)
                    (cond
                     ((characterp limit)
                      (emit/ru4 'ruchar member limit label))
                     ((char-set-p limit)
                      (let* ((cs (char-set-ensure-bitvector limit))
                             (bv (char-set-bitvector cs))
                             (type (char-set-bitvector-type cs)))
                        (ecase type
                          (cs7  (emit/ru4 'rucs7  member bv label))
                          (cs7+ (emit/ru4 'rucs7+ member bv label))
                          (cs8  (emit/ru4 'rucs8  member bv label))
                          (cs8+ (emit/ru4 'rucs8+ member bv label))
                          (cs16 (emit/ru4 'rucs16 member bv label)))))
                     ((symbolp limit)
                      (emit/ru4 'ruanchor member limit label))))
                   ((eq member 'any)
                    (cond
                     ((characterp limit)
                      (emit2 'rauchar (char-code limit) 0)
                      (mark-reloc label))
                     ((char-set-p limit)
                      (let* ((cs (char-set-ensure-bitvector limit))
                             (bv (char-set-bitvector cs))
                             (type (char-set-bitvector-type cs)))
                        (ecase type
                          (cs7  (emit2 'raucs7  (newconst bv) 0))
                          (cs7+ (emit2 'raucs7+ (newconst bv) 0))
                          (cs8  (emit2 'raucs8  (newconst bv) 0))
                          (cs8+ (emit2 'raucs8+ (newconst bv) 0))
                          (cs16 (emit2 'raucs16 (newconst bv) 0)))
                        (mark-reloc label)))
                     ((symbolp limit)
                      (emit2 'rauanchor (anchor-index limit) 0)
                      (mark-reloc label))))
                   ((eq member 'any-except-newline)
                    (cond
                     ((characterp limit)
                      (emit2 'rnuchar (char-code limit) 0)
                      (mark-reloc label))
                     ((char-set-p limit)
                      (let* ((cs (char-set-ensure-bitvector limit))
                             (bv (char-set-bitvector cs))
                             (type (char-set-bitvector-type cs)))
                        (ecase type
                          (cs7  (emit2 'rnucs7  (newconst bv) 0))
                          (cs7+ (emit2 'rnucs7+ (newconst bv) 0))
                          (cs8  (emit2 'rnucs8  (newconst bv) 0))
                          (cs8+ (emit2 'rnucs8+ (newconst bv) 0))
                          (cs16 (emit2 'rnucs16 (newconst bv) 0)))
                        (mark-reloc label)))
                     ((symbolp limit)
                      (emit2 'rnuanchor (anchor-index limit) 0)
                      (mark-reloc label))))
                   (t
                    (error "regexp internal error: bad repeat-until/push")))))
               ))
      ;; Fill in jump destinations
      (loop for (loc . label) in relocmap
          do (let ((addr (cdr (assoc label labelmap))))
               (unless addr
                 (error "regexp internal error: undefined label usage"))
               (setf (aref codevec loc)
                 (logior addr (aref codevec loc)))))
      ;; Peephole optimization--if jump destination is jump or success,
      ;; shortcut them.
      (loop with code-jump = (vm-insn-code 'jump)
          and code-success = (vm-insn-code 'success)
          and code = nil
          for i below (length codevec)
          do (setf code (aref codevec i))
             (when (= code code-jump)
               (loop for imm = (aref codevec (1+ i))
                   while (let ((c (aref codevec imm)))
                           (cond
                            ((= c code-jump)
                             (setf (aref codevec (1+ i))
                               (aref codevec (1+ imm))))
                            ((= c code-success)
                             (setf (aref codevec i) code-success)
                             (setf (aref codevec (1+ i)) code-success)
                             nil)
                            (t nil)))))
             (let* ((insn (nth code *vm-insn*))
                    (type (cadr insn)))
               (incf i type)))
      ;; Returns two _simple_ vectors
      (values (make-array (list (fill-pointer codevec))
                          :element-type 'integer
                          :initial-contents codevec)
              (make-array (list (fill-pointer constvec))
                          :initial-contents constvec)
      ))))

(defun vm-disassemble (codevec constvec)
  (loop for i below (length codevec)
      do (let* ((code (svref codevec i))
                (insn (nth code *vm-insn*))
                (opc  (car insn))
                (type (cadr insn)))
           (labels ((show-imm0 (imm)
                      (case (caddr insn)
                        ((c) (code-char imm))
                        ((v) (svref constvec imm))
                        (t imm))))
             (ecase type
               ((0)
                (format t "~3d  ~10s~%" i opc))
               ((1)
                (format t "~3d  ~10s ~s~%" i opc
                        (show-imm0 (svref codevec (1+ i))))
                (incf i))
               ((2)
                (format t "~3d  ~10s ~s ~s~%" i opc
                        (show-imm0 (svref codevec (1+ i)))
                        (svref codevec (+ 2 i)))
                (incf i 2))
               ((3)
                (format t "~3d  ~10s ~s ~s ~s~%" i opc
                        (show-imm0 (svref codevec (1+ i)))
                        (svref codevec (+ 2 i))
                        (svref codevec (+ 3 i)))
                (incf i 3))
               ((4)
                (format t "~3d  ~10s ~s ~s ~s ~s~%" i opc
                        (show-imm0 (svref codevec (1+ i)))
                        (svref codevec (+ 2 i))
                        (svref codevec (+ 3 i))
                        (svref codevec (+ 4 i)))
                (incf i 4))
               ((5)
                (format t "~3d  ~10s ~s ~s ~s~%" i opc
                        (show-imm0 (svref codevec (1+ i)))
                        (svref codevec (+ 2 i))
                        (svref codevec (+ 3 i))
                        (svref codevec (+ 4 i))
                        (svref codevec (+ 5 i)))
                (incf i 5))
               ))
           )))

;;-----------------------------------------------------------
;; VM closure definitions
;;

(defmacro generate-vm-lambda (&body body)
  `(lambda (xinput xstart xend return-type)
     (declare (optimize (speed 3) (safety 0) (space 0) #-lispworks (compile-speed 0))
              (inline char= char-equal
                      < <= > >= logand ash + - 1+ 1- *
                      schar svref sbit)
              )
     (unless (eq default-return-type :unknown)
       (setf return-type default-return-type))
     (unless (stringp xinput)
       (error "regexp matcher: string required, but got ~a" xinput))
     (with-underlying-simple-vector (xinput input ipos input-len)
       (declare (type simple-string input))
       (let ((start (+ (or xstart 0) ipos))
             (end   (if xend (+ xend ipos) input-len))
             (len   (- input-len ipos)))
         (declare (regexp-dim start end len))
         (when (or (< start 0) (> start len))
           (error "start argument out of bound: ~s" start))
         (when (> end len)
           (error "end argument out of bound: ~s" end))
         (let ((start-max (- end minimum-length))
               stack           ;; stack vector. allocated by iil instruction.
               (ssize   0)     ;; stack size
               (ip      start) ;; input pointer
               (sp      stack-base) ;; stack pointer
               (pc      0)     ;; program counter
               sub-base
               sub-end
               (tail-string-pos -1) ;; tail string position
               tail-string-len)
           #+allegro (declare (type regexp-dim
                          start-max ssize ip sp pc
                          tail-string-pos tail-string-len
                          sub-base sub-end)
                    (type simple-vector stack))
           (and (<= start start-max)
                (progn ,@body)))))))

;; Generates the case expression of VM instruction dispatcher.
;; Deals with variations of failure continuations.
(defmacro vm-case (&rest clauses)
  (labels ((with-operands (insn body)
             (ecase (vm-insn-type insn)
               (0  `(progn ,@body))
               (1  `(let ((imm0 (svref codevec pc)))
                      (declare (type regexp-dim imm0))
                      (incf pc)
                      ,@body))
               (2  `(let ((imm0 (svref codevec pc))
                          (imm1 (svref codevec (1+ pc))))
                      (declare (type regexp-dim imm0 imm1))
                      (incf pc 2)
                      ,@body))
               (3  `(let ((imm0 (svref codevec pc))
                          (imm1 (svref codevec (1+ pc)))
                          (imm2 (svref codevec (+ 2 pc))))
                      (declare (type regexp-dim imm0 imm1 imm2))
                      (incf pc 3)
                      ,@body))
               (4  `(let ((imm0 (svref codevec pc))
                          (imm1 (svref codevec (1+ pc)))
                          (imm2 (svref codevec (+ 2 pc)))
                          (imm3 (svref codevec (+ 3 pc))))
                      (declare (type regexp-dim imm0 imm1 imm2 imm3))
                      (incf pc 4)
                      ,@body))
               (5  `(let ((imm0 (svref codevec pc))
                          (imm1 (svref codevec (1+ pc)))
                          (imm2 (svref codevec (+ 2 pc)))
                          (imm3 (svref codevec (+ 3 pc)))
                          (imm4 (svref codevec (+ 4 pc))))
                      (declare (type regexp-dim imm0 imm1 imm2 imm3 imm4))
                      (incf pc 5)
                      ,@body))
               ))
           (generate-fc-variations (insn body)
             (let* ((insn/t   (symbol-append insn '/t))
                    (insn/nil (symbol-append insn '/nil))
                    (insn/pop (symbol-append insn '/pop))
                    (base-type (vm-insn-type insn)))
               `((,(vm-insn-code insn/t)
                  ,(with-operands insn/t
                     `((unless (progn ,@body) (go fail)))))
                 (,(vm-insn-code insn/nil)
                  ,(with-operands insn/nil
                     `((unless (progn ,@body)
                         (if (>* sp stack-base) (vpop pc) (go fail))))))
                 (,(vm-insn-code insn/pop)
                  ,(with-operands insn/pop
                     `((unless (progn ,@body)
                         (if (>* sp stack-base) (decf sp))
                         (setf pc ,(ecase base-type
                                     ((1) 'imm0)
                                     ((2) 'imm1)
                                     ((3) 'imm2)
                                     ((4) 'imm3)
                                     ))))))
                 (,(vm-insn-code insn)
                  ,(with-operands insn
                     `((unless (progn ,@body)
                         (setf pc ,(ecase base-type
                                     ((1) 'imm0)
                                     ((2) 'imm1)
                                     ((3) 'imm2)
                                     ((4) 'imm3)
                                     ))))))
                 )))
           )
    `(case (prog1 (the regexp-dim (svref codevec pc)) (incf pc))
       ,@(mapcan
          (lambda (clause)
            (destructuring-bind (insn . body) clause
              (cond ((consp insn)
                     (generate-fc-variations (car insn) body))
                    (t
                     ;; normal case
                     `((,(vm-insn-code insn)
                        ,(with-operands insn body)))))))
          clauses)
       (t
        (decf pc)
        (error
         "regexp-vm implementation error: unknown opcode in #x~8,'0x at ~d~%"
         (svref codevec pc) pc))
       )))

;; Entry point of closure creation.  This one just preprocess some data,
;; and calls the real body, make-fast-vm-closure.
(defun make-fast-vm (fe-code num-submatches num-repetitions minimum-length
                     use-stack lookahead-set named-submatches return-type)
  (declare (ignore lookahead-set))
  (declare (type fixnum num-submatches num-repetitions minimum-length))
  (multiple-value-bind (codevec constvec)
      (vm-assemble fe-code num-submatches num-repetitions)
    (when *vm-show-disassemble*
      (vm-disassemble codevec constvec))
    (let* ((stack-base (+ num-repetitions (* (1- num-submatches) 3)))
           )
      (make-fast-vm-closure codevec constvec (1- num-submatches)
                            num-repetitions minimum-length
                            stack-base
                            (or use-stack (> stack-base 0))
                            named-submatches
                            return-type))))

;; Returns the VM closure.
;; Note: at this point num-submatches already excludes (sub 0).
(defun make-fast-vm-closure (codevec constvec num-submatches
                             num-repetitions minimum-length
                             stack-base use-stack named-submatches
                             default-return-type)
  (declare (type simple-vector codevec constvec))
  (declare (type regexp-dim num-submatches num-repetitions
                 stack-base minimum-length))
  (generate-vm-lambda
   (setf sub-base num-repetitions)
   (setf sub-end  (+ num-repetitions (* 3 num-submatches)))
   (macrolet ((=* (a b)
                `(= (the fixnum ,a) (the fixnum ,b)))
              (<* (a b)
                `(< (the fixnum ,a) (the fixnum ,b)))
              (>* (a b)
                `(> (the fixnum ,a) (the fixnum ,b)))
              (<=* (a b)
                `(<= (the fixnum ,a) (the fixnum ,b)))
              (>=* (a b)
                `(>= (the fixnum ,a) (the fixnum ,b)))
              (init-stack ()
                `(when use-stack
                   (setf stack
                     #+allegro (excl::allocate-resource 'backup-vector)
                     #-allegro (make-array 255 :initial-element nil))
                   (setf ssize 255)))
              (fini-stack ()
                `(when (= ssize 255)
                   #+allegro (excl::deallocate-resource 'backup-vector stack)))
              (peekc ()
                `(and (<* ip end) (schar input ip)))
              (vpush (&rest vals)
                (let ((nvals (length vals)))
                  `(progn
                     (when (>=* (+ sp ,nvals) ssize)
                       (let* ((nsize (the regexp-dim (ash ssize 2)))
                              (nvec  (make-array nsize :initial-element nil)))
                         (declare (simple-vector nvec))
                         (loop for i of-type regexp-dim below ssize
                             do (setf (svref nvec i) (svref stack i)))
                         #+allegro (excl::deallocate-resource 'backup-vector stack)
                         (setf ssize nsize)
                         (setf stack nvec)))
                     ,@(loop for i below nvals
                           as v = (pop vals)
                           collect `(setf (svref stack (+ sp ,i))
                                      (the fixnum ,v)))
                     (incf sp ,nvals)
                     )))
              (vpop (&rest locs)
                (let ((nlocs (length locs)))
                  `(progn
                     ,@(loop for i from 1 to nlocs
                           as l = (pop locs)
                           collect `(setf ,l (svref stack (- sp ,i))))
                     (decf sp ,nlocs))))
              ($reg (off)
                `(the regexp-dim (svref stack ,off)))
              ($reg1 (off)
                `(the regexp-dim (svref stack (1+ ,off))))
              ($reg2 (off)
                `(the regexp-dim (svref stack (+ ,off 2))))
              (repeat (step check)
                `(loop for i of-type regexp-dim from ip by ,step
                     while (<* i end)
                     while ,check
                     finally (setf ip i)))
              (repeat-sub (step reg check)
                `(loop for i of-type regexp-dim from ip by ,step
                     while (<* i end)
                     while ,check
                     finally (unless (= i ip)
                               (setf ($reg  ,reg) (- i ,step)) ;; start
                               (setf ($reg1 ,reg) i)           ;; end
                               (setf ip i))))
              (repeat-until (out-check in-check label)
                `(loop for i of-type regexp-dim from ip
                     until (or (>=* i end) (not ,in-check))
                     when ,out-check
                     do (vpush i ,label)
                     finally (setf ip i)))
              (repeat-cs-until (out-check cstype csvec label)
                `(case ,cstype
                   (0 (repeat-until ,out-check
                                    (cs7-check (schar input i) ,csvec)
                                    ,label))
                   (1 (repeat-until ,out-check
                                    (cs7+-check (schar input i) ,csvec)
                                    ,label))
                   (2 (repeat-until ,out-check
                                    (cs8-check (schar input i) ,csvec)
                                    ,label))
                   (3 (repeat-until ,out-check
                                    (cs8+-check (schar input i) ,csvec)
                                    ,label))
                   (4 (repeat-until ,out-check
                                    (cs16-check (schar input i) ,csvec)
                                    ,label))))
              (repeat-any-until (out-check label)
                `(repeat-until ,out-check t ,label))
              (repeat-anl-until (out-check label)
                `(repeat-until ,out-check
                               (not (char= (schar input i) #\newline))
                               ,label))
              (vm-clear-regs ()
                (let ((i (gensym "vm-clear-regs-i")))
                  `(loop for ,i of-type regexp-dim
                       from sub-base
                       below sub-end
                       by 3
                       do (setf (svref stack ,i) -1))))
              (char-set-check ((cmp char limit) imm)
                (let ((cc (gensym "char-set-check-cc"))
                      (bv (gensym "char-set-check-bv")))
                  `(let ((,cc (the regexp-dim (char-code ,char)))
                         (,bv (the bit-vector (svref constvec ,imm))))
                     (,(if (eq cmp '<) 'and 'or)
                         (,cmp ,cc ,limit)
                         (not (= (the fixnum (sbit ,bv ,cc)) 0))))))
              (cs7-check (char imm)
                `(char-set-check (<  ,char 128) ,imm))
              (cs7+-check (char imm)
                `(char-set-check (>= ,char 128) ,imm))
              (cs8-check (char imm)
                `(char-set-check (<  ,char 256) ,imm))
              (cs8+-check (char imm)
                `(char-set-check (>= ,char 256) ,imm))
              (cs16-check (char imm)
                `(char-set-check (<  ,char 65536) ,imm))
              (bol-check (input-pt)
                `(or (=* ,input-pt 0)
                     (char= (schar input (1- ,input-pt)) #\newline)))
              (eol-check (input-pt)
                `(or (=* ,input-pt end)
                     (char= (schar input ,input-pt) #\newline)))
              (bos-check (input-pt)
                `(=* ,input-pt 0))
              (eos-check (input-pt)
                `(=* ,input-pt end))
              (eos-nl-check (input-pt)
                `(or (=* ,input-pt end)
                     (and (=* ,input-pt (- end 1))
                          (char= (schar input ,input-pt) #\newline))))
              ;; NB: we assume *char-set-word* has cs7+-type bitvector.
              (word-char-p (ip)
                (let ((c (gensym "word-char-p-c"))
                      (wbv (char-set-bitvector *char-set-word*)))
                  `(let ((,c (char-code (schar input ,ip))))
                     (or (>=* ,c 128)
                         (not (=* (sbit ,wbv ,c) 0))))))
              (wb-check (input-pt)
                `(cond ((=* ,input-pt 0)
                        (if (=* ,input-pt end) nil (word-char-p ,input-pt)))
                       ((=* ,input-pt end)
                        (word-char-p (1- ,input-pt)))
                       ((word-char-p (1- ,input-pt))
                        (not (word-char-p ,input-pt)))
                       (t
                        (word-char-p ,input-pt))))
              (nwb-check (input-pt)
                `(not (wb-check ,input-pt)))
              ;; advance-start-index
              (advance-start-index (condition)
                `(loop until (and (< ip end) ,condition)
                     do (if (>* (incf start) start-max)
                            (go fail))))
              ;; floating-tail-sting
              (floating-tail-string (ci?)
                (let ((str (gensym "fts-str"))
                      (vec (gensym "fts-vec"))
                      (len (gensym "fts-len"))
                      (prelen (gensym "fts-prelen"))
                      (si  (gensym "fts-si"))
                      (i   (gensym "fts-i")))
                  `(let* ((,str (the simple-string (svref constvec imm0)))
                          (,vec (the simple-vector (svref constvec imm1)))
                          (,len (length ,str))
                          (,prelen (- minimum-length ,len))
                          (,si  (+ start ,prelen)))
                     (declare (type regexp-dim ,len ,prelen ,si))
                     (and
                      (>* ,si tail-string-pos)
                      (let ((,i (vm-fast-search ,str ,len ,vec
                                                input ,si end ,ci?)))
                        (unless ,i (go fail))
                        (setf tail-string-pos ,i)
                        (setf tail-string-len ,len))))))
              ;; inlined substr
              (substr (s e)
                (let ((result (gensym)))
                  `(loop with ,result = (make-string (- ,e ,s))
                       for i of-type regexp-dim from ,s below ,e
                       for j of-type regexp-dim from 0
                       do (setf (schar ,result j) (schar input i))
                       finally (return ,result))))
              (collect-results (collector)
                (let ((i (gensym "collect-results-i"))
                      (s (gensym "collect-results-s"))
                      (e (gensym "collect-results-e")))
                  `(loop for ,i of-type regexp-dim below num-submatches
                       collect (let ((,s (the regexp-dim
                                           (svref stack
                                                  (+ num-repetitions
                                                     (* ,i 3)))))
                                     (,e (the regexp-dim
                                           (svref stack
                                                  (+ num-repetitions
                                                     (* ,i 3) 1)))))
                                 (and (>=* ,s 0)
                                      (>=* ,e 0)
                                      (,collector ,s ,e))))))
              (return-results (flag primary others)
                `(values-list (cons ,flag (cons ,primary ,others))))
              )
                                        ;(vm-clear-regs)
     (loop
       (tagbody
         (vm-case
          ;; Outer loop stuff
          (cil        (when (>* start start-max) (return nil)))
          (ril        (vm-clear-regs)
                      (setf ip start)
                      (setf sp stack-base))
          (iil        (init-stack)
                      (vm-clear-regs)
                      (setf ip start)
                      (setf sp stack-base))
          (cil+iil    (when (>* start start-max) (return nil))
                      (init-stack)
                      (vm-clear-regs)
                      (setf ip start)
                      (setf sp stack-base))
          (isi1       (incf start))
          (isi        (incf start imm0))
          (isi1+cil   (when (>* (incf start) start-max) (return nil)))
          (isi+cil    (when (>* (incf start imm0) start-max) (return nil)))
          (asi-char   (let ((ch (code-char imm0)))
                        (advance-start-index
                         (char= ch (schar input start)))))
          (asi-cs7    (let ((bv (the bit-vector (svref constvec imm0))))
                        (advance-start-index
                         (let ((cc (char-code (schar input start))))
                           (and (< cc 128)
                                (not (= (sbit bv cc) 0)))))))
          (asi-cs7+   (let ((bv (the bit-vector (svref constvec imm0))))
                        (advance-start-index
                         (let ((cc (char-code (schar input start))))
                           (or (>= cc 128)
                               (not (= (sbit bv cc) 0)))))))
          (asi-cs8    (let ((bv (the bit-vector (svref constvec imm0))))
                        (advance-start-index
                         (let ((cc (char-code (schar input start))))
                           (and (< cc 256)
                                (not (= (sbit bv cc) 0)))))))
          (asi-cs8+   (let ((bv (the bit-vector (svref constvec imm0))))
                        (advance-start-index
                         (let ((cc (char-code (schar input start))))
                           (or (>= cc 256)
                               (not (= (sbit bv cc) 0)))))))
          (asi-cs16   (let ((bv (the bit-vector (svref constvec imm0))))
                        (advance-start-index
                         (let ((cc (char-code (schar input start))))
                           (or (< cc 65536)
                               (not (= (sbit bv cc) 0)))))))
          (fts        (floating-tail-string nil))
          (fts-ci     (floating-tail-string t))
          (sfts       (setf start tail-string-pos)
                      (setf ip (+ start imm0)))

          ;; Jumps
          (jump       (setf pc imm0))
          (jump-reg   (setf pc ($reg imm0)))

          ;; Saving/loading
          (save-ip    (setf ($reg imm0) ip))
          (save-sp    (setf ($reg imm0) sp))
          (save-isp   (setf ($reg imm0) ip)
                      (setf ($reg imm1) sp))
          (save-sub   (setf ($reg imm1) ($reg  imm0))  ;; start
                      (setf ($reg imm2) ($reg1 imm0))) ;; end
          (load-ip    (setf ip ($reg imm0)))
          (load-sp    (setf sp ($reg imm0)))
          (load-isp   (setf ip ($reg imm0))
                      (setf sp ($reg imm1)))
          (load-sub   (setf ($reg  imm0) ($reg imm1))  ;; start
                      (setf ($reg1 imm0) ($reg imm2))) ;; end
          (load/set-sub (cond ((<=* ($reg imm1) 0)
                               (setf ($reg  imm0) ($reg imm2))  ;; start
                               (setf ($reg1 imm0) ($reg imm3))) ;; end
                              (t
                               (setf ($reg  imm0) (- ip imm4)) ;; start
                               (setf ($reg1 imm0) ip))))       ;; end
          (sub-ipsave (if (<* (decf ip imm0) start)
                          (go fail)
                        (setf ($reg imm1) ip)))

          ;; Push/pop
          (push-rep   (vpush ($reg imm0)))
          (push-sub   (vpush ($reg  imm0)   ;; start
                             ($reg1 imm0)   ;; end
                             ($reg2 imm0))) ;; mark
          (push-ip    (vpush ip
                             imm0))
          (push-repip (vpush ($reg imm0)
                             ip
                             imm1))
          (push-subip (vpush ($reg  imm0)   ;; start
                             ($reg1 imm0)   ;; end
                             ($reg2 imm0)   ;; mark
                             ip
                             imm1))
          (push-fc    (vpush imm0))
          (pop-rep    (vpop ($reg imm0)))
          (pop-sub    (vpop ($reg2 imm0)    ;; mark
                            ($reg1 imm0)    ;; end
                            ($reg  imm0)))  ;; start
          (pop-ip     (vpop ip))
          (pop-repip  (vpop ip
                            ($reg imm0)))
          (pop-subip  (vpop ip
                            ($reg2 imm0)    ;; mark
                            ($reg1 imm0)    ;; end
                            ($reg  imm0)))  ;; start

          ;; Submatch
          (start-sub  (setf ($reg imm0) ip)) ;; mark
          (end-sub    (setf ($reg  imm0) ($reg2 imm0)) ;; start <- mark
                      (setf ($reg1 imm0) ip)) ;; end
          (cancel-sub (setf ($reg imm0) -1))  ;; start
          (set-sub    (setf ($reg  imm0) (- ip imm1)) ;; start
                      (setf ($reg1 imm0) ip))         ;; end
          (sub-sub    (decf ($reg  imm0) imm1)        ;; start
                      (decf ($reg1 imm0) imm1))       ;; end

          ;; Register operations
          (reset      (setf ($reg imm0) 0))
          (dec        (decf ($reg imm0)))
          (inc        (incf ($reg imm0)))
          (inc-jump   (incf ($reg imm0)) (setf pc imm1))
          (set        (setf ($reg imm0) imm1))

          ;; Conditional branches
          (dec-bgez   (if (>=* (decf ($reg imm0)) 0)
                          (setf pc imm1)))
          (inc-blt    (if (<*  (incf ($reg imm0)) imm1)
                          (setf pc imm2)))
          (biple      (if (<=* ip ($reg imm0))
                          (setf pc imm1)))
          (bv         (if (or (<* ($reg  imm0) 0)  ;; start
                              (<* ($reg1 imm0) 0)) ;; end
                          (setf pc imm1)))

          ;; Match operations
          ((char)     (let ((ch (peekc)))
                        (and ch (=* (char-code ch) imm0) (incf ip))))
          ((char-ci)  (let ((ch (peekc)))
                        (and ch (char-equal ch (code-char imm0)) (incf ip))))
          ((pchar)    (and (<* ip end)
                           (=* (char-code (schar input ip)) imm0)))
          ((pchar-ci) (and (<* ip end)
                           (char-equal (schar input ip)
                                       (code-char imm0))))
          ((cs7)      (let ((ch (peekc)))
                        (and ch (cs7-check  ch imm0) (incf ip))))
          ((cs7+)     (let ((ch (peekc)))
                        (and ch (cs7+-check ch imm0) (incf ip))))
          ((cs8)      (let ((ch (peekc)))
                        (and ch (cs8-check  ch imm0) (incf ip))))
          ((cs8+)     (let ((ch (peekc)))
                        (and ch (cs8+-check ch imm0) (incf ip))))
          ((cs16)     (let ((ch (peekc)))
                        (and ch (cs16-check ch imm0) (incf ip))))
          ((pcs7)     (and (<* ip end)
                           (cs7-check  (schar input ip) imm0)))
          ((pcs7+)    (and (<* ip end)
                           (cs7+-check (schar input ip) imm0)))
          ((pcs8)     (and (<* ip end)
                           (cs8-check  (schar input ip) imm0)))
          ((pcs8+)    (and (<* ip end)
                           (cs8+-check (schar input ip) imm0)))
          ((pcs16)    (and (<* ip end)
                           (cs16-check (schar input ip) imm0)))
          ((str)      (let* ((s (svref constvec imm0))
                             (l (length s)))
                        (declare (type simple-string s)
                                 (type regexp-dim l))
                        (and (<=* l (- end ip))
                             (loop
                                 for i of-type regexp-dim from ip
                                 for j of-type regexp-dim below l
                                 always (char= (schar input i) (schar s j))
                                 finally (setf ip i)))))
          ((str-ci)   (let* ((s (svref constvec imm0))
                             (l (length s)))
                        (declare (type simple-string s)
                                 (type regexp-dim l))
                        (and (<=* l (- end ip))
                             (loop
                                 for i of-type regexp-dim from ip
                                 for j of-type regexp-dim below l
                                 always (char-equal (schar input i)
                                                    (schar s j))
                                 finally (setf ip i)))))
          ((pstr)     (let* ((s (svref constvec imm0))
                             (l (length s)))
                        (declare (type simple-string s)
                                 (type regexp-dim l))
                        (and (<=* l (- end ip))
                             (loop for c across s
                                 for i of-type regexp-dim from ip
                                 always (char= c (schar input i))))))
          ((pstr-ci)  (let* ((s (svref constvec imm0))
                             (l (length s)))
                        (declare (type simple-string s)
                                 (type regexp-dim l))
                        (and (<=* l (- end ip))
                             (loop for c across s
                                 for i of-type regexp-dim from ip
                                 always (char-equal c (schar input i))))))
          ((tstr)     (cond
                       ((<* ip tail-string-pos) nil)
                       ((=* ip tail-string-pos)
                        (incf ip tail-string-len)
                        (go success))
                       (t
                        (let* ((s (svref constvec imm0))
                               (l (length s)))
                          (declare (type simple-string s)
                                   (type regexp-dim l))
                          (and (<=* l (- end ip))
                               (loop
                                   for i of-type regexp-dim from ip
                                   for j of-type regexp-dim below l
                                   always (char= (schar input i) (schar s j))
                                   finally (setf ip i)))))))
          ((tstr-ci)  (cond
                       ((<* ip tail-string-pos) nil)
                       ((=* ip tail-string-pos)
                        (incf ip tail-string-len)
                        (go success))
                       (t
                        (let* ((s (svref constvec imm0))
                               (l (length s)))
                          (declare (type simple-string s)
                                   (type regexp-dim l))
                          (and (<=* l (- end ip))
                               (loop
                                   for i of-type regexp-dim from ip
                                   for j of-type regexp-dim below l
                                   always (char-equal (schar input i)
                                                      (schar s j))
                                   finally (setf ip i)))))))
          ((ref)      (let* ((s ($reg  imm0))
                             (e ($reg1 imm0)))
                        (declare (type regexp-dim s e))
                        (and (>=* s 0) (>=* e 0)
                             (<=* (+ ip (- e s)) end)
                             (loop
                                 for i of-type regexp-dim from ip
                                 for j of-type regexp-dim from s below e
                                 always (char= (schar input i)
                                               (schar input j))
                                 finally (setf ip i)))))
          ((pref)     (let* ((s ($reg  imm0))
                             (e ($reg1 imm0)))
                        (declare (type regexp-dim s e))
                        (and (>=* s 0) (>=* e 0)
                             (<=* (+ ip (- e s)) end)
                             (loop
                                 for i of-type regexp-dim from ip
                                 for j of-type regexp-dim from s below e
                                 always (char= (schar input i)
                                               (schar input j))))))
          ((ref-ci)   (let* ((s ($reg  imm0))
                             (e ($reg1 imm0)))
                        (declare (type regexp-dim s e))
                        (and (>=* s 0) (>=* e 0)
                             (<=* (+ ip (- e s)) end)
                             (loop
                                 for i of-type regexp-dim from ip
                                 for j of-type regexp-dim from s below e
                                 always (char-equal (schar input i)
                                                    (schar input j))
                                 finally (setf ip i)))))
          ((pref-ci)  (let* ((s ($reg  imm0))
                             (e ($reg1 imm0)))
                        (declare (type regexp-dim s e))
                        (and (>=* s 0) (>=* e 0)
                             (<=* (+ ip (- e s)) end)
                             (loop
                                 for i of-type regexp-dim from ip
                                 for j of-type regexp-dim from s below e
                                 always (char-equal (schar input i)
                                                    (schar input j))))))
          ((any)      (and (<* ip end) (incf ip)))
          ((any-nl)   (let ((ch (peekc)))
                        (and ch (not (char= ch #\newline)) (incf ip))))
          ((bol)      (bol-check ip))
          ((eol)      (eol-check ip))
          ((bos)      (bos-check ip))
          ((eos)      (eos-check ip))
          ((eos-nl)   (eos-nl-check ip))
          ((wb)       (wb-check ip))
          ((nwb)      (nwb-check ip))
          ((fail)     nil)
          ((sub-ip)   (and (>=* ip imm0) (decf ip imm0)))

          (char*      (let ((ch (code-char imm0)))
                        (repeat 1 (char= ch (schar input i)))))
          (char-ci*   (let ((ch (code-char imm0)))
                        (repeat 1 (char-equal ch (schar input i)))))
          (char*-sub  (let ((ch (code-char imm0)))
                        (repeat-sub 1 imm1 (char= ch (schar input i)))))
          (char-ci*-sub (let ((ch (code-char imm0)))
                          (repeat-sub 1 imm1 (char-equal ch (schar input i)))))
          (cs7*       (repeat 1 (cs7-check  (schar input i) imm0)))
          (cs7+*      (repeat 1 (cs7+-check (schar input i) imm0)))
          (cs8*       (repeat 1 (cs8-check  (schar input i) imm0)))
          (cs8+*      (repeat 1 (cs8+-check (schar input i) imm0)))
          (cs16*      (repeat 1 (cs16-check (schar input i) imm0)))
          (cs7*-sub   (repeat-sub 1 imm1 (cs7-check  (schar input i) imm0)))
          (cs7+*-sub  (repeat-sub 1 imm1 (cs7+-check (schar input i) imm0)))
          (cs8*-sub   (repeat-sub 1 imm1 (cs8-check  (schar input i) imm0)))
          (cs8+*-sub  (repeat-sub 1 imm1 (cs8+-check (schar input i) imm0)))
          (cs16*-sub  (repeat-sub 1 imm1 (cs16-check (schar input i) imm0)))
          (str*       (let* ((s (svref constvec imm0))
                             (l (length s)))
                        (repeat l
                                (loop for k of-type regexp-dim below l
                                    for j of-type regexp-dim from i
                                    always (and (<* j end)
                                                (char= (schar s k)
                                                       (schar input j)))))))
          (str-ci*    (let* ((s (svref constvec imm0))
                             (l (length s)))
                        (repeat l
                                (loop for k of-type regexp-dim below l
                                    for j of-type regexp-dim from i
                                    always (and (<* j end)
                                                (char-equal
                                                 (schar s k)
                                                 (schar input j)))))))
          (str*-sub   (let* ((s (svref constvec imm0))
                             (l (length s)))
                        (repeat-sub
                         l imm1
                         (loop for k of-type regexp-dim below l
                             for j of-type regexp-dim from i
                             always (and (<* j end)
                                         (char= (schar s k)
                                                (schar input j)))))))
          (str-ci*-sub (let* ((s (svref constvec imm0))
                              (l (length s)))
                         (repeat-sub
                          l imm1
                          (loop for k of-type regexp-dim below l
                              for j of-type regexp-dim from i
                              always (and (<* j end)
                                          (char-equal
                                           (schar s k)
                                           (schar input j)))))))
          (any*        (setf ip end))  ;; very special case!
          (any-nl*     (repeat 1 (not (char= #\newline (schar input i)))))
          (any*-sub    (unless (= ip end)
                         (setf ip end)
                         (setf ($reg  imm0) (1- ip))
                         (setf ($reg1 imm0) ip)))
          (any-nl*-sub (repeat-sub 1 imm0
                                   (not (char= #\newline (schar input i)))))

          (ruchar      (repeat-cs-until (=* (char-code (schar input i)) imm2)
                                        imm0 imm1 imm3))
          (rucs7       (repeat-cs-until (cs7-check (schar input i) imm2)
                                        imm0 imm1 imm3))
          (rucs7+      (repeat-cs-until (cs7+-check (schar input i) imm2)
                                        imm0 imm1 imm3))
          (rucs8       (repeat-cs-until (cs8-check (schar input i) imm2)
                                        imm0 imm1 imm3))
          (rucs8+      (repeat-cs-until (cs8+-check (schar input i) imm2)
                                        imm0 imm1 imm3))
          (rucs16      (repeat-cs-until (cs16-check (schar input i) imm2)
                                        imm0 imm1 imm3))
          (ruanchor    (case imm2
                         (0 (repeat-cs-until (bol-check i) imm0 imm1 imm3))
                         (1 (repeat-cs-until (eol-check i) imm0 imm1 imm3))
                         (2 (repeat-cs-until (bos-check i) imm0 imm1 imm3))
                         (3 (repeat-cs-until (eos-check i) imm0 imm1 imm3))
                         (4 (repeat-cs-until (eos-nl-check i) imm0 imm1 imm3))
                         (5 (repeat-cs-until (wb-check  i) imm0 imm1 imm3))
                         (6 (repeat-cs-until (nwb-check i) imm0 imm1 imm3))))

          (rauchar     (repeat-any-until (=* (char-code (schar input i)) imm0)
                                         imm1))
          (raucs7      (repeat-any-until (cs7-check (schar input i) imm0)
                                         imm1))
          (raucs7+     (repeat-any-until (cs7+-check (schar input i) imm0)
                                         imm1))
          (raucs8      (repeat-any-until (cs8-check (schar input i) imm0)
                                         imm1))
          (raucs8+     (repeat-any-until (cs8+-check (schar input i) imm0)
                                         imm1))
          (raucs16     (repeat-any-until (cs16-check (schar input i) imm0)
                                         imm1))
          (rauanchor   (case imm0
                         (0 (repeat-any-until (bol-check i) imm1))
                         (1 (repeat-any-until (eol-check i) imm1))
                         (2 (repeat-any-until (bos-check i) imm1))
                         (3 (repeat-any-until (eos-check i) imm1))
                         (4 (repeat-any-until (eos-nl-check i) imm1))
                         (5 (repeat-any-until (wb-check i) imm1))
                         (6 (repeat-any-until (nwb-check i) imm1))))

          (rnuchar     (repeat-anl-until (=* (char-code (schar input i)) imm0)
                                         imm1))
          (rnucs7      (repeat-anl-until (cs7-check (schar input i) imm0)
                                         imm1))
          (rnucs7+     (repeat-anl-until (cs7+-check (schar input i) imm0)
                                         imm1))
          (rnucs8      (repeat-anl-until (cs8-check (schar input i) imm0)
                                         imm1))
          (rnucs8+     (repeat-anl-until (cs8+-check (schar input i) imm0)
                                         imm1))
          (rnucs16     (repeat-anl-until (cs16-check (schar input i) imm0)
                                         imm1))
          (rnuanchor   (case imm0
                         (0 (repeat-anl-until (bol-check i) imm1))
                         (1 (repeat-anl-until (eol-check i) imm1))
                         (2 (repeat-anl-until (bos-check i) imm1))
                         (3 (repeat-anl-until (eos-check i) imm1))
                         (4 (repeat-anl-until (eos-nl-check i) imm1))
                         (5 (repeat-anl-until (wb-check i) imm1))
                         (6 (repeat-anl-until (nwb-check i) imm1))))

          (success     (go success))
          )
         (go next)
        fail
         (fini-stack)
         (return nil)
        success
         (return
           (case return-type
             ((:string)
              (let ((submatches (collect-results substr)))
                (fini-stack)
                (return-results t (substr start ip) submatches)))
             ((:index)
              (let ((submatches (collect-results cons)))
                (fini-stack)
                (return-results t (cons start ip) submatches)))
             ((:match)
              (let ((submatches (collect-results cons)))
                (fini-stack)
                (return (make-regular-expression-match
                         (cons (cons start ip) submatches)
                         input
                         num-submatches
                         named-submatches))))
             (t (fini-stack) t)))
        next
         ))
     )))

;;;
;;; For development
;;;

(defun hack-vm (string &key ignore-whitespace case-fold single-line multiple-lines)
  (let ((.ignore-case. case-fold)
        (.single-line. single-line)
        (.multiple-lines. multiple-lines)
        (.ignore-whitespace. ignore-whitespace))
    (multiple-value-bind (code nsubs nreps use-stack minlen fixed laset)
        (fe-compile-regexp (parse-re string :extended-mode ignore-whitespace)
                           nil)
      (declare (ignore use-stack minlen fixed laset))
      (multiple-value-bind (codevec constvec)
          (vm-assemble code nsubs nreps)
        (vm-disassemble codevec constvec)))))

;;;;==============================================================
;;;;  A reference VM implementation (ref-vm)
;;;;

;;; This back-end is to check correctness of front-end compiler.
;;; Consideration for the speed is minimal.

;;; OBSOLETED.

;(defvar *regexp-vm-trace* nil)

;(defun make-ref-vm (fe-code num-submatches num-repetitions minimum-length
;                    use-stack lookahead-set)
;  (declare (optimize (space 3)))
;  (declare (ignore use-stack lookahead-set))
;  (let ((labeltab (sort (coerce
;                         (mapcon #'(lambda (insns)
;                                     (when (and (consp (car insns))
;                                                (eq (caar insns) 'label))
;                                       (list insns)))
;                                 fe-code)
;                         'vector)
;                        #'< :key #'cadar))
;        )
;    (lambda (input start end return-type)
;      (declare (optimize (space 3)))
;      (and
;       (<= minimum-length (- end start))
;       (let ((ip   start) ;; input pointer
;             (code fe-code)
;             (subs (make-array (list (* num-submatches 3))
;                               :element-type 'integer
;                               :initial-element -1)) ;; submatch registers
;             (reps (make-array (list num-repetitions)
;                               :element-type 'integer
;                               :initial-element 0)) ;; repetition registers
;             (stack (make-array (list 65536)  ;; for now, just a fixed size.
;                                :element-type 'integer))
;             (sp    0) ;; stack pointer
;             (steps 0) ;; for benchmark
;             )
;         (macrolet ((next (insn)
;                      `(progn (setf code ,insn) (go next)))
;                    (goto-label (label)
;                      `(next (svref labeltab ,label)))
;                    (fail (fcont)
;                      `(cond ((eq ,fcont t) (go advance-input))
;                             ((not ,fcont) (go dynamic-fail))
;                             ((integerp ,fcont) (decf sp) (goto-label ,fcont))
;                             (t (goto-label (car ,fcont)))))
;                    (getc  ()
;                      `(and (< ip end)
;                            (prog1 (schar input ip) (incf ip))))
;                    (vpush (val)
;                      `(progn (setf (svref stack sp) ,val)
;                              (incf sp)))
;                    (vpop ()
;                      `(progn (decf sp)
;                              (svref stack sp)))
;                    (sub-mark (i)
;                      `(svref subs (* ,i 3)))
;                    (sub-start (i)
;                      `(svref subs (+ (* ,i 3) 1)))
;                    (sub-end (i)
;                      `(svref subs (+ (* ,i 3) 2)))
;                    )
;           (loop
;             (when *regexp-vm-trace*
;               (format t "~25s ~2d ~a |~{~2d ~}~%"
;                       (car code) ip
;                       (if (<= start ip (1- end)) (schar input ip) " ")
;                       (loop for i from 0 to (1- sp)
;                           collect (svref stack i))))
;             (tagbody
;               (when (null code)
;                 ;; success
;                 (when *regexp-vm-trace*
;                   (format t "steps: ~3d~%" steps))
;                 (return
;                   (values-list
;                    (list* t
;                           (loop for i from 0 to (1- num-submatches)
;                               collect (let ((s (sub-start i))
;                                             (e (sub-end i)))
;                                         (and (>= s 0)
;                                              (>= e 0)
;                                              (case return-type
;                                                ((:string)
;                                                 (subseq input s e))
;                                                ((:index)
;                                                 (cons s e))))))))))
;               (incf steps)
;               (destructuring-bind (op &rest args) (car code)
;                 (case op
;                   ((label) (next (cdr code)))
;                   ((jump)  (goto-label (car args)))
;                   ((try)
;                    (destructuring-bind (fcont &rest regs) args
;                      (loop for (type num) in regs
;                          do (case type
;                               (sub (vpush (sub-mark num))
;                                    (vpush (sub-start num))
;                                    (vpush (sub-end num)))
;                               (rep (vpush (svref reps num)))))
;                      (vpush ip)
;                      (vpush fcont)
;                      (next (cdr code))))
;                   ((push-fc)
;                    (vpush (car args))
;                    (next (cdr code)))
;                   ((pop)
;                    (setf ip (vpop))
;                    (loop for (type num) in args
;                        do (case type
;                             (sub (setf (sub-end num) (vpop))
;                                  (setf (sub-start num) (vpop))
;                                  (setf (sub-mark num) (vpop)))
;                             (rep (setf (svref reps num) (vpop)))))
;                    (next (cdr code)))
;                   ((cut)
;                    (setf sp 0)
;                    (next (cdr code)))
;                   ((save-ip)
;                    (destructuring-bind (reg) args
;                      (setf (svref reps (cadr reg)) ip))
;                    (next (cdr code)))
;                   ((save-sp)
;                    (destructuring-bind (reg) args
;                      (setf (svref reps (cadr reg)) sp))
;                    (next (cdr code)))
;                   ((load-ip)
;                    (destructuring-bind (reg) args
;                      (setf ip (svref reps (cadr reg))))
;                    (next (cdr code)))
;                   ((load-sp)
;                    (destructuring-bind (reg) args
;                      (setf sp (svref reps (cadr reg))))
;                    (next (cdr code)))
;                   ((sub-ip)
;                    (destructuring-bind (num fcont) args
;                      (decf ip num)
;                      (if (< ip 0)
;                          (fail fcont)
;                        (next (cdr code)))))
;                   ((inc)
;                    (incf (svref reps (cadar args)))
;                    (next (cdr code)))
;                   ((dec)
;                    (decf (svref reps (cadar args)))
;                    (next (cdr code)))
;                   ((fail)
;                    (fail (car args)))
;                   ((char)
;                    (destructuring-bind (char fcont) args
;                      (let ((ch (getc)))
;                        (if (and ch (char= char ch))
;                            (next (cdr code))
;                          (fail fcont)))))
;                   ((char-ci)
;                    (destructuring-bind (char fcont) args
;                      (let ((ch (getc)))
;                        (if (and ch (char-equal char ch))
;                            (next (cdr code))
;                          (fail fcont)))))
;                   ((string string-ci)
;                    (destructuring-bind (str fcont) args
;                      (let ((l (length str)))
;                        (if (or (> l (- end ip))
;                                (mismatch input str
;                                          :start1 ip :end1 (+ ip l)
;                                          :test (case op
;                                                  (string #'char=)
;                                                  (string-ci #'char-equal))))
;                            (fail fcont)
;                          (progn
;                            (incf ip l)
;                            (next (cdr code)))))))
;                   ((any)
;                    (let ((ch (getc)))
;                      (if ch (next (cdr code))
;                        (fail (car args)))))
;                   ((any-except-newline)
;                    (let ((ch (getc)))
;                      (if (and ch (not (char= ch #\newline)))
;                          (next (cdr code))
;                        (fail (car args)))))
;                   ((bol)
;                    (if (or (= ip 0)
;                            (char= (schar input (1- ip)) #\newline))
;                        (next (cdr code))
;                      (fail (car args))))
;                   ((eol)
;                    (if (or (= ip end)
;                            (char= (schar input ip) #\newline))
;                        (next (cdr code))
;                      (fail (car args))))
;                   ((bos)
;                    (if (= ip 0)
;                        (next (cdr code))
;                      (fail (car args))))
;                   ((eos)
;                    (if (= ip end)
;                        (next (cdr code))
;                      (fail (car args))))
;                   ((eos-newline)
;                    (if (or (= ip end)
;                            (and (= ip (- end 1))
;                                 (char= (schar input ip) #\newline)))
;                        (next (cdr code))
;                      (fail (car args))))
;                   ((word-boundary)
;                    (if (word-boundary-p ip input end)
;                        (next (cdr code))
;                      (fail (car args))))
;                   ((not-word-boundary)
;                    (if (word-boundary-p ip input end)
;                        (fail (car args))
;                      (next (cdr code))))
;                   ((char-set)
;                    (destructuring-bind (cset fcont) args
;                      (let ((ch (getc)))
;                        (if (and ch (match-char-set nil ch cset))
;                            (next (cdr code))
;                          (fail fcont)))))
;                   ((char-set-ci)
;                    (destructuring-bind (cset fcont) args
;                      (let ((ch (getc)))
;                        (if (and ch (match-char-set t ch cset))
;                            (next (cdr code))
;                          (fail fcont)))))
;                   ((submatch-start)
;                    (let ((regnum (cadar args)))
;                      (setf (sub-mark regnum) ip))
;                    (next (cdr code)))
;                   ((submatch-end)
;                    (let ((regnum (cadar args)))
;                      (setf (sub-start regnum) (sub-mark regnum))
;                      (setf (sub-end regnum) ip))
;                    (next (cdr code)))
;                   ((reference reference-ci)
;                    (destructuring-bind (regnum fcont) args
;                      (let ((s (sub-start regnum))
;                            (e (sub-end regnum)))
;                        (if (or (< s 0) (< e 0)
;                                (> (+ ip (- e s)) end)
;                                (mismatch input input
;                                          :test (if (eq op 'reference)
;                                                    #'char=
;                                                  #'char-equal)
;                                          :start1 ip
;                                          :end1 (+ ip (- e s))
;                                          :start2 s
;                                          :end2 e))
;                            (fail fcont)
;                          (progn
;                            (incf ip (- e s))
;                            (next (cdr code)))))))
;                   ((reset)
;                    (let ((regnum (cadar args)))
;                      (setf (svref reps regnum) 0)
;                      (next (cdr code))))
;                   ((increment-branch<)
;                    (destructuring-bind (reg max label) args
;                      (if (< (incf (svref reps (cadr reg))) max)
;                          (goto-label label)
;                        (next (cdr code)))))
;                   ((decrement-branch>0)
;                    (destructuring-bind (reg label) args
;                      (if (> (decf (svref reps (cadr reg))) 0)
;                          (goto-label label)
;                        (next (cdr code)))))
;                   ((branch-if-ip<=)
;                    (destructuring-bind (reg label) args
;                      (if (<= ip (svref reps (cadr reg)))
;                          (goto-label label)
;                        (next (cdr code)))))
;                   ((branch-if-void)
;                    (destructuring-bind (sub label) args
;                      (if (or (< (sub-start sub) 0)
;                              (< (sub-end sub) 0))
;                          (goto-label label)
;                        (next (cdr code)))))
;                   ((set set-label)
;                    (destructuring-bind (reg label) args
;                      (setf (svref reps (cadr reg)) label)
;                      (next (cdr code))))
;                   ((invalidate)
;                    (loop for reg in args
;                        when (eq (car reg) 'sub)
;                        do (setf (sub-start (cadr reg)) -1))
;                    (next (cdr code)))
;                   ((jump-reg)
;                    (destructuring-bind (reg) args
;                      (goto-label (svref reps (cadr reg)))))
;                   (otherwise
;                    (format t "unsupported insn: ~s~%" op)
;                    (next (cdr code)))
;                   ))
;              dynamic-fail
;               (unless (<= sp 0)
;                 (let ((fcont (vpop)))
;                   (goto-label fcont)))
;               ;; fallthrough
;              advance-input
;               (incf start)
;               (when (> minimum-length (- end start)) (return nil))
;               (setf code fe-code)
;               (loop for i from 0 to (1- (* num-submatches 3))
;                   do (setf (svref subs i) -1))
;               (setf ip start)
;               (setf sp 0)
;               ;; fallthrough
;              next
;               )))))
;      )))

;(defun word-boundary-p (ip input end)
;  (labels ((word-char-p (char)
;             (match-char-set nil char *char-set-word*)))
;    (cond ((= ip 0)
;           (if (= ip end)
;               nil
;             (word-char-p (schar input ip))))
;          ((= ip end)
;           (word-char-p (schar input (1- ip))))
;          ((word-char-p (schar input (1- ip)))
;           (not (word-char-p (schar input ip))))
;          (t
;           (word-char-p (schar input ip))))))

;(defun match-char-set (ci char cset)
;  (declare (ignore ci))
;  (labels ((char-in-range? (code ranges)
;             (if (null ranges)
;                 nil
;               (or (<= (caar ranges) code (cdar ranges))
;                   (char-in-range? code (cdr ranges))))))
;    (char-in-range? (char-code char) (char-set-ranges cset))))


