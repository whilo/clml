;; -*- mode: common-lisp; package: excl -*-
;;
;; copyright (c) 1997-2005 Franz Inc, Berkeley, CA  - All rights reserved.
;; copyright (c) 2002-2007 Franz Inc, Oakland, CA - All rights reserved.
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
;; $Id: excl.cl,v 2.29.2.1 2007/06/20 21:56:27 layer Exp $

(defpackage "EXCL"
  (:use "COMMON-LISP")
  #+sbcl (:import-from "ASDF" "RUN-SHELL-COMMAND")
  #+lispworks (:import-from "SYSTEM" "RUN-SHELL-COMMAND")
  (:export "WITH-UNDERLYING-SIMPLE-VECTOR"
           "DELIMITED-STRING-TO-LIST"
           "DELIMITED-STRING-TO-LIST-STRING"
           "DELIMITED-STRING-TO-LIST-CHAR"
           "POSITION-CHAR"
           "LIST-TO-DELIMITED-STRING"
           "XOR"
           #-allegro "RUN-SHELL-COMMAND"))

(in-package :excl)

(eval-when (:compile-toplevel :load-toplevel :execute)
(defun parse-macro-body (body env)
  ;; parse the body of a macro looking for and returning two values:
  ;;   a list of all declarations
  ;;   the body without the declarations
  ;; env is the macro environment
  (do ((bb body (cdr bb))
       (declares))
      ((null bb)
       (values (nreverse declares) nil))
    (let ((first (macroexpand (car bb) env #+allegro t)))
      (if (and (consp first) (eq 'declare (car first)))
	  (push first declares)
        (return (values (nreverse declares) bb))))))
)

(defmacro with-underlying-simple-vector ((array simple-vector-var
					  &optional displacement-var
						    length-var
						    explicit-end
						    allow-nil)
					 &body body &environment env)
  (multiple-value-bind (decls body-forms) (parse-macro-body body env)
    (let ((sv-1 (gensym))
	  (dv-1 (gensym))
	  (lv-1 (gensym)))
      `(let ((,sv-1 ,array)
	     ,@(and displacement-var `((,dv-1 0)))
	     ,@(and length-var `(,lv-1)))
	 ,@(when displacement-var
	     `((declare (type adim ,dv-1))))
	 ,@(when length-var
	     `((declare (type adim ,lv-1))))
	 ,(let ((body `(if (typep ,sv-1 'simple-array)
                           ,(when length-var
				  `(setq ,lv-1 (or ,explicit-end (length ,sv-1))))
                         ;; otherwise should be error at the moment
                         (error "with-underlying-simple-vector not yet supported for ~A." ,sv-1)
                         #+ignore
                         (if* (lvectorp ,sv-1)
                            then ,(when length-var
                                    `(setq ,lv-1 (or ,explicit-end (lv_size ,sv-1))))
                          elseif (svectorp ,sv-1)
                            then ,(when length-var
                                    `(setq ,lv-1 (or ,explicit-end (sv_size ,sv-1))))
                            else ,@(when length-var
                                     `((setq ,lv-1
                                         (or ,explicit-end
                                             (ah-fill-pointer ,sv-1)
                                             (car (ah-dims ,sv-1))))))
                                 (loop
                                   ,@(when displacement-var
                                       `((incf ,dv-1
                                               (the adim (ah-displacement ,sv-1)))))
                                   (setq ,sv-1 (ah-data ,sv-1))
                                   (when (consp ,sv-1)
                                     (setq ,sv-1 (cdr ,sv-1))
                                     (return)))
                                 ,@(when length-var
                                     `((setq ,lv-1 (+ ,dv-1 ,lv-1))))))))
	    (if allow-nil
		`(if ,sv-1
		     ,body
                   ,(when length-var
                      `(setq ,lv-1 most-positive-fixnum)))
	      body))
	 (let ((,simple-vector-var ,sv-1)
	       ,@(and displacement-var `((,displacement-var ,dv-1)))
	       ,@(and length-var `((,length-var ,lv-1))))
	   ,@decls
	   ,@body-forms)))))

(defun delimited-string-to-list (string delimiter-string-or-char)
  ;; Returns a list of substrings of string, separating the original string
  ;; wherever delimiter-string-or-char appears (the delimiter characters do
  ;; not appear in any of the substrings).  For example,
  ;;   (delimited-string-to-list "one two three" #\space)
  ;; returns ("one" "two" "three"), and
  ;;   (delimited-string-to-list "one, two, three" ", ")
  ;; returns ("one" "two" "three").
  (declare (optimize (speed 3)))
  (when (not (stringp string))
    (error "Expected first argument to be a string, but got `~s'." string))
  (let ((string (if (simple-string-p string)
                    string
                  (with-underlying-simple-vector (string ss)
                    ss))))
    (when (eql 0 (length string)) (return-from delimited-string-to-list nil))
    (let ((s (if (simple-string-p delimiter-string-or-char)
                 (if (= 1 (length delimiter-string-or-char))
                     (schar delimiter-string-or-char 0)
                   delimiter-string-or-char)
               (if (characterp delimiter-string-or-char)
                   delimiter-string-or-char
                 (error "Not a simple-string or character: ~s"
                        delimiter-string-or-char)))))
      (if (stringp s)
          (delimited-string-to-list-string string s)
        (delimited-string-to-list-char string s)))))

(defun delimited-string-to-list-string (string ss)
  (declare (optimize (speed 3)))
  (do* ((len-ss (length ss))
        (len-string (length string))
        (res '())
        (start 0)
        last-end
        end)
      ((null (setq end (search ss string :start2 start)))
       (if last-end
           (progn
             (incf last-end len-ss)
             (if (< last-end len-string)
                 (push (subseq string last-end) res)
               (push "" res))
             (nreverse res))
         (list string)))
    (push (subseq string start end) res)
    (setq start (+ end len-ss))
    (setq last-end end)))

(defun delimited-string-to-list-char (string char)
  (declare (optimize (speed 3)))
  (do* ((len-string (length string))
        (res '())
        (start 0)
        last-end
        end)
      ((null (setq end (position-char char string start len-string)))
       (if last-end
           (progn
             (incf last-end)
             (if (< last-end len-string)
                 (push (subseq string last-end) res)
               (push "" res))
             (nreverse res))
         (list string)))
    (push (subseq string start end) res)
    (setq start (+ end 1))
    (setq last-end end)))

(defun position-char (char string start max)
  (declare (optimize (speed 3)))
  (do* ((i start (1+ i)))
      ((= i max) nil)
    (when (char= char (schar string i)) (return i))))

(defun list-to-delimited-string (list delimiter-string-or-char)
  ;; Formats a list of objects into a single string, with
  ;; delimiter-char-or-string inserted between the objects. The print
  ;; representation of the objects is used in the resulting string.
  ;; For example,
  ;;   (list-to-delimited-string '("one" "two" "three") #\space)
  ;; returns "one two three", and
  ;;   (list-to-delimited-string '(:foo :bar) ", ")
  ;; returns "foo, bar".
  (when (null list) (return-from list-to-delimited-string ""))
  (flet ((stringify (x)
           (if (numberp x)
               (princ-to-string x)
               (string x))))
    (do* ((ss (if (simple-string-p delimiter-string-or-char)
                  delimiter-string-or-char
                (if (characterp delimiter-string-or-char)
                    (make-string 1 :initial-element delimiter-string-or-char)
                  (error "Not a simple-string or character: ~s"
                         delimiter-string-or-char))))
          (res (stringify (car list)))
          (ll (cdr list) (cdr ll)))
        ((null ll) res)
      (setq res (concatenate 'simple-string res ss (stringify (car ll)))))))

(defun xor (&rest x)
  (cond
   ((atom x) nil)
   ((atom (cdr x)) (car x))
   ((car x) (not (apply #'xor (cdr x))))
   (t (apply #'xor (cdr x)))))

#||

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MD5 in lisp

(eval-when (compile)
  (ff:def-foreign-type md5-ctx
      (:struct
       (buf (:array :int 4))            ; scratch buffer
       (i (:array :int 4))              ; number of _bits_ handled mod 2^64
       (in (:array :unsigned-char 64))  ; input buffer
       ))
  )

(eval-when (compile eval)
  (defconstant .md5-ctx-size. (ff:sizeof-fobject 'md5-ctx)))

;;;(ff:def-foreign-call (.md5-string "MD5String")
;;;    ((inbuf (* :char)) (inlen :int) (outbuf (* :char)))
;;;  :strings-convert nil)
;;;
;;;(ff:def-foreign-call (.md5-init "MD5Init")
;;;    ((md5-context (* md5-ctx))))
;;;
;;;(ff:def-foreign-call (.md5-update "MD5Update")
;;;    ((md5-context (* md5-ctx))
;;;     (inbuf (* :char))
;;;     (inlen :int))
;;;  :strings-convert nil)
;;;
;;;(ff:def-foreign-call (.md5-final "MD5Final")
;;;    ((outbuf (* :char))
;;;     (md5-context (* md5-ctx)))
;;;  :strings-convert nil)

;; The runtime startup code uses md5, and the ffi isn't initialized yet, so
;; do syscalls instead:

(eval-when (compile eval) (load "code/sysdefs.cl"))

(defun .md5-string (inbuf inlen outbuf)
  (.primcall 'sys::lisp-syscall #.sc-md5-string inbuf inlen outbuf))

(defun .md5-init (context)
  (.primcall 'sys::lisp-syscall #.sc-md5-init context))

(defun .md5-update (context inbuf inlen)
  (.primcall 'sys::lisp-syscall #.sc-md5-update context inbuf inlen))

(defun .md5-final (outbuf context)
  (.primcall 'sys::lisp-syscall #.sc-md5-final outbuf context))


(defun md5-init ()
  (let ((context (ff::allocate-fobject 'md5-ctx :lisp)))
    (.md5-init context)
    context))

(defun md5-context-p (thing)
  (typecase thing
    ((simple-array (unsigned-byte 8) (*))
     (= (length thing) .md5-ctx-size.))))

;; desired effect:
;; (defun md5-update (context data &key (start 0) (end (length data))
;;                                       (external-format :default))

(defun md5-update (context data &rest args)
  (if (= (length args) 1) 
      ;; old style
      (md5-update-internal context data :end (first args))
    ;; new style
    (apply 'md5-update-internal context data args)))

(define-compiler-macro md5-update (context data &rest args)
  (if (= (length args) 1) 
      (progn
        ;; old style
        (warn "3-argument style of md5-update is deprecated.  Please use (md5-update context data &key start end external-format) style")
        `(md5-update-internal ,context ,data :end ,(first args)))
    ;; new style
    `(md5-update-internal ,context ,data ,@args)))

(defun md5-update-internal (context data &key (start 0) 
                                                (end (length data))
                                                (external-format :default))
  (if (not (md5-context-p context))
      (error "md5-update: 'context' must be an md5 context returned from md5-init"))
  (with-native-string (data data :start start :end end
                              :native-length-var xlen
                              :external-format external-format)
    (.md5-update context data xlen))
  (values))


(defun md5-final (context &key (return :integer))
  (if (not (md5-context-p context))
      (error "md5-update: 'context' must be an md5 context returned from md5-init"))
  (let ((outbuf (make-array 16 :element-type '(unsigned-byte 8))))
    (.md5-final outbuf context)
    (md5-result outbuf return)))

(defun md5-result (outbuf return)
  (ecase return
    (:usb8
     outbuf)
    (:integer
     (md5-result-to-integer outbuf))
    (:hex
     (with-output-to-string (s)
       (dotimes (n 16)
         (format s "~2,'0x" (aref outbuf n)))))))
         
(defun md5-string (string &key (start 0) (end (length string))
                               (external-format :default)
                               (return :integer))
  (let ((outbuf (make-array 16 :element-type '(unsigned-byte 8))))
    (with-native-string (string string :native-length-var len
                                :start start :end end
                                :external-format external-format)
      (.md5-string string len outbuf))
    (md5-result outbuf return)))
    

(defun md5-file (filespec &key (return :integer))
  (with-open-file (stream filespec :direction :input
                   ;; should this be a gray stream?
                   ;; No:
                   ;; :element-type '(unsigned-byte 8)
                   ;; [bug10772]: Make this straight through:
                   :external-format :void) ; [rfe5230]
    (do* ((context (md5-init))
          (read-size (min (file-length stream) #.(* 1024 8)))
          (buffer (make-array read-size :element-type '(unsigned-byte 8)))
          (n #1=(read-sequence buffer stream) #1#))
        ((or (= n 0) (< n read-size))
         (when (> n 0) (md5-update context buffer :end n))
         (md5-final context :return return))
      (md5-update context buffer :end n))))

(defun md5-result-to-integer (array)
  (do* ((result
         (excl::.primcall 'sys::new-bignum
           #.(/ 16 (sys::mdparam 'comp::md-bignum-bigit-bytes))))
        (i 0 (1+ i))
        (i2 15 (1- i2)))
      ((= i 16)
       ;; Normalize bignum [bug14150]:
       (values (excl::.primcall 'sys::one-bigit-div-in-place result 1)))
    (setf (sys:memref
           result
           #.(sys::mdparam 'comp::md-bignum-data0-adj)
           ;; Can't use read-vector and the :endian-swap keyword in
           ;; md5-file because we'd have to make the element type
           ;; (unsigned-byte 32), and that would add complications from
           ;; use of padding.
           #+little-endian i
           #+(and (not 64bit) big-endian) (logxor i 1)
           #+(and 64bit big-endian) (logxor i 3)
           :unsigned-byte)
      (aref array i2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Blowfish crypto moved to ../private/blowfish.cl

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rsa encryption and decryption routines moved to ../private/rsa.cl

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; crypto utilities

(defun hex-string-to-integer (string &optional (start 0) end)
  ;; Efficiently convert `string' to a number, assuming that it's a string
  ;; of hex digits, like you'd find in an MD5 signature.
  ;; For example: (hex-string-to-integer "deadbeef") => 3735928559
  ;; Here's a comparison with parse-integer:
  ;;  (parse-integer "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef" :radix 16)
  ;;   space allocation:
  ;;   3 cons cells, 1,952 other bytes, 0 static bytes
  ;;  (hex-string-to-integer "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef")
  ;;   space allocation:
  ;;   1 cons cell, 32 other bytes, 0 static bytes
  (or end (setq end (length string)))
  (let ((length-of-hex (- end start)))
    (when (or (not (plusp length-of-hex))
              (do* ((char-index start (1+ char-index)))
                  ((= char-index end) t)
                (when (not (char= #\0 (char string char-index)))
                  (return nil))))
      (return-from hex-string-to-integer 0))

    (let* ((result-bytes ;; one char in `string' is 4 bits
            (ceiling length-of-hex 2))
           (bigits (ceiling result-bytes
                            #.(sys::mdparam 'comp::md-bignum-bigit-bytes)))
           (result (excl::.primcall 'sys::new-bignum bigits))
           (si (1- end))
           byte)

      ;; set most significant bigit to 0, in case we don't set all of it
      (setf (sys:memref
             result
             #.(sys::mdparam 'comp::md-bignum-data0-adj)
             (ash (1- bigits) #-64bit 1 #+64bit 2)
             #.(sys::mdparam 'comp::md-bignum-bigit-format))
        0)
      (dotimes (bi result-bytes)
        (setq byte
          (let* ((lsn ;; least significant nibble
                  (let ((res (digit-char-p (char string si) 16)))
                    (when (null res)
                      (error "bad digit in hex string: ~c." (char string si)))
                    res))
                 (msn ;; most significant nibble
                  (when (>= (decf si) start)
                    (let ((res (digit-char-p (char string si) 16)))
                      (when (null res)
                        (error "bad digit in hex string: ~c."
                               (char string si)))
                      res))))
            (if* msn
               then (+ lsn (ash msn 4))
               else lsn)))
        (setf (sys:memref
               result
               #.(sys::mdparam 'comp::md-bignum-data0-adj)
               #+little-endian bi
               #+(and (not 64bit) big-endian) (logxor bi 1)
               #+(and 64bit big-endian) (logxor bi 3)
               :unsigned-byte)
          byte)
        (decf si))

      (values
       ;; normalize result (result is either a fixnum or bignum):
       (excl::.primcall 'sys::one-bigit-div-in-place result 1)))))

(defun hex-string-to-usb8-array (string &key (start 0) (end (length string)))
  (declare (optimize (speed 3)))
  (let* ((len (- end start))
         (bytes (/ len 2))
         (hexdigs "0123456789abcdef"))
    (if (< len 0)
        (error "'start' must be less than or equal to 'end'"))
    (if (oddp len)
        (error "An even number of characters must be used"))
    (let ((arr (make-array bytes :element-type '(unsigned-byte 8)))
          (pos start))
      (macrolet ((decode-char (char)
                   `(the (integer 0 15)
                      (or (position ,char hexdigs :test #'char-equal)
                          (error "Invalid hex character: ~a" ,char)))))
        (dotimes (n bytes)
          (setf (aref arr n)
            (logior (ash (decode-char (char string pos)) 4)
                    (decode-char (char string (1+ pos)))))
          (incf pos 2))
        arr))))

(defun usb8-array-to-hex-string (arr &key (start 0) (end (length arr)))
  (with-output-to-string (s)
    (dotimes (n (- end start))
      (format s "~2,'0x" (aref arr start))
      (incf start))))

(defun integer-to-hex-string (integer)
  ;; Efficiently convert an integer to a hex string.  Yes, this is more
  ;; efficient than the version below (generates less garbage and is
  ;; faster).  I don't like having to specify a string in the other
  ;; version, too.
  (format nil "~x" integer))

(defun string-to-integer (string &key start end)
  (octets-to-integer (string-to-octets string
                                       :start start
                                       :end end
                                       :null-terminate nil)))

(defun octets-to-integer (octets)
  (let ((n 0))
    (dotimes (i (length octets))
      (setq n (+ n (ash (aref octets i) (* 8 i)))))
    n))

(defun integer-to-string (integer)
  (let* ((len (ceiling (/ (integer-length integer) 8)))
         (s (make-string len)))
    (dotimes (i len)
      (setf (aref s i)
        (sys::fixnum-to-char (logand #xff integer)))
      (setq integer (ash integer -8)))
    s))

#+unused
(defun integer-to-octets (integer)
  (let* ((len (ceiling (/ (integer-length integer) 8)))
         (o (make-array len :element-type '(unsigned-byte 8))))
    (dotimes (i len)
      (setf (aref o i) (logand #xff integer))
      (setq integer (ash integer -8)))
    o))

;; info on base64 conversion (section 6):
;; http://www.ietf.org/internet-drafts/draft-ietf-openpgp-rfc2440bis-00.txt

(defvar *to-base64*
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")

(defun integer-to-base64-string (integer &optional (column 52))
  (with-output-to-string (s)
    (do* ((len (integer-length integer))
          (len8 (round-up len 8))
          (padded-len (round-up len8 6))
          (shift (- padded-len len8))
          (integer (ash integer shift))
          (ngroups (/ padded-len 6))
          (remain (- 24 (mod padded-len 24)))
          (i 0 (1+ i))
          (res '())
          n)
        ((= i ngroups)
         (do* ((break-col (when column (round-up column 4)))
               (col 0 (1+ col))
               (chars res (cdr chars)))
             ((null chars)
              (if* (< remain 8)
                 then (write-char #\= s)
               elseif (< remain 16)
                 then (write-char #\= s)
                      (write-char #\= s)))
           (when (and break-col (> col break-col))
             (write-char #\newline s)
             (setq col 0))
           (write-char (car chars) s)))
      (setq n (logand #x3f integer))
      (setq integer (ash integer -6))
      (push (schar *to-base64* n) res))))

(defun base64-string-to-integer (string)
  (do* ((value 0)
        (i 0 (1+ i))
        (max (length string))
        (pad 0)
        n)
      ((= i max)
       (if* (= pad 2)
          then (ash value -4)
        elseif (= pad 1)
          then (ash value -2)
          else (assert (zerop pad))
               value))
    (setq n (base64-digit-char (schar string i)))
    (if* (= -1 n)
       thenret ;; ignore
     elseif (= -2 n)
       then (incf pad)
       else (setq value (+ (ash value 6) n)))))

(defun usb8-array-to-base64-string-1 (usb8-array 
                                      &key (wrap-at-column 52)
                                           (start 0)
                                           (end (length usb8-array)))
  (declare (optimize speed)
           (fixnum start end))
  (with-underlying-simple-vector (usb8-array thing disp)
    (declare ((simple-array (unsigned-byte 8) (*)) thing)
             (fixnum disp))
    (incf start disp)
    (incf end disp)

    (let ((column 0)
          (len (- end start)))
      (declare (fixnum column len))

      (flet ((output-base64 (s bits fill)
               (when (and wrap-at-column (>= column wrap-at-column))
                 (write-char #\newline s)
                 (setq column 0))
               
               (write-char (schar *to-base64* (logand 63 (ash bits -18))) s)
               (write-char (schar *to-base64* (logand 63 (ash bits -12))) s)
               (if* (null fill)
                  then (write-char 
                        (schar *to-base64* (logand 63 (ash bits -6)))
                        s)
                       (write-char (schar *to-base64* (logand 63 bits)) s)
                elseif (eql 2 fill)
                  then (write-char #\= s)
                       (write-char #\= s)
                elseif (eql 1 fill)
                  then (write-char 
                        (schar *to-base64* (logand 63 (ash bits -6)))
                        s)
                       (write-char #\= s))
               (if wrap-at-column
                   (incf column 4))))
        (with-output-to-string (s)
          (do* ((ngroups (truncate len 3)
                         (1- ngroups))
                (left-over (nth-value 1 (truncate len 3)))
                (i start)
                bits)
              ((= 0 ngroups)
               (if* (= 2 left-over)
                  then (setq bits ;; make 24 bits of info, pad last 8
                         (+ (ash (aref thing i) 16)
                            (ash (aref thing (the fixnum (+ i 1))) 8)))
                       (output-base64 s bits 1)
                elseif (= 1 left-over)
                  then (setq bits ;; make 24 bits of info, pad last 16
                         (ash (aref thing i) 16))
                       (output-base64 s bits 2)))
            (declare (fixnum ngroups left-over i bits))
            
            (setq bits ;; make 24 bits of info
              (+ (ash (aref thing i) 16)
                 (ash (aref thing (the fixnum (+ i 1))) 8)
                 (aref thing (the fixnum (+ i 2)))))
            (setq i (+ i 3))
            
            (output-base64 s bits nil)))))))

(defun usb8-array-to-base64-string (usb8-array &rest more)
  (declare (optimize speed))
  ;; If exactly one additional argument was passed, then the old
  ;; argument format is being used.
  (if* (and more (null (cdr more)))
     then (usb8-array-to-base64-string-1 usb8-array
                                         :wrap-at-column (first more))
     else (apply #'usb8-array-to-base64-string-1 usb8-array more)))

(define-compiler-macro usb8-array-to-base64-string (usb8-array &rest more)
  ;; If exactly one additional argument was passed, then the old
  ;; argument format is being used.
  (if* (and more (null (cdr more)))
     then `(usb8-array-to-base64-string-1 ,usb8-array
                                          :wrap-at-column ,(first more))
     else `(usb8-array-to-base64-string-1 ,usb8-array ,@more)))

(defun string-to-base64-string-1 (string
                                  &key (wrap-at-column 52)
                                       (start 0)
                                       (end (length string))
                                       external-format)
  (declare (optimize speed))
  (let ((buf (make-array 4096 :element-type '(unsigned-byte 8))))
    (declare (dynamic-extent buf))
    
    (if (null external-format)
        (setf external-format (crlf-base-ef :latin1)))
    
    (multiple-value-bind (usb8 len)
        (string-to-octets string 
                          :start start :end end
                          :null-terminate nil
                          :external-format external-format
                          :mb-vector buf
                          :make-mb-vector? t)
      (usb8-array-to-base64-string-1 usb8 :end len
                                     :wrap-at-column wrap-at-column))))

(defun string-to-base64-string (string &rest more)
  ;; If exactly one additional argument was passed, then the old
  ;; argument format is being used.
  (if* (and more (null (cdr more)))
     then (string-to-base64-string-1 string
                                     :wrap-at-column (first more))
     else (apply #'string-to-base64-string-1 string more)))

(define-compiler-macro string-to-base64-string (string &rest more)
  ;; If exactly one additional argument was passed, then the old
  ;; argument format is being used.
  (if* (and more (null (cdr more)))
     then `(string-to-base64-string-1 ,string
                                      :wrap-at-column ,(first more))
     else `(string-to-base64-string-1 ,string ,@more)))


(defun base64-string-to-usb8-array (string 
                                    &key (start 0) (end (length string))
                                         output)
  (declare (optimize speed)
           (fixnum start end))
  (with-underlying-simple-vector (string string disp)
    (declare (simple-string string)
             (fixnum disp)
             ((simple-array (unsigned-byte 8) (*))))
    (incf start disp)
    (incf end disp)
    
    (let ((new-size (ceiling (* 6 (- end start)) 8)))
      (if (and output (< (length output) new-size))
          (setf output nil))
      
      (do* ((i start (1+ i))
            (pad 0)
            (res (or output 
                     (make-array new-size :element-type '(unsigned-byte 8))))
            (resi 0)
            (counter 0)
            (bits 0)
            n)
          ((= i end)
           ;;(format t "bits=~x, pad=~s, counter=~s~%" bits pad counter)
           (when (and (= 0 pad) (> counter 1))
             (error "At least ~d bits missing at end of encoding."
                    (* (- 4 counter) 6)))
           (if* (= 0 counter)
              thenret
            elseif (= 1 counter)
              then (error "At least 2 bits missing at end of encoding.")
            elseif (= 2 counter)
              then ;; We have 2 missing base64 digits, so add 12 to the
                   ;; shift starting point of -16.
                   (setf (aref res resi) (logand (ash bits -4) 255))
                   (incf resi)
            elseif (= 3 counter)
              then ;; shift by -10 instead of -16 because 1 base64 digit is
                   ;; missing and that is 6 bits.
                   (setf (aref res resi) (logand (ash bits -10) 255))
                   (incf resi)
                   (setf (aref res resi) (logand (ash bits -2) 255))
                   (incf resi))
           
           (if (null output)
               (.primcall 'sys::shrink-svector res resi))
           (values res resi))
      
        (declare (fixnum i pad new-size resi counter bits n))
      
        (if* (= -1 (setq n (base64-digit-char (schar string i))))
           thenret ;; ignore
         elseif (= -2 n)
           then (incf pad)
           else (assert (zerop pad))
                (setq bits (+ (the fixnum (ash bits 6)) n))
                (incf counter)
                (when (= 4 counter)
                  (setf (aref res resi) (logand (ash bits -16) 255))
                  (incf resi)
                  (setf (aref res resi) (logand (ash bits -8) 255))
                  (incf resi)
                  (setf (aref res resi) (logand bits 255))
                  (incf resi)
                  (setq counter 0 bits 0)))))))

(defun base64-string-to-string (string
                                &key (start 0) (end (length string))
                                     external-format)
  (declare (optimize speed))
  (let ((buf (make-array 4096 :element-type '(unsigned-byte 8))))
    (declare (dynamic-extent buf))
    
    (if (null external-format)
        (setf external-format (crlf-base-ef :latin1)))
    
    (multiple-value-bind (res len)
        (base64-string-to-usb8-array string :start start :end end
                                     :output buf)
      (values (octets-to-string res :end len
                                :external-format external-format)))))

(defun base64-encode-stream (instream outstream &key (wrap-at 72))
  (declare (optimize (speed 3)))
  ;; inbuf _must_ be a size which is a multiple of three.  The 
  ;; encoding code depends on it.  outbuf must be 4/3rds bigger than
  ;; inbuf.
  (let ((inbuf (make-array #.(* 3 4096) :element-type '(unsigned-byte 8)))
        (outbuf (make-array #.(* 4 4096) :element-type 'character))
        remaining end outpos inpos value)
    (declare (dynamic-extent inbuf outbuf)
             (fixnum remaining outpos end inpos value))
            
    (macrolet ((outchar (char)
                 `(progn
                    (setf (schar outbuf outpos) ,char)
                    (incf outpos)))
               (outchar-base64 (x)
                 `(outchar (schar excl::*to-base64* (logand ,x 63)))))
      
      (flet ((read-full-vector (buf stream)
               (let ((pos 0)
                     (max (length buf))
                     newpos)
                 (declare (fixnum pos max newpos))
                 (while (< pos max)
                   (setf newpos (read-vector buf stream :start pos))
                   (if* (= newpos pos)
                      then (return))
                   (setf pos newpos))
                 pos)))

        (while (/= 0 (setf end (read-full-vector inbuf instream)))
          (setf remaining end)
          (setf inpos 0)
          (setf outpos 0)
          (while (> remaining 0)
            (if* (>= remaining 3)
               then (setf value (logior (ash (aref inbuf inpos) 16)
                                        (ash (aref inbuf (+ 1 inpos)) 8)
                                        (aref inbuf (+ 2 inpos))))
                    (incf inpos 3)
                    (decf remaining 3)
                    (outchar-base64 (ash value -18))
                    (outchar-base64 (ash value -12))
                    (outchar-base64 (ash value -6))
                    (outchar-base64 value)
             elseif (= remaining 2)
               then (setf value (logior (ash (aref inbuf inpos) 16)
                                        (ash (aref inbuf (+ 1 inpos)) 8)))
                    (incf inpos 2)
                    (decf remaining 2)
                    (outchar-base64 (ash value -18))
                    (outchar-base64 (ash value -12))
                    (outchar-base64 (ash value -6))
                    (outchar #\=)
               else (setf value (ash (aref inbuf inpos) 16))
                    (incf inpos)
                    (decf remaining)
                    (outchar-base64 (ash value -18))
                    (outchar-base64 (ash value -12))
                    (outchar #\=)
                    (outchar #\=)))
                
          ;; generate output.
          (if* (null wrap-at)
             then (write-string outbuf outstream :end outpos)
             else (setf inpos 0)
                  (while (< inpos outpos)
                    (let ((len (min (- outpos inpos) wrap-at)))
                      (write-string outbuf outstream 
                                    :start inpos
                                    :end (+ inpos len))
                      (incf inpos len)
                      (write-char #\newline outstream)))))))))

;; Used by base64-decode-stream
(defconstant *base64-byte-to-byte* 
    #.(let ((arr (make-array 257 :element-type 'fixnum)))
        (setf (aref arr 256) -3) 
        (dotimes (n 256)
          (setf (aref arr n)
            (if* (<= #.(char-int #\A) n #.(char-int #\Z))
               then (- n #.(char-int #\A))
             elseif (<= #.(char-int #\a) n #.(char-int #\z))
               then (+ 26 (- n #.(char-int #\a)))
             elseif (<= #.(char-int #\0) n #.(char-int #\9))
               then (+ 52 (- n #.(char-int #\0)))
             elseif (= #.(char-int #\+) n)
               then 62
             elseif (= #.(char-int #\/) n)
               then 63
             elseif (= #.(char-int #\=) n)
               then -2
               else -1)))
        arr))

(defun base64-decode-stream (instream outstream &key count (error-p t))
  (declare (optimize (speed 3)))
  ;; outbuf must have a size that is a multiple of 3. 
  ;; 1366*3=4098.  This value is down further in the code as well.
  (let ((outbuf (make-array #.(* 1366 3) :element-type '(unsigned-byte 8)))
        (outpos 0)
        byte1 byte2 byte3 byte4)
    (declare (dynamic-extent outbuf)
             ((integer 0 4095) outpos)
             ((unsigned-byte 8) byte1 byte2 byte3 byte4))

    (macrolet ((my-read-byte ()
                 `(block my-read-byte 
                    (if* count
                       then (if* (<= count 0)
                               then (return-from my-read-byte 256)
                               else (decf count)))
                    (read-byte instream nil 256)))
               
               (flush ()
                 (let ((start (gensym)))
                   `(let ((,start 0))
                      (declare (fixnum ,start))
                      (while (< ,start outpos)
                        (setf ,start
                          (write-vector outbuf outstream 
                                        :start ,start :end outpos)))
                      (setf outpos 0)))))
      

      (macrolet ((get-byte (var)
                   `(loop
                      (setf ,var (aref *base64-byte-to-byte* (my-read-byte)))
                      (if (not (eq ,var -1))
                          (return))))
                 
                 (bail ()
                   `(progn
                      (flush)
                      (return-from base64-decode-stream nil))))
                 
        (flet ((check-eof (var)
                 (when (eq var -3)
                   (if* error-p
                      then (error "Premature end of input while base64 decoding")
                      else (bail)))))

          (loop
            (get-byte byte1)

            (if (eq byte1 -3) ;; EOF
                (return))
        
            (get-byte byte2)
            (check-eof byte2)
            (get-byte byte3)
            (check-eof byte3)
            (get-byte byte4)
            (check-eof byte4)
      
            (when (or (= byte1 -2) (= byte2 -2))
              (if* error-p
                 then (error "Invalid base64 encoding ('=' character in wrong position)")
                 else (bail)))
      
            (setf (aref outbuf outpos) 
              (logior (ash byte1 2) (ash byte2 -4)))
            (incf outpos)
      
            (when (eq byte3 -2)
              (if (eq byte4 -2) ;; double equal sign
                  (return))
              
              (if* error-p 
                 then (error "Invalid base64 encoding ('=' not doubled)")
                 else (bail)))
        
            (setf (aref outbuf outpos)
              (logior (logand (ash byte2 4) #xf0)
                      (ash byte3 -2)))
            (incf outpos)
        
            (if (= byte4 -2)
                (return))
        
            (setf (aref outbuf outpos)
              (logior (logand (ash byte3 6) #xc0) byte4))
            (incf outpos)
        
            (if (>= outpos #.(* 1366 3))
                (flush)))

          (flush)
          t)))))

(defun base64-digit-char (char &aux (code (char-code char)))
  (declare (optimize (speed 3) (safety 0) (debug 0))
           ((integer 0 65535) code))
  ;; 0 or the 6-bit code
  ;; -1 => ignore
  ;; -2 => padding char
  (if* (<= #.(char-int #\A) code #.(char-int #\Z))
     then (- code #.(char-int #\A))
   elseif (<= #.(char-int #\a) code #.(char-int #\z))
     then (+ 26 (- code #.(char-int #\a)))
   elseif (<= #.(char-int #\0) code #.(char-int #\9))
     then (+ 52 (- code #.(char-int #\0)))
   elseif (char= #\+ char)
     then 62
   elseif (char= #\/ char)
     then 63
   elseif (char= #\= char)
     then -2
     else -1))

#+ignore ;; only works for values of n which are powers of 2!  Use one below.
(defun round-up (a n)
  (declare (optimize (speed 3) (safety 0))
           (fixnum n))
  ;; round `a' up to next larger multiple of `n'
  (logand (+ a (- n 1)) (lognot (- n 1))))

(defun round-up (a n)
  ;; round `a' up to next larger multiple of `n'
  (declare (optimize (speed 3))
           (fixnum n))
  (if* (zerop (mod a n))
     then a
     else (* (+ 1 (floor (/ a n))) n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; stuff from aclwin that is used by cg, documented and exported in the
;; base lisp:

#+mswindows
(eval-when (compile eval)
  (defconstant *file_attribute_readonly* #x00000001)
  (defconstant *file_attribute_hidden* #x00000002)
  (defconstant *file_attribute_system* #x00000004)
  (defconstant *file_attribute_directory* #x00000010)
  (defconstant *file_attribute_archive* #x00000020)
  ;;(defconstant *file_attribute_encrypted* #x00000040)
  (defconstant *file_attribute_normal* #x00000080)
  (defconstant *file_attribute_temporary* #x00000100)
  ;;(defconstant *file_attribute_sparse_file* #x00000200)
  ;;(defconstant *file_attribute_reparse_point* #x00000400)
  ;;(defconstant *file_attribute_compressed* #x00000800)
  ;;(defconstant *file_attribute_offline* #x00001000)
  ;;(defconstant *file_attribute_not_content_indexed* #x00002000)
  )

#+mswindows
(compiler-let ((*record-xref-info* nil))
  (ff:def-foreign-call (.get-file-attributes "GetFileAttributesA")
      ((filename (* :char)))
    :strings-convert nil
    :returning :int)
  (ff:def-foreign-call (.set-file-attributes "SetFileAttributesA")
      ((filename (* :char))
       (attributes :int))
    :strings-convert nil
    :returning :int)

  (defun get-file-attributes (filespec)
    (with-native-string (s (namestring filespec))
      (let ((res (.get-file-attributes s)))
        (when (= -1 res)
          (.error "Could not get file attributes for ~a." filespec))
        res)))

  (defun (setf get-file-attributes) (new-attributes filespec)
    (with-native-string (s (namestring filespec))
      (when (= 0 (.set-file-attributes s new-attributes))
        (.error "Could not set file attributes of ~a." filespec))
      new-attributes))
  )

(defun combined-file-attributes (bits bool current-attributes)
  (if* bool
     then (logior current-attributes bits)
     else (logandc2 current-attributes bits)))

(defun file-read-only-p (filespec
                         &aux (pathname
                               (or (probe-file filespec)
                                   (error "~a does not exist." filespec))))
  #+mswindows
  (let ((fa (get-file-attributes (namestring pathname))))
    (logtest fa #.*file_attribute_readonly*))
  #-mswindows
  (let* ((mode (excl::filesys-permission (namestring pathname))))
    (= 0 (logand mode #o300))))

(defun (setf file-read-only-p) (bool filespec)
  #-mswindows (declare (ignore bool filespec))
  #-mswindows (.error "This function only works on Windows.")
  #+mswindows
  (setf (get-file-attributes filespec)
    (combined-file-attributes #.*file_attribute_readonly*
                              bool
                              (get-file-attributes filespec))))

(defun file-hidden-p (filespec)
  #-microsoft (declare (ignore filespec))
  #-microsoft (error "This function only works on Windows.")
  #+microsoft
  (let* ((pathname (or (probe-file filespec)
                       (error "~a does not exist." filespec)))
         (fa (excl::raw-file-attributes (namestring pathname))))
    (logtest fa #.*file_attribute_hidden*)))

(defun (setf file-hidden-p) (bool filespec)
  #-mswindows (declare (ignore bool filespec))
  #-mswindows (.error "This function only works on Windows.")
  #+mswindows
  (setf (get-file-attributes filespec)
    (combined-file-attributes #.*file_attribute_hidden*
                              bool
                              (get-file-attributes filespec))))

(defun file-system-p (filespec)
  #-microsoft (declare (ignore filespec))
  #-microsoft (error "This function only works on Windows.")
  #+microsoft
  (let* ((pathname (or (probe-file filespec)
                       (error "~a does not exist." filespec)))
         (fa (excl::raw-file-attributes (namestring pathname))))
    (logtest fa #.*file_attribute_system*)))

(defun (setf file-system-p) (bool filespec)
  #-mswindows (declare (ignore bool filespec))
  #-mswindows (.error "This function only works on Windows.")
  #+mswindows
  (setf (get-file-attributes filespec)
    (combined-file-attributes #.*file_attribute_system*
                              bool
                              (get-file-attributes filespec))))

(defun file-archive-p (filespec)
  #-microsoft (declare (ignore filespec))
  #-microsoft (error "This function only works on Windows.")
  #+microsoft
  (let* ((pathname (or (probe-file filespec)
                       (error "~a does not exist." filespec)))
         (fa (excl::raw-file-attributes (namestring pathname))))
    (logtest fa #.*file_attribute_archive*)))

(defun (setf file-archive-p) (bool filespec)
  #-mswindows (declare (ignore bool filespec))
  #-mswindows (.error "This function only works on Windows.")
  #+mswindows
  (setf (get-file-attributes filespec)
    (combined-file-attributes #.*file_attribute_archive*
                              bool
                              (get-file-attributes filespec))))

(defun file-normal-p (filespec)
  #-microsoft (declare (ignore filespec))
  #-microsoft (error "This function only works on Windows.")
  #+microsoft
  (let* ((pathname (or (probe-file filespec)
                       (error "~a does not exist." filespec)))
         (fa (excl::raw-file-attributes (namestring pathname))))
    (logtest fa #.*file_attribute_normal*)))

(defun (setf file-normal-p) (bool filespec)
  #-mswindows (declare (ignore bool filespec))
  #-mswindows (.error "This function only works on Windows.")
  #+mswindows
  (setf (get-file-attributes filespec)
    (combined-file-attributes #.*file_attribute_normal*
                              bool
                              (get-file-attributes filespec))))

(defun file-temporary-p (filespec)
  #-microsoft (declare (ignore filespec))
  #-microsoft nil
  #+microsoft
  (let* ((pathname (or (probe-file filespec)
                       (error "~a does not exist." filespec)))
         (fa (excl::raw-file-attributes (namestring pathname))))
    (logtest fa #.*file_attribute_temporary*)))

(defun (setf file-temporary-p) (bool filespec)
  #-mswindows (declare (ignore bool filespec))
  #-mswindows (.error "This function only works on Windows.")
  #+mswindows
  (setf (get-file-attributes filespec)
    (combined-file-attributes #.*file_attribute_temporary*
                              bool
                              (get-file-attributes filespec))))

(defun file-attributes (filespec)
  #-microsoft (declare (ignore filespec))
  #-microsoft (error "This function only works on Windows.")
  #+microsoft
  (let* ((pathname (or (probe-file filespec)
                       (error "~a does not exist." filespec)))
         (fa (excl::raw-file-attributes (namestring pathname))))
    (values (when (probe-file filespec) t)
            (logtest fa #.*file_attribute_readonly*)
            (logtest fa #.*file_attribute_hidden*)
            (logtest fa #.*file_attribute_system*)
            (logtest fa #.*file_attribute_directory*)
            (logtest fa #.*file_attribute_archive*)
            (logtest fa #.*file_attribute_normal*)
            (logtest fa #.*file_attribute_temporary*))))

(defun rename-file-raw (filespec new-name &key follow-symlinks)
  ;; Like cl:rename-file, except it doesn't do
  ;;   (merge-pathnames new-name filespec)
  ;; to get a defaulted-new-name used instead of new-name.  Doing this
  ;; merge means
  ;;   (rename-file "tmp/foo.cl" "tmp/bar.cl")
  ;; do this in UNIX-speak:
  ;;   mv tmp/foo.cl tmp/tmp/bar.cl
  ;; which is insane to anyone that has used `mv', or the Windows
  ;; version called `move'.
  (let ((new-name (pathname new-name))
        (old-truename (truename filespec :follow-symlinks follow-symlinks)))
    (filesys-rename-file (namestring old-truename)
                         (namestring
                          (merge-pathnames
                           (translate-logical-pathname new-name))))
    (values new-name old-truename (truename new-name :follow-symlinks nil))))

(defun rename-file-acl6.1 (filename new-file)
  (setq filename (defaultify-a-pathname filename nil))
  (let* ((t-filename (merge-pathnames (translate-logical-pathname filename)))
         (t-new-file (merge-pathnames (translate-logical-pathname new-file)))
         (new-name (merge-pathnames t-new-file t-filename)))
    (filesys-rename-file (namestring t-filename) (namestring new-name))
    (values new-name t-filename t-new-file)))

(defun compare-files (filespec1 filespec2)
  ;; compare the contents of filespec1 and filespec2,
  ;; returning t if they are the same, nil otherwise.
  (declare (optimize speed))
  (with-open-file (s1 filespec1 :direction :input)
    (with-open-file (s2 filespec2 :direction :input)
      (do* ((buf1 (make-array 2048 :element-type '(unsigned-byte 8)))
            (buf2 (make-array 2048 :element-type '(unsigned-byte 8)))
            (p1 #1=(the fixnum (read-sequence buf1 s1)) #1#)
            (p2 #1=(the fixnum (read-sequence buf2 s2)) #1#))
          ((or (= p1 0) (= p2 0))
           (and (= p1 0) (= p2 0)))
        (declare (fixnum p1 p2))
        (when (or (/= p1 p2)
                  (not (octet-vector-equalp buf1 buf2 p1)))
          (return nil))))))

;; a faster version is below, written by Duane and based on simple-string=
;; from hash.cl.
#+ignore 
(defun octet-vector-equalp (buf1 buf2 len)
  (declare (optimize speed)
           (fixnum len)
           (type (unsigned-byte 8) buf1 buf2))
  (do* ((i 0 (the fixnum (1+ i))))
      ((= i len) t)
    (declare (fixnum i))
    (when (/= (the fixnum (aref buf1 i))
              (the fixnum (aref buf2 i)))
      (return nil))))

(defun octet-vector-equalp (vec1 vec2
                            &optional length)
  (declare (optimize (speed 3) (safety 0) (debug 0))
           (type (simple-array (unsigned-byte 8) (*)) vec1 vec2)
           (type fixnum length))
  (excl::atomically
   (let ((vec1start
          (excl::ll :+ vec1
                    comp::(ll :fixnum-to-mi
                              #.(- (sys::mdparam 'md-lvector-data0-adj)
                                   (sys::mdparam 'md-lvws)))))
         (vec2start
          (excl::ll :+ vec2
                    comp::(ll :fixnum-to-mi
                              #.(- (sys::mdparam 'md-lvector-data0-adj)
                                   (sys::mdparam 'md-lvws))))))
     (let ((len (excl::lv_size vec1)))
       (declare (type fixnum len))
       (if* length
          then (when (or (< len length)
                         (< (the fixnum (excl::lv_size vec2)) length))
                 (return-from octet-vector-equalp nil))
               (setq len length)
          else (when (not (eq len (excl::lv_size vec2)))
                 (return-from octet-vector-equalp nil)))
       (when (eq len 0)
         (return-from octet-vector-equalp t))
       (setq len (excl::ll :fixnum-to-mi len))
       (let ((i (excl::ll :fixnum-to-mi #.(sys::mdparam 'comp::md-lvws))))
         (loop
           (when (excl::ll :>= i len)
             (let ((mask
                    comp::(ll :aref-nat
                              (ll :+ (load-time-value
                                      excl::*word-mask-array*)
                                  (ll :fixnum-to-mi
                                      #.(sys::mdparam
                                         'md-lvector-data0-adj)))
                              (ll :lsl (ll :logand
                                             (ll :- excl::len
                                                 (ll :fixnum-to-mi 1))
                                             (ll :fixnum-to-mi
                                                 #.(1- (sys::mdparam
                                                        'comp::md-lvws))))
                                    (ll :fixnum-to-mi
                                        #.(sys::mdparam
                                           'comp::md-fixnum-shift))))))
               (return (eq (excl::ll :logand
                                     (excl::ll :aref-nat vec1start i)
                                     mask)
                           (excl::ll :logand
                                     (excl::ll :aref-nat vec2start i)
                                     mask)))))
           (unless (eq (excl::ll :aref-nat vec1start i)
                       (excl::ll :aref-nat vec2start i))
             (return nil))
           (setq i (excl::ll
                      :+ i
                      (excl::ll :fixnum-to-mi
                                #.(sys::mdparam 'comp::md-lvws))))))))))

#-mswindows
(compiler-let ((*record-xref-info* nil))
  (ff:def-foreign-call (syscall-realpath "realpath")
      ((path (* :char))
       (resolved_path :int))
    :strings-convert t
    :returning :int
    :error-value :errno)
  )

(eval-when (compile eval)
  (defmacro physical-namestring (filespec)
    `(namestring (excl::merge-to-physical ,filespec)))
  )
  
#-mswindows
(defun realpath (filespec)
  ;; The following is fairly tricky code, so some comments:
  ;; - the `o' binding is needed because without it the static storage
  ;;   might be reclaimed
  ;; - lispval-other-to-address doesn't return a pointer to the start of
  ;;   the data, as I originally thought
  (let* ((o (make-array *path-max* :element-type '(unsigned-byte 8)
                        :allocation :lispstatic-reclaimable))
         (s (+ (lispval-other-to-address o)
               #.(* 2 (sys::mdparam 'comp::md-lvbs)))) ;; [bug15560]
         (rp
          (multiple-value-bind (res errno)
              (syscall-realpath (physical-namestring filespec) s)
            (if* (= res 0)
               then (perror errno "realpath failed")
               else (values (native-to-string s))))))
    (if* (file-directory-p rp)
       then (excl::pathname-as-directory rp)
       else (pathname rp))))

#+mswindows
(compiler-let ((*record-xref-info* nil))
  (ff:def-foreign-variable
      (lisp-disable-tray-exit "lisp_disable_tray_exit")
      :type :signed-long)
  )

#+mswindows
(defun console-control (&key (tray nil tray-given)
                             (tray-exit nil tray-exit-given)
                             (minimize nil minimize-given)
                             (maximize nil maximize-given)
                             (close nil close-given)
                             (show nil show-given)
                             (size nil size-given)
                             (title nil title-given))
  ;; tray nil => don't show tray icon
  ;; tray t   => show tray icon
  ;;
  ;; tray-exit nil => can't exit lisp from the tray
  ;; tray-exit t   => can exit lisp from the tray
  ;;
  ;; minimize nil   => disabled
  ;; minimize :hide => hide instead of minimize
  ;; minimize t     => normal behavior, minimize
  ;;
  ;; maximize nil   => disabled
  ;; maximize t     => normal behavior, maximize
  ;;
  ;; size max => set the size, in bytes, the console can grow to `max'.
  ;;    After the console hits this size, it is truncated
  ;;
  ;; close :minimize => close button, menu and Alt-F4 minimize
  ;; close :hide => close button, menu and Alt-F4 hide
  ;; close nil => close button, menu and Alt-F4 hide are not active
  ;; close t => close button, menu and Alt-F4 hide behave normally
  ;;
  ;; The value of `show' can be any of the following:
  ;;   keyword value             win32 API def
  ;;   nil, :hide                SW_HIDE
  ;;   t, :normal, :shownormal   SW_SHOWNORMAL (aka SW_NORMAL)
  ;;   :showminimized            SW_SHOWMINIMIZED
  ;;   :maximize, :showmaximized SW_SHOWMAXIMIZED (aka SW_MAXIMIZE)
  ;;   :shownoactivate           SW_SHOWNOACTIVATE
  ;;   :show                     SW_SHOW
  ;;   :minimize                 SW_MINIMIZE
  ;;   :showminnoactive          SW_SHOWMINNOACTIVE
  ;;   :showna                   SW_SHOWNA
  ;;   :restore                  SW_RESTORE
  ;;   :showdefault              SW_SHOWDEFAULT
  ;; title <string> => change the Windows window title to <string>
  
  (when tray-given (tray-icon-control (if tray 1 0)))
  
  (when tray-exit-given
    (let ((current (sys:memref-int lisp-disable-tray-exit 0 0 :signed-long)))
      ;; current == 0 for enabled tray exit
      ;; current == 1 for disabled tray exit
      (if* (and (= current 0) ;; enabled
                (null tray-exit))
         then ;; disable tray exit
              (setf (sys:memref-int lisp-disable-tray-exit 0 0 :signed-long)
                1)
       elseif (and (= current 1) ;; disabled
                   tray-exit)
         then ;; enable tray exit
              (setf (sys:memref-int lisp-disable-tray-exit 0 0 :signed-long)
                0))))
  
  (when minimize-given
    ;;  (the `maybe' part is that we don't know if there _is_ a console)
    (if* (eq minimize :hide) ;; hide the console instead
       then (maybe-set-minmax-state 1 2)
     elseif minimize ;; normal state
       then (maybe-set-minmax-state 1 1)
       else ;; disable minimize button
            (maybe-set-minmax-state 1 0)))
  
  (when maximize-given
    ;;  (the `maybe' part is that we don't know if there _is_ a console)
    (if* maximize ;; normal state
       then (maybe-set-minmax-state 2 1)
       else ;; disable maximize button
            (maybe-set-minmax-state 2 0)))

  (when close-given
    ;;  (the `maybe' part is that we don't know if there _is_ a console)
    (if* (eq close :minimize)
       then (maybe-disable-close-button 2)
     elseif (eq close :hide)
       then (maybe-disable-close-button 3)
     elseif close
       then (maybe-enable-close-button)
       else (maybe-disable-close-button 1)))
  
  (when show-given
    ;; the `maybe' part is that we don't know if there _is_ a console.
    (maybe-show-console-window
     (case show
       ((nil :hide) 0)
       ((t :normal :shownormal) 1)
       (:showminimized 2)
       ((:maximize :showmaximized) 3)
       (:shownoactivate 4)
       (:show 5)
       (:minimize 6)
       (:showminnoactive 7)
       (:showna 8)
       (:restore 9)
       (:showdefault 10))))
  
  (when size-given
    ;; the `maybe' part is that we don't know if there _is_ a console.
    (when (not (numberp size))
      (.error "`size' must be a number: ~s." size))
    (maybe-set-console-size size))
  
  (when title-given
    (when (not (simple-string-p title))
      (.error "`title' must be a simple-string: ~s." title))
    (with-native-string (title title)
      (maybe-set-console-title title)))
  
  (values))

#+mswindows
(compiler-let ((*record-xref-info* nil))
  (ff:def-foreign-variable (lisp-scriptfd "lisp_scriptfd")
      :type :signed-long)
  )

#+mswindows
(defun reading-from-script-file-p ()
  (>= (sys:memref-int lisp-scriptfd 0 0 :signed-long)
      0))

(defun make-escaped-string (string &key (escape #\%)
                                        (passed #'alphanumericp)
                                        escaped)
  (flet ((test-one (char test)
           (typecase test
             (character (eql char test))
             ((member t :all) t)
             (null nil)
             (sequence (position char test))
             (otherwise (funcall test char)))))
    (flet ((test (char escape escaped passed)
             (or (test-one char escape)
                 (test-one char escaped)
                 (null (test-one char passed)))))
      (let* ((len (length string)) (newlen len) new char)
        (typecase escape
          (character nil)
          (string (setf escape (elt escape 0)))
          (otherwise (error "escape argument ~S is not a character" escape)))
        (dotimes (i len)
          (setf char (elt string i))
          (when (test char escape escaped passed)
            (incf newlen 2)))
        (cond ((eql len newlen) string)
              (t (setf new (make-string newlen))
                 (do ((i 0 (1+ i)) (j 0))
                     ((eql i len) new)
                   (setf char (elt string i))
                   (cond ((test char escape escaped passed)
                          (setf (elt new j) escape)
                          (multiple-value-bind (d1 d2)
                              (truncate (char-code char) 16)
                            (incf j)
                            (setf (elt new j) (elt "0123456789abcdef" 
                                                   (logand d1 15)))
                            (incf j)
                            (setf (elt new j) (elt "0123456789abcdef" d2))))
                         (t (setf (elt new j) char)))
                   (incf j))))))))
||#

(provide :excl)
