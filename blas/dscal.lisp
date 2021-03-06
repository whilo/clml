;;; Compiled by f2cl version:
;;; ("$Id: f2cl1.l,v 1.209 2008/09/11 14:59:55 rtoy Exp $"
;;;  "$Id: f2cl2.l,v 1.37 2008/02/22 22:19:33 rtoy Rel $"
;;;  "$Id: f2cl3.l,v 1.6 2008/02/22 22:19:33 rtoy Rel $"
;;;  "$Id: f2cl4.l,v 1.7 2008/02/22 22:19:34 rtoy Rel $"
;;;  "$Id: f2cl5.l,v 1.197 2008/09/11 15:03:25 rtoy Exp $"
;;;  "$Id: f2cl6.l,v 1.48 2008/08/24 00:56:27 rtoy Exp $"
;;;  "$Id: macros.l,v 1.106 2008/09/15 15:27:36 rtoy Exp $")

;;; Using Lisp International Allegro CL Enterprise Edition 8.1 [64-bit Linux (x86-64)] (Oct 7, 2008 17:13)
;;; 
;;; Options: ((:prune-labels nil) (:auto-save t)
;;;           (:relaxed-array-decls nil) (:coerce-assigns :as-needed)
;;;           (:array-type ':array) (:array-slicing t)
;;;           (:declare-common nil) (:float-format double-float))

(in-package "BLAS")


(defun dscal (n da dx incx)
  (declare (type (double-float) da) (type (array double-float (*)) dx)
   (type (f2cl-lib:integer4) incx n))
  (f2cl-lib:with-multi-array-data ((dx double-float dx-%data%
                                    dx-%offset%))
    (prog ((i 0) (m 0) (mp1 0) (nincx 0))
          (declare (type (f2cl-lib:integer4) nincx mp1 m i))
          (if (or (<= n 0) (<= incx 0)) (go end_label))
          (if (= incx 1) (go label20))
          (setf nincx (f2cl-lib:int-mul n incx))
          (f2cl-lib:fdo (i 1 (f2cl-lib:int-add i incx))
                        ((> i nincx) nil)
                        (tagbody
                            (setf (f2cl-lib:fref dx-%data% (i) ((1 *))
                                                 dx-%offset%)
                                  (* da
                                     (f2cl-lib:fref dx-%data% (i)
                                                    ((1 *))
                                                    dx-%offset%)))
                          label10))
          (go end_label)
     label20 (setf m (mod n 5))
          (if (= m 0) (go label40))
          (f2cl-lib:fdo (i 1 (f2cl-lib:int-add i 1)) ((> i m) nil)
                        (tagbody
                            (setf (f2cl-lib:fref dx-%data% (i) ((1 *))
                                                 dx-%offset%)
                                  (* da
                                     (f2cl-lib:fref dx-%data% (i)
                                                    ((1 *))
                                                    dx-%offset%)))
                          label30))
          (if (< n 5) (go end_label))
     label40 (setf mp1 (f2cl-lib:int-add m 1))
          (f2cl-lib:fdo (i mp1 (f2cl-lib:int-add i 5)) ((> i n) nil)
                        (tagbody
                            (setf (f2cl-lib:fref dx-%data% (i) ((1 *))
                                                 dx-%offset%)
                                  (* da
                                     (f2cl-lib:fref dx-%data% (i)
                                                    ((1 *))
                                                    dx-%offset%)))
                            (setf (f2cl-lib:fref dx-%data%
                                                 ((f2cl-lib:int-add i
                                                                    1))
                                                 ((1 *)) dx-%offset%)
                                  (* da
                                     (f2cl-lib:fref dx-%data%
                                                    ((f2cl-lib:int-add i
                                                                       1))
                                                    ((1 *))
                                                    dx-%offset%)))
                            (setf (f2cl-lib:fref dx-%data%
                                                 ((f2cl-lib:int-add i
                                                                    2))
                                                 ((1 *)) dx-%offset%)
                                  (* da
                                     (f2cl-lib:fref dx-%data%
                                                    ((f2cl-lib:int-add i
                                                                       2))
                                                    ((1 *))
                                                    dx-%offset%)))
                            (setf (f2cl-lib:fref dx-%data%
                                                 ((f2cl-lib:int-add i
                                                                    3))
                                                 ((1 *)) dx-%offset%)
                                  (* da
                                     (f2cl-lib:fref dx-%data%
                                                    ((f2cl-lib:int-add i
                                                                       3))
                                                    ((1 *))
                                                    dx-%offset%)))
                            (setf (f2cl-lib:fref dx-%data%
                                                 ((f2cl-lib:int-add i
                                                                    4))
                                                 ((1 *)) dx-%offset%)
                                  (* da
                                     (f2cl-lib:fref dx-%data%
                                                    ((f2cl-lib:int-add i
                                                                       4))
                                                    ((1 *))
                                                    dx-%offset%)))
                          label50))
          (go end_label)
     end_label (return (values nil nil nil nil)))))

(in-package #-gcl #:cl-user #+gcl "CL-USER")
#+#.(cl:if (cl:find-package '#:f2cl) '(and) '(or))
(eval-when (:load-toplevel :compile-toplevel :execute)
  (setf (gethash 'fortran-to-lisp::dscal
                 fortran-to-lisp::*f2cl-function-info*)
        (fortran-to-lisp::make-f2cl-finfo :arg-types '((fortran-to-lisp::integer4)
                                                       (double-float)
                                                       (array
                                                        double-float
                                                        (*))
                                                       (fortran-to-lisp::integer4))
          :return-values '(nil nil nil nil)
          :calls 'nil)))

