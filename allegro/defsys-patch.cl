;;;
(in-package "DEFSYS")

(defmethod compile-module ((module lisp-module) &rest keys)
  (let* ((p (get-package module))
         (package (or (and p
                           (if (packagep p)
                               p
                             (find-package p)))
                      *package*))
         (*package* package)
         ;;(product-pathname (product-pathname module :new t))
         (product-pathname (product-pathname module))
         (source-pathname (source-pathname module)))
    (unless (or .interpreted-mode. (interpreted module))
      (progv *recurse-bind-vars* *recurse-bind-vals*
        #+sbcl (apply #'compile-file source-pathname keys) ; sbcl bug
        #-sbcl (apply #'compile-file source-pathname :output-file product-pathname keys))
      (if (compile-satisfies-load module)
          (make-module-up-to-date module)))
    t))