;; -*- mode: common-lisp; package: defsys -*-
;;
;;
;; copyright (c) 1985, 1986 Franz Inc, Alameda, Ca.
;; copyright (c) 1986-2005 Franz Inc, Berkeley, CA  - All rights reserved.
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
;; $Id: defsys.cl,v 2.49 2007/04/17 21:27:36 layer Exp $

#+lispworks
(eval-when (:compile-toplevel :load-toplevel :execute)
  (progn
    (setf (symbol-function 'clos::load-defmethod)
      #'clos::load-defmethod-m)
    (setf (symbol-value 'system::*fasl-file-type*)
      system::*binary-file-type*)
    (setf (symbol-function 'clos::intern-eql-specializer)
      #'common-lisp::identity)))

#+sbcl
(defpackage "SB-MOP"
  (:nicknames "CLOS"))

(defpackage "DEFSYS"
  (:use "COMMON-LISP")
  (:import-from #+sbcl "SB-PCL" #-sbcl "CLOS" "LOAD-DEFMETHOD")
  (:import-from "CLOS" "INTERN-EQL-SPECIALIZER")
  (:import-from #+sbcl "SB-INT"
                #+lispworks "SYSTEM"
                "LOGICAL-PATHNAME-P" "*FASL-FILE-TYPE*")
  (:export "DEFSYSTEM" "FIND-SYSTEM" "LOAD-SYSTEM"
           "DEFSYSTEM-1" "UNDEFSYSTEM" "COMPILE-SYSTEM" "MAP-SYSTEM"
           "SHOW-SYSTEM" #-lispworks "CONCATENATE-SYSTEM"
           "TOUCH-SYSTEM" "CLEAN-SYSTEM"))

(in-package "DEFSYS")

(eval-when (eval load)
  (provide :defsys)
  (provide :defsystem))

#-allegro
(defvar *source-file-types* '("cl" "lsp" "lisp" nil))

#-allegro
(defmacro named-function (name function)
  (declare (ignore name))
  `(function,function))

#+sbcl
(defun shell (command)
  (sb-ext:run-program "/bin/sh" (list "-c" command) :input t :output t :wait t :pty nil))

#-allegro
(defun pathname-relative-p (pathname)
  (let ((dc (pathname-directory pathname)))
    (or (null dc)
        (eq :relative (car dc)))))

#-allegro
(defun copy-file (from to
                  &key overwrite force remove-destination verbose
                  &allow-other-keys
                  &aux from-filename to-filename if-exists from-is-stream
                  to-is-stream close-from close-to)
  (when (not (setq from-is-stream (streamp from)))
    (setq from (pathname from))
    (setq from-filename (namestring from)))
  (when (not (setq to-is-stream (streamp to)))
    (setq to (pathname to))
    (setq to-filename (namestring to)))
  (if (or overwrite force)
      (setq if-exists :supersede)
    (setq if-exists :error))
  (when (and (not (or overwrite force remove-destination))
             (not to-is-stream)
             (probe-file to))
    (error 'file-error :pathname to
           :format-control "Destination file ~a exists."
           :format-arguments `(,to)))
  (when (and (not to-is-stream)
             remove-destination
             (probe-file to))
    (delete-file to-filename))
  (labels ((do-copy (&aux (error t) from-stream to-stream)
             (declare (optimize (speed 3)))
             (when verbose
               (format t "~&;; copying file ~a to ~a~%"
                       (if from-is-stream :stream from)
                       (if to-is-stream :stream to)))
             (unwind-protect
                 (let ((buf
                        ;; 4k buffers are fastest on linux
                        (make-array #.(* 4 1024)
                                    :element-type '(unsigned-byte 8))))
                   (declare (dynamic-extent buf))
                   (setq from-stream (if from-is-stream
                                         from
                                       (progn
                                         (setq close-from t)
                                         (open from-filename
                                               #-allegro :element-type #-allegro '(unsigned-byte 8)))))
                   (setq to-stream
                     (if to-is-stream
                         to
                       (progn
                         (setq close-to t)
                         (handler-case
                             (open to-filename
                                   :direction :output
                                   :if-exists if-exists
                                   :if-does-not-exist :create
                                   #-allegro :element-type #-allegro '(unsigned-byte 8))
                           (error (c)
                             (if force
                                 (progn
                                   (ignore-errors (delete-file to-filename))
                                   (open to-filename
                                         :direction :output
                                         :if-exists if-exists
                                         :if-does-not-exist :create
                                         #-allegro :element-type #-allegro '(unsigned-byte 8)))
                               (error c)))))))
                   (loop as x = (read-sequence buf from-stream)
                       until (= x 0)
                       do (write-sequence buf to-stream :end x))
                   (setq error nil))
               ;; Cleanup forms
               (when (and from-stream close-from) (close from-stream))
               (when (and to-stream close-to) (close to-stream)))
         
             #+ignore
             (when (and (null error)
                        (not from-is-stream)
                        (not to-is-stream))
               (when preserve-time
                 (excl::filesys-set-time-from-file from-filename to-filename))
               (excl::filesys-chmod to-filename
                                    (excl::filesys-permission from-filename)))))
    (do-copy)))

;; [rfe6329]
#+process-autoloads
(excl::autoload-from "code/defsys-s.cl"
                     defsystem defsystem-1 undefsystem find-system
                     load-system compile-system map-system
                     show-system concatenate-system
                     touch-system clean-system)

;; association list of system objects and names
;; for bootstrapping reasons, this is in the excl package.
#+allegro
(without-package-locks
 (defvar *systems* nil))
#-allegro
(defvar *systems* nil)

;; class that will be used for making system instances
(defvar *default-system-class* 'defsys::default-system)

(defvar *default-module-class* 'defsys::lisp-module)

(defvar *default-module-group-class* 'defsys::default-module-group)

(defvar *default-file-type* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; WARNING: you must add any state global variables to
;;;;; *recurse-bind-vars* and *recurse-bind-vals* below, so that recursive
;;;;; defsys operation is preserved.
(defvar *recurse-bind-vars*
    '(.silent-mode. .include-components. .interpreted-mode.
      .simulate-mode. .recompile-mode. .reload-mode.
      .compile-during-load-mode. .system-operation-start-time.
      .toplevel-system-operation-in-progress. .toplevel-system-operation-id.))
(defvar *recurse-bind-vals*
    (list
     nil ;; .silent-mode.
     t ;; .include-components.
     nil ;; .interpreted-mode.
     nil ;; .simulate-mode.
     nil ;; .recompile-mode.
     nil ;; .reload-mode.
     nil ;; .compile-during-load-mode.
     (encode-universal-time 59 59 11 31 12 2999);;.system-operation-start-time.
     nil ;; .toplevel-system-operation-in-progress.
     0 ;; .toplevel-system-operation-id.
     ))
(defvar .silent-mode. nil)
(defvar .include-components. t)
(defvar .interpreted-mode. nil)
(defvar .simulate-mode. nil)
(defvar .recompile-mode. nil)
(defvar .reload-mode. nil)
(defvar .compile-during-load-mode. nil)
(defvar .system-operation-start-time.)
(setf .system-operation-start-time.
  (encode-universal-time 59 59 11 31 12 2999))
(defvar .toplevel-system-operation-in-progress. nil)
(defvar .toplevel-system-operation-id. 0)

(defvar .force-dependent-recompile.) ;; give this NO VALUE!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; States are used to cache information about objects while a system
;; operation is going on.  We throw out the state information at the
;; beginning of each top-level system operation since the user may have
;; done things outside of defsystem (editing,compiling,etc) to change the
;; states of modules.  So we can't trust the information except within one
;; operation.
;;
;; Valid states of a module are:
;;   :up-to-date
;;   :image-out-of-date  (i.e. loaded version (if any) is older than
;;                        product file)
;;   :product-out-of-date (source is newer than product)
;;
;; module-groups and systems cannot have :product-out-of-date
;; since there is more than one product file per module-group/system

;; assoc list of objects and states used while a system operation is in
;; progress to cache state information
(defvar .object-states. nil)
(defvar .simulation-object-states. nil)

;; functions for dealing with states:

(defun get-object-state (object)
  (if .simulate-mode.
      (cdr (assoc object .simulation-object-states.))
    (cdr (assoc object .object-states.))))

(defun set-object-state (object new-state)
  (unless .simulate-mode.
    (push (cons object new-state) .object-states.))
  (push (cons object new-state) .simulation-object-states.))

(defun set-real-object-state (object new-state)
  (push (cons object new-state) .object-states.))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; macro needed to deal with things when we aren't sure if the thing is a
;; list or atom
;; (redefined as a function in excl package)
#+ignore
(defmacro eq-or-memq (obj1 obj2)
  `(if (consp ,obj2)
      (franz::memq ,obj1 ,obj2)
    (eq ,obj1 ,obj2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; error reporting macros:

(defun system-error (non-system)
  (error "expected object of class system, but got: ~s" non-system))

(defun module-error (non-module)
  (error "expected object of class module, but got: ~s" non-module))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; printing functions/macros (indentation scheme stolen from trace.cl)
;;

;; maximun number of spaces to indent
(defvar .max-defsys-indentation. 40)
(defvar .indent-level. 0)

(defun defsys-p&i ()
  (min (1+ (* .indent-level. 2)) .max-defsys-indentation.))

(eval-when (compile load eval)
(defmacro defsys-explain (control-string &rest args)
  (declare (dynamic-extent args))
  `(unless .silent-mode.
     (format t
             ,(format nil "~~&~~@<;~~@;~~V:T~~:I~a~~:@>~~%" control-string)
             (defsys-p&i)
             ,@args)))
)                                       ; eval-when

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; system, module-group, and module base classes

(defclass defsystem-base-class ()
          ())

(defclass system (defsystem-base-class
                  dependency-graph)
          ()
  )

(defclass module-group (defsystem-base-class
                        dependency-graph)
          ()
  )

(defclass module (defsystem-base-class
                  dependency-graph)
          ()
  )

(defgeneric defsys-object-p (object)
  )

(defmethod defsys-object-p ((object defsystem-base-class))
  t)

(defmethod defsys-object-p (non-defsystem-object)
  (declare (ignore non-defsystem-object))
  nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; module-container is an object that contains modules.
;; It is a superclass of both default-system and default-module-group
(defclass module-container (defsystem-base-class)
          ((modules :accessor modules :initarg :modules :initform nil)
           (default-module-class :accessor default-module-class
                                 :initarg :default-module-class
                                 :initform *default-module-class*)))

;; default-classes for system, module and file
(defclass default-system (system module-container)
          ((pretty-name :accessor pretty-name :initarg :pretty-name
                        :initform nil :type string)
           (name :accessor system-name :initarg :name :initform nil :type string)
           (default-package :accessor default-package :initarg :default-package
                            :initform *package*)
           (default-pathname :accessor default-pathname
                             :initarg :default-pathname :initform #p"./")
           (default-file-type :accessor default-file-type
                              :initarg :default-file-type
                              :initform nil)
           (property-list :accessor property-list :initarg :property-list
                          :initform nil)
           (parent-object :accessor parent-object
                          :initarg :parent-object
                          :initform nil)
           (named-module-groups :accessor named-module-groups
                                :initarg :named-module-groups
                                :initform nil)

           (load-date :accessor load-date :initarg :load-date
                      :initform 0)
           ;; this gets initialized in the shared-initialize after method
           (module-table :accessor module-table)))

(defmethod print-object ((system default-system) stream)
  (print-unreadable-object (system stream :type t :identity t)
    (format stream "~s" (pretty-name system))))

;; reader methods for properties of default-system
(defmethod serial-p ((system default-system))
  (getf (property-list system) :serial-p))

(defclass default-module-group (module-group module-container)
          ((default-package :accessor default-package
                            :initarg :default-package :initform nil)
           (default-pathname :accessor default-pathname
                             :initarg :default-pathname :initform nil)
           (named-module-groups :accessor named-module-groups
                                :initarg :named-module-groups  :initform nil)
           (pretty-name :accessor pretty-name :initarg :name
                        :initform "<unnamed>"
                        :type string)
           (interpreted :accessor interpreted
                        :initarg :interpreted :initform nil)
           (load-date :accessor load-date :initarg :load-date
                      :initform 0)
           (property-list :accessor property-list
                          :initarg :property-list :initform nil)
           (parent-object :accessor parent-object
                          :initarg :parent-object :initform nil)))

(defmethod print-object ((module-group default-module-group) stream)
  (print-unreadable-object (module-group stream :type t :identity t)
    (format stream "~s" (pretty-name module-group))))

;;; reader methods for properties of default-module-group
(defmethod compile-satisfies-load ((module-group default-module-group))
  (getf (property-list module-group) :compile-satisfies-load))

(defmethod serial-p ((module-group default-module-group))
  (getf (property-list module-group) :serial-p))

(defclass default-module (module)
          ;; can optimize these out to be just property-list in the modules
          ;; that have them defined, and nothing in other modules--to save
          ;; a lot of space--or can make subclasses that have the
          ;; additional slots.
          ((default-package :accessor default-package
                            :initarg :default-package :initform nil)
           (default-pathname :accessor default-pathname
                             :initarg :default-pathname
                             :initform nil)
           (pretty-name :accessor pretty-name :initarg :name
                        :initform "<unnamed>"
                        :type string)
           (file :accessor module-file :initarg :file :initform nil
                 :type string)
           (property-list :accessor property-list
                          :initarg :property-list :initform nil)
           (interpreted :accessor interpreted
                        :initarg :interpreted :initform nil)
           ;; this id is checked against .toplevel-system-operation-id. to
           ;; see if the cache is valid for the current operation
           (product-date-cache-id :accessor product-date-cache-id
                                :initform nil)
           (source-date-cache-id :accessor source-date-cache-id
                                :initform nil)
           (cached-product-write-date :accessor cached-product-write-date
                                      :initform 0)
           (cached-source-write-date :accessor cached-source-write-date
                                      :initform 0)
           (cached-source-pathname :accessor cached-source-pathname
                                   :initform nil)
           (parent-object :accessor parent-object
                              :initarg :parent-object
                              :initform nil)
           ;; these slots get initialized in the shared-initialize after method
           (load-date :accessor load-date :initarg :load-date)
           ))

(defmethod print-object ((module default-module) stream)
  (print-unreadable-object (module stream :type t :identity t)
    (format stream "~s" (pretty-name module))))

;;; reader method for properties of default-module

(defmethod compile-satisfies-load ((module default-module))
  (getf (property-list module) :compile-satisfies-load))

(defmethod force-dependent-recompile ((module default-module))
  (getf (property-list module) :force-dependent-recompile))

(defmethod concatenate-system-ignore ((module default-module))
  (getf (property-list module) :concatenate-system-ignore))

(defmethod force-load ((module default-module))
  (getf (property-list module) :force-load))

(defmethod force-load ((module t)) nil)

(defmethod force-compile ((module default-module))
  (getf (property-list module) :force-compile))

(defmethod force-compile ((module t)) nil)



;;;;;;;;;;;;;;;

;; Define the standard set of module types

(defclass lisp-module (default-module)
          ())

(defclass text-module (default-module)
          ())

(defclass foreign-module (default-module)
          ())

(defclass c-module (foreign-module)
          ())

(defclass fortran-module (foreign-module)
          ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Dependency handling
;;
;; Dependency lists are alists of keyword/list pairs
;; like the following:
;; ((:compile (:compile module-a) (:compile module-b)
;;            (:load module-a))
;;  (:load (:load module-group-foo)
;;         (#'my-dependency-handler-function module-blah)))
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; dependency graph mixin
(defclass dependency-graph ()
          ((dependencies :accessor dependencies
                         :initarg :dependencies
                         :initform nil)
           (compile-dependencies :accessor compile-dependencies
                                 :initarg :compile-dependencies
                                 :initform nil)))

(defmethod dependencies ((obj symbol))
  (when obj
    (let ((system (find-system obj)))
      (if system
          (dependencies system)
        nil))))

(defmethod compile-dependencies ((obj symbol))
  (when obj
    (compile-dependencies (find-system obj t))))


(defgeneric add-dependency (depending dependency-keyword dependency-info)
  )

(defmethod add-dependency ((depending dependency-graph)
                           dependency-keyword dependency-info)
  ;; if there is already a dependency of this type then just add to the
  ;; list otherwise add a new entry for this type of dependency.
  (let ((existing-dependency-list (assoc dependency-keyword
                                         (dependencies depending))))
    (if existing-dependency-list
        (nconc (cdr existing-dependency-list) (list dependency-info))
      (push `(,dependency-keyword ,dependency-info)
            (dependencies depending)))))

(defgeneric add-compile-dependency (depending depended-on)
  )

(defmethod add-compile-dependency ((depending dependency-graph)
                           depended-on)
  (push depended-on (compile-dependencies depending)))

(eval-when (compile eval)
(defmacro get-dependencies-by-operation (dependency-info)
  ;; dependency-info is a operation/module pair
  `(rest (assoc (first ,dependency-info)
                (dependencies (second ,dependency-info)))))
)                                       ; eval-when

(defun check-circularity (depending-node dependency-info dependency-keyword)
  (let ((thing-to-match `(,dependency-keyword ,depending-node)))
    (if (circularity-p thing-to-match
                       (get-dependencies-by-operation dependency-info))
      ;; maybe should signal this error at a higher level so it can be of use
      ;; to the user??
      (error
       "Circular dependency found when adding ~s dependency to ~s."
       dependency-keyword depending-node))))

(defun circularity-p (thing-to-match list-to-search)
  (cond ((null list-to-search)
         nil)
        (t
         (let ((found-match nil))
           (do ((item (first list-to-search) (first list-to-search)))
               ((or (null list-to-search)
                    found-match) found-match)
             (if (equal thing-to-match item)
                 (return t))
             (setf list-to-search (rest list-to-search))
             (if (symbolp (first item))
                 (setf found-match (circularity-p thing-to-match
                                                  (get-dependencies-by-operation
                                                   item)))))))))




;; assoc list of dependency-keyword/dependency-handler pairs
(defvar .dependency-handlers. nil)

(eval-when (compile load eval)
(defmacro get-dependency-handler (dependency)
  `(cdr (assoc ,dependency .dependency-handlers.)))

(defmacro define-dependency-handler (dependency-name handler-function)
  `(push (cons ,dependency-name ,handler-function)
         .dependency-handlers.))
)                                       ; eval-when

(define-dependency-handler :load
                           #'(lambda (module keys)
                               (apply #'load-module-action module
                                      :allow-other-keys t keys)))

(define-dependency-handler :compile
                           #'(lambda (module keys)
                               (apply #'compile-module-action module
                                      :allow-other-keys t keys)))

(defmethod handle-dependencies ((obj dependency-graph) dependency-keyword keys)
  (let ((dependencies (cdr (assoc dependency-keyword (dependencies obj))))
        ;; bug2353, we have to temporarily flush the simulation cache when
        ;; not already in simulation mode, so that actions resulting from
        ;; this call will actually take place and won't be fooled by the cache.
        (.simulation-object-states. (if .simulate-mode.
                                        .simulation-object-states.
                                      nil)))
    (when dependencies
      (dolist (dependency-pair dependencies)
        ;;; dependency-pair is (:<operation> module-name) as described above
        (let ((dependency (first dependency-pair))
              (value (second dependency-pair)))
          (cond ((symbolp dependency)
                 (funcall (get-dependency-handler dependency)
                          (lookup-module obj value t) keys))
                ((functionp dependency)
                 (funcall dependency value))
                (t (error "~a is an invalid dependency" dependency))))))))

(defmethod check-compile-dependencies ((obj dependency-graph) keys)
  ;; try to compile each of the compile dependencies and record which
  ;; ones needed to be compiled.
  ;; also check the product-write-dates to see if some files in the
  ;; depended-system were compiled (either by hand or during a previous
  ;; compile-system operation) and thus this system is now out
  ;; of date with respect to the depended one.
  (let ((compile-dependencies (compile-dependencies obj)))
    (when compile-dependencies
      (let ((out-of-date-modules nil)
            (oldest-module-date (oldest-module-date obj)))
        (dolist (dependency (compile-dependencies obj))
          (let ((system-or-module (lookup-module obj dependency)))
            (if (or (apply #'compile-module-action system-or-module
                           :allow-other-keys t keys)
                    (> (newest-module-date system-or-module)
                       oldest-module-date))
                (push (pretty-name system-or-module) out-of-date-modules))))
        out-of-date-modules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun add-to-module-list (system-or-mg new-module)
  ;; add to end of list to keep original order
  (setf (modules system-or-mg)
    (cond ((null (modules system-or-mg))
           (list new-module))
          (t (append (modules system-or-mg) (list new-module))))))

(defun add-to-named-module-groups (system-or-mg new-module-group)
  (push new-module-group (named-module-groups system-or-mg)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; predicates for default defsys classes
(defgeneric system-p (system)
  )

(defmethod system-p (non-system)
  (declare (ignore non-system))
  nil)

(defmethod system-p ((system default-system))
  t)

(defgeneric module-group-p (module-group)
  )

(defmethod module-group-p ((module-group module-group))
  t)

(defmethod module-group-p (non-module-group)
  (declare (ignore non-module-group))
  nil)

(defgeneric module-p (module)
  )

(defmethod module-p ((module module))
  t)

(defmethod module-p (non-module)
  (declare (ignore non-module))
  nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Module methods for default classes
;;;
;;; These are the methods that perform the real work, when an action
;;; actually needs to be performed.  They are called from the
;;; *-module-action methods. They are not called when .simulate-mode. is
;;; non-nil.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; load-module methods
;;

(defgeneric load-module (module &key)
  )

(defmethod load-module (non-module &key)
  (module-error non-module))

(defmethod load-module ((module default-module) &key)
  ;; perform the load of the product file
  ;; this method should handle all non-lisp modules where it is an error to
  ;; load source.
  (let ((pathname (product-pathname module)))
    (progv *recurse-bind-vars* *recurse-bind-vals*
      (load pathname))
    (setf (load-date module) (get-universal-time))
    t))

(defmethod load-module ((module lisp-module) &key)
  ;; perform the load of the product file
  (let* ((p (get-package module))
         (package (or (and p
                           (if (packagep p)
                               p
                             (find-package p)))
                      *package*))
         (*package* package)
         (pathname (if (or .interpreted-mode. (interpreted module))
                       (source-pathname module)
                     (product-pathname module))))
    (progv *recurse-bind-vars* *recurse-bind-vals*
      (load pathname))
    (setf (load-date module) (get-universal-time))
    t))

(defmethod load-module ((module foreign-module) &key)
  ;; perform the load of the foriegn object file
  (let ((pathname (product-pathname module)))
    (progv *recurse-bind-vars* *recurse-bind-vals*
      (load pathname))
    (setf (load-date module) (get-universal-time))
    t))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compile-module methods
;;

(defgeneric compile-module (module &key)
  )

(defmethod compile-module (non-module &key)
  (module-error non-module))

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

(defmethod compile-module ((module c-module) &key)
  ;; do something like: "cc -c -o foo.o foo.c"
  (shell
   #+(and dynload (not sunos4))
   (concatenate 'string
     ;; Generate CC command line. Might possibly want to use aCC on hpux11.64
     #+linux "gcc" #-linux "cc"
     #+hpux " +z -Ae" #+(and hpux (not 64bit)) " +DA1.1" 
                      #+(and hpux 64bit) " +DA2.0W"
     #+(or macosx macosx64) " -dynamic"
     " -c "
     #+tru64 "-G 0 " #+(and tru64 (not 64bit)) "-taso -xtaso -xtaso_short "
     #+linux "-fPIC " #+freebsd "-fPIC -DPIC " #+sparc "-K pic "
     #+sgi "-KPIC " #+rs6000 "-D_BSD -D_NO_PROTO -D_NONSTD_TYPES -D_MBI=void "
     (namestring (source-pathname module))
     " -o " (namestring (intermediate-pathname module))
     ";"
     ;; Generate ld (or bin/make_shared) command line.
     #-(or tru64 rs6000) "ld"
     #+(or tru64 rs6000) (namestring (merge-pathnames "bin/make_shared"
                                (translate-logical-pathname "sys:")))
     #+linux " --shared" #+sparc " -G" #+sgi " -shared -all"
     #+hpux " -b" #+(and hpux 64bit) " +s"
     #+freebsd " -Bshareable -Bdynamic"
     #+macosx " -bundle /usr/lib/bundle1.o -undefined suppress"
     #+macosx64 " -arch ppc64 -bundle -flat_namespace"
     " -o " (namestring (product-pathname module))
     " "
     (namestring (intermediate-pathname module)))
   #-(and dynload (not sunos4))
   (concatenate 'string
     "cc -c -o "
     (namestring (product-pathname module))
     " "
     (namestring (source-pathname module)))))


(defmethod compile-module ((module fortran-module) &key)
  ;; do something like: "f77 -c -o foo.o foo.f"
  (shell (concatenate 'string
                           "f77 -c -o "
                           (namestring (product-pathname module))
                           " "
                           (namestring (source-pathname module)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; map-module method
;;

(defmethod map-module ((module default-module) fun &key)
  (funcall fun module))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; simulate-action and execute action are called from the *-module-action
;; methods to either simulate or perform an action on a module-container
;; respectively. Which one gets called depends upon the value of
;; .simulate-mode.
;; The method is recursively invoked on each of the modules in the
;; container object.
;;
(defmethod simulate-action ((obj module-container) method keys)
  (let ((.simulate-mode. t)
        (.silent-mode. t))
    (dolist (module (modules obj))
      ;; this is a simulation, so we can stop at the first one that returns
      ;; t (i.e the first one that needed to be loaded or compiled)
      (when (apply method module :allow-other-keys t keys)
        (return-from simulate-action t)))
    ;; if we get here, then they all returned nil
    nil))

(defmethod execute-action ((obj module-container) method keys)
  (let ((result nil))
    (dolist (module (modules obj))
      (setf result
        (or (apply method module :allow-other-keys t keys)
            result)))
    result))

(defmethod execute-serial-compile-action ((obj module-container) keys)
  ;; return two values, first is whether any were compiled, second is if
  ;; all were compiled.
  (let ((all-compiled nil) (one-compiled nil))
    (dolist (module (modules obj))
      (let ((compiled (apply #'compile-module-action
                             module :allow-other-keys t keys)))
        (if compiled
            (progn
              (setf all-compiled (and all-compiled t))
              (setf one-compiled t)
              (apply #'load-module-action module :allow-other-keys t keys))
          (if (force-load module)
              (apply #'load-module-action module :allow-other-keys t keys)))))
    (values all-compiled one-compiled)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Module action methods for default classes
;;;
;;; These methods determine if an action should actually be done and then
;;; either do it or simulate it.
;;; Dependencies and are checked in these methods.
;;; They are called from the system operation methods.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; load-module-action methods

(defgeneric load-module-action (module &rest keys &key &allow-other-keys)
  )

(defmethod load-module-action (non-module &rest keys &key &allow-other-keys)
  (declare (ignore keys))
  (module-error non-module))

;;;; there is a major problem with the following function: it doesn't check
;;;; dependecies when :compile t is given and modules on which the current
;;;; module depends were recompiled.

(defmethod load-module-action ((module default-module) &rest keys
                               &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (let ((load-date (load-date module))
        (state (get-object-state module))
        temp
        (retval nil))

    ;; first eliminate cases where module doesn't need to be loaded:
    (when (and state (eq state :up-to-date))
      (return-from load-module-action nil))

    (when (and (product-newer-than-source module) ; added by dkl 2/17/93
               (/= 0 (setq temp (product-write-date module)))
               (>= load-date
                   (if .interpreted-mode.
                       (source-write-date module)
                     temp)))
      (make-module-up-to-date module)
      ;; return nil since it has already been loaded
      (return-from load-module-action nil))

    (when (and (not .interpreted-mode.)
               (not (product-newer-than-source module)))
      ;; if we get here, we know that the product is out of date, so either
      ;; compile it, or print a warning.
      (if .compile-during-load-mode.
          (apply #'compile-module-action module :allow-other-keys t keys)
        ;; print a warning if source is newer
        (if (probe-file (product-pathname module))
            (defsys-explain
                "Source is newer than product for module: ~s."
                (pretty-name module)))))

    ;; now do the actual load:
    (let ((.indent-level. (+ 1 .indent-level.)))
      (handle-dependencies module :load keys)
      (if .interpreted-mode.
          (defsys-explain "Loading source for module: ~s."
              (pretty-name module))
        (defsys-explain "Loading product for module: ~s."
            (pretty-name module)))
      (if .simulate-mode.
          (setq retval t)
        (progn
          (setq retval
            (apply #'load-module module :allow-other-keys t keys))
          (make-module-up-to-date module)))
      retval)))


(defmethod load-module-action ((obj module-container) &rest keys
                               &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (let ((state (get-object-state obj))
        (result nil))

    (when (eq state :up-to-date)
      (return-from load-module-action nil))

    #+ignore
    (format t "m-c: dep ~s~%" (dependencies obj))
    (when (dependencies obj)
      ;; Now we need to figure out if the object is out of date.
      ;; We don't want to handle dependencies unless we know that the object
      ;; is out of date, but we don't know this unless we actually try to
      ;; load it (because of the recursive structure of the objects).
      ;; So first we simulate loading it, which will determine if it really
      ;; needs to be loaded, then we can handle the dependencies and really
      ;; load it. Note that file write dates and module states get cached
      ;; during the simulation, so this isn't as inefficient as it seems.

      #+ignore
      (format t "  simulate-action for compile: ~s~%"
              (simulate-action obj #'compile-module-action keys))

;;;;(break "foo")

      (when .compile-during-load-mode.
        (when (simulate-action obj #'compile-module-action keys)
          (handle-dependencies obj :compile keys)))

      (when (simulate-action obj #'load-module-action keys)
        (handle-dependencies obj :load keys)))

    ;; now do the actual load:
    (setq result (execute-action obj #'load-module-action keys))
    (set-object-state obj :up-to-date)
    result))


(defmethod load-module-action ((system-name symbol) &rest keys
                               &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (when .include-components.
    (let ((system (find-system system-name)))
      (if system (apply #'load-module-action system :allow-other-keys t keys)
        (error "There is no such system defined: ~s" system-name)))))


(defmethod load-module-action ((system system)
                                  &rest keys
                                  &key &allow-other-keys)
  (declare (ignore keys))
  (when .include-components.
    (call-next-method)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compile-module-action methods

(defgeneric compile-module-action (module &rest keys &key &allow-other-keys)
  )

(defmethod compile-module-action (non-module &rest keys &key &allow-other-keys)
  (declare (ignore keys))
  (module-error non-module))

(defmethod compile-module-action ((module default-module) &rest keys
                                  &key &allow-other-keys)
  (declare (dynamic-extent keys))

  (let ((state (if (or (force-compile module)
                       (and (boundp '.force-dependent-recompile.)
                            .force-dependent-recompile.))
                   :product-out-of-date
                 (get-object-state module))))

    #+ignore
    (format t "c-m-a: default-module: state is ~s (~s)~%" state module)

    ;; first eliminate cases where module doesn't need to be compiled:
    (when (and state
               (or (eq state :up-to-date)
                   (eq state :image-out-of-date)))
      (return-from compile-module-action nil))

    ;; this is used in simulation mode to avoid recomputing lots of stuff:
    (when (and state
               (eq state :needs-compilation))
      (return-from compile-module-action t))

    (let (
          ;; Compile the compile-dependencies if they need it and get
          ;; the list of those who were recompiled.
          (causes (check-compile-dependencies module keys))
          (retval nil)
          (.indent-level. (+ 1 .indent-level.)))
      ;; if there were any compile dependencies that needed to be
      ;; recompiled, then this module must be recompiled.
      (cond (causes
             (defsys-explain
                 "~
Compiling module ~s because it is out of date with respect to:~{ ~S~}."
              (pretty-name module) causes))
            ((or .interpreted-mode. (interpreted module))
             (return-from compile-module-action nil))
            ((or (eq state :product-out-of-date)
                 (not (product-newer-than-source module)))
             (when (force-dependent-recompile module)
               (setq .force-dependent-recompile. t))
             (if (probe-file (product-pathname module))
                 (defsys-explain "~
Compiling module ~s because the product file is out of date."
                     (pretty-name module))
               (defsys-explain "~
Compiling module ~s because the product file does not exist."
                   (pretty-name module))))
            ;; if we get here, then the module doesn't need to be compiled
            (t
             (set-object-state module :image-out-of-date)
             (return-from compile-module-action nil)))

      ;; now do the actual compile:
      (handle-dependencies module :compile keys)
      (cond  (.simulate-mode.
              (set-real-object-state module :product-out-of-date)
              ;;(set-object-state module :image-out-of-date)
              (set-object-state module :needs-compilation)
              (setf retval t))
             (t
              (setf retval
                (apply #'compile-module module :allow-other-keys t keys))
              (invalidate-product-date-cache module)
              (set-object-state module :image-out-of-date)))
      retval)))

(defmethod compile-module-action ((obj module-container) &rest keys
                                  &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (let ((state (get-object-state obj)))
    ;; if obj has already been compiled and we know it then return nil
    (when (and state
               (or (eq state :up-to-date)
                   (eq state :image-out-of-date)))
      (return-from compile-module-action nil))

    ;; otherwise determine if it needs to be compiled
    (let ((causes (check-compile-dependencies obj keys))
          (.indent-level. (if (system-p obj) (+ 1 .indent-level.)
                            .indent-level.))
          (result nil))
      (when causes
        (defsys-explain
         "Compiling ~s because dependents are out of date: ~{ ~S~}."
         (pretty-name obj) causes)
        ;; make the modules contained in this object out of date so
        ;; they will get recompiled
        (make-module-product-out-of-date obj)
        (setf state :product-out-of-date))

      (when (dependencies obj)
        ;; Now we need to figure out if the object is out of date.
        ;; We don't want to handle dependencies unless we know that the
        ;; object is out of date, but we don't know this unless we
        ;; actually try to compile it (because of the recursive structure
        ;; of the objects). So first we simulate compiling it, which will
        ;; determine if it really needs to be compiled, then we can handle
        ;; the dependencies and really compile it.
        ;; Note that file write dates and module states get cached
        ;; during the simulation, so this isn't as inefficient as it seems.

        (if (or (eq state :product-out-of-date)
                (simulate-action obj #'compile-module-action keys))
            (handle-dependencies obj :compile keys)))

      (print-compiling-message obj)

      ;; if this is a serial module-group then have to load each module
      ;; right after compilation.
      (cond ((serial-p obj)
             (multiple-value-bind (all-compiled one-compiled)
                 (execute-serial-compile-action obj keys)
               ;; up-to-date because all the modules get loaded
               (set-object-state obj (if all-compiled
                                         :up-to-date
                                       :image-out-of-date))
               (setf result one-compiled)))
            (t
             (setf result (execute-action obj #'compile-module-action keys))
             (set-object-state obj :image-out-of-date)))
      result)))

(defmethod compile-module-action ((system-name symbol) &rest keys
                                  &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (when .include-components.
    (let ((system (find-system system-name)))
      (if system
          (apply #'compile-module-action system :allow-other-keys t keys)
        (error "There is no such system defined: ~s" system-name)))))

(defmethod compile-module-action ((system system)
                                  &rest keys
                                  &key &allow-other-keys)
  (declare (ignore keys))
  (when .include-components.
    (call-next-method)))

(defmethod print-compiling-message ((system default-system))
  (defsys-explain "Compiling system: ~s." (pretty-name system)))

(defmethod print-compiling-message ((module-group default-module-group))
  )

(defmethod print-compiling-message ((module default-module))
  (defsys-explain "Compiling module: ~s." (pretty-name module)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; map-module-action methods

(defmethod map-module-action ((module default-module) fun
                              &rest keys &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (defsys-explain "Mapping function to module: ~s." (pretty-name module))
  (unless .simulate-mode.
    (apply #'map-module module fun :allow-other-keys t keys)))

(defmethod map-module-action ((obj module-container) fun
                              &rest keys &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (defsys-explain "Mapping function to: ~s." (pretty-name obj))
  (mapcar #'(lambda (module)
              (apply #'map-module-action module fun :allow-other-keys t keys))
          (components obj)))

(defmethod map-module-action ((system-name symbol) fun &rest keys
                               &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (let ((system (find-system system-name)))
    (cond (system
           (defsys-explain "Mapping function to: ~s." (pretty-name system))
           (apply #'map-module-action system fun :allow-other-keys t keys))
          (t
           (error "There is no such system defined: ~s" system-name)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;
;;; System operations
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compile-system methods

(defgeneric compile-system (system &key)
  )

(defmethod compile-system (non-system &key)
  (system-error non-system))

(defmethod compile-system ((system-name symbol)
                           &rest keys
                           &key ((:recompile .recompile-mode.)
                                 .recompile-mode.)
                                ((:silent .silent-mode.) .silent-mode.)
                                (no-warn nil)
                                ((:reload .reload-mode.) .reload-mode.)
                                ((:include-components .include-components.)
                                 .include-components.)
                                ((:simulate .simulate-mode.) .simulate-mode.)
                                (module-keys nil)
                           &allow-other-keys)
  (declare (dynamic-extent keys))
  (let ((system (find-system system-name))
        (result nil))
    (handler-bind ((warning #'(lambda (c)
                                (declare (ignore c))
                                (if no-warn (muffle-warning)))))
      (cond (system
             (cond (.toplevel-system-operation-in-progress.
                    (setf result
                      (apply #'compile-system system :module-keys module-keys
                             keys)))
                   (t
                    (let ((.toplevel-system-operation-in-progress. t)
                          (.object-states. nil)
                          (.simulation-object-states. nil))
                      (incf .toplevel-system-operation-id.)
                      (setf result
                        (apply #'compile-system system :module-keys module-keys
                               keys))))))
            (t
             (error "There is no such system defined: ~s" system-name)))
      result)))

(defmethod compile-system :around ((system default-system)
                                   &key &allow-other-keys)
  (loop
    (with-simple-restart
        (nil "retry the compile-system of ~a" system)
      (return-from compile-system
        (with-compilation-unit ()
          (cond (.toplevel-system-operation-in-progress.
                 (call-next-method))
                (t
                 (let ((.toplevel-system-operation-in-progress. t)
                       (.object-states. nil)
                       (.simulation-object-states. nil))
                   (incf .toplevel-system-operation-id.)
                   (call-next-method)))))))))

(defmethod compile-system ((system default-system)
                           &key ((:recompile .recompile-mode.)
                                 .recompile-mode.)
                                ((:silent .silent-mode.) .silent-mode.)
                                (no-warn nil)
                                ((:reload .reload-mode.) .reload-mode.)
                                ((:include-components .include-components.)
                                 .include-components.)
                                ((:simulate .simulate-mode.) .simulate-mode.)
                                (module-keys nil))
  (let ((.system-operation-start-time. (get-universal-time))
        (result nil)
        (vars (when (not (boundp '.force-dependent-recompile.))
                '(.force-dependent-recompile.)))
        (values (when (not (boundp '.force-dependent-recompile.))
                  '(nil))))
    ;; This bogosity is to insure that .force-dependent-recompile. is bound
    ;; only in the outer call to compile-system, because we want to
    ;; globally change the value in the middle of a recursive call to
    ;; compile-system and have it effect all remaining calls to
    ;; compile-system.
    (progv vars values
      (handler-bind ((warning #'(lambda (c)
                                  (declare (ignore c))
                                  (if no-warn (muffle-warning)))))
        (unless .silent-mode.
          (defsys-explain "Compiling system: ~s." (pretty-name system)))

        (when .recompile-mode.
          (make-module-product-out-of-date system))

        (dolist (module (modules system))
          (setf result
            (or (apply #'compile-module-action module
                       :allow-other-keys t module-keys)
                result)))
        result))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; load-system methods

(defgeneric load-system (system &key)
  )

(defmethod load-system ((system-name symbol)
                        &rest keys
                        &key ((:silent .silent-mode.) .silent-mode.)
                             (no-warn nil)
                             ((:reload .reload-mode.) .reload-mode.)
                             ((:include-components .include-components.)
                              .include-components.)
                             ((:simulate .simulate-mode.) .simulate-mode.)
                             ((:interpreted .interpreted-mode.)
                              .interpreted-mode.)
                             ((:compile .compile-during-load-mode.)
                              .compile-during-load-mode.)
                             (module-keys nil)
                             &allow-other-keys)
  (declare (dynamic-extent keys))
  (let ((system (find-system system-name)))
    (handler-bind ((warning #'(lambda (c)
                                (declare (ignore c))
                                (if no-warn (muffle-warning)))))
      (cond (system
             (cond (.toplevel-system-operation-in-progress.
                    (apply #'load-system system :module-keys module-keys
                           keys))
                   (t
                    (let ((.toplevel-system-operation-in-progress. t)
                          (.object-states. nil)
                          (.simulation-object-states. nil))
                      (incf .toplevel-system-operation-id.)
                      (apply #'load-system system :module-keys module-keys
                             keys)))))
            (t
             (error "There is no such system defined: ~s" system-name))))))

(defmethod load-system (non-system &key)
  (system-error non-system))

(defmethod load-system ((system default-system)
                        &key ((:silent .silent-mode.) .silent-mode.)
                             (no-warn nil)
                             ((:reload .reload-mode.) .reload-mode.)
                             ((:include-components .include-components.)
                              .include-components.)
                             ((:simulate .simulate-mode.) .simulate-mode.)
                             ((:interpreted .interpreted-mode.)
                              .interpreted-mode.)
                             ((:compile .compile-during-load-mode.)
                              .compile-during-load-mode.)
                             (module-keys nil))
  (handler-bind ((warning #'(lambda (c)
                              (declare (ignore c))
                              (if no-warn (muffle-warning)))))
    (let ((.system-operation-start-time. (get-universal-time)))
      (unless .silent-mode.
        (defsys-explain "Loading system: ~s." (pretty-name system)))

      (when .reload-mode.
        (dolist (module (modules system))
          (make-module-out-of-date module)))

      (apply #'load-module-action system :allow-other-keys t module-keys))))

(defmethod load-system :around ((system default-system)
                                &key compile &allow-other-keys)
  (if compile
      (with-compilation-unit () (call-next-method))
    (call-next-method)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; map-system methods

(defgeneric map-system (system fun &key)
  )

(defmethod map-system (non-system fun &key)
  (declare (ignore fun))
  (system-error non-system))

(defmethod map-system ((system-name symbol) fun
                       &rest keys
                       &key
                       ;; note this default, since this is usualy a
                       ;; batch-type operation...
                       ((:silent .silent-mode.) t)
                       ((:simulate .simulate-mode.) .simulate-mode.)
                       ((:include-components .include-components.)
                        .include-components.)
                       (module-keys nil)
                       &allow-other-keys)
  (declare (dynamic-extent keys))
  (let ((system (find-system system-name)))
    (if system (apply #'map-system system fun :module-keys module-keys
                      keys)
      (error "There is no such system defined: ~s" system-name))))

(defmethod map-system ((system default-system) fun
                       &key
                       ;; note this default, since this is usualy a
                       ;; batch-type operation...
                       ((:silent .silent-mode.) t)
                       ((:simulate .simulate-mode.) .simulate-mode.)
                       ((:include-components .include-components.)
                        .include-components.)
                       (module-keys nil))
  (dolist (module (components system))
    (apply #'map-module-action module fun :allow-other-keys t module-keys)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; concatenate-system methods

(defgeneric concatenate-system (system destination &key)
  )

(defmethod concatenate-system (non-system destination &key)
  (declare (ignore destination))
  (system-error non-system))

(defmethod concatenate-system ((system-name symbol) destination
                               &key
                               ((:include-components .include-components.)
                                 .include-components.)
                               ((:silent .silent-mode.) .silent-mode.)
                               ((:simulate .simulate-mode.) .simulate-mode.))
  (let ((system (find-system system-name)))
    (if system (concatenate-system system destination)
      (error "There is no such system defined: ~s" system-name))))

(defmethod concatenate-system ((system default-system)
                               destination
                               &key
                               ((:include-components .include-components.)
                                .include-components.)
                               ((:silent .silent-mode.) .silent-mode.)
                               ((:simulate .simulate-mode.)
                                .simulate-mode.))
  ;; This used to return nil when the destination could not be created, but
  ;; an error seems more reasonable.  The documentation is silent on the
  ;; return value issue.
  (flet ((append-files (input-files output-file)
           (with-open-file (s output-file
                            ;; Use simple-streams
                            #-allegro :element-type #-allegro '(unsigned-byte 8)
                            :direction :output :if-exists :supersede
                            :if-does-not-exist :create)
             (dolist (input-file input-files)
               (copy-file input-file s)))
           t))
    (let ((pathnames nil))
      (map-system system
                  #'(lambda (module)
                      (cond ((concatenate-system-ignore module))
                            (t (pushnew (namestring
                                         (translate-logical-pathname
                                          (product-pathname module)))
                                        pathnames
                                        :test #'string=))))
                  :include-components .include-components.)
      (setq pathnames (reverse pathnames))
      (defsys-explain "Concatenating system ~s with pathnames:~{ ~s~}."
          (pretty-name system) pathnames)
      (unless .simulate-mode.
        (append-files pathnames destination))
      pathnames)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; clean-system methods

(defmethod clean-system (non-system &key)
  (system-error non-system))

(defmethod clean-system ((system-name symbol)
                        &key
                        ((:silent .silent-mode.) .silent-mode.)
                        ((:simulate .simulate-mode.) .simulate-mode.))
  (let ((system (find-system system-name)))
    (if system (clean-system system)
      (error "There is no such system defined: ~s" system-name))))

(defmethod clean-system ((system default-system)
                        &key
                        ((:silent .silent-mode.) .silent-mode.)
                        ((:simulate .simulate-mode.) .simulate-mode.))
  (defsys-explain "Cleaning system: ~s." (pretty-name system))
  (map-system system #'(lambda (module)
                        (let ((path (product-pathname module)))
                          (when (probe-file path)
                            (defsys-explain "deleting file: ~s." path)
                            (unless .simulate-mode.
                              (delete-file path)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; touch-system methods

(defmethod touch-system (non-system &key)
  (system-error non-system))

(defmethod touch-system ((system-name symbol)
                         &key
                        ((:silent .silent-mode.) .silent-mode.)
                        ((:simulate .simulate-mode.) .simulate-mode.))
  (let ((system (find-system system-name)))
    (if system (touch-system system)
      (error "There is no such system defined: ~s" system-name))))

(defmethod touch-system ((system default-system)
                         &key
                        ((:silent .silent-mode.) .silent-mode.)
                        ((:simulate .simulate-mode.) .simulate-mode.))
  (let ((pathnames nil))
    (defsys-explain "Touching files of system: ~s." (pretty-name system))
    (map-system system #'(lambda (module)
                           (push (namestring (product-pathname module))
                                 pathnames)))
    (setf pathnames (reverse pathnames))
    ;; now format the list into a form that we can send to touch:
    (let* ((*print-circle* nil)
           (command (format nil "touch ~{~s ~}" pathnames)))
      (unless .simulate-mode. (shell command)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; show-system methods

(defgeneric show-system (system &key))

(defmethod show-system (non-system &key)
  (system-error non-system))

(defmethod show-system ((system-name symbol) &rest keys &key &allow-other-keys)
  (declare (dynamic-extent keys))
  (apply #'show-system (find-system system-name t) keys)
  (values))

(defmethod show-system ((system default-system) &rest keys
                        &key &allow-other-keys)
  (declare (ignorable keys))
  (let ((.indent-level. (+ 1 .indent-level.))
        (temp nil))
    (defsys-explain "System: ~s" (pretty-name system))
    (unless .toplevel-system-operation-in-progress.
      (let ((.toplevel-system-operation-in-progress. t))
        (incf .indent-level.)
        (defsys-explain "default package: ~s" (default-package system))
        (defsys-explain "default pathname: ~s" (default-pathname system))
        (defsys-explain "default module class: ~s" (default-module-class system))
        (when (setf temp (default-file-type system))
          (defsys-explain "default file type: ~s" temp))
        (when (setf temp (dependencies system))
          (show-dependencies temp))
        (defsys-explain "the system contains the following modules:")
        (dolist (module (modules system))
          (show-module module)))))
  (values))

(defgeneric show-module (object)
  )

(defmethod show-module ((module default-module))
  (let ((.indent-level. (+ 1 .indent-level.))
        (temp nil))
    (defsys-explain "Module: ~s" (pretty-name module))
    (incf .indent-level.)
    (defsys-explain "source file: ~s" (module-file module))
    (when (setf temp (default-package module))
      (defsys-explain "default package: ~s" temp))
    (when (setf temp (default-pathname module))
      (defsys-explain "default pathname: ~s" temp))
    (when (setf temp (dependencies module))
      (show-dependencies temp))))


(defmethod show-module ((module-group default-module-group))
  (let ((.indent-level. (+ 1 .indent-level.))
        (temp nil))
    (defsys-explain "Module-group: ~s" (pretty-name module-group))
    (incf .indent-level.)
    (when (setf temp (default-package module-group))
      (defsys-explain "default package: ~s" temp))
    (when (setf temp (default-pathname module-group))
      (defsys-explain "default pathname: ~s" temp))
    (when (setf temp (default-module-class module-group))
      (defsys-explain "default module class: ~s" temp))
    (when (setf temp (dependencies module-group))
      (show-dependencies temp))
    (defsys-explain "the module-group contains the following modules:")
    (dolist (module (modules module-group))
      (show-module module))))

(defmethod show-module ((system default-system))
  (show-system system))

(defmethod show-module ((system-name symbol))
  (show-system (find-system system-name)))


(defun show-dependencies (dependencies)
  (defsys-explain "Dependencies:")
  (let ((.indent-level. (+ 1 .indent-level.)))
    (dolist (dependency-alist dependencies)
      (defsys-explain "before ~a dependencies:" (first dependency-alist))
      (incf .indent-level.)
      (dolist (dependency-pair (rest dependency-alist))
        (defsys-explain "~a ~s" (first dependency-pair)
                        (second dependency-pair))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;  File comparison and date caching methods
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun validate-product-date-cache (module)
  (setf (product-date-cache-id module) .toplevel-system-operation-id.))

(defun invalidate-product-date-cache (module)
  (setf (product-date-cache-id module) 0))

(defun product-date-cache-valid-p (module)
  (and .toplevel-system-operation-in-progress.
       (eq .toplevel-system-operation-id.
           (product-date-cache-id module))))

(defun validate-source-date-cache (module)
  (setf (source-date-cache-id module) .toplevel-system-operation-id.))

(defun invalidate-source-date-cache (module)
  (setf (source-date-cache-id module) 0))

(defun source-date-cache-valid-p (module)
  (and .toplevel-system-operation-in-progress.
       (eq .toplevel-system-operation-id.
           (source-date-cache-id module))))

(defun product-write-date (module)
  (if (interpreted module)
      (source-write-date module)
    (cond ((product-date-cache-valid-p module)
           (cached-product-write-date module))
          (t
           (validate-product-date-cache module)
           (setf (cached-product-write-date module)
             (let ((pathname (product-pathname module)))
               (if (probe-file pathname)
                   (file-write-date pathname)
                 ;; 0 if file doesn't exist.
                 0)))))))

(defun source-write-date (module)
  (cond ((source-date-cache-valid-p module)
         (cached-source-write-date module))
        (t
         (let ((temp (file-write-date (source-pathname module))))
           (cond (temp
                  (validate-source-date-cache module)
                  (setf (cached-source-write-date module) temp))
                 (t (error 'file-error :pathname (source-pathname module)
                           :format-control "Can't find any source file for module: ~a"
                           :format-arguments `(,module))))))))

(defmethod product-newer-than-source ((module default-module))
  (> (product-write-date module)
     (source-write-date module)))

(defmethod product-newer-than-image ((module default-module))
  (let ((date (product-write-date module)))
    (if (\= 0 date)
        (> date
           (load-date module))
      nil)))

(defmethod source-newer-than-image ((module default-module))
  (let ((date (source-write-date module)))
    (if date
        (> date
           (load-date module))
      nil)))

(defmethod default-file-type ((module default-module))
  (or (default-file-type (containing-system module))
      *default-file-type*))

(defmethod oldest-module-date ((module default-module))
  (product-write-date module))

(defmethod oldest-module-date ((obj module-container))
  (let ((oldest-date (encode-universal-time 59 59 11 31 12 2999))
        (.silent-mode. t)
        (.include-components. nil))
    (map-module-action obj #'(lambda (module)
                               (let ((date (product-write-date module)))
                                 (if (< date oldest-date)
                                     (setf oldest-date date)))))
    oldest-date))

(defmethod oldest-module-date ((system-name symbol))
  (oldest-module-date (find-system system-name t)))

(defmethod newest-module-date ((module default-module))
  (product-write-date module))

(defmethod newest-module-date ((obj module-container))
  (let ((newest-date 0)
        (.silent-mode. t)
        (.include-components. nil))
    (map-module-action obj #'(lambda (module)
                               (let ((date (product-write-date module)))
                                 (if (> date newest-date)
                                     (setf newest-date date)))))
    newest-date))

(defmethod newest-module-date ((system-name symbol))
  (newest-module-date (find-system system-name t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defgeneric source-pathname (module)
  )

(defmethod source-pathname (non-module)
  (module-error non-module))

(defmethod source-pathname ((module lisp-module))
  ;; 8/17/93 (gkj): fix to allow absolute module filenames
  (or (cached-source-pathname module)
      (let* ((module-path (get-pathname module))
             (file-name (module-file module))
             (default-file-type (default-file-type module))
             (file-types *source-file-types*)
             (other-default
              (merge-pathnames module-path *default-pathname-defaults*)))
        (or (and default-file-type
                 (let ((path (merge-pathnames
                              (pathname file-name)
                              (merge-pathnames
                               module-path
                               (make-pathname :type default-file-type)))))
                   (when (probe-file path)
                     (setf (cached-source-pathname module) path)
                     path)))
            (dolist (ftype file-types)
              (let ((path (merge-pathnames
                           (pathname file-name)
                           (merge-pathnames
                            module-path
                            (make-pathname :type ftype)))))
                (when (probe-file path)
                  (setf (cached-source-pathname module) path)
                  (return path))))
            (dolist (ftype file-types)
              (let ((path (merge-pathnames
                           (pathname file-name)
                           (merge-pathnames
                            other-default
                            (make-pathname :type ftype)))))
                (when (probe-file path)
                  (setf (cached-source-pathname module) path)
                  (return path))))
            (error 'file-error :pathname file-name
                   :format-control "Can't find any source file for module: ~a"
                   :format-arguments `(,module))))))

(defmethod source-pathname ((module c-module))
  (let ((module-path (get-pathname module))
        (file-name (module-file module))
        (file-type (or (default-file-type module) "c")))
    (make-pathname :name file-name :type file-type :defaults module-path)))

(defmethod source-pathname ((module fortran-module))
  (let ((module-path (get-pathname module))
        (file-name (module-file module))
        (file-type (or (default-file-type module) "f")))
    (make-pathname :name file-name :type file-type :defaults module-path)))

(defmethod source-pathname ((module text-module))
  (make-pathname :name (module-file module) :type nil :defaults (get-pathname module)))

(defgeneric product-pathname (module)
  )

(defgeneric intermediate-pathname (module))

(defmethod product-pathname (non-module)
  (module-error non-module))

(defun logical-merge (p &optional defaults)
  (let ((p (pathname p)))
    (when (and (logical-pathname-p p)
               (pathname-relative-p p))
      ;; If we have a relative logical pathname, then translate it, because
      ;; we'll get gobbligook if we don't; see bug3699 for a good
      ;; explanation.
      (setq p (translate-logical-pathname p)))
    (if defaults
        (merge-pathnames p defaults)
      p)))

(defmethod product-pathname ((module lisp-module))
  (logical-merge (make-pathname :type *fasl-file-type*)
                 (source-pathname module)))

(defmethod product-pathname ((module foreign-module))
  (logical-merge (make-pathname
                  :type #+dlfcn "so" #+dlwin "dll" #+dlhp "sl" #+dlmac "dylib" #-dynload "o")
                 (source-pathname module)))

(defmethod product-pathname ((module text-module))
  (logical-merge (source-pathname module)))

(defmethod intermediate-pathname ((module foreign-module))
  (logical-merge (make-pathname :type "o")
                 (source-pathname module)))

;;;;;;;;;;;;;

(defmethod get-package ((module default-module))
  (or (default-package module)
      (get-package (parent-object module))))

(defmethod get-package ((module-group default-module-group))
  (or (default-package module-group)
      (get-package (parent-object module-group))))

(defmethod get-package ((system default-system))
  (default-package system))


(defmethod get-pathname ((module default-module))
  (logical-merge (or (default-pathname module)
                     (get-pathname (parent-object module)))))

(defmethod get-pathname ((module-group default-module-group))
  (logical-merge (or (default-pathname module-group)
                     (get-pathname (parent-object module-group)))))

(defmethod get-pathname ((system default-system))
  (logical-merge (default-pathname system)))

(defmethod get-module-class ((module default-module))
  (or (type-of module)
      (get-module-class (parent-object module))))

(defmethod get-module-class ((module-group default-module-group))
  (or (default-module-class module-group)
      (get-module-class (parent-object module-group))))

(defmethod get-module-class ((system default-system))
  (default-module-class system))

;;;;;;;;;;;;;;

(defmethod make-module-out-of-date ((module default-module))
  (setf (load-date module) 0)
  (set-object-state module :image-out-of-date))

(defmethod make-module-out-of-date ((obj module-container))
  (dolist (module (modules obj))
    (make-module-out-of-date module)))

(defmethod make-module-product-out-of-date ((module default-module))
  (setf (cached-product-write-date module) 0) ; a hack...
  (validate-product-date-cache module)
  (set-object-state module :product-out-of-date))

(defmethod make-module-product-out-of-date ((obj module-container))
  (set-object-state obj :product-out-of-date)
  (dolist (module (modules obj))
    (make-module-product-out-of-date module)))

(defmethod make-module-product-out-of-date ((obj symbol))
  (make-module-product-out-of-date (find-system obj t)))

(defmethod make-module-up-to-date ((module default-module))
  (set-object-state module :up-to-date)
  (setf (load-date module) (get-universal-time)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The following macros, functions and methods handle the creation and
;;; reintialization of systems.   Shared-initialize methods are used to
;;; process the forms given to the DEFSYSTEM macro.
;;;
;;;
;;;  Explanation of syntax allowed in defsystem:
;;;
;;;  module-name := symbol | "file-name"
;;;
;;;  module-id := module-name | (module-name system-name)
;;;
;;;  module := "file-name" | module-id | module-definition
;;;
;;;  module-group-name := symbol
;;;
;;;  module-definition :=
;;;       ( {:serial | :parallel | :definitions} {module}+ )
;;;     | ( :module-group module-group-name {module}+ )
;;;     | ( :module { module-group-name | "file-name" | ("file-name"+)
;;;         (module-option)*)
;;;     | ( "filename" (module-option)*)
;;;
;;;  module-definition-list := ( {module-definition}* )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defmacro defsystem (system-name options &body modules)
  `(progn
     #+allegro (excl::record-source-file ',system-name :type 'defsystem)
     (defsystem-1 ',system-name ',options ',modules)))

(defun defsystem-1 (system-name options modules)
  (ensure-system system-name options modules)
  system-name)

(defmacro undefsystem (system-name)
  `(undefsystem-1 ',system-name))

(defun undefsystem-1 (system-name)
  (setf *systems*
    (delete system-name *systems* :key #'car)))


(defun keywordify-options (options)
  ;; take an options list like ((:foo bar) (:blah 1 2 3)) and change it
  ;; into something that can be used as keyword args for the
  ;; shared-initialize method like: (:foo bar :blah (1 2 3))
  (let ((newlist nil))
    (dolist (option options)
      (push (first option) newlist)
      (if (> (length option) 2)
          (push (rest option) newlist)
        (push (second option) newlist)))
    (reverse newlist)))

(defun keywordify-module-definition (module-definition)
  (case (first module-definition)
    ((:parallel :serial :definitions)
     `(,(first module-definition) ,(rest module-definition)))
    ((:module-group)
     (destructuring-bind (name short-form &rest options)
         (rest module-definition)
       `(,@(keywordify-module-definition short-form) :name ,name
         ,@(keywordify-options options))))
    (otherwise (error "~a is an invalid short-form keyword"
                             (first module-definition)))))

(defun process-module-group-keyword (new-module-group value-list)
  ;; value-list is a list of (NAME SHORT-FORM {OPTION}*)
  ;; see spec for full details
  (destructuring-bind (name short-form &rest options) value-list
    (add-to-module-list new-module-group
                        (apply #'make-instance (type-of new-module-group)
                            :parent-object new-module-group
                            :name name
                            :default-module-class
                            (get-module-class new-module-group)
                            :allow-other-keys t
                            `(,(first short-form) ,(rest short-form)
                              ,@(keywordify-options options))))
    new-module-group))

(defun process-module-keyword (new-module-group inputs)
  ;; inputs is a list of file-names that must be made into modules
  (dolist (input inputs)
    (cond ((symbolp input)
           (push (find-system input)
                 (modules new-module-group)))
          ((stringp input)
           ;; create the module from the file name
           (add-to-module-list new-module-group
                               (ensure-module new-module-group input
                                              :module-class
                                              (get-module-class
                                               new-module-group))))
          (t (error "~s is not a valid module input" input))))
  new-module-group)

(defun parse-requirement (requirement)
  (let ((dependencies nil)
        (operation (first requirement)))
    (dolist (module-name (rest requirement))
        (push `(,operation ,module-name) dependencies))
    (reverse dependencies)))

(defun process-in-order-to (module-group value-list)
  ;; parse the dependency info and add a new dependency
  ;; to the module-group
  (destructuring-bind (operation requirement) value-list
    (let ((dependencies (parse-requirement requirement)))
      (dolist (single-operation (if (atom operation) (list operation) operation))
        (dolist (single-dependency dependencies)
          (add-dependency module-group single-operation single-dependency))))))

(defun process-uses-definitions-from (module-group value-list)
  (when (atom value-list) (setf value-list (list value-list)))
  (dolist (module-name value-list)
    (add-dependency module-group :compile
                    `(:load ,module-name))
    (add-dependency module-group :load
                    `(:load ,module-name))
    (add-compile-dependency module-group module-name)))

(defun process-recompile-on (module-group value-list)
  (when (atom value-list) (setf value-list (list value-list)))
  (dolist (module-name value-list)
    (add-dependency module-group :compile
                    `(:compile ,module-name))
    (add-compile-dependency module-group module-name)))

(defun process-load-before-compile (module-group value-list)
  (when (atom value-list) (setf value-list (list value-list)))
  (dolist (module-name value-list)
    (add-dependency module-group :compile
                    `(:load ,module-name))))

(defun ensure-system (name options module-definition-list
                      &key (system-class
                            *default-system-class*))
  ;; look for an existing system by that name:
  (let ((old-system (find-system name)))
    (cond (old-system
           ;; change class if a different one is specified
           (unless (eq system-class (type-of old-system))
             (change-class old-system system-class))
           ;; now reinitialize the old system
           (apply #'shared-initialize old-system
                  t
                  :name name
                  :module-definition-list module-definition-list
                  options))
          ;; no existing system, so create a new one
          (t
           (let ((new-system (apply #'make-instance system-class
                                    :name name
                                    :module-definition-list module-definition-list
                                    options)))
             (pushnew (cons name new-system) *systems*)
             new-system)))))



(defmethod shared-initialize :before ((instance defsystem-base-class)
                                      slot-names
                                      &key)
  ;; This is a hack to get the slots that have :initforms to revert to those
  ;; initforms even though they may already be bound.
  ;; ** maybe this should be reinitialize-instance instead of shared-init??
  (let* ((class (class-of instance))
         (slotds (clos:compute-slots class)))
    (dolist (slotd slotds)
      (let ((slot-name (clos:slot-definition-name slotd)))
        (when (and slot-names
                   (or (eq slot-names 't)
                       (member slot-name slot-names)))
          (let ((initfunction (clos:slot-definition-initfunction slotd)))
            ;; if it has an initform, then reinit the slot regardless
            ;; of whether it is already bound
            (when initfunction
              (setf (slot-value instance slot-name)
                (funcall initfunction)))))))))



(defmethod shared-initialize :after ((system default-system)
                                     slot-names
                                     &key pretty-name
                                     property-list
                                     dependencies
                                     module-definition-list)
  (declare (ignore slot-names))

  ;; first initialize the module-table, but only if there isn't one already.
  (unless (slot-boundp system 'module-table)
    (setf (module-table system) (make-hash-table :test #'equal)))

  ;; now process the options given with the system definition
  (if pretty-name
    (if (not (stringp pretty-name))
        (error
               "~s is not a valid pretty-name which must be a string"
               pretty-name)
      (setf (pretty-name system) pretty-name))
    ;; if no pretty-name supplied, just use system-name
    (setf (pretty-name system) (symbol-name (system-name system))))
  (when property-list
    (if (not (and (listp property-list) (atom (second property-list))))
        (error "~s is not a valid property-list" property-list)
      (setf (getf (property-list system) (first property-list))
        (second property-list))))
  (when dependencies
    ;; value should be of the form:
    ;; ((:in-order-to SYSTEM-OPERATION (SYSTEM-OPERATION system))
    ;;  (:in-order-to SYSTEM-OPERATION (SYSTEM-OPERATION system)) ...)
    (dolist (dependency dependencies)
      (destructuring-bind (key operation requirement) dependency
        (cond ((not (eq :in-order-to key))
               (error "Invalid system dependency, expected :in-order-to, but got: ~a" key))
              ((atom operation)
               (add-dependency system operation (parse-requirement requirement)))
              (t (dolist (single-operation operation)
                   (add-dependency system single-operation
                                   (parse-requirement requirement))))))))
  (dolist (module-def module-definition-list)
    (add-to-module-list system (process-module-definition system module-def))))



(defmethod shared-initialize :after ((new-module-group default-module-group)
                                     slot-names
                                     &key
                                     (name nil name-sup)
                                     (module-group nil module-group-sup)
                                     (inputs nil inputs-sup)
                                     (serial nil serial-sup)
                                     (parallel nil parallel-sup)
                                     (definitions nil definitions-sup)
                                     ;; dependencies
                                     (in-order-to nil i-o-t-sup)
                                     (uses-definitions-from nil u-d-f-sup)
                                     (recompile-on nil recomp-on-sup)
                                     (load-before-compile nil l-b-c-sup)
                                     ;;
                                     (compile-satisfies-load nil c-s-l-sup)
                                     ;;
                                     (package nil package-sup)
                                     (pathname nil pathname-sup)
                                     (module-class nil module-class-sup)
                                     )
  (declare (ignore slot-names))
  (when name-sup
    (setf (pretty-name new-module-group) name)
    ;; only named module-groups get added to the named-module-groups
    ;; of the containing system
    (add-to-named-module-groups (parent-object new-module-group)
                                new-module-group))
  ;; handle dependencies if supplied
  (when i-o-t-sup
    (process-in-order-to new-module-group in-order-to))
  (when u-d-f-sup
    (process-uses-definitions-from new-module-group uses-definitions-from))
  (when recomp-on-sup
    (process-recompile-on new-module-group recompile-on))
  (when l-b-c-sup
    (process-load-before-compile new-module-group load-before-compile))

  (when c-s-l-sup
    (setf (getf (property-list new-module-group) :compile-satisfies-load) ;bug2261
      compile-satisfies-load))

  (when package-sup
    (setf (default-package new-module-group) package))

  (when pathname-sup
    (setf (default-pathname new-module-group) pathname))

  (when module-class-sup
    (setf (default-module-class new-module-group) module-class))

  ;; now do special handling for the particular module spec
  (cond (serial-sup
         (setf (getf (property-list new-module-group) :serial-p) t)
         (process-module-list new-module-group serial :serial))
        (parallel-sup
         (process-module-list new-module-group parallel :parallel))
        (definitions-sup
         (process-module-list new-module-group definitions :definitions))
        (module-group-sup
         ;; this only occurs when :module-group is used in a short-form
         (process-module-group-keyword new-module-group module-group))
        (inputs-sup
         ;; this happens when :module spec has a list of inputs
         (process-module-keyword new-module-group inputs)))
  )

(defmethod shared-initialize :after ((new-module default-module)
                                     slot-names
                                     &key
                                     (name nil name-sup)
                                     (compile-method nil comp-meth-sup)
                                     (load-method nil load-meth-sup)
                                     ;; dependencies
                                     (in-order-to nil i-o-t-sup)
                                     (uses-definitions-from nil u-d-f-sup)
                                     (recompile-on nil recomp-on-sup)
                                     (load-before-compile nil l-b-c-sup)
                                     ;;
                                     (compile-satisfies-load nil c-s-l-sup)
                                     (product-file nil product-file-sup)
                                     ;;
                                     (module-class nil m-c-sup)
                                     ;;
                                     (force-dependent-recompile
                                      nil f-d-r-sup)
                                     (force-load nil f-l-sup)
                                     (force-compile nil f-c-sup)
                                     (concatenate-system-ignore
                                      nil c-s-i-sup))
  (declare (ignore slot-names))

  ;; first initialize the date slots if they don't have values already:
  (unless (slot-boundp new-module 'load-date)
    (setf (load-date new-module) 0))

  ;; now process the options given
  (when name-sup
    (setf (pretty-name new-module) name)
    ;; only named modules get added to the named-module-groups
    ;; of the containing system
    (add-to-named-module-groups (parent-object new-module)
                                new-module))
  ;; handle dependencies if supplied
  (when i-o-t-sup
    (process-in-order-to new-module in-order-to))
  (when u-d-f-sup
    (process-uses-definitions-from new-module uses-definitions-from))
  (when recomp-on-sup
    (process-recompile-on new-module recompile-on))
  (when l-b-c-sup
    (process-load-before-compile new-module load-before-compile))

  (when c-s-l-sup
    (setf (getf (property-list new-module) :compile-satisfies-load)
      compile-satisfies-load))

  (when f-d-r-sup
    (setf (getf (property-list new-module) :force-dependent-recompile)
      force-dependent-recompile))

  (when c-s-i-sup
    (setf (getf (property-list new-module) :concatenate-system-ignore)
      concatenate-system-ignore))

  (when f-l-sup
    (setf (getf (property-list new-module) :force-load)
      force-load))
  
  (when f-c-sup
    (setf (getf (property-list new-module) :force-compile)
      force-compile))

  (when comp-meth-sup
    ;; define a special compile method for this module
    (load-defmethod 'compile-module :qualifiers 'nil
         :specializers `(,(intern-eql-specializer new-module))      ;bug2989
         :lambda-list `((module (eql ,new-module)) &key)
         :function (named-function (method
                                    compile-module
                                    ((eql `,new-module)))
                     (lambda
                         (module &key &allow-other-keys)
                       (progn module)
                       (block
                           compile-module
                         (funcall compile-method module))))
         :plist 'nil))

  (when load-meth-sup
    ;; define a special load method for this module
    (load-defmethod 'load-module :qualifiers 'nil
         :specializers `(,(intern-eql-specializer new-module))      ;bug2989
         :lambda-list `((module (eql ,new-module)) &key)
         :function (named-function (method
                                         load-module
                                         ((eql `,new-module)))
                                        (lambda
                                         (module &key &allow-other-keys)
                                         (progn module)
                                         (block
                                          load-module
                                          (funcall load-method module))))
         :plist 'nil))

  (when product-file-sup
       (load-defmethod 'product-pathname :qualifiers 'nil
         :specializers `(,(intern-eql-specializer new-module))      ;bug2989
         :lambda-list `((module (eql ,new-module)))
         :function (named-function (method
                                    product-pathname
                                    ((eql `,new-module)))
                     (lambda
                         (module)
                       (progn module)
                       (block
                           product-pathname
                         (if (or (stringp product-file)
                                 (pathnamep product-file))
                             product-file
                           (funcall product-file module)))))
         :plist 'nil))

  ;; When module-class is supplied, need to change the class of this module.
  ;; isn't this fun??
  (when m-c-sup
    (change-class new-module module-class))

  )


;;; system-or-mg could be a system or a module-group
(defun process-module-definition (system-or-mg module-def)
  ;; must return the new module-group/system
  (cond ;; of the form ("module-name" :option foo :option2 foo2 ...)
        ((stringp (first module-def))
         (apply #'ensure-module system-or-mg (first module-def)
                :name (first module-def)
                :allow-other-keys t (keywordify-options (rest module-def))))
        (t (let ((new-module-group nil))
             (case (first module-def)
               ;; short form module-definitions:
               ((:parallel :serial :definitions)
                (setf new-module-group
                  (apply #'make-instance *default-module-group-class*
                         :parent-object system-or-mg
                         :default-module-class
                         (get-module-class system-or-mg)
                         (keywordify-module-definition module-def))))
               ((:module-group)
                (destructuring-bind (name short-form &rest options)
                    (rest module-def)
                  (setf new-module-group
                    (apply #'make-instance *default-module-group-class*
                           :parent-object system-or-mg
                           :default-module-class
                           (get-module-class system-or-mg)
                           :name name
                           `(,@(keywordify-module-definition short-form)
                               ,@(keywordify-options options))))))
               ((:module)
                (destructuring-bind (name inputs &rest options)
                    (rest module-def)
                  ;; if there is just one file specified then
                  ;; just create a module, otherwise create a
                  ;; module group.
                  (cond ((symbolp inputs)
                         (setf new-module-group name))
                        ((stringp inputs)
                         (setf new-module-group
                           (apply #'ensure-module
                                  system-or-mg
                                  inputs
                                  :name name
                                  :allow-other-keys t
                                  (keywordify-options options))))
                        (t
                         (setf new-module-group
                           (apply #'make-instance
                                  *default-module-group-class*
                                  :name name
                                  :parent-object system-or-mg
                                  :default-module-class
                                  (get-module-class system-or-mg)
                                  :inputs inputs
                                  (keywordify-options options)))))
                  new-module-group))
               (otherwise
                (error "~a is an invalid module specification"
                       module-def)))
           new-module-group))))

;;; system-or-mg could be a system or a module-group
(defun process-module-list (system-or-mg module-list module-type)
  (unless (null module-list)
    (let ((new-module nil)
          (previous-module (process-module system-or-mg (first
                                                         module-list))))
      (add-to-module-list system-or-mg previous-module)
      (dolist (module (rest module-list))
        (setf new-module (process-module system-or-mg module))
        ;; if its a system then have to create a new module-group cause we don't
        ;; want to add dependencies directly to the system object here.
        (when (system-p new-module)
          (setf new-module (make-instance *default-module-group-class*
                             :parent-object system-or-mg
                             :name (concatenate 'string
                                     "<container for "
                                     (pretty-name new-module)
                                     ">")
                             :default-module-class (get-module-class system-or-mg)
                             :modules (list new-module))))
        (add-dependencies new-module previous-module module-type)
        (add-to-module-list system-or-mg new-module)
        (setf previous-module new-module))
      system-or-mg)))

(defun process-module (system-or-mg module)
  ;; must return the new module
  (cond ((stringp module) ;; file-name
         (ensure-module system-or-mg module))
        ((symbolp module)
         ;; system or module name, find the actual module or system
         (or (lookup-module-by-name system-or-mg module)
             (ensure-system module nil nil)))
        ((listp module)   ;; module-definition
         (process-module-definition system-or-mg module))
        (t (error "~s is not a valid module definition" module))))


(defun module-lookup (system pathname)
  (gethash pathname (module-table system)))

(defun add-to-module-table (system module pathname)
  (setf (gethash pathname (module-table system))
    module))

(defun ensure-module (system-or-mg file-name
                      &rest keys
                      &key package pathname module-class name
                      &allow-other-keys)
  (declare (dynamic-extent keys))
  ;; Note on module redefinition:
  ;; Modules are uniquely identified within a system by the full pathname.
  ;; It is an error to have more than one module with the same pathname in
  ;; the same system.
  ;; Modules are hashed into the module-table of the containing-system by
  ;; pathname.  So to determine if a module is being redefined, we look it
  ;; up in the module-table.

  (unless module-class
    (setf module-class (get-module-class system-or-mg)))

  (let ((old-module
         (module-lookup (containing-system system-or-mg)
                        (merge-pathnames file-name
                                         (or pathname
                                             (default-pathname system-or-mg)
                                             *default-pathname-defaults*)))))
    ;; First check for globbing in the filename.
    ;; If present then we have to expand the filename and create a module for each.
    (cond  #+ignore
           ((or (find #\~ file-name) (find #\{ file-name))
            (error "Error: invalid character found in module name: ~s"
                   file-name))
           ((or (find #\* file-name) (find #\? file-name)
                (find #\[ file-name))
            (let* ((dirname (merge-pathnames file-name
                                             (or pathname
                                                 (get-pathname system-or-mg)
                                                 *default-pathname-defaults*)))
                   (files (directory dirname :glob t)))
              (unless files
                (warn "Directory ~s expanded to nothing" dirname))
              ;; create a new module group in which to put the new modules
              (let ((new-module-group (apply #'make-instance
                                             (type-of system-or-mg)
                                             :name (or name file-name)
                                             :parent-object system-or-mg
                                             :default-module-class
                                             (or module-class
                                                 (get-module-class system-or-mg))
                                             :default-package package
                                             :default-pathname pathname
                                             keys)))
                (dolist (file files)
                  (add-to-module-list new-module-group
                                      (ensure-module new-module-group
                                                     (file-namestring file))))
                new-module-group)))
           ;; The normal cases (no globbing)
           (old-module
            ;; change class if a different one is specified
            (unless (eq module-class (type-of old-module))
              (change-class old-module module-class))
            ;; call it with slot-names = t so it restores initforms to slots
            ;; not explicitly specified.
            (apply #'shared-initialize old-module t
                   :default-package package
                   :default-pathname pathname
                   :file file-name
                   :name (or name file-name)
                   :parent-object system-or-mg
                   keys))
           (t
            (let ((new-module (apply #'make-instance module-class
                                     :default-package package
                                     :default-pathname pathname
                                     :file file-name
                                     :name (or name file-name)
                                     :parent-object system-or-mg
                                     keys)))
              (add-to-module-table (containing-system new-module)
                                   new-module
                                   (merge-pathnames file-name
                                                    (or pathname
                                                        (default-pathname system-or-mg)
                                                        *default-pathname-defaults*)))
              new-module)))))


(defun lookup-module (system-or-mg module &optional (errorp nil))
  (if (defsys-object-p module)
      module
    (lookup-module-by-name system-or-mg module errorp)))

(defun lookup-module-by-name (system-or-mg module-name &optional (errorp nil))
  (let ((temp nil))
    (cond ((null system-or-mg)
           (if (not errorp) nil
             (error "Can't find a module named: ~a:" module-name)))
          ;; if just a module, then look at its parents
          ((module-p system-or-mg)
           (lookup-module-by-name (parent-object system-or-mg)
                                  module-name errorp))
          ;; if module-name is of form (module-name system-name) then look
          ;; for the module in the named system
          ((listp module-name)
           (lookup-module-by-name (find-system (second module-name))
                                  (first module-name) errorp))
          ;; else look for a named module-group in this system or
          ;; module-group
          ((find module-name (named-module-groups system-or-mg)
                 :key #'pretty-name :test #'equal))
          ;; else try looking up the chain of parent module-group/systems
          ((and (setf temp (parent-object system-or-mg))
                (lookup-module-by-name temp module-name errorp)))
          ;; if there is no module by that name, then look for a system by
          ;; that name
          ((find-system module-name))
          ;; failed
          (errorp
           (error "Can't find a module named: ~a" module-name))
          (t nil))))

(defun find-system (system-name &optional (errorp nil))
  (let ((result (cdr (assoc system-name *systems*))))
    (if (and errorp (null result))
        (error "Can't find a system named: ~a" system-name)
      result)))

(defun list-all-systems ()
  (mapcar #'cdr *systems*))

(defun add-dependencies (depending depended-on module-type)
  (case module-type
    (:serial (add-dependency depending :load `(:load ,depended-on))
             (add-dependency depending :compile `(:load ,depended-on)))
    (:parallel) ;; no dependencies
    (:definitions (add-dependency depending :load `(:load ,depended-on))
                  (add-dependency depending :compile `(:load ,depended-on))
                  (add-dependency depended-on :compile
                                  `(,#'make-module-product-out-of-date
                                    ,depending)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; accessors for property lists

(defun defsys-getf (module indicator &optional default)
  (getf (property-list module) indicator default))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; containing-system finds the root system object

(defgeneric containing-system (object)
  )

(defmethod containing-system ((module default-module))
  (containing-system (parent-object module)))

(defmethod containing-system ((module-group default-module-group))
  (containing-system (parent-object module-group)))

(defmethod containing-system ((system default-system))
  system)


;;;;;;;;;;;;;;;;;;;

(defun components (system-or-mg)
  (if .include-components.
      (modules system-or-mg)
    (let ((result nil))
      ;; get rid of component systems:
      (dolist (module (modules system-or-mg))
        (unless (or (symbolp module) (system-p module))
          (push module result)))
      (nreverse result))))

;;;;;;;;;;;;;;;;;;

(defgeneric update-system (system &key)
  )

(defmethod update-system (non-system &key)
  (system-error non-system))

(defmethod update-system ((system-name symbol)
                          &key (date (get-universal-time)))
  (update-system (find-system system-name) :date date))

(defmethod update-system ((system default-system)
                          &key (date (get-universal-time)))
  (dolist (module (modules system))
    (update-module module :date date)))

;;

(defgeneric update-module (module &key)
  )

(defmethod update-module (non-module &key)
  (module-error non-module))

(defmethod update-module ((module default-module) &key date)
  (setf (load-date module) date))

(defmethod update-module ((obj module-container) &key date)
  (dolist (module (modules obj))
    (update-module module :date date)))
