;;;; multimethod.scm
;;;; Kon Lovett, Sep '09

(module multimethod (;export
  (define-multiclass make-multi)
  (define-multimethod make-method)
  get-method
  remove-method!
  methods
  prefer-method!
  prefers)

  (import scheme
          chicken
          (only data-structures topological-sort conc)
          (only srfi-1 not-pair? alist-cons cons* remove! find-tail list-copy)
          (only srfi-18 make-mutex)
          #;
          (only srfi-69 alist->hash-table hash-table-ref/default hash-table-set!
                        hash-table-exists? symbol-hash make-hash-table
                        equal?-hash)
          (only synch synch)
          type-checks
          type-errors)

  (require-library data-structures srfi-1 srfi-18 #;srfi-69 synch type-checks type-errors)

(define (*length- ls)
  (if (null? ls) 0
      (let loop ((ls ls) (len 0))
        (cond ((null? ls) len )
              ((not-pair? ls) (- len) )
              (else (loop (cdr ls) (add1 len)) ) ) ) ) )

(define (*procedure-arity fn)
  (and-let* ((info (procedure-information fn)))
    (if (null? info) 0
        (let ((arity (*length- (cdr info))))
          (if (negative? arity) (exact->inexact (- arity))
              arity ) ) ) ) )

(define (procedure-arity fn)
  (check-procedure 'procedure-arity fn)
  (*procedure-arity fn) )

;;

(define (error-dispatch-check loc id dispatch-val ex)
  (error loc "while computing dispatching-value" ex id dispatch-val) )

(define (error-dispatch loc id args)
  (error loc "no matching method" id args) )

(define (error-not-defined loc id)
  (error loc "multi already defined" id) )

(define (error-defined loc id)
  (error loc "multi is undefined" id) )

(define (error-arity loc id obj)
  (error loc "mis-matched arity" id obj) )

(define (error-finite-arity loc id obj)
  (error loc "procedure must have finite arity" id obj) )

;; multi-info
(define (make-mui arity fn methods prefers) (vector arity fn methods prefers))
(define (mui-arity mui) (vector-ref mui 0))
(define (mui-dispatch-fn mui) (vector-ref mui 1))
(define (mui-methods mui) (vector-ref mui 2))
(define (mui-prefers mui) (vector-ref mui 3))

;; method info
(define (make-mei val fn) (cons val fn))
(define (mei-dispatch-val mei) (car mei))
(define (mei-fn mei) (cdr mei))

;;

(define (arity-match? mui dispatch-val)
  (= (mui-arity mui) (*length- dispatch-val)) )

(define (dispatching-value loc id dispatch-fn args)
  (handle-exceptions ex
      (error-dispatch-check loc id args ex)
    (apply dispatch-fn args) ) )

(define (dispatch-match? dispatch-val-x dispatch-val-y)
  (isa? dispatch-val-x dispatch-val-y) )

;;

; methods list is (<id> <method-info> ...) so initial pair has identity.

(define (method-list methods) (cdr methods))
(define (method-list-set! methods ls) (set-cdr! methods ls))

; prefers dag is (<id> <node> ...) so initial pair has identity.
; <node> : (<method-info> ...)
;
; first node is built as LIFO queue based on method creation order in time.

(define (prefers-dag prefers) (cdr prefers))
(define (prefers-dag-set! prefers ls) (set-cdr! prefers ls))

; adds method-info as the first in a methods list

(define (*add-method! methods prefers mei)
  ; push on as vertex, old vertex becomes first in adjacency list
  (let ((dag (prefers-dag prefers)))
    (prefers-dag-set! prefers (if (null? dag) (list mei)
                                  (let ((lifo (car dag)) (nodes (cdr dag)))
                                    (cons (cons mei lifo) nodes)))) )
  (method-list-set! methods (cons mei (method-list methods))) )

; finds method-info in a methods list

(define (*get-method methods dispatch-val)
  (let loop ((ls (method-list methods)))
    (and (not (null? ls))
         (let ((mei (car ls)))
           (cond ((dispatch-match? dispatch-val (mei-dispatch-val mei))
                  mei )
                 (else
                  (loop (cdr ls)) ) ) ) ) ) )

; deletes method-info from a methods list & returns it

(define (*remove-method! methods dispatch-val)
  (let loop ((ls (method-list methods)) (prev methods))
    (and (not (null? ls))
         (let ((mei (car ls)))
           (cond ((dispatch-match? dispatch-val (mei-dispatch-val mei))
                  (set-cdr! prev (cdr ls))
                  mei )
                 (else
                  (loop (cdr ls) ls) ) ) ) ) ) )

; returns an alist of (dispatch-val . fn)

(define (*methods methods)
  (let loop ((ls (method-list methods)) (al '()))
    (if (null? ls) al
       (let ((mei (car ls)))
         (loop (cdr ls) (alist-cons (mei-dispatch-val mei) (mei-fn mei) al)) ) ) ) )

(define (find-node-pair nodes mei)
  (find-tail (lambda (vertex) (eq? mei (car vertex))) nodes) )
  
(define (*prefer-method! methods prefers mei-x mei-y)
  ; edit the prefers graph
  (let* ((dag (prefers-dag prefers))
         ; the catch-all node
         (lifo (car dag))
         ; remove any existing references to mei-x & mei-y in lifo
         (wo-lifo (remove! (cut eq? mei-x <>) (remove! (cut eq? mei-x <>) lifo)))
         ; actual prefered orders
         (nodes (cdr dag))
         ; existing node for vertex mei-x
         (node-pair (find-node-pair nodes mei-x))
         ; when no existing node make a new one, otherwise
         ; edit the existing node to enforce prefered order
         (prefered-dag (if (not node-pair) (cons* wo-lifo (list mei-x mei-y) nodes)
                           (let* ((node (car node-pair))
                                  (adj-ls (cdr node))
                                  (wo-adj-ls (remove! (cut eq? mei-y <>) adj-ls))
                                  (prefered-node (cons* mei-x mei-y wo-adj-ls)) )
                             (set-car! node-pair prefered-node) ; replace existing node
                             (cons wo-lifo nodes) ) ) ) )
    (prefers-dag-set! prefers prefered-dag) )
    ; use the new topological order for the method list
    (let ((ls (topological-sort (prefers-dag prefers) eq?)))
      (method-list-set! methods ls) ) )

;;

(define ((make-dispatcher id methods dispatch-fn) . args)
  (let ((val (dispatching-value 'multi-method-dispatch id dispatch-fn args)))
    (let ((mei (*get-method methods val)))
      (if mei (apply (mei-fn mei) args)
          (error-dispatch 'multi-method-dispatch id args) ) ) ) )

;;

; the multimethod map of id -> multi-info

(define +mm+ (make-mutex 'multimethod))

#|
(define get-mui)
(define set-mui!)
(let ((mm (make-hash-table eq? symbol-hash)))
  (set! get-mui (lambda (id) (hash-table-ref/default mm id #f)))
  (set! set-mui! (lambda (id mui) (hash-table-set! mm id mui))) )
|#

(define (get-mui id) (get id 'multimethod))
(define (set-mui! id mui) (put! id 'multimethod mui))

;;

(define (make-multi id dispatch-fn)
  (check-symbol 'make-multi id 'id)
  (check-procedure 'make-multi dispatch-fn 'dispatch-fn)
  (synch +mm+
    (when (get-mui id) (error-not-defined 'make-multi id))
    (let ((arity (procedure-arity dispatch-fn)))
      (unless arity (error-arity 'make-multi id dispatch-fn))
      (unless (exact? arity) (error-finite-arity 'make-multi id dispatch-fn))
      (let* ((methods (list id))
             (prefers (list id))
             (dispatcher (make-dispatcher id methods dispatch-fn)) )
        (set-mui! id (make-mui arity dispatch-fn methods prefers))
        dispatcher ) ) ) )

(define (make-method id dispatch-val fn)
  (check-symbol 'make-method id 'id)
  (check-list 'make-method dispatch-val 'dispatch-val)
  (check-procedure 'make-method fn 'fn)
  (synch +mm+
    (let ((mui (get-mui id)))
      (unless mui (error-defined 'make-method id))
      (unless (arity-match? mui dispatch-val) (error-arity 'make-method id dispatch-val))
      (dispatching-value 'make-method id (mui-dispatch-fn mui) dispatch-val) ;check to see if works
      (*add-method! (mui-methods mui) (mui-prefers mui) (make-mei dispatch-val fn)) ) ) )

;;

(define (get-method id dispatch-val)
  (check-symbol 'get-method id 'id)
  (synch +mm+
    (and-let* ((mui (get-mui id))
               (mei (*get-method (mui-methods mui) dispatch-val)) )
      (mei-fn mei) ) ) )

(define (remove-method! id dispatch-val)
  (check-symbol 'remove-method! id 'id)
  (synch +mm+
    (and-let* ((mui (get-mui id)))
      (*remove-method! (mui-methods mui) dispatch-val) ) ) )
      
(define (methods id)
  (check-symbol 'methods id 'id)
  (synch +mm+
    (and-let* ((mui (get-mui id))
               (al (*methods (mui-methods mui))) )
      al ) ) )

(define (prefer-method! id dispatch-val-x dispatch-val-y)
  (check-symbol 'prefer-method id 'id)
  (synch +mm+
    (and-let* ((mui (get-mui id))
               (mei-x (*get-method (mui-methods mui) dispatch-val-x))
               (mei-y (*get-method (mui-methods mui) dispatch-val-y)) )
      (*prefer-method! (mui-methods mui) (mui-prefers mui) mei-x mei-y) ) ) )

(define (prefers id)
  (check-symbol 'prefers id 'id)
  (synch +mm+
    (and-let* ((mui (get-mui id)))
      (list-copy (prefers-dag (mui-prefers mui))) ) ) )

;;

#|

(define-multiclass null type-of)
(define-multimethod (null x) 'list (list))
(define-multimethod (null x) 'string "")

(define-multiclass area (cut hash-table-ref/default <> 'shape))
(define-multimethod (area x) 'rect (* (hash-table-ref x 'wd) (hash-table-ref x 'ht)))
(define-multimethod (area x) 'circle (* PI (hash-table-ref x 'radius) (hash-table-ref x 'radius)))

(define-multiclass (area x) (and (shape? x) (shape-kind x)))
(define-multimethod (area x) ('rect) (* (rect-wd x) (rect-ht x)))
(define-multimethod (area x) ('circle) (* PI (circle-radius x) (circle-radius x)))

(define-multiclass (area x) (and (record-instance? x) (record-instance-tag? x)))
(define-multimethod (area x) ('rect) (* (rect-wd x) (rect-ht x)))
(define-multimethod (area x) ('circle) (* PI (circle-radius x) (circle-radius x)))

|#

#;(import-for-syntax type-of)
#;(begin-for-syntax (require-library type-of))

(define-for-syntax (predname obj)
#;(print "(type-of " obj ") = " (type-of obj))
  (string->symbol (conc (->string obj) #\?)) )

(define-syntax define-multiclass
  (syntax-rules ()
    ((_ (?id ?arg0 ...) (?exp0 ...) ?opt0 ...)
      (letrec-syntax ((dspexp (er-macro-transformer
                                (lambda (frm rnm cmp)
                                  (let ((_and (rnm 'and)))
                                    (let ((arg (cadr frm))
                                          (exp (caddr frm)))
                                      (cond ((keyword? (strip-syntax exp))
                                              `(,_and (,(predname exp) ,arg) ,arg))
                                            ((symbol? (strip-syntax exp))
                                              `(,_and (,(predname exp) ,arg) ,arg))
                                            (else
                                              exp) ) ) ) ) ) )
                      (dspfn (syntax-rules ()
                               ((_ (?arg0 ...) (?exp0 ...))
                                 (lambda (?arg0 ...) (list (dspexp ?arg0 ?exp0) ...))))) )
          (define ?id (make-multi '?id (dspfn (?arg0 ...) (?exp0 ...)) ?opt0 ...)) ) ) ) )

(define-syntax define-multimethod
  (syntax-rules ()
    ((_ (?id ?arg0 ...) (?val0 ...) ?exp0 ...)
      (make-method '?id (list ?val0 ...) (lambda (?arg0 ...) ?exp0 ...)) ) ) )

) ;module multimethod
