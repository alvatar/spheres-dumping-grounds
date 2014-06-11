;;!!! Prototype-based object system for SchemeSpheres
;; Extension to the prototype-based object system for scheme types
;; .author Kenneth A Dicke, 2008


;;! Global table of deputies
(define deputy-alist '()) ;; A globle table

;;! Find method in a deputy object
(define (deputy-method-finder sym obj)
  ;; Answer a method or #f
  (cond
   ((deputy-object obj)
    => ;; object representing a Scheme native type
    (lambda (deputy) (($ lookup deputy) sym))) ; no delegation
   (else #f)))

;;! Hook into tiny-talk -> (method lookup) function
(custom-method-finder deputy-method-finder)
                             
;;! Deputy object creation
(define (deputy-object thing)
  (let loop ((deps deputy-alist))
    (cond
     ((null? deps) #f)
     (((caar deps) thing) (cdar deps))
     (else (loop (cdr deps))))))

;;! Adds a deputy
(define (add-deputy! predicate object)
  (unless (and (procedure? predicate)
               (object? object))
          (error 'add-deputy!
                 "requires a predicate and an object"
                 predicate object))
  (cond
   ((assq predicate deputy-alist)
    =>
    (lambda (bucket) (set-cdr! bucket object)))
   (else (set! deputy-alist
               (cons (cons predicate object) deputy-alist)))))

;;! Boolean deputy
(add-deputy! boolean?
             (object ()
                     ((name self) 'boolean)
                     ((=? self other)
                      (or (and self other)
                          (and (not self) (not other))))
                     ((shallow-clone self) (if self #t #f))
                     ((deep-clone self) (if self #t #f))))

;;! Symbol deputy
(add-deputy! symbol?
             (object ()
                     ((name self) 'symbol)
                     ((=? self other) (eq? self other))
                     ((shallow-clone self) self)
                     ((deep-clone self) self)))

;;! Char deputy
(add-deputy! char?
             (object ()
                     ((name self) 'character)
                     ((=? self other) (and (char? other)(char=? self other)))
                     ((shallow-clone self) self)
                     ((deep-clone self) self)))

;;! Procedure deputy
(add-deputy! procedure?
             (object ()
                     ((name self) 'procedure)
                     ((=? self other) (eq? self other))
                     ((shallow-clone self) self)
                     ((deep-clone self) self)))

;;! Number deputy
(add-deputy! number?
             (object ()
                     ((name self) 'number)
                     ((negate self) (- self))
                     ((=? self other) (= self other))
                     ((shallow-clone self) self)
                     ((deep-clone self) self)))

;;! Slice operation for indexed collections
(define (slice indexed-coll start end repackage)
  ;; start-inclusive end-exclusive
  ;; repackage is list-><whatever>
  (let loop ((elts '())
             (index (- end 1)))
    (if (< index start)
        (repackage elts)
        (loop (cons ($ iref indexed-coll index) elts) (- index 1)))))

;;! String deputy
;; length map for-each every? any? collect reject join
;; iref slice
(add-deputy! string?
             (object ()
                     ((name self)
                      'string)
                     ((join self other)
                      (string-append self other))
                     ((length self)
                      (string-length self))
                     ((iref self index)
                      (string-ref self index))
                     ((slice self start end)
                      ;;(slice self start end list->string)
                      (substring self start end))
                     ((=? self other)
                      (and (string? other) (string=? self other)))
                     ((for-each self proc)
                      (let ((limit (string-length self)))
                        (let loop ((index 0))
                          (if (>= index limit)
                              'OK
                              (begin (proc (string-ref self index))
                                     (loop (+ index 1)))))))
                     ((map self proc)
                      (let ((limit (string-length self)))
                        (let loop ((index 0) (results '()))
                          (if (>= index limit)
                              (list->string (reverse results))
                              (loop (+ index 1)
                                    (cons (proc (string-ref self index))
                                          results))))))
                     ((every  self proc)
                      ($ every (string->list self) proc))
                     ((any self proc)
                      ($ any (string->list self) proc))
                     ((shallow-clone self)
                      (string-copy self))
                     ((deep-clone self)
                      (string-copy self))
                     ((collect self proc)
                      (call-with-values (lambda () (partition proc (string->list self)))
                        (lambda (yes no) (list->string yes))))
                     ((reject self proc)
                      (call-with-values (lambda () (partition proc (string->list self)))
                        (lambda (yes no) (list->string no))))))

;;! Vector deputy
;; length map for-each every? any? collect reject join
;; iref slice (for indexed collections only)
(add-deputy! vector?
             (object ()
                     ((name self)
                      'vector)
                     ((join self other) ;; (vector-append self other)
                      (unless (vector? other)
                              (error 'vector:join
                                     "requires two vectors to append together"
                                     self other))
                      (list->vector
                       (append (vector->list self)
                               (vector->list other))))
                     ((=? self other)
                      (and (vector? other)
                           (or (eq? self other)
                               (and (= (vector-length self) (vector-length other))
                                    (call-with-current-continuation
                                     (lambda (return)
                                       (vector-for-each
                                        (lambda (a b)
                                          (unless ($ =? a b) (return #f)))
                                        self other)
                                       (return #t)))))))
                     ((length self)
                      (vector-length self))
                     ((iref self index)
                      (vector-ref self index))
                     ((slice self start end)
                      (slice self start end list->vector))
                     ((for-each self proc)
                      (vector-for-each proc self))
                     ((map self proc)
                      (vector-map proc self))
                     ((every self proc)
                      ($ every (vector->list self) proc))
                     ((any self proc)
                      ($ any (vector->list self) proc))
                     ((shallow-clone self)
                      (vector-map values self))
                     ((deep-clone self)
                      (vector-map values self))
                     ((collect self proc)
                      (call-with-values (lambda () (partition proc (vector->list self)))
                        (lambda (yes no) (list->vector yes))))
                     ((reject self proc)
                      (call-with-values (lambda () (partition proc (vector->list self)))
                        (lambda (yes no) (list->vector no))))))
;;! List deputy
;; length map for-each every? any? collect reject join
;; iref slice
(add-deputy! list?
             (object ()
                     ((name self) 'list)
                     ((length self)
                      (length self))
                     ((join self other)
                      (append self other))
                     ((=? self other)
                      (equal? self other))
                     ((iref  self index)
                      (list-ref self index))
                     ((slice self start end)
                      ;; start-inclusive end-exclusive
                      (let start-loop ((list self) (index 0))
                        (if (< index start)
                            (start-loop (cdr list) (+ 1 index))
                            ;; ASSERT: (= index start)
                            (let collect-loop ((elts '()) (list list) (index index) )
                              (if (< index end)
                                  (collect-loop (cons (car list) elts)
                                                (cdr list)
                                                (+ index 1))
                                  (reverse elts))))))
                     ((every self proc)
                      (every proc self))
                     ((any self proc)
                      (any proc self))
                     ((shallow-clone self)
                      (map values self))
                     ((deep-clone self)
                      (map values self)) ;; bogus
                     ((for-each self proc)
                      (for-each proc self))
                     ((map self proc)
                      (map proc self))
                     ((collect self proc)
                      (call-with-values (lambda () (partition proc self))
                        (lambda (yes no) yes)))
                     ((reject self proc)
                      (call-with-values (lambda () (partition proc self))
                        (lambda (yes no) no)))))
