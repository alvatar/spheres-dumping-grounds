;;; Copyright (c) 2010 by Álvaro Castro-Castilla, All Rights Reserved.
;;; Licensed under the GPLv3 license, see LICENSE file for full description.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Records implemented as prototypes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare (standard-bindings)
         (extended-bindings)
         (block))

(import prototype)

(define-syntax %?define-prototype-record
  (syntax-rules ()
    ((_ ?name
        ?maker                       ; for seamless record integration
        (?constructor ?arg ...)
        ?type-checker
        (?field ?accessor) ...)
     (begin
       (define-prototype-check ?type-checker)
       (define (?constructor ?arg ...)
         (object ((?arg ?arg) ...)
                 ((?type-checker self) #t)
                 ((type self) ?name)))
       (define ?maker ?constructor)
       (define (?accessor instance) ($ ?field instance))
       ...))))

(define-macro (define-prototype-record name field . fields)
  (let ((namestr (symbol->string name)))
    `(%?define-prototype-record
      ',name
      ,(string->symbol (string-append "make-" namestr))
      (,(string->symbol (string-append "new-" namestr)) ,field ,@fields)
      ,(string->symbol (string-append namestr "?"))
      ,@(map (lambda (f) `(,f ,(string->symbol
                           (string-append namestr "-" (symbol->string f)))))
             (cons field fields)))))
