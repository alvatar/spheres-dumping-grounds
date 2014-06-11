;;; Copyright (c) 2010 by Álvaro Castro-Castilla, All Rights Reserved.
;;; Licensed under the GPLv3 license, see LICENSE file for full description.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SRFI-9 modified to build records with lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare (standard-bindings)
         (extended-bindings)
         (block)
         (mostly-generic))

(define-syntax define-list-record-type
  (syntax-rules ()
    ((define-record-type type
       (constructor constructor-tag ...)
       predicate
       (field-tag accessor . more) ...)
     (begin
       (define type
         (make-record-type 'type '(field-tag ...)))
       (define constructor
         (record-constructor type '(constructor-tag ...)))
       (define predicate
         (record-predicate type))
       (define-record-field type field-tag accessor . more)
       ...))))

(define-syntax define-record-field
  (syntax-rules ()
    ((define-record-field type field-tag accessor)
     (define accessor (record-accessor type 'field-tag)))
    ((define-record-field type field-tag accessor modifier)
     (begin
       (define accessor (record-accessor type 'field-tag))
       (define modifier (record-modifier type 'field-tag))))))

(define (record-type record)
  (car record))

(define :record-type #f)
(set! :record-type (list :record-type ':record-type '(name field-tags)))

(define (make-record-type name field-tags)
  (list :record-type
        name
        field-tags))

(define (record-type-name record-type)
  (cadr record-type))

(define (record-type-field-tags record-type)
  (caddr record-type))

(define (field-index type tag)
  (let loop ((i 0) (tags (record-type-field-tags type)))
    (cond ((null? tags)
           (error "record type has no such field" type tag))
          ((eq? tag (car tags))
           i)
          (else
           (loop (+ i 1) (cdr tags))))))

(define (record-constructor type tags)
  (lambda args (cons (record-type-name type) args)))

(define (record-predicate type)
  (lambda (thing)
    (and (record? thing)
         (eq? (record-type thing)
              (record-type-name type)))))

(define (record-accessor type tag)
  (let ((index (field-index type tag)))
    (lambda (thing)
      (if (eq? (record-type thing)
               (record-type-name type))
          (record-ref thing index)
          (error "accessor applied to bad value" type tag thing)))))

(define (record-modifier type tag)
  (let ((index (field-index type tag)))
    (lambda (thing value)
      (if (eq? (record-type thing)
               (record-type-name type))
          (record-set! thing index value)
          (error "modifier applied to bad value" type tag thing)))))

(define record-marker (list 'record-marker))

(define record? list?)

(define (record-ref record index)
  (list-ref record (+ index 1)))

;;;;; THIS BELOW NEEDS TESTING

(define (insert elm pos lst) 
  (if (= pos 0) 
      (cons elm lst) 
      (if (null? lst) 
          (error "out-of-reach") 
          (cons lst (insert elm (- pos 1) lst)))))

  (define-syntax list-set! 
    (syntax-rules () 
      [(list-set! lst pos elm) 
       (set! lst (insert elm pos lst))]))

(define (record-set! record index value)
  (list-set! record (+ index 1) value))
