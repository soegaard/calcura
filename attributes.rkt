#lang racket/base
;;;
;;; Attributes
;;; 

; This file implements attributes as a bitset.
; The number of chosen attributes is so small,
; the bitset can be represented as a fixnum.

;;;
;;; Dependencies
;;;

(require (for-syntax racket/base racket/syntax syntax/parse)
         racket/fixnum)

;;;
;;; Forms for definining attributes
;;;

(define-syntax (define-attribute stx)
  (syntax-parse stx
    [(_define-attribute name:id bit-index:nat has?:id set:id)
     (with-syntax ([bit-mask (expt 2 (syntax-e #'bit-index))])
       (syntax/loc stx
         (begin
           ; has-attribute-name? : Fixnum -> Boolean
           (provide has?)
           (define (has? attributes)
             (bitwise-bit-set? attributes bit-index))
           ; set-attribute-name : Fixnum -> Boolean
           (provide set)
           (define (set attributes)
             (bitwise-ior attributes bit-mask)))))]))


(define-syntax (define-attributes stx)
  (syntax-parse stx
    [(_define-attributes name ...)
     ; bit indices for each name
     (define names (syntax->list #'(name ...)))
     (define is    (for/list ([i    (in-naturals)]
                              [name (in-list names)])
                     i))
     (define hass  (for/list ([name (in-list names)])
                     (format-id name "has-attribute-~a?" name)))
     (define sets  (for/list ([name (in-list names)])
                     (format-id name "set-attribute-~a" name)))
     
     (with-syntax ([(i ...)          is]
                   [(j ...)          (reverse is)]
                   [(rev-name ...)   (reverse names)]
                   [(has? ...)       hass]
                   [(set  ...)       sets]
                   ; Functions defined by the macro
                   [attributes->list (format-id stx "attributes->list")]
                   [has-attribute?   (format-id stx "has-attribute?")])
       (syntax/loc stx
         (begin
           (define-attribute name i has? set)
           ...
           ; attributes->list : Fixnum -> (Listof Symbol)
           (provide attributes->list)
           (define (attributes->list attributes)
             (define symbols '())
             (when (bitwise-bit-set? attributes j)
               (set! symbols (cons 'rev-name symbols)))
             ...
             symbols)
           ; has-attribute? : Fixnum Symbol -> Boolean
           ; (provide has-attribute?)
           (define (has-attribute? attributes attribute-name)
             (case attribute-name
               [(name) (has? attributes)]
               ...
               [else (raise-arguments-error
                      'has-attribute? "expected a valid attribute name"
                      "attribute-name (as symbol)" attribute-name)]))
           )))]))

;;;
;;; The actual attributes
;;;

(define-attributes
  Constant        ; all derivatives of the function are zero
  Flat            ; the function is associative
  HoldAll         ; the arguments of the function are not evaluated
  HoldAllComplete ; 
  HoldFirst
  HoldRest 
  Listable
  Locked
  NHoldAll
  NHoldFirst
  NHoldRest
  NumericFunction
  OneIdentity
  Orderless
  Protected
  ReadProtected
  SequenceHold
  Stub
  Temporary)

;;;
;;; Tests
;;;

(list "has-attribute-name?"
      (and
       ; Constant
       (equal? (has-attribute-Constant? 0) #f)
       (equal? (has-attribute-Constant? 1) #t)
       (equal? (has-attribute-Constant? 2) #f)
       (equal? (has-attribute-Constant? 3) #t)
       ; Flat
       (equal? (has-attribute-Flat? 0) #f)
       (equal? (has-attribute-Flat? 1) #f)
       (equal? (has-attribute-Flat? 2) #t)
       (equal? (has-attribute-Flat? 3) #t))
      "set-attribute-name"
      (and
       ; Constant (bit 0)
       (= (set-attribute-Constant 0) 1)
       (= (set-attribute-Constant 1) 1)
       (= (set-attribute-Constant 2) 3)
       (= (set-attribute-Constant 3) 3)
       (= (set-attribute-Constant 4) 5)
       ; Flat (bit 1)
       (= (set-attribute-Flat 0) 2)
       (= (set-attribute-Flat 1) 3)
       (= (set-attribute-Flat 2) 2)
       (= (set-attribute-Flat 3) 3)
       (= (set-attribute-Flat 4) 6)
      ))

       

            

