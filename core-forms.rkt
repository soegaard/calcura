#lang racket/base
;;;
;;; Representation
;;; 

; An `expression` is either an `atom` or a `form`.
; Atoms are booleans, numbers, symbols and strings.
; The head of an atom is implicit.

; A non-atomic expression is called a `form`. 
; A form is represented by a form-structure holding both the head and the elements in a vector.

; The struct (form parts) consists of a head (an expression) and the parts (a vector).
; The vector holds both the head and the elements (vector head e₁ e₂ ...).
; This is done to allow efficient indexing of the elements.

; As a convention all functions that return forms (or atoms) are capitalized.

(require "structs.rkt")
;; (struct expr (hc)              #:transparent) ; hc = hash code
;; (struct form expr (head parts) #:transparent) ; parts = (vector #f element ...)
(require (only-in math/bigfloat bigfloat?))


(provide atom?

         Form
         MakeForm

         expression-hash-code
         parts-hash-code
         
         do-head
        
         form-elements
         form-hash-code
         form-length
         form-ref

         parts-length
         parts-ref
         
         in-elements
         in-elements*
         in-form
         in-head)

(require (for-syntax racket/base racket/syntax syntax/parse)
         racket/format
         racket/hash-code
         racket/sequence)

;;; Atoms

(define (atom? x)
  (or (number? x)
      (bigfloat? x)
      (symbol? x)
      (boolean? x)   ; Use 'True and 'False ?
      (string? x)))

;;; We aim to make it easy to change the representation of forms.
;;; Therefore we introduce some helpers.

; (define (form-head       form) ...)
; (define (form-attributes form) ...)
; Implicitly defined by (struct form ...) .

(define (form-hash-code expr)
  ; the hash code of the form
  (expr-hc expr))

(define (form-elements expr)
  ; the elements as a Racket list
  (cdr (vector->list (form-parts expr))))

(define (form-ref expr i)
  ; 1-based index
  (vector-ref (form-parts expr) i))

(define (form-length expr)
  ; number of elements in the form
  (- (vector-length (form-parts expr)) 1))

; parts is a vector of the form (vector #f expr ...)
(define (parts-length parts) 
  (- (vector-length parts) 1))

(define (parts-ref parts i)
  (vector-ref parts i))

(define-syntax-rule (in-head expr)
  (in-value (do-head expr)))



(define (expression-hash-code expr)
  (if (expr? expr)
      (expr-hc expr)
      (equal-hash-code expr))) ; the atomic case

(define (parts-hash-code parts)
  (hash-code-combine*
   (for/list ([p (in-vector parts 1)])
     (expression-hash-code p))))

(define-syntax (MakeForm stx)
  (syntax-parse stx
    [(_MakeForm head parts)
     (syntax/loc stx
       (do-make-form2 head parts))]))

; (Form head arguments)
;    Used to construct forms from arguments represented as Racket lists.
;    Note: Not a builtin. 
(define Form
  (case-lambda
    [(head arguments) ; arguments is a Racket list
     (MakeForm head (list->vector (cons #f arguments)))]))


(define do-make-form2
  (let ()
    (define forms-ht (make-hashalw))    
    (λ (head parts)
      ; compute hash code
      (define hc0 (expression-hash-code head))
      (define hc1 (parts-hash-code parts))
      (define hc  (hash-code-combine hc0 hc1))
      ; find possible equivalent form
      (define existing-form (hash-ref forms-ht hc #f))
      ; if found return it, otherwise store the form
      (define (make-new-form)
        (define new-form (form hc head parts))
        (hash-set! forms-ht hc new-form)
        new-form)      
      (cond
        [existing-form (if (and (equal-always? head (do-head existing-form))
                                (for/and ([p  (in-vector parts 1)]
                                          [ep (in-elements existing-form)])
                                  (equal-always? p ep)))
                           existing-form
                           (make-new-form))]
        [else          (make-new-form)]))))

; Head[expr]
(define do-head
  (λ (form)
    (case (form-length form)
      ; Return head of expression
      [(1) (define expr (form-ref form 1))
           (cond
             [(form?   expr)  (form-head expr)]
             [(symbol? expr)  'Symbol]
             [(and (number? expr)
                   (exact? expr)) (cond
                                    [(integer?  expr) 'Integer]
                                    [(rational? expr) 'Rational]
                                    [else
                                     (error 'Head (~a "internal error - exact?, got: " expr))])]
             [(real?     expr) 'Real]
             [(number?   expr) 'Number]
             [(boolean?  expr) 'Boolean]
             [(string?   expr) 'String]
             [(bigfloat? expr) 'Number]
             [else
              (error 'Head (~a "internal error - implement Head for: " expr))])]
      ; Wrap expression with head
      [(2)  (define expr (form-ref form 1))
            (define head (form-ref form 2))
            (Form head (list expr))]
      [else form])))

(define in-elements
  ; The indices `start` and `end` are 1-based.
  ; Both `start` and `end` are inclusive.
  ; Note: Since the head occupy slot 0, the first element has index 1.
  (case-lambda
    [(form)
     (define parts (form-parts form))
     (define n     (vector-length parts))
     (make-do-sequence
      (λ ()
        (initiate-sequence
         #:init-pos                1
         #:next-pos                add1
         #:pos->element            (λ (i) (vector-ref parts i))
         #:continue-with-pos?      (λ (i) (< i n)))))]
    [(form start)
     (define parts (form-parts form))
     (define n     (vector-length parts))     
     (make-do-sequence
      (λ ()
        (initiate-sequence
         #:init-pos                start
         #:next-pos                add1
         #:pos->element            (λ (i) (vector-ref parts i))
         #:continue-with-pos?      (λ (i) (< i n)))))]
    [(form start end)
     (define parts (form-parts form))
     (define n     (vector-length parts))
     (make-do-sequence
      (λ ()
        (initiate-sequence
         #:init-pos                start
         #:next-pos                add1
         #:pos->element            (λ (i) (vector-ref parts i))
         #:continue-with-pos?      (λ (i) (<= i end)))))]
    [(form start end step)
     (define parts (form-parts form))
     (define n     (vector-length parts))
     (make-do-sequence
      (λ ()
        (initiate-sequence
         #:init-pos                start
         #:next-pos                (λ (i) (+ i step))
         #:pos->element            (λ (i) (vector-ref parts i))
         #:continue-with-pos?      (λ (i) (<= i end)))))]))

(define-syntax-rule (in-form form)
  (in-sequences (in-head     form)
                (in-elements form)))

; (in-elements* forms)
(define (in-elements* forms)
  ; `forms` is a Racket list
  (cond
    [(null? forms)       (in-list '())]
    [(null? (cdr forms)) (in-elements (car forms))]
    [else                (in-sequences (in-elements  (car forms))
                                       (in-elements* (cdr forms)))]))
