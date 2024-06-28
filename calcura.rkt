#lang racket/base
(require racket/format
         racket/list
         racket/match
         racket/vector
         racket/sequence
         "for-parts.rkt")

(require (for-syntax syntax/for-body syntax/parse racket/syntax racket/base)
         syntax/parse/define)

;;;
;;; Attributes Table
;;;

; Each command has an associated set of attributes.
; The user can read and set these with Attributes, SetAttributes and more.
; The functions below are for implementing these.

(define attributes-table (make-hasheq))  ; symbol -> list of symbols

(define (get-attributes name-symbol)
  (hash-ref attributes-table name-symbol #f))

(define (set-attributes! name-symbol attribute-symbols)
  (hash-set! attributes-table name-symbol attribute-symbols))

;;;
;;; The global symbol table of commands
;;;

(define builtins-table   (make-hasheq))  ; symbol -> procedure

(define (get-builtin symbol)
  (hash-ref builtins-table symbol #f))

(define (set-builtin! symbol proc)
  (hash-set! builtins-table symbol proc))


;;;
;;; EXPRESSIONS
;;;

; Symbolically an expression have the form h[e₁, e₂,...].

; The `head` of an expression is `h` and the `e₁, e₂,...` are
; called the `elements` of an expression.

; Both the head and elements of an expression are expressions themselves.

;;; Representation

; An `expression` is either an `atom` or a `form`.
; Atoms are booleans, numbers, symbols and strings.
; The head of an atom is implicit.

; A non-atomic expression is called a `form`. 
; A form is represented by a form-structure holding both the head and the elements in a vector.

; The struct (form parts) consists of a head (an expression) and the parts (a vector).
; The vector holds both the head and the elements (vector head e₁ e₂ ...).
; This is done to allow efficient indexing of the elements.

; As a convention all functions that return forms (or atoms) are capitalized.

(struct expr ()                           #:transparent)
(struct form expr (head attributes parts) #:transparent) ; parts = (vector #f element ...)

(define make-form form) ; extra constructor (used when `form` is shadowed


;;; We aim to make it easy to change the representation of forms.
;;; Therefore we introduce some helpers.

; (define (form-head       form) ...)
; (define (form-attributes form) ...)
; Implicitly defined by (struct form ...) .

(define (form-elements expr)
  ; the elements as a Racket list
  (cdr (vector->list (form-parts expr))))

(define (form-ref expr i)
  ; 1-based index
  (vector-ref (form-parts expr) i))

(define (form-length expr)
  ; number of elements in the form
  (- (vector-length (form-parts expr)) 1))


(define-syntax-rule (in-head expr)
  (in-value (Head expr)))


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
  
;;; Atoms

(define (atom? x)
  (or (number? x)
      (symbol? x)
      (boolean? x)   ; Use 'True and 'False ?
      (string? x)))

;;; Forms

; Not a builtin.
; Used to construct forms from arguments represented as Racket lists.
(define Form
  (case-lambda
    [(head arguments)
     ; arguments is a Racket list
     (Form head '() arguments)]
    [(head attributes arguments)
     (form head attributes (list->vector (cons #f arguments)))]))

(define (has-head? form symbol)
  (and (form? form)
       (eq? (form-head form) symbol)))

(define (all-arguments-symbols? form)
  (for/and ([arg (in-elements form)])
    (symbol? arg)))
  

(define (same-heads? exprs head)
  (cond
    [(list? exprs) (for/and ([expr (in-list exprs)])
                     (eq? (Head expr) head))]
    [(form? exprs) (for/and ([expr (in-elements exprs)])
                     (eq? (Head expr) head))]
    [else
     (error 'same-heads (~a "got: " exprs))]))

(define (list-form?   x) (and (form? x) (eq? (form-head x) 'List)))
(define (splice-form? x) (and (form? x) (eq? (form-head x) 'Splice)))

;;;
;;; Attributes
;;;

; We are going to use Attributes and SetAttributes to define
; a convenience macro `(define-command ...)`. Therefore we
; must manually set attributes and builtins here.

; Attributes[symbol]
; Attributes[string]
; Attributes[{symbol₁, symbol₂, ...}]
(set-attributes! 'Attributes '(HoldAll Listable Protected))

(define (Attributes . args)
  (DoAttributes (Form 'Attributes args)))

(define (DoAttributes form)
  ; We can assume form is an Attributes form
  (case (form-length form)
    [(1) (define arg (form-ref form 1))
         (cond
           [(string? arg)         (Attributes (string->symbol arg))]
           [(symbol? arg)         (define symbol arg)
                                  (define attrs (hash-ref attributes-table symbol #f))
                                  (cond
                                    [attrs (Form 'List attrs)]
                                    [else  (Form 'List '())])]
           [(has-head? arg 'List) (cond
                                    [(all-arguments-symbols? arg)
                                     (define symbols (form-elements arg))
                                     (Form 'List (map Attributes symbols))]
                                    [else
                                     form])])]
    [else form]))

(set-builtin! 'Attributes DoAttributes)


                                 
; SetAttributes[symbol, attr]
; SetAttributes[string, attr]
; SetAttributes[symbol, {attr₁, attr₂, ...}]
; SetAttributes[{symbol₁, ...}, {attr₁, ...}]
(set-attributes! 'SetAttributes '(HoldFirst Protected))

(define (SetAttributes . args)
  (DoSetAttributes (Form 'SetAttributes args)))

(define (DoSetAttributes form)
  ; Note: Since this is evaluated for the side-effect, 'Null is returned.
  (define (List? x) (has-head? x 'List))
  (case (form-length form)
    [(2) (define arg1 (form-ref form 1))
         (define arg2 (form-ref form 2))
         (match* (arg1 arg2)
           [((? symbol? symbol) (? symbol? attr)) (define attrs (hash-ref attributes-table symbol '()))
                                                  (unless (memq attr attrs)
                                                    (hash-set! attributes-table symbol (cons attr attrs)))
                                                  'Null]
           [((? string? string) (? symbol? attr)) (SetAttributes (string->symbol string) attr)]
           [((? symbol? symbol) (? List? attrs))  (for ([at (in-elements attrs)])
                                                    (SetAttributes symbol at))
                                                  'Null]           
           [((? List? symbols) (? List? attrs))   (cond
                                                    [(and (same-heads? symbols 'Symbol)
                                                          (same-heads? attrs   'Symbol))
                                                     (for ([symbol (in-elements symbols)])
                                                       (SetAttributes symbol attrs))
                                                     'Null])]
           [(_ _) form])]
    [else form]))

(set-builtin! 'SetAttributes DoSetAttributes)


;;; Definition of builtin commands

; To define a command, one needs a function that implements it.
; It is a standard Racket function that returns a form (or an atom).
; The name of the command is put into the global symbol table.
; The attributes of the command must be set.

; Each command has a name.
; Each command defines two procedures:
;   - (Name arg ...)
;   - (NameForm form)
; The first  procedure simply calls (NameForm (Form (list args ...)).
; The second procedure receives an Name form and rewrites it.
; If no rewrites are possible, the same (in the sense of eq?) form is returned.

(define-syntax (define-command stx)
  (syntax-parse stx
    [(_define-command Name #:attributes attrs  expr)
     (with-syntax ([DoName (format-id #'Name "Do~a" #'Name)])
       (syntax/loc stx
         (begin
           (set-attributes! 'Name attrs)
           (define (Name . args) (DoName (Form 'Name args)))
           (define DoName expr)
           (set-builtin! 'Name DoName))))]))


(define-command AtomQ #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(1)  (define expr (form-ref form 1))
            (atom? expr)]
      [else form])))
            

; IMPORTANT
;   - when a new head symbol is added below, the function Order needs to be updated.
(define-command Head #:attributes '(Protected)
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
             [else
              (error 'Head (~a "internal error - implement Head for: " expr))])]
      ; Wrap expression with head
      [(2)  (define expr (form-ref form 1))
            (define head (form-ref form 2))
            (Form head (list expr))]
      [else form])))


; Length[expr]
;   Return the number of elements in the expression `expr`.
(define-command Length #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(1) (define expr (form-ref form 1))
           (cond
             [(form? expr) (form-length expr)]
             [(atom? expr) 0]
             [else
              (error 'Length (~a "internal error - expected an expression as the first argument, got: " expr))])]
      [else form])))


; The symbol 'Nothing will be automatically from lists.
(define-command Nothing #:attributes '(Protected)
  (λ (form)    
    'Nothing))


; Apply[f,expr]
;   Replaces the head of `expr` with `f`.
;   If `expr` has no head (an atom) return `expr`. 
(define-command Apply #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(2)  (define f    (form-ref form 1))
            (define expr (form-ref form 2))
            (cond
              [(form? expr) (make-form f '() (form-parts expr))]
              [else         expr])]
      [else form])))


; A splice form will splice the elements into a surrounding list. 
(define-command Splice #:attributes '(Protected)
  (λ (form)
    form))


(define-command List #:attributes '(Locked Protected)
  (λ (form)
    (define (nothing?     x) (eq? x 'Nothing))
    
    (define (splice as)
      (let loop ([as as] [ass '()])
        (cond
          [(null? as) (if (null? ass)
                          '()
                          (loop (car ass) (cdr ass)))]
          [else       (define a (car as))
                      (if (splice-form? a)
                          (loop (form-elements a)
                                (cons (cdr as) ass))
                          (cons a
                                (loop (cdr as) ass)))])))

    ; If neither there are no Splice or Nothing subforms, we can take a fast path.
    (define splice-needed?             (for/or ([expr (in-elements form)]) (splice-form? expr)))
    (define removal-of-nothing-needed? (for/or ([expr (in-elements form)]) (nothing?     expr)))
    (cond
      [(and splice-needed? removal-of-nothing-needed?)
       ; 1. If an element is a (Splice list) then the elements of `list` are spliced.
       (define spliced-args (splice (form-elements form)))
       ; 2. Occurrences of 'Nothing are filtered away.
       (define cleaned-args
         (if (memf nothing? spliced-args)
             (for/list ([arg (in-list spliced-args)]
                        #:unless (eq? arg 'Nothing))
               arg)
             spliced-args))
       (Form 'List cleaned-args)]
      [splice-needed?
       (define spliced-args (splice (form-elements form)))
       (Form 'List spliced-args)]
      [removal-of-nothing-needed?
       (define args         (form-elements form))
       (define cleaned-args (filter (λ (arg) (not (eq? arg 'Nothing))) args))
       (Form 'List cleaned-args)]
      ; Fast path, we can return the original form
      [else
       form])))


;  Note:      The symbol x is sorted as if it was written 1*x. Thus 1/2 x << x.
;  Rationale: This bring x and r*x next to each other.
;  Also note: This means the type order for symbols and forms must be the same.

(define (times-by-form? a b) ; is a = (Times number b)
  ; b is a symbol
  (and (form? a)
       (eq? (form-head a) 'Times)
       (= (form-length a) 2)
       (eq? (form-ref a 2) b)
       (number? (form-ref a 1))))

(define (times-form? a)
  (and (form? a)
       (eq? (form-head a) 'Times)))

(define (symbol->times-form x)
  (make-form 'Times '() (vector 1 x)))

(define (times-constant a)
  (cond
    [(> (form-length a) 0) (define r (form-ref a 1))
                           (if (number? r)
                               r
                               1)]
    [else 1]))
      

(define-command Order #:attributes '(Protected)
  (let ()
    (define the-form-order 100)
    (define type-order-ht
      (hasheq
       ; Numbers
       'Integer  0
       'Rational 0
       'Real     0
       'Number   0
       'Boolean  1
       'String   2
       ; Symbols including Nothing, Missing
       'Symbol   the-form-order
       'Nothing  the-form-order
       'Missing  the-form-order
       ; Forms are missing from this table
       ; Form    the-form-order
       ))
    (define (type-order x)
      (hash-ref type-order-ht (Head x) the-form-order))
    (define (NumberOrder a b)
      (cond
        [(and (real? a) (real? b))
         (cond
           [(eq? a b) 0]
           [(< a b)   1]
           [(> a b)  -1]
           [else      0])]
        [else
         (define ra (real-part a))
         (define rb (real-part b))
         (define ca (imag-part a))
         (define cb (imag-part b))
         (cond
           [(< ra rb)  1]
           [(> ra rb) -1]
           [else      (cond
                        [(= ca cb)              0]
                        [(< (abs ca) (abs cb))  1]
                        [(> (abs ca) (abs cb)) -1]
                        [(< ca cb)              1]
                        [(> ca cb)             -1]
                        [else                  (error 'NumberOrder "internal error")])])]))
    (define (BooleanOrder a b)
      (cond
        [(equal? a b) 0]
        [a            1]
        [else        -1]))
    (define (StringOrder a b)
      (cond
        [(string=? a b)  0]
        [(string<? a b)  1]
        [else           -1]))
    (define (SymbolOrder a b)
      (StringOrder (symbol->string a) (symbol->string b)))
    (define (FormOrder a b)
      (define la (Length a))
      (define lb (Length b))
      (cond
        [(< la lb)  1]
        [(> la lb) -1]
        [else     (case (Order (Head a) (Head b))
                    [(1)   1]
                    [(-1) -1]
                    [else 
                     (define res (for/or ([ea (in-elements a)]
                                          [eb (in-elements b)])
                                   (case (Order ea eb)
                                     [( 1)    1]
                                     [(-1)   -1]
                                     [else   #f])))
                          (or res
                              0)])]))
    (λ (form)
      (case (form-length form)
        [(2) (define a (form-ref form 1))
             (define b (form-ref form 2))
             (define ta (type-order a))
             (define tb (type-order b))
             (cond
               [(< ta tb)       1]
               [(> ta tb)      -1]
               [(equal? a b)    0]
               [else
                (case ta
                  [(0)   (NumberOrder  a b)]
                  [(1)   (BooleanOrder a b)]
                  [(2)   (StringOrder  a b)]
                  [(100) ; Symbols and forms both end up here
                   (cond
                     ; note: (times-by-form? a b) ; is a = (Times number b)                     
                     [(and (symbol? a) (symbol? b))           (SymbolOrder  a b)]
                     [(and (symbol? a) (times-by-form? b a))  (NumberOrder 1 (times-constant b))] 
                     [(and (symbol? a) (times-form? b))       (Order (symbol->times-form a) b)]   
                     [(and (symbol? b) (times-by-form? a b))  (NumberOrder (times-constant a) 1)] 
                     [(and (symbol? b) (times-form? a))       (Order a (symbol->times-form b))]   
                     [else                                    (FormOrder a b)])]
                  [else  (error 'Order "internal error")])])]
        [else form]))))

; Sort[list]
; Sort[list,p]
;   Even though the usual case is sorting of lists, one can sort a form.
;   In that case, the arguments are sorted and the head is kept.
(define-command Sort #:attributes '(Protected)
  (λ (orig-form)
    (case (form-length orig-form)
      [(1) (define form (form-ref orig-form 1))
           (cond
             [(form? form) (Sort form Order)]
             [else          orig-form])]
      [(2) (define form (form-ref orig-form 1))
           (define p    (form-ref orig-form 2))
           (cond
             [(form? form)
              (define parts (vector-copy (form-parts form)))
              (vector-sort! parts (λ (f1 f2) (case (p f1 f2) [(1 #t) #t] [else #f]))
                            1)
              (make-form (form-head form) '() parts)]
             [else orig-form])]
      [else orig-form])))


(define-command Rule #:attributes '(Protected SequenceHold)
  (λ (form)
    (case (form-length form)
      [(2)   (define lhs (form-ref form 1))
             (define rhs (form-ref form 2))
             (Form 'Rule (list lhs rhs))]
      [else  form])))


(define-command ListQ #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(1)  (define x (form-ref form 1))
            (eq? (Head x) 'List)]
      [else form])))


;;; Evaluation

(define $IterationLimit 10) ; default is 4096

(define (Eval expr)
  ; Loop until we find a fix-point or the limit is reached
  (let loop ([i 0] [expr expr])
    (define expr1 (Eval1 expr))
    (cond
      [(eq? expr1 expr)      expr]
      [(= i $IterationLimit) expr]
      [else                  (loop (+ i 1) (Eval1 expr1))])))


(define (Eval1 expr)
  ; (displayln (list 'Eval1 (FullForm expr)))
  (cond
    [(atom? expr) expr]
    [(form? expr) (define form expr)
                  ; 1. Evaluate head
                  (define h (let ([head (form-head form)])
                              (if (symbol? head)
                                  head
                                  (Eval head))))
                  ; 2. Get attributes
                  (define attributes (form-elements (Attributes h)))
                  ; 3. Evaluate arguments unless something is holded
                  (define exprs (form-elements form))
                  (define evaluated-exprs
                    (cond
                      [(memq 'HoldAll   attributes)
                       ; All arguments are skip evaluation
                       exprs]
                      [(memq 'HoldFirst attributes)
                       ; Skip evaluation of the first argument
                       (cond
                         [(null? exprs)       '()]
                         [(null? (cdr exprs)) exprs]
                         [else                (cons (car exprs)
                                                    (map Eval exprs))])]
                      [(memq 'HoldRest attributes)
                       ; Only evaluate the first argument
                       (cond
                         [(null? exprs)       '()]
                         [(null? (cdr exprs)) (list (Eval (car exprs)))]
                         [else                (cons (Eval (car exprs))
                                                    (cdr exprs))])]                  
                      ; default is to evaluate all arguments in order
                      [else (map Eval exprs)]))
                  (displayln (list 'evaluated-exprs evaluated-exprs)) 
                  ; 4. Flatten any arguments of the form Sequence[e₁,...]
                  (define sequence-flattened-parts
                    (let ()
                      (define (build es ess)
                        (cond
                          [(and (null? es) (null? ess)) '()]
                          [(null? es)                   (build (car ess) (cdr ess))]
                          [(SequenceQ (car es))         (build (form-elements (car es))
                                                               (cons (cdr es) ess))]
                          [else                         (cons (car es)
                                                              (build (cdr es) ess))]))
                      (if (memq 'SequenceHold attributes)
                          evaluated-exprs
                          (build evaluated-exprs '()))))
                  (displayln (list 'sequence-flattened-parts sequence-flattened-parts))
                  ; 5. If h has the attribute 'Flat, flatten subexpressions with head h
                  (define flat-flattened-parts
                    (let ()
                      (define (h-head? x)
                        (and (form? x) (eq? (Head x) h)))
                      (define (build es ess)
                        (cond
                          [(and (null? es) (null? ess)) '()]
                          [(null? es)                   (build (car ess) (cdr ess))]
                          [(h-head? (car es))           (build (form-elements (car es))
                                                               (cons (cdr es) ess))]
                          [else                         (cons (car es)
                                                              (build (cdr es) ess))]))
                      (if (memq 'Flat attributes)
                          (build sequence-flattened-parts '())
                          sequence-flattened-parts)))
                  (displayln (list 'flat-flattened-parts flat-flattened-parts))
                  ; 6. Reconstruct the form
                  (define new-form (let ()
                                     (define new (Form h (form-attributes form) flat-flattened-parts))
                                     (if (equal? new form) form new)))
                  (displayln (list 'new-form (FullForm new-form) (eq? form new-form)))
                  ; (displayln (list 'new-form (FullForm new-form)))
                  ; 7. If h has the attribute 'Listable, thread
                  (displayln (list 'attributes attributes (and (memq 'Listable attributes) #t)))
                  (define threaded-form
                    (cond
                      [(memq 'Listable attributes)  (if (> (form-length new-form) 0)
                                                        (do-thread2 new-form new-form 'List)
                                                        new-form)]
                      [else new-form]))
                  (displayln (list 'threaded-form (FullForm threaded-form) (eq? form threaded-form)))
                  ; (define threaded-form new-form)
                  (cond
                    [(not (eq? new-form threaded-form)) threaded-form]
                    [else
                     ; 8. If h has the attribute 'OrderLess, sort the arguments.
                     (define sorted-form
                       (cond
                         [(memq 'Orderless attributes)
                          (define new-sorted (Sort new-form))
                          (if (equal? new-sorted form) form new-sorted)]
                         [else new-form]))
                     (displayln (list 'sorted-form (FullForm sorted-form) (eq? form sorted-form)))
                     ; 9. If h is a builtin, we call it.
                     (let ()
                       (define proc (get-builtin h))                       
                       (cond
                         [proc (define result (proc sorted-form))
                               (displayln (list 'proc proc (FullForm result)))
                               result]
                         [else sorted-form]))])]))




; Missing[]
; Missing["reason"]
; Missing["reason", expr]
;   A form with head 'Missing represents missing data.
;   It's possible to associate an optional reason and an option expr with the missing data.
(define-command Missing #:attributes '(Protected ReadProtected)
  (λ (form)
    form))


; MissingQ[expr]
;   Is the head of `expr` the symbol 'Missing?
(define-command MissingQ #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(1) (define expr (form-ref form 1))
           (eq? (Head expr) 'Missing)]
      [else form])))


(define-command Sequence #:attributes '(Protected)
  (λ (form)
    form))

(define (SequenceQ x) ; not a builtin
  (and (form? x) (eq? (Head x) 'Sequence)))


; Catenate[{e₁, e₂, ...}]
;   Return a single list with the elements in the expressions.
;   If an expression has head 'Missing it is omitted.
;   Analogy: append*
(define-command Catenate #:attributes '(Protected)
  (λ (form)
    (define (non-missing? x) (not (MissingQ x)))
    (case (form-length form)
      [(1) (define exprs (form-ref form 1))           
           (define (non-missing? x) (or (not (form? x)) (not (MissingQ x))))
           (cond
             [(list-form? exprs)
              (case (form-length exprs)
                [(1) (define e1 (form-ref exprs 1))
                     (define missing-count (for/sum ([e (in-elements e1)])
                                             (if (MissingQ e) 1 0)))
                     (cond
                       [(> missing-count 0)  (define parts
                                               (for/parts #:length (- (Length e1) missing-count)
                                                          ([e (in-elements e1)]
                                                           #:unless (MissingQ e))
                                                 e))
                                             (make-form 'List '() parts)]
                       [else e1])]
                [else (define parts (for/parts([e (in-elements* (filter non-missing? (form-elements exprs)))]
                                               #:unless (MissingQ e))
                                      e))
                      (make-form 'List '() parts)])]
             [else form])]
      ; default
      [else form])))



; Join[list₁, list₂, ...]
; // Join[list₁, list₂, ..., n] - TODO
;   Concatenates the lists. The arguments can also be other forms,
;   but they need to have the same head.
;   If the last argument, n, is a natural number, the objects at level n
;   in each list are joined.
; Analogy: append
(define-command Join #:attributes '(Flat OneIdentity Protected)
  (λ (form)
    (case (form-length form)
      [(0)  (List)]
      [(1)  (define expr (form-ref form 1))
            (cond
              [(form? expr) expr]
              [(atom? expr) (begin
                              ; todo - warning that nonatomic expression was expected
                              form)]
              [else         (error 'Join "internal error")])]
      
      [else (define expr1       (form-ref form 1))
            (define exprs       (cdr (form-elements form)))
            (define head1       (Head expr1))
            (define (head1? x)  (eq? x head1))
            (define heads       (map Head exprs))
            (define same-heads? (andmap head1? heads))
            (cond
              [same-heads?
               (define total-len (apply + (map Length (cons expr1 exprs))))
               (define parts     (for/parts #:length (+ total-len 1)
                                            ([x (in-elements* (cons expr1 exprs))])
                                   x))
               (make-form head1 '() parts)]
              ; Not all heads were the same
              [else
               form])])))

(define-command Append #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(2)  (define expr (form-ref form 1))
            (define elem (form-ref form 2))
            (cond
              [(form? expr) (define n     (Length expr))
                            (define parts (for/parts #:length (+ n 2)
                                                      ([x (in-sequences                                                           
                                                           (in-elements expr)
                                                           (in-value    elem))])
                                            x))
                            (make-form (Head expr) '() parts)]
              [else         (begin
                              ; TODO - warning here
                              form)])]
      [else form])))


; Prepend[expr,elem]
;   Prepend the element `elem` to `expr` .
; Prepend[elem] TODO
;   Operator version. The operator will prepend `elem` when applied.
(define-command Prepend #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(2)  (define expr (form-ref form 1))
            (define elem (form-ref form 2))
            (cond
              [(form? expr) (define n     (Length expr))
                            (define parts (for/parts #:length (+ n 2)
                                                     ([x (in-sequences    
                                                          (in-value    elem)
                                                          (in-elements expr))])
                                            x))
                            (make-form (Head form) '() parts)]
              [else         (begin
                              ; TODO - warning here
                              form)])]
      [else form])))

; Insert[list, elem, n]
;   Insert the element `elem` in the list `list` so it have position `n`.
(define-command Insert #:attributes '(Protected)
  (λ (form)
    (case (form-length form)
      [(3)  (define list (form-ref form 1))
            (define elem (form-ref form 2))
            (define n    (form-ref form 3))

            ; (displayln `(list ,list elem ,elem n ,n))
            
            (cond
              [(exact-integer? n)
               (cond
                 [(= n 0)      (begin
                                 ; TODO - warning
                                 form)]
                 
                 [(< n 0)      (define l (Length form))
                               (Insert form elem (+ l n 2))]
                 
                 [(form? form) (define l  (Length list))
                               (cond
                                 [(<= 1 n (+ l 1))
                                  (define parts (for/parts #:length (+ l 2)
                                                           ([x (in-sequences                                                          
                                                                (in-elements list 1 (- n 1))
                                                                (in-value    elem)
                                                                (in-elements list n l))])
                                                  x))
                                  (displayln parts)
                                  (make-form (Head list) '() parts)]
                                 [else
                                  (begin
                                    ; TODO - warn n out of bounds
                                    form)])]
                 
                 [else         (begin
                                 ; TODO - warning here
                                 form)])]
              [else form])]
      [else form])))

(define (all-equal? xs)
  (cond
    [(null? xs)       #t]
    [(null? (cdr xs)) #t]
    [else             (define x0 (car xs))
                      (define (is-x0? x) (equal? x x0))
                      (andmap is-x0? (cdr xs))]))

    

; Thread[f[args]]
; Thread[f[args], h]
;   Note: Since threading is needed inside `Eval` we implement
;         the actual threading in a helper function `do-thread2`.
(define-command Thread #:attributes '(Protected)
  (λ (form)
    ; This handles the case: Thread[f[args], h]
    ; The form orig-form is returned, if nothing can be done.
    (case (form-length form)
      [(1)  (do-thread2 form (form-ref form 1) 'List)]
      [(2)  (do-thread2 form (form-ref form 1) (form-ref form 2))]
      [else form])))

(define (do-thread2 orig-form f-args head)
  ; (displayln `(do-thread2 ,(FullForm orig-form) ,(FullForm f-args) ,head))
  (cond
    [(atom? f-args) orig-form]
    [(form? f-args)
     (define f      (form-head f-args))
     (define args   (form-ref f-args 1))

     (define h      (or head (form-ref form 2)))
     
     ; 1. Determine the length of arguments with head h.
     ;    To thread, these must all have the same length.
     (define h-indices (for/list ([i   (in-naturals 1)]
                                  [arg (in-elements f-args)]
                                  #:when (has-head? arg h))
                         i))
     (define h-lengths (map (λ (i) (Length (form-ref f-args i)))
                            h-indices))
     (define same?     (all-equal? h-lengths))
     
     ; 2. Generate the subexpression
     (cond
       [(not same?)       orig-form]
       [(null? h-indices) orig-form]
       [else              (define dim (car h-lengths))                          
                          (make-form h '()
                                     (for/parts ([i (in-inclusive-range 1 dim)])
                                       (make-form (Head f-args) '()
                                                  (for/parts ([arg (in-elements f-args)])
                                                    (if (has-head? arg h)
                                                        (form-ref arg i)
                                                        arg)))))])]
    [else (error 'Thread "internal error, got non-expression")]))


; Power[x,y]
;   TODO - WIP
(define-command Power #:attributes '(Listable NumericFunction OneIdentity Protected)
  (λ (form)
    (case (form-length form)
      [(2)  (define x (form-ref form 1))
            (define y (form-ref form 2))
            (cond
              ; x¹ = x 
              [(equal? y 1)                            x]              
              [(and (number? x) (number? y))           (expt x y)]
              ; x⁰ = 1
              [(equal? y 0)                            1]
              ; (ab)^c = a^c b^c  when c<>0 is an integer
              [(and (has-head? x 'Times) (integer? y)) (define factors (for/parts ([x (in-elements x)])
                                                                         (Power x y)))
                                                       (make-form 'Times '() factors)]
              ; (a^b)^c = a^(bc) when c is an integer
              [(and (and (has-head? x 'Power) (= (form-length x) 2))
                    (integer? y))
               (define a (form-ref x 1))
               (define b (form-ref x 2))
               (Power a (Times b y))]
              ; default
              [else form])]
      [else form])))


; Times[expr, ...]
;   The operation has attributes Flat, Orderless, and, OneIdentity.
;   This means, the evaluation loop will:
;     - flatten Times        (no arguments is a Times form)
;     - sort the arguments  (the factors are collected a priori)
;     - nested one-argument Times have been reduced to a single one
;   Since the arguments are sorted, we can assume the numbers
;   are at the beginning.

(define-command Times #:attributes '(Flat Listable NumericFunction OneIdentity Orderless Protected)
  (λ (form)
    ; count how many times x0 occurs in the beginning of xs
    (define (count-same x0 xs)
      (cond
        [(null? xs)            0]
        [(equal? (car xs) x0)  (+ 1 (count-same x0 (cdr xs)))]
        [else                  0]))

    (case (form-length form)
      ; Times[] = 1
      [(0)  1]
      ; Times[expr] = expr
      [(1)  (form-ref form 1)]
      ; Times[expr₁, ...]
      [else
       (define parts         (form-parts form))
       (define end           (vector-length parts))
       ; index of first non-number
       (define number-end    (let loop ([i 1])
                               (cond
                                 [(< i end) (if (number? (vector-ref parts i))
                                                (loop (+ i 1))
                                                i)]
                                 [else    i])))
       (define product       (for/product ([x (in-vector parts 1 number-end)])   x))
       (define other         (for/list    ([x (in-vector parts number-end end)]) x))

       (define result  (cond
                         ; 
                         [(= product 0) (if (exact? product) 0 0.0)]
                         [else
                          (let loop ([factors '()]
                                     [exprs   other])
                            (cond
                              [(null? exprs) (define fs (reverse factors))
                                             (define all (if (= product 1) fs (cons product fs)))
                                             (if (and (not (null? all)) (null? (cdr all)))
                                                 (car all)
                                                 (Form 'Times all))]
                              [else          (define expr0 (car exprs))
                                             (define i (count-same expr0 (cdr exprs)))
                                             (cond
                                               [(= i 0) (loop (cons expr0 factors)
                                                              (cdr exprs))]
                                               [else    (loop (cons (Power expr0 (+ i 1)) factors)
                                                              (drop (cdr exprs) i))])]))]))
       result])))


; Plus[expr, ...]
;   The operation has attributes Flat, Orderless, and, OneIdentity.
;   This means, the evaluation loop will:
;     - flatten Plus        (no arguments is a Plus form)
;     - sort the arguments  (the terms are collected a priori)
;     - nested one-argument Plus have been reduced to a single one
;   Since the arguments are sorted, we can assume the numbers
;   are at the beginning.


(define-command Plus #:attributes '(Flat Listable NumericFunction OneIdentity Orderless Protected)
  (λ (form)
    (displayln (FullForm form))
  ;; ; count how many times x0 occurs in the beginning of xs
  (define (count-same x0 xs)
    (cond
      [(null? xs)            0]
      [(equal? (car xs) x0)  (+ 1 (count-same x0 (cdr xs)))]
      [else                  0]))

    (case (form-length form)
      ; Plus[] = 0
      [(0)  0]
      ; Plus[expr] = expr
      [(1)  (form-ref form 1)]
      ; Plus[expr₁, ...]
      [else
       (define parts         (form-parts form))
       (define end           (vector-length parts))
       ; index of first non-number
       (define number-end    (let loop ([i 1])
                               (cond
                                 [(< i end) (if (number? (vector-ref parts i))
                                                (loop (+ i 1))
                                                i)]
                                 [else    i])))
       (define sum           (for/sum  ([x (in-vector parts 1 number-end)])   x))
       (define other         (for/list ([x (in-vector parts number-end end)]) x))

       (define result  (let loop ([terms '()]
                                  [exprs other])
                         (cond
                           [(null? exprs) (define ts (reverse terms))
                                          (define all (if (= sum 0) ts (cons sum ts)))
                                          (if (null? (cdr all))
                                              (car all)
                                              (Form 'Plus all))]
                           [else          (define expr0 (car exprs))
                                          (define i (count-same expr0 (cdr exprs)))
                                          (cond
                                            [(= i 0) (loop (cons expr0 terms)
                                                           (cdr exprs))]
                                            [else    (loop (cons (Times (+ i 1) expr0) terms)
                                                           (drop (cdr exprs) i))])])))
       result])))


; Minus[x]
(define-command Minus #:attributes '(Listable NumericFunction Protected)
  (λ (form)
    (case (form-length form)
      [(1)  (define x (form-ref form 1))
            (Times -1 x)]
      [else form])))

; Divide[x,y]
(define-command Divide #:attributes '(Listable NumericFunction Protected)
  (λ (form)
    (case (form-length form)
      [(2)  (define x (form-ref form 1))
            (define y (form-ref form 2))
            (cond
              [(equal? y 0) 'ComplexInfinity]
              [(equal? x y) 1]
              [else         (Times x (Power y -1))])]
      [else form])))



(define (FullForm expr)
  (cond
    [(atom? expr) expr]
    [(form? expr) (cons (FullForm (form-head expr))
                        (map FullForm (form-elements expr)))]
    [else
     (list 'RACKET expr)]))




(List 1 2 3) 
(Head (List 1 2 3))
(List 1 2 'Nothing 3 4)
(List 1 2 (Nothing 3 4) 5 6)
(Head (Nothing 3 4))
(List 1 2 (Splice 3 4) 5 6)
(List 1 2 (Splice 3 (Splice 4 5) 6) 7)
(equal? (Length (List 1 2 3)) 3)
(equal? (Length 1)            0) 
(equal? (Length 'x)           0)
(equal? (Length "foo")        0) 
(equal? (AtomQ 'foo)          #t)
(equal? (AtomQ (List 'foo))   #f) 
(equal? (Catenate (List (List 1 2 3) (Missing) (List 4 5 6))) (List 1 2 3 4 5 6))
(equal? (Join (List 1 2 3) (List 4 5 6)) (List 1 2 3 4 5 6))


;; (Plus 1 2 3)
;; (Length (Plus 1 2 3))
;; (Head (Plus 1 2 3))
;; (Apply 'Minus (Plus 1 2 3))


;; From bugs"
(equal? (Order (Power 'y -1) (Power 'x -1)) -1)


;; Tests from rascas

(equal? (FullForm (Eval (Minus (Divide (Times 'x 'y) 3))))
        '(Times -1/3 x y))

(equal? (FullForm (Power (Power (Power 'x 1/2) 1/2) 8))
        '(Power x 2))

(equal? (FullForm (Eval (Power (Times (Power (Times 'x 'y) 1/2) (Power 'z 2)) 2)))
        '(Times x y (Power z 4)))

(equal? (Eval (Divide 'x 'x)) 1)


;; ; TODO [1]: Times needs to fuse powers with same base
(FullForm (Eval (Times (Divide 'x 'y)
                       (Divide 'y 'x))))

(equal? (FullForm (Times 2 'x))       '(Times 2 x))
(equal? (FullForm (Times 2 'x 'y 'z)) '(Times 2 x y z))

;; ; TODO : Samme issue as TODO [1]
(equal? (Power 'x 5) (Eval (Times (Power 'x 2) (Power 'x 3))))


;; Thread
(equal? (FullForm (Thread (Apply 'f (List (List 1 2 3)))))
        '(List (f 1) (f 2) (f 3)))
(equal? (FullForm (Thread (Apply 'f (List (List 1 2 3) 'x))))
        '(List (f 1 x) (f 2 x) (f 3 x)))
(equal? (FullForm (Thread (Apply 'f (List (List 1 2 3) (List 'x 'y 'x)))))
        '(List (f 1 x) (f 2 y) (f 3 x)))
(equal? (FullForm (Thread (Apply '== (List (List 'a 'b 'c) (List 'x 'y 'x)))))
        '(List (== a x) (== b y) (== c x)))

; TODO: Log, Equal

#;(equal? (FullForm (Thread (Log (Equal 'x 'y) 'Equal)))
          ...)

; TODO - more tests for Thread
(equal? (FullForm (Eval (Eval (Times (List 1 2 3) 4))))
        '(List 4 8 12))

; TODO - 
;; > (FullForm (Plus 'x 'x (Times 3 'x)))
;; '(Plus (Times 2 x) (Times 3 x))
