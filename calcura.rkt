#lang racket/base
;;;
;;; Calcura
;;;

;; Calcura is a computer algebra system inspired by Mathematica.

;;;
;;; Dependencies
;;;

(require racket/format
         racket/hash-code
         racket/list
         racket/match
         racket/port
         racket/promise
         racket/vector
         racket/sequence
         "for-parts.rkt"
         "vector-utils.rkt"
         "match-utils.rkt")

(require (for-syntax syntax/for-body syntax/parse racket/syntax racket/base)
         syntax/parse/define)

;;;
;;; Notes
;;;

;; The construct `in-sequences` has overhead.
;; Look into ways of not using it.


;;;
;;; Attributes Table
;;;

; Each symbol has an associated set of attributes.
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

; Besides expressions of the form h[e₁, e₂,...] there is also atomic expressions.


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

(struct expr (hc)              #:transparent) ; hc = hash code
(struct form expr (head parts) #:transparent) ; parts = (vector #f element ...)

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
        [existing-form (if (and (equal-always? head (Head existing-form))
                                (for/and ([p  (in-vector parts 1)]
                                          [ep (in-elements existing-form)])
                                  (equal-always? p ep)))
                           existing-form
                           (make-new-form))]
        [else          (make-new-form)]))))

;;; Atoms

(define (atom? x)
  (or (number? x)
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
  (in-value (Head expr)))

; (FullForm expr)
;   Convert the expression to S-expression form.
(define (FullForm expr)
  (cond
    [(atom? expr) expr]
    [(form? expr) (cons (FullForm (form-head expr))
                        (map FullForm (form-elements expr)))]
    [else
     (list 'RACKET expr)]))

; (InputForm expr)
;   Convert to string suitable for input in the Wolfram language.
(define (InputForm expr)
  ; 1. Generate a tree of things to output
  (define full (FullForm expr))
  (define (out expr)
    (match expr
      [(list head e ...) (list head "[" (add-between (map out e) ", ") "]")]
      [_                 expr]))       
  ; 2. Output the tree
  (define (output-tree x)
    (with-output-to-string
      (λ ()
        (let loop ([x x])
          (cond
            [(null? x) (void)]
            [(list? x) (map loop x)]
            [else      (display x)])))))
  (output-tree (out full)))




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

;;;
;;; match-form and match-parts
;;;

(define-syntax (match-form stx)
  (syntax-case stx (else)
    [(_match-form form-expr [(head-sym elem-pat ...) . more] ...)
     (syntax/loc stx
       (let ([form-val form-expr])
         (unless (form? form-val)
           (raise-syntax-error 'match-form (~a "expected form, got: " form-val)))
         (match form-val
           [(form _ 'head-sym _ (vector #f elem-pat ...)) . more]
           ...
           [_ (raise-syntax-error 'match-form (~a "no matching clause for " form-val))])))]
    [(_match-form form-expr [(head-sym elem-pat ...) . more] ... [else . more-else])
     (syntax/loc stx
       (let ([form-val form-expr])
         (unless (form? form-val)
           (raise-syntax-error 'match-form (~a "expected form, got: " form-val)))
         (match form-val
           [(form _ 'head-sym _ (vector #f elem-pat ...)) . more]
           ...
           [_ . more-else])))]))

(define-syntax (match-parts stx)
  (syntax-case stx (else)
    [(_match-parts form-expr [(elem-pat ...) . more] ...)
     (syntax/loc stx
       (let ([form-val form-expr])
         (unless (form? form-val)
           (raise-syntax-error 'match-form (~a "expected form, got: " form-val)))
         (match form-val
           [(form _ _ (vector _ elem-pat ...)) . more]
           ...
           [_ (raise-syntax-error 'match-parts (~a "no matching clause for " form-val))])))]
    [(_match-parts form-expr [(elem-pat ...) . more] ... [else . more-else])
     (syntax/loc stx
       (let ([form-val form-expr])
         (unless (form? form-val)
           (raise-syntax-error 'match-form (~a "expected form, got: " form-val)))
         (match form-val
           [(form _ _ (vector _ elem-pat ...)) . more]
           ...
           [_ . more-else])))]))

;;;
;;; Match expanders
;;;

;; Example:
;; > (match-form (List 1 2 3) [(List 1 2 3) 'yes])

(define-syntax-rule
  (define-match-expanders ([name: predicate] ...))
  (begin
    (define-match-expander name:
      (λ (stx)
        (syntax-case stx (_)
          [(_name: _) (syntax/loc stx (? predicate))]
          [(_name: x) (syntax/loc stx (? predicate x))])))
    ...))

(define (exact-zero? x)       (and (number? x) (exact? x) (zero? x)))
(define (exact-one? x)        (and (number? x) (exact? x) (= x 1)))
(define (positive-integer? x) (and (number? x) (exact? x) (> x 0)))
(define (negative-integer? x) (and (number? x) (exact? x) (< x 0)))

(define-match-expanders ([integer:  exact-integer?]
                         [rational: exact-rational?]
                         [real:     real?]
                         [complex:  complex?]
                         [symbol:   symbol?]
                         [atom:     atom?]
                         [boolean:  boolean?]
                         [string:   string?]
                         [number:   number?]
                         [zero:     exact-zero?]
                         [one:      exact-one?]
                         [positive-integer:  positive-integer?]
                         [negative-integer:  negative-integer?]))

; (form: _)                      match any form
; (form: x)                      match any form, bind it to x
; (form: x h)                    match any form with head h, bind it to x
; (form: (head-sym elm-pat ...)) match a form with head `head-sym` and parts matching `elm-pat ...`.
(define-match-expander form:
  (λ (stx)
    (syntax-case stx (_)
      [(_form: (head-sym elm-pat ...)) (syntax/loc stx (form _ 'head-sym (vector #f elm-pat ...)))]
      [(_form: _)                      (syntax/loc stx (? form?))]
      [(_form: name)                   (syntax/loc stx (? form? name))]
      [(_form: name head)              (syntax/loc stx (? (λ (x) (has-head? x head)) name))])))

(define-match-expander parts:
  (λ (stx)
    (syntax-case stx ()
      [(_parts: name)                   (syntax/loc stx (and (? form?) (app (λ (x) (form-parts x)) name)))])))

(define-match-expander elements:
  (λ (stx)
    (syntax-case stx ()
      [(_elements: elm-pat ...)         (syntax/loc stx (and (? form?) 
                                                             (app (λ (x) (form-parts x)) 
                                                                  (vector #f elm-pat ...))))])))

; (head: h)  match any form and bind the head to h
(define-match-expander head:
  (λ (stx)
    (syntax-case stx ()
      [(_head: name)         (syntax/loc stx (and (? form?) 
                                                  (app (λ (x) (form-head x)) 
                                                       name)))])))

;;; Forms

; (Form head arguments)
;    Used to construct forms from arguments represented as Racket lists.
;    Note: Not a builtin. 
(define Form
  (case-lambda
    [(head arguments) ; arguments is a Racket list
     (MakeForm head (list->vector (cons #f arguments)))]))

; ToExpression
;   Convert an S-expression into an Expression (form).
(define (ToExpression s-expr)
  (cond
    [(atom?  s-expr)  s-expr]
    [(empty? s-expr)  (List)]
    [(list?  s-expr)  (define es   (map ToExpression s-expr))
                      (define head (first es))
                      (define args (rest es))
                      (Form head args)]))


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
    (match-parts form
      [(expr) (cond
                [(form? expr) (form-length expr)]
                [(atom? expr) 0]
                [else         (error 'Length (~a "internal error - expected an expression "
                                                 "as the first argument, got: " expr))])]
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
    (match-parts form
     [(f expr) (cond
                 [(form? expr) (MakeForm f (form-parts expr))]
                 [else         expr])]
     [else form])))


(define-command Depth #:attributes '(Protected)
  (λ (form)
    (define (depth expr)
      (if (form? expr)
          (+ 1 (for/fold ([m 1]) ([x (in-elements expr)])
                 (max m (depth x))))
          1))
    (define (depth/heads expr)
      (if (form? expr)
          (+ 1 (for/fold ([m 1]) ([x (in-form expr)])
                 (max m (depth/heads x))))
          1))
    (match-parts form
     [(expr)              (depth expr)]
     ; [(expr Heads->True)  (depth/heads expr)]  ; todo: implement options
     [else   form])))


; A `level specification` is one of:
;  - n            Levels 1 to n (inclusive)
;  - Infinity     Levels 1 and greater
;  - List[n]      Level `n` only
;  - List[n₁, n₂] Levels `n₁` to `n₂` (inclusive)

; Interpretation of `n`:
;   If `n` is positive, then "level n" consists of the elements that needs two indices
;   If `n` is negative, then "level n" consists of the elements with *depth* n
;   If `n` is zero, the level consists of the entire expression.

; (in-level-spec level-spec)
;   Returns a sequence of individual levels.
(define (in-level-spec level-spec)
  (match level-spec
    [(positive-integer: n)                       (in-range  1 (+ n 1))]
    [(negative-integer: n)                       (in-range -1 (- n 1) -1)]
    [(form: (List (integer: n)))                 (in-value n)]
    [(form: (List (integer: n₁) (integer: n₂)))  (in-inclusive-range n₁ n₂)]
    [0                                           empty-sequence] ; Since we count from 1.
    ['Infinity                                   (in-naturals 1)]
    [_                                           #f]))

;; ; traverse
;; ;   Depth first traversal
;; (define (traverse expr [start 1] [end (Length expr)] [level 1])
;;   ; Loop returns the depth of the expresion `expr`.
;;   (define (loop expr start end level)
;;     (for ([i (in-inclusive-range start end)])
;;       (define e (form-ref expr i))
;;       ; (displayln (list e 'i i 'level level))
;;       (cond
;;         [(atom? e) (define d level)
;;                    (displayln (list 'e e 'd d))
;;                    d]
;;         [(form? e) (define d (loop e 1 (form-length e) (+ level 1)))
;;                    (displayln (list 'e e 'd d))
;;                    d])))
;;   (loop expr start end level))



; Level[expr, levelspec]
;   Returns list of all subexpressions of `expr` on the level(s) given by `levelspec`.
;   If `levelspec` is List[-1] then a list of all atomic values is returned.
;   Traversal is in depth-first order.
(define-command Level #:attributes '(Protected)
  (λ (form)
    ; single-depth
    ;   Return list of all expressions with depth `depth`.
    (define (single-depth expr depth)
      (define xs '())
      ; Loop returns the depth of the expresion `expr`.
      (define (loop expr)
        (+ 1 (for/fold ([d 0])
                       ([e (in-elements expr)])
               (max d 
                    (cond
                      [(atom? e) (define d 1)
                                 (when (= d depth)
                                   (set! xs (cons e xs)))
                                 d]
                      [(form? e) (define d (loop e))
                                 (when (= d depth)
                                   (set! xs (cons e xs)))
                                 d])))))
      (cond
        [(atom? expr) (if (= depth 1) (list expr) '())]
        [else         (define d (loop expr))
                      (if (= d depth)
                          (reverse (cons expr xs))
                          (reverse xs))]))

    ; single-level
    ;   Return list of all elements with level `level`.
    ;   Assume: level>=0
    (define (single-level expr level)
      (case level
        [(0)  (list expr)]
        [(1)  (if (form? expr)
                  (for/list ([e (in-elements expr)]) e)
                  '())]
        ; level > 1
        [else (define prev-level (single-level expr (- level 1)))
              (flatten (for/list ([expr (in-list prev-level)]
                                  #:unless (atom? expr))
                         (for/list ([e (in-elements expr)])
                           e)))]))
    ; Unpack level specification and collect one level/depth at a time.
    (match-parts form
     [(expr level-spec) (define levels (in-level-spec level-spec))
                        (cond
                          [levels (define single-levels 
                                    (for/list ([level levels])
                                      (cond
                                        [(= level 0) (list expr)]
                                        [(> level 0) (single-level expr level)]
                                        [(< level 0) (single-depth expr (- level))])))
                                  (Form 'List (flatten single-levels))]
                          [else   form])]                        
     [else form])))



; Map[f,expr]
;   Apply the function `f` to each element on the first level of `expr`.


(define-command Association #:attributes '(HoldAllComplete Protected)
  (λ (form)
    form))

(define-command Rule #:attributes '(Protected SequenceHold)
  (λ (form)
    form))

;; (define-command Part #:attributes '(NHoldRest Protected ReadProtected)
;;   (λ (form)
;;     (match-parts form
;;       [(expr (integer: i)) (cond
;;                              [(= i 0) (Head expr)]
;;                              [(> i 0) (define n (form-length 
                                        



; A splice form will splice the elements into a surrounding list. 
(define-command Splice #:attributes '(Protected)
  (λ (form)
    form))

; List[e₁, e₂, ...]
;   Constructs a list of elements e₁, e₂, ...
;   A "Nothing" element will automatically be removed.
;   If an element is a Splice expression, the elements of the
;   Splice expression are "spliced" into the resulting list.
(define-command List #:attributes '(Locked Protected)
  (λ (form)
    (define (nothing? x) (eq? x 'Nothing))
    
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

    ; If there are neither Splice nor Nothing subforms, we can take a fast path.
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


;;;
;;; Patterns
;;;

;; ; _  or Blank[]   matches any expression
;; ; _h or Blank[h]  matches any expression with head `h`
;; (define-match-expander Blank
;;   (λ (stx)
;;     (syntax-case stx (Blank)
;;       [(Blank)    #'_]
;;       [(Blank h)  #'(? (λ (x) (eq? (Head x) 'h)))]
;;       [_       (raise-syntax-error 'Blank "expected: Blank" stx)])))

;; ; sym:obj or Pattern[sym,obj]   matches the pattern `obj` and assigns the value to `sym`

;; (define-match-expander Pattern
;;   (λ (stx)
;;     (syntax-case stx (Pattern)
;;       [(Pattern sym obj) (symbol? (syntax-e #'sym))
;;        #'(and obj sym)])))

;; (equal? (FullForm (match (List 1 2 3)
;;                          [(Pattern x (Blank Join)) (List 'Join x)]
;;                          [(Pattern x (Blank List)) (List 'List x)]
;;                          [_ 'no]))
;;         '(List List (List 1 2 3)))

;; ; p.. or Repeated[p]   matches one or more expression that matches the pattern p
;; (define-match-expander Repeated
;;   (λ (stx)
;;     (syntax-case stx (Repeated)
;;       [(Repeated p) 
;;        #'(p (... ...))])))

;; (equal? (FullForm (match (List 1 2 3)
;;                     [(Pattern xs (ListPattern (Repeated _))) (Form 'List xs)]))
;;         '(List List (List 1 2 3)))


;  Note:      The symbol x is sorted as if it was written 1*x. Thus 1/2 x << x.
;  Rationale: This bring x and r*x next to each other.
;  Also note: This means the type order for symbols and forms must be the same.

(define (times-form? a)
  (and (form? a)
       (eq? (form-head a) 'Times)))

(define (times? a)
  ; Is `a` of the form
  ;  - symbol
  ;  - Times[number, symbol]
  ;  - Times[number]          // Note:  should reduce to `number`
  ;  - Times[symbol]
  (or (symbol? a)
      (and (times-form? a)
           (or (and (= (form-length a) 2)
                    (number? (form-ref a 1))
                    (symbol? (form-ref a 2)))
               (and (= (form-length a) 1)
                    (or (number? (form-ref a 1))
                        (symbol? (form-ref a 1))))))))

(define (times-variable? a)
  (and (times? a)
       (or (and (= (form-length a) 1)
                (symbol? (form-ref a 1)))
           (and (= (form-length a) 2)
                (and (number? (form-ref a 1))
                     (symbol? (form-ref a 2)))))))

(define (times-variable a)
  (if (symbol? a)
      a
      (and (form? a)
           (or (and (= (form-length a) 1)
                    (symbol? (form-ref a 1))
                    (form-ref a 1))
               (and (= (form-length a) 2)
                    (number? (form-ref a 1))
                    (symbol? (form-ref a 2))
                    (form-ref a 2))))))

(define (times-coefficient a)
  (define res
    (if (symbol? a)
        1
        (if (times-form? a)
            (and (> (form-length a) 0)
                 (if (number? (form-ref a 1))
                     (form-ref a 1)
                     1))
            1))) ; (Power x 3) has the coefficient 1
  (if (eq? res #f)
      (begin
        (error 'times-coefficient (~a a)))
      res))

(define (times-by? a b) ; is a = (Times number b)
  (and (times? b)
       (eq? (times-variable b) a)))

(define (term-replace-coefficient term coef)
  (match* (coef term)
    ; todo: check whether the literal 1 matches 1.0
    [(1 (symbol: sym))                     sym]
    [(1 (form: (Times (number: _) _ ...))) (define new-parts (vector-set/copy (form-parts term) 1 coef))
                                           (MakeForm 'Times new-parts)]
    [(1 term)                              term]
     
    [(_ (symbol: sym))                     (MakeForm 'Times (vector #f coef sym))]    
    [(_ (form: (Times (number: _) _ ...))) (define new-parts (vector-set/copy (form-parts term) 1 coef))
                                           (MakeForm 'Times new-parts)]    
    [(_ (form: (Times  _ ...)))            (define parts (form-parts term))
                                           (define n     (vector-length parts))
                                           (define new-parts (make-vector (+ n 1)))
                                           (vector-set! new-parts 1 coef)
                                           (vector-copy! new-parts 2 parts 1)
                                           (MakeForm 'Times new-parts)]
    [(_ term)                              (MakeForm 'Times (vector #f coef term))]
    [(_ _)                                 (error 'term-replace-coefficient)]))

(define-command Order #:attributes '(Protected)
  (let ()
    ; The following Times-related functions are used
    ; in order to sort a symbol x the same as Times[number,x].
    (define (symbol->times-form x)
      (MakeForm 'Times (vector #f 1 x)))

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
                    [( 1)  1]
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
    (define (power?         f) (and (form? f) (= (form-length f) 2) (eq? (form-head f) 'Power)))
    (define (power-base     f) (form-ref f 1))
    (define (power-exponent f) (form-ref f 2))
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
                     ; Case: At least one symbol.
                     [(and (symbol? a) (symbol? b))  (SymbolOrder a b)]
                     [(and (symbol? a) (times?  b))  (if (eq? (times-variable a) (times-variable b))
                                                         (NumberOrder 1 (times-coefficient b))
                                                         (SymbolOrder a (times-variable    b)))]
                     [(and (symbol? a) (power? b))   (if (eq? a (power-base b))
                                                         1 ; symbol first
                                                         (Order a (power-base     b)))]
                     [(and (times? a) (symbol? b))   (if (eq? (times-variable a) b)
                                                         (NumberOrder (times-coefficient a) 1)
                                                         (SymbolOrder (times-variable    a) b))]
                     [(and (power? a) (symbol? b))   (if (eq? (power-base a) b)
                                                         -1 ; symbol first
                                                         (Order (power-base     a) a))]

                     ; symbol and Times[number, symbol] are treated the same
                     ; 
                     [(and (times? a) (times? b)) (if (eq? (times-variable a) (times-variable b))
                                                      (NumberOrder (times-coefficient a) (times-coefficient b))
                                                      (SymbolOrder (times-variable    a) (times-variable    b)))]
                     [else                        (FormOrder a b)])]
                  [else  (error 'Order "internal error")])])]
        [else form]))))

; Sort[list]
; Sort[list,p]
;   Even though the usual case is sorting of lists, one can sort a form.
;   In that case, the arguments are sorted and the head is kept.
(define-command Sort #:attributes '(Protected)
  (λ (orig-form)
    (define (do-sort form p)
      (cond
        [(form? form)
         (define parts (vector-copy (form-parts form)))
         (vector-sort! parts  (λ (f1 f2) (case (p f1 f2) [(1 #t) #t] [else #f]))  1)
         (MakeForm (form-head form) parts)]
        [else orig-form]))

    (match-parts orig-form
      [( (form: list)   )  (do-sort list Order)]
      [( (form: list) p )  (do-sort list p)]
      [else orig-form])))



(define-command ListQ #:attributes '(Protected)
  (λ (form)
    (match-parts form
      [(x)  (eq? (Head x) 'List)]
      [else form])))


;;; Evaluation

(define $IterationLimit 10) ; default is 4096

(define Eval
  (let ()
    ; eval-ht : hash-code -> expression
    (define eval-ht (make-hasheq))
    ; Eval : Expression -> Expression
    (λ (expr)
      (define expr0 expr) ; initial expression
      
      ; Loop until we find a fix-point or the limit is reached.
      (let loop ([i 0] [expr expr])
        (define old-result (hash-ref eval-ht expr #f))
        (cond
          [old-result old-result]
          [else
           (define expr1 (Eval1 expr))
           (cond
             [(eq? expr1 expr)      (hash-set! eval-ht expr0 expr)
                                    expr]
             [(= i $IterationLimit) (hash-set! eval-ht expr0 expr)
                                    expr]
             [else                  (loop (+ i 1) (Eval1 expr1))])])))))


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
                  ; (displayln (list 'evaluated-exprs evaluated-exprs)) 
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
                  ; (displayln (list 'sequence-flattened-parts sequence-flattened-parts))
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
                  ; (displayln (list 'flat-flattened-parts flat-flattened-parts))
                  ; 6. Reconstruct the form
                  (define new-form (let ()
                                     (define new (Form h flat-flattened-parts))
                                     (if (equal? new form) form new)))
                  ; (displayln (list 'new-form (FullForm new-form) (eq? form new-form)))
                  ; (displayln (list 'new-form (FullForm new-form)))
                  ; 7. If h has the attribute 'Listable, thread
                  ; (displayln (list 'attributes attributes (and (memq 'Listable attributes) #t)))
                  (define threaded-form
                    (cond
                      [(memq 'Listable attributes)  (if (> (form-length new-form) 0)
                                                        (do-thread2 new-form new-form 'List)
                                                        new-form)]
                      [else new-form]))
                  ; (displayln (list 'threaded-form (FullForm threaded-form) (eq? form threaded-form)))
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
                     ; (displayln (list 'sorted-form (FullForm sorted-form) (eq? form sorted-form)))
                     ; 9. If h is a builtin, we call it.
                     (let ()
                       (define proc (get-builtin h))                       
                       (cond
                         [proc (define result (proc sorted-form))
                               ; (displayln (list 'proc proc (FullForm result)))
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
    (match-parts form
      [(expr) (eq? (Head expr) 'Missing)]
      [else   form])))


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
    (define (non-missing? x) (not (has-head? x 'Missing)))
    (match-parts form
      [(exprs) (cond
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
                                                 (MakeForm 'List parts)]
                           [else e1])]
                    [else (define parts (for/parts([e (in-elements* (filter non-missing? (form-elements exprs)))]
                                                   #:unless (MissingQ e))
                                          e))
                          (MakeForm 'List parts)])]
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
               (define parts     (for/parts #:length total-len
                                   ([x (in-elements* (cons expr1 exprs))])
                                   x))
               (MakeForm head1 parts)]
              ; Not all heads were the same
              [else
               form])])))

; Append[expr,elem]    append `elem` to `expr` - i.e. add a new last element to `expr`
; Append[elem]         operator version, when applied it will append `elem`
(define-command Append #:attributes '(Protected)
  (λ (form)
    (match-parts form
      [((form: expr) elem) (define n     (form-length expr))
                           (define parts (for/parts #:length (+ n 1)
                                           ([x (in-sequences (in-elements expr)
                                                             (in-value    elem))])
                                           x))
                           (MakeForm (form-head expr) parts)]
      [(atom elem)         (begin ; TODO - warning here
                             form)]
      [else form])))


; Prepend[expr,elem]
;   Prepend the element `elem` to `expr` .
; Prepend[elem] TODO
;   Operator version. The operator will prepend `elem` when applied.
(define-command Prepend #:attributes '(Protected)
  (λ (form)
    (match-parts form
      [((form: expr) elem)  (define n     (Length expr))
                            (define parts (for/parts #:length (+ n 1)
                                            ([x (in-sequences (in-value    elem)
                                                              (in-elements expr))])
                                            x))
                            (MakeForm (form-head expr) parts)]
      [(atom elem)          form]   ; TODO - warning here
      [else                 form])))

; Insert[list, elem, n]
;   Insert the element `elem` in the list `list` so it have position `n`.
(define-command Insert #:attributes '(Protected)
  (let ()
    (define (do-insert orig-form list elem n)
      (define l (form-length list))
      (cond
        [(<= 1 n (+ l 1))
         (define parts (for/parts #:length (+ l 1)
                         ([x (in-sequences
                              (in-elements list 1 (- n 1))
                              (in-value    elem)
                              (in-elements list n l))])
                         x))
         (MakeForm (form-head list) parts)]
        [else
         ; TODO - warn n out of bounds
         orig-form]))
    
    (λ (form)
      (match-parts form
        [((form: list) elem (integer: n))
         (cond
           [(= n 0)      form] ; TODO - warning here
           [(< n 0)      (define l (Length form))
                         (do-insert form list elem (+ l n 2))]           
           [else         (do-insert form list elem n)])]
        [else form]))))


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
    (match-parts form
      [(args)   (do-thread2 form args 'List)]
      [(args h) (do-thread2 form args h)]
      [else     form])))


(define (do-thread2 orig-form f-args h)
  ; (displayln `(do-thread2 ,(FullForm orig-form) ,(FullForm f-args) ,head))
  (match f-args
    [(atom: _) orig-form]

    [(form: (f args))
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
                          (MakeForm h 
                                    (for/parts ([i (in-inclusive-range 1 dim)])
                                      (MakeForm (Head f-args) 
                                                (for/parts ([arg (in-elements f-args)])
                                                  (if (has-head? arg h)
                                                      (form-ref arg i)
                                                      arg)))))])]

    [else orig-form]))


; Power[x,y]
;   TODO - WIP
(define-command Power #:attributes '(Listable NumericFunction OneIdentity Protected)
  (λ (form)
    ; (displayln (FullForm form))
    (match-parts form
      [(x y) (cond
               ; fast path
               [(and (number? x) (number? y))           (expt x y)]
               ; x¹ = x 
               [(equal? y 1)                            x]
               ; x⁰ = 1
               [(equal? y 0)                            1]
               ; 1^x = 1
               [(equal? x 1)                            1]
               ; (ab)^c = a^c b^c  only if c<>0 is an integer
               [(and (has-head? x 'Times) (integer? y)) (define factors (for/parts ([x (in-elements x)])
                                                                          (Power x y)))
                                                        (MakeForm 'Times factors)]
               ; (a^b)^c = a^(bc) only if c is an integer
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
    ; (displayln (FullForm form))
    (define (same? x y) ; check that x and y seen as powers have the same base
      ; The complication is that x and x^2 must be collected into one factor.
      (match* (x y)
        ; Note: The (x x) only works if the attribute fields are the same
        ; [(x x)                                                               #t]
        ; First argument is a symbol
        [((symbol: x) (symbol: x))                                             #t]
        [((symbol: _) (symbol: _))                                             #f]
        [((symbol: x) (form: (Power x (real: _))))                             #t]
        [((symbol: _) _)                                                       #f]
        ; First argument is a Times-form.
        [((form: (Power x _)) (form: (Power x _)))                             #t]
        ; First argument is a general form
        [((and (head: h) (elements: x ...)) (and (head: h) (elements: x ...))) #t]  ; same as (x x) but ignores attributes
        [(_ _)                                                                 #f]))

    (match-parts form
      ; Times[] = 1
      [()  1]
      ; Times[expr] = expr
      [(expr)  expr]
      ; Times[expr₁, ...]
      [else
       (define parts         (form-parts form))
       (define end           (vector-length parts))
       ; index of first non-number
       (define number-end    (vector-index-where-prefix-ends number? parts 1))
       ; multiply numbers in prefix
       (define product       (for/product  ([x (in-vector parts 1 number-end)]) x))
       ;; It's now time to collect like factors into a single Power-form.
       ; Partition the terms into spans of like terms.
       (define others        (span-indices parts number-end same?))
       (define n             (length others))

       (define (factor-exponent a)
         (match a
           ; a = a^1
           [(form: (Power a r)) r]
           [_                   1]))
       (define (factor-base a)
         (match a
           [(form: (Power a r)) a]
           [_                   a]))
       (define (factor-replace-exponent power new-exponent)
         (cond
           [(exact-one? new-exponent) (match power
                                        [(form: (Power a r)) a]
                                        [_                   power])]
           [else                      (match power
                                        [(form: (Power a r)) (Power a     new-exponent)]
                                        [_                   (Power power new-exponent)])]))
       (define (multiply-span vec span)
         ; span = (cons span-start span-length)
         (define span-start  (car span))
         (define span-length (cdr span))
         (define span-end    (+ span-start span-length))
         ; All factors in a span have the same base.
         ; Add the exponents and keep the base.
         (define exponent    (if (= span-length 1) ; fast path
                                 (factor-exponent (vector-ref vec span-start))
                                 (for/fold ([expo (factor-exponent (vector-ref vec span-start))])
                                           ([i    (in-range (+ span-start 1) span-end)])
                                   (Plus expo (factor-exponent (vector-ref vec i))))))
         (factor-replace-exponent (vector-ref vec span-start) exponent))

       (cond
         ; no other factor than the numeric coefficient
         [(null? others) product]
         [else
          (define result-parts  (collect-vector #:length (if (exact-one? product) n (+ n 1))
                                                (λ (collect)
                                                  (collect #f) 
                                                  (unless (exact-one? product)
                                                    (collect product))
                                                  (for ([span (in-list others)])
                                                    (collect (multiply-span parts span))))))
          
          ; Since Times[factor]=factor examine the number of parts here.
          (case (parts-length result-parts)
            [(0)  1]
            [(1)  (parts-ref result-parts 1)]
            [else (MakeForm 'Times result-parts)])])])))



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
    ; (displayln (FullForm form))
    (define (same? x y)
      ; The complication is that x and 3*x must be collected into one term.
      (match* (x y)
        ; Note: The (x x) only works if the attribute fields are the same
        ; [(x x)                                                               #t]
        ; First argument is a symbol
        [((symbol: x) (symbol: x))                                             #t]
        [((symbol: _) (symbol: _))                                             #f]
        [((symbol: x) (form: (Times _ x)))                                     #t]
        [((symbol: _) _)                                                       #f]
        ; First argument is a Times-form.
        [((form: (Times (number: _) ... x ...)) (form: (Times (number: _) ... x ...))) #t]
        ; The rule above replaces the four below. If the invariant holds that
        ; Times always reduces prefix numbers to a single number, so everything works.
        ; [((form: (Times (number: _) x ...)) (form: (Times (number: _) x ...))) #t]
        ; [((form: (Times             x ...)) (form: (Times             x ...))) #t]
        ; [((form: (Times (number: _) x ...)) (form: (Times             x ...))) #t]
        ; [((form: (Times             x ...)) (form: (Times (number: _) x ...))) #t]
        
        ; First argument is a general form
        [((and (head: h) (elements: x ...)) (and (head: h) (elements: x ...))) #t]  ; same as (x x) but ignores attributes
        [(_ _)                                                                 #f]))

    (match-parts form
      ; Plus[] = 0
      [()  0]
      ; Plus[expr] = expr
      [(expr)  expr]
      ; Plus[expr₁, ...]
      [else
       (define parts         (form-parts form))
       (define end           (vector-length parts))
       ; index of first non-number
       (define number-end    (vector-index-where-prefix-ends number? parts 1))
       ; sum numbers in prefix
       (define sum           (for/sum  ([x (in-vector parts 1 number-end)]) x))
       ;; It's now time to collect like terms into a single Times-form.
       ; Partition the terms into spans of like terms.
       (define others        (span-indices parts number-end same?))
       (define n             (length others))
       
       (define (sum-span vec span)
         ; span = (cons span-start span-length)
         (define span-start  (car span))
         (define span-length (cdr span))
         (define coef        (if (= span-length 1) ; fast path
                                 (times-coefficient (vector-ref vec span-start))
                                 (for/fold ([sum 0]) ([i (in-range span-start (+ span-start span-length))])
                                   (+ sum (times-coefficient (vector-ref vec i))))))
         (if (exact-zero? coef)
             0
             (term-replace-coefficient (vector-ref vec span-start) coef)))

       (cond
         ; no terms than the numeric constant term
         [(null? others) sum]
         [else
          (define result-parts  (collect-vector #:length (if (exact-zero? sum) n (+ n 1))
                                                (λ (collect)
                                                  (collect #f) 
                                                  (unless (exact-zero? sum)
                                                    (collect sum))
                                                  (for ([span (in-list others)])
                                                    (collect (sum-span parts span))))))

          ; Since Plus[term]=term examine the number of parts here.
          (if (= (parts-length result-parts) 1)
              (parts-ref result-parts 1)
              (MakeForm 'Plus result-parts))])])))


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

;;;
;;; REPL
;;;

(define (repl)
  (displayln "Calcura 2024")
  (define (loop)
    (display "> ")
    (define s-expr (read))
    (case s-expr
      [(Exit Quit exit quit)
       (void)]
      [else
       (define expr   (ToExpression s-expr))
       (define result (time (Eval expr)))
       (displayln (FullForm result))
       (loop)]))
  (loop))

; FromRacketCAS : S-expression -> Expression
;   This converts an s-expression using standard Racket notation
;   (as used in racket-cas) to an Expression used by Calcura.
(define (FromRacketCAS s-expr)
  (define names (hasheq '+    'Plus
                        '-    'Minus
                        '*    'Times
                        '/    'Divide
                        'sqrt 'Sqrt
                        'expt 'Power
                        'exp  'Exp
                        'sin  'Sin
                        'cos  'Cos
                        'tan  'Tan
                        'log  'Log))

  (define (convert-symbol s)
    (hash-ref names s s))
  
  (define (convert s)
    (cond
      [(symbol? s) (convert-symbol s)]
      [(list?   s) (map convert s)]
      [else        s]))

  (ToExpression (convert s-expr)))



;;;
;;; Tests
;;;

(list "Basic Tests"
      (and  (equal? (FullForm (List 1 2 3))                           '(List 1 2 3))
            (equal? (FullForm (Head (List 1 2 3)))                    'List)
            (equal? (FullForm (List 1 2 'Nothing 3 4))                '(List 1 2 3 4))
            (equal? (FullForm (List 1 2 (Nothing 3 4) 5 6))           '(List 1 2 5 6))
            (equal? (FullForm (Head (Nothing 3 4)))                   'Symbol)
            (equal? (FullForm (List 1 2 (Splice 3 4) 5 6))            '(List 1 2 3 4 5 6))
            (equal? (FullForm (List 1 2 (Splice 3 (Splice 4 5) 6) 7)) '(List 1 2 3 4 5 6 7))
            
            (equal? (Length (List 1 2 3))  3)
            (equal? (Length 1)             0) 
            (equal? (Length 'x)            0)
            (equal? (Length "foo")         0) 
            (equal? (AtomQ 'foo)           #t)
            (equal? (AtomQ (List 'foo))    #f)
            
            (equal? (Catenate (List (List 1 2 3) (Missing) (List 4 5 6))) (List 1 2 3 4 5 6))
            (equal? (Join (List 1 2 3) (List 4 5 6))                      (List 1 2 3 4 5 6))
            )
      "Basic Plus"
      (and  (equal? (Plus)                                 0)
            (equal? (Plus 2)                               2)
            (equal? (Plus 2 3)                             5)
            (equal? (Plus 2 3 4)                           9)
            (equal? (Plus 2 -2)                            0)
            (equal? (Plus 2 -2 3 -3)                       0)
            (equal? (Plus 'x)                              'x)
            (equal? (Plus 0 'x)                            'x)
            (equal? (FullForm (Plus 'x 'x))                '(Times 2 x))
            (equal? (FullForm (Plus 'x 'x 'x))             '(Times 3 x))
            (equal? (FullForm (Plus 'x 'x (Times 3 'x)))   '(Times 5 x))
            (equal? (Plus 'x (Times -1 'x))                0)
            (equal? (Length (Plus 1 'x))                   2)
            (equal? (Head (Plus 1 'x))                     'Plus))
      "Basic Times"
      (and  (equal? (FullForm (Times))                     1)
            (equal? (FullForm (Times 42))                  42)
            (equal? (FullForm (Times 2 3 5))               30)
            (equal? (FullForm (Times 2 3 'x))              '(Times 6 x))
            (equal? (FullForm (Times 2 1/2 'x))            'x)
            (equal? (FullForm (Length (Times 'x 'y)))      2)
            (equal? (FullForm (Times 'x 'x))               '(Power x 2))
            (equal? (FullForm (Times 'x (Power 'x 2)))     '(Power x 3))
            (equal? (FullForm (Times 3 'x 'x))             '(Times 3 (Power x 2)))
            (equal? (FullForm (Times 3 'x (Power 'x 2)))   '(Times 3 (Power x 3)))
            )
      "Basic Power"
      (and  (equal? (FullForm (Power 'x 0))                1)
            (equal? (FullForm (Power 1 'x))                1)
            (equal? (FullForm (Power (Times 'a 'b)    3))  '(Times (Power a 3) (Power b 3)))
            (equal? (FullForm (Power (Times 'a 'b 'c) 3))  '(Times (Power a 3) (Power b 3) (Power c 3)))
            (equal? (FullForm (Power (Times 'a 'b)    'x)) '(Power (Times a b) x))
            (equal? (FullForm (Power (Power 'x 2) 3))      '(Power x 6))            
            )
      "Depth"
      (and  (equal? (Depth 1)                   1)
            (equal? (Depth (List 1))            2)
            (equal? (Depth (List 1 (List 2) 3)) 3))
      "Level"
      (and "atomic expression"
           (equal? (FullForm (Level 42 (List  0))) '(List 42))
           (equal? (FullForm (Level 42 (List  1))) '(List))
           (equal? (FullForm (Level 42 (List -1))) '(List 42))
           (equal? (FullForm (Level 42 (List -2))) '(List))
           "simple form"
           ; The expression `(List 1)` has depth 2.
           (equal? (FullForm (Level (List 1) (List   0)))  '(List (List 1)))
           (equal? (FullForm (Level (List 1) (List   1)))  '(List 1))
           (equal? (FullForm (Level (List 1) (List   2)))  '(List))
           (equal? (FullForm (Level (List 1) (List  -1)))  '(List 1))
           (equal? (FullForm (Level (List 1) (List  -2)))  '(List (List 1)))
           (equal? (FullForm (Level (List 1) (List  -3)))  '(List))
           "nested form"
           ; The expression has depth 4.
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List  0)))  '(List (List 1 (List 2 (List 3) 4))))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List  1)))  '(List 1 (List 2 (List 3) 4)))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List  2)))  '(List 2 (List 3) 4))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List  3)))  '(List 3))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List  4)))  '(List))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List -1)))  '(List 1 2 3 4))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List -2)))  '(List (List 3)))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List -3)))  '(List (List 2 (List 3) 4)))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List -4)))  '(List (List 1 (List 2 (List 3) 4))))
           (equal? (FullForm (Level (List 1 (List 2 (List 3) 4)) (List -5)))  '(List)))
           
      "Exposed Bug"
      (and  (equal? (Order (Power 'y -1) (Power 'x -1)) -1))
      "Rascas (Tests from the Rascas test suite)"
      (and  (equal? (FullForm (Eval (Minus (Divide (Times 'x 'y) 3))))
                    '(Times -1/3 x y))
            (equal? (FullForm (Power (Power (Power 'x 1/2) 1/2) 8))
                    '(Power x 2))
            (equal? (Divide 'x 'x) 1)
            (equal? (FullForm
                     (Eval1 (Eval1 (Times (Divide 'x 'y)
                                          (Divide 'y 'x)))))    1)
            (equal? (Times (Power 'x 2) (Power 'x 3))           (Power 'x 5))
            (equal? (FullForm (Eval1 (Eval1 (Power (Times (Power (Times 'x 'y) 1/2) (Power 'z 2)) 2))))
                    '(Times x y (Power z 4)))
            )
      "Thread"
      (list (equal? (FullForm (Thread (Apply 'f (List (List 1 2 3)))))
                    '(List (f 1) (f 2) (f 3)))
            (equal? (FullForm (Thread (Apply 'f (List (List 1 2 3) 'x))))
                    '(List (f 1 x) (f 2 x) (f 3 x)))
            (equal? (FullForm (Thread (Apply 'f (List (List 1 2 3) (List 'x 'y 'x)))))
                    '(List (f 1 x) (f 2 y) (f 3 x)))
            (equal? (FullForm (Thread (Apply '== (List (List 'a 'b 'c) (List 'x 'y 'x)))))
                    '(List (== a x) (== b y) (== c x))))      
      
      ) ; end of tests


;; ; TODO: Log, Equal

;; #;(equal? (FullForm (Thread (Log (Equal 'x 'y) 'Equal)))
;;           ...)

;; ; TODO - more tests for Thread
;; (equal? (FullForm (Eval (Eval (Times (List 1 2 3) 4))))
;;         '(List 4 8 12))

;; ; TODO - 
;; ;; > (FullForm (Plus 'x 'x (Times 3 'x)))
;; ;; '(Plus (Times 2 x) (Times 3 x))

;; (FullForm (Eval (Plus 3 (Times 4 'x 'y) (Times 5 'x 'y))))
;; '(Plus 3 (Times 4 x y) (Times 5 x y))


; (Join 1 2 3)
