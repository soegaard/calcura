#lang racket/base
;; This module implements `for/vector!` and `for*/vector!`.
;; They are similar to `for/vector` and `for*/vector` but instead
;; of starting from scratch with a newly allocated vector, they
;; start with an existing vector.

;; The first variation for `for/vector!` uses an initial vector
;; and a start position, where the generated elements are inserted.
;;   (for/vector! init-vec start for-clauses body ...)

;; If the generated elements fit in the initial vector, no allocations
;; are done.

;; > (define v (list->vector (range 16)))
;; > v
;; > '#(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)

;; > (define w (for/vector! v 3 ([x (in-range 100 105)]) x))
;; > w
;; '#(0 1 2 100 101 102 103 104 8 9 10 11 12 13 14 15)
;; > (eq? v w)
;; #t

;; If the generated elements doesn't fit in the initial vector,
;; the vector is grown using the same method as `for/vector`
;; The final vector is shrinked, so the generated elements just fit.

;; > (define v (list->vector (range 4)))
;; > v
;; > '#(0 1 2 3)

;; > (define w (for/vector! v 3 ([x (in-range 100 105)]) x))
;; > w
;; '#(0 1 2 100 101 102 103 104)
;; > (eq? v w)
;; #f

;; The initial vector is also extended if the `start` element
;; is greater than the length of the initial vector.

;; > (define v (list->vector (range 4)))
;; > v
;; > '#(0 1 2 3)

;; > (define w (for/vector! v 10 ([x (in-range 100 105)]) x))
;; > w
;; '#(0 1 2 3 0 0 0 0 0 0 100 101 102 103 104)
;; > (eq? v w)
;; #f


;; The second variation for `for/vector!` uses beside the initial vector
;; the start position also an #:length length-expr.
;; Like `for/vector` this variation will always produce a vector
;; that has the length `length-expr`.
;; If the initial vector has the same length, it is mutated.
;; If not, a new vector will be made with elements from the initial vector.
;; If it is expanded, the fill element is 0.
;; It is an error, if start is not smaller than the value of `length-expr`.

;; > (for/vector! (make-vector 10) 2 #:length 5 ([x (in-range 10 13)]) x)
;; '#(0 0 10 11 12)

;; > (for/vector! (make-vector 0) 2 #:length 5 ([x (in-range 10 13)]) x)
;; '#(0 0 10 11 12)

;; The final variation has both a length and a fill.

;; > (for/vector! (make-vector 2) 4 #:length 6 #:fill '_ ([x (in-range 10 13)]) x)
;; '#(0 0 _ _ 10 11)


(require (for-syntax racket/base)
         (only-in racket/private/for split-for-body)
         racket/unsafe/ops)

(define (grow-vector vec)
  (define n (vector-length vec))
  (define new-vec (make-vector (* 2 n)))
  (vector-copy! new-vec 0 vec 0 n)
  new-vec)

(define (shrink-vector vec i)
  (define new-vec (make-vector i))
  (vector-copy! new-vec 0 vec 0 i)
  new-vec)

(define (grow-vector/fill vec fill)
  (define n (vector-length vec))
  (define new-vec (make-vector (* 2 n) fill))
  (vector-copy! new-vec 0 vec 0 n)
  new-vec)

(define (grow-init-vector init-vec start fill)
  ; make sure `start` is a valid index of vec
  (if (< (vector-length init-vec) start)
      (grow-init-vector (grow-vector/fill init-vec fill) start fill)
      init-vec))

(define (adjust-init-vector vec len fill)
  (define n (vector-length vec))
  ; Note: for_/vector! checks that (< start len).
  (cond
    [(= n len)     vec]
    [else          (define new-vec (make-vector len fill))
                   (vector-copy! new-vec 0 vec 0 (min len n))
                   new-vec]))


(define-for-syntax (for_/vector! stx orig-stx for_/vector!-stx for_/fold/derived-stx wrap-all?)
  (syntax-case stx ()
    [(_ init-vec-expr start (for-clause ...) body ...)
     (with-syntax ([orig-stx orig-stx]
                   [for_/vector! for_/vector!-stx]
                   [for_/fold/derived for_/fold/derived-stx]
                   [((middle-body ...) (last-body ...)) (split-for-body stx #'(body ...))])
       (syntax/loc stx
         (let ([init-vec init-vec-expr])
           (unless (vector? init-vec)
             (raise-argument-error 'for_/vector! "vector?" init-vec))
           (let-values ([(vec i)
                         (for_/fold/derived
                          orig-stx
                          ([vec (grow-init-vector init-vec start 0)]
                           [i   start])
                          (for-clause ...) 
                          middle-body ...
                          (let ([new-vec (if (eq? i (unsafe-vector*-length vec))
                                             (grow-vector vec)
                                             vec)])
                            (unsafe-vector*-set! new-vec i (let () last-body ...))
                            (values new-vec (unsafe-fx+ i 1))))])
             (if (eq? vec init-vec)
                 vec
                 (shrink-vector vec i))))))]
    [(_ init-vec-expr start-expr #:length length-expr #:fill fill-expr (for-clause ...) body ...)
     (with-syntax ([orig-stx orig-stx]
                   [(limited-for-clause ...)
                    ;; If `wrap-all?', wrap all binding clauses. Otherwise, wrap
                    ;; only the first and the first after each keyword clause:
                    (let loop ([fcs (syntax->list #'(for-clause ...))] [wrap? #t])
                      (cond
                        [(null? fcs) null]
                        [(keyword? (syntax-e (car fcs)))
                         (if (null? (cdr fcs))
                             fcs
                             (list* (car fcs) (cadr fcs) (loop (cddr fcs) #t)))]
                        [(not wrap?)
                         (cons (car fcs) (loop (cdr fcs) #f))]
                        [else
                         (define fc (car fcs))
                         (define wrapped-fc
                           (syntax-case fc ()
                             [[ids rhs]
                              (or (identifier? #'ids)
                                  (let ([l (syntax->list #'ids)])
                                    (and l (andmap identifier? l))))
                              (syntax/loc fc [ids (stop-after
                                                   rhs
                                                   (lambda x
                                                     (unsafe-fx= i len)))])]
                             [_ fc]))
                         (cons wrapped-fc
                               (loop (cdr fcs) wrap-all?))]))]
                   [((middle-body ...) (last-body ...)) (split-for-body stx #'(body ...))]
                   [for_/vector! for_/vector!-stx]
                   [for_/fold/derived for_/fold/derived-stx])
       (syntax/loc stx
         (let ([len length-expr] [start start-expr] [init-vec init-vec-expr] [fill fill-expr])
           (unless (exact-nonnegative-integer? len)
             (raise-argument-error 'for_/vector! "exact-nonnegative-integer?" len))
           (unless (exact-nonnegative-integer? start)
             (raise-argument-error 'for_/vector! "exact-nonnegative-integer?" start))
           (unless (vector? init-vec)
             (raise-argument-error 'for_/vector! "vector?" init-vec))
           (unless (< start len)
             (raise-argument-error 'for_/vector! "start must be smaller than the vector length" start))
           (let ([v (adjust-init-vector init-vec len fill)])
             (unless (zero? len)
               (for_/fold/derived
                orig-stx 
                ([i start])
                (limited-for-clause ...)
                middle-body ...
                (unsafe-vector*-set! v i (let () last-body ...))
                (unsafe-fx+ 1 i)))
             v))))]
    [(_ init-vec-expr start-expr #:length length-expr (for-clause ...) body ...)
     (for_/vector! #'(fv init-vec-expr start-expr #:length length-expr #:fill 0 (for-clause ...) body ...) 
                   orig-stx for_/vector!-stx for_/fold/derived-stx wrap-all?)]))

(define-syntax (for/vector! stx)
  (for_/vector! stx stx #'for/vector! #'for/fold/derived #f))

(define-syntax (for*/vector! stx)
  (for_/vector! stx stx #'for*/vector! #'for*/fold/derived #t))

