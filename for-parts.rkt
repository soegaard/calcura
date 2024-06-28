#lang racket/base
(require (for-syntax racket/base)
         (only-in racket/private/for split-for-body)
         racket/unsafe/ops)

(provide for/parts for*/parts)

; The parts of a form are represented as vectors whose first elment is #f.
; Since Calcura indices are 1-based, this choice means
; no index are needed when accessing elements.

; We need versions of `for/vector` and `for/vector*` that puts
; an initial #f in front of the elements.
; We have borrowed the implementations of `for/vector` and `for/vector*`
; from `racket/private/for.rkt`


(define (grow-vector vec)
  (define n (vector-length vec))
  (define new-vec (make-vector (* 2 n)))
  (vector-copy! new-vec 0 vec 0 n)
  new-vec)

(define (shrink-vector vec i)
  (define new-vec (make-vector i))
  (vector-copy! new-vec 0 vec 0 i)
  new-vec)

(define-for-syntax (for_/parts stx orig-stx for_/parts-stx for_/fold/derived-stx wrap-all?)
  (syntax-case stx ()
    [(_ (for-clause ...) body ...)
     (with-syntax ([orig-stx orig-stx]
                   [for_/fold/derived for_/fold/derived-stx]
                   [((middle-body ...) (last-body ...)) (split-for-body stx #'(body ...))])
       (syntax/loc stx
         (let-values ([(vec i)
                       (for_/fold/derived
                        orig-stx
                        ([vec (make-vector 16 #f)]
                         [i 1])
                        (for-clause ...) 
                        middle-body ...
                        (let ([new-vec (if (eq? i (unsafe-vector*-length vec))
                                           (grow-vector vec)
                                           vec)])
                          (unsafe-vector*-set! new-vec i (let () last-body ...))
                          (values new-vec (unsafe-fx+ i 1))))])
           (shrink-vector vec i))))]
    [(_ #:length length-expr #:fill fill-expr (for-clause ...) body ...)
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
                   [for_/parts for_/parts-stx]
                   [for_/fold/derived for_/fold/derived-stx])
       (syntax/loc stx
         (let ([len length-expr])
           (unless (exact-nonnegative-integer? len)
             (raise-argument-error 'for_/parts "exact-nonnegative-integer?" len))
           (let ([v (make-vector len fill-expr)])
             (unless (zero? len)
               (for_/fold/derived
                orig-stx 
                ([i 0])
                (limited-for-clause ...)
                middle-body ...
                (unsafe-vector*-set! v i (let () last-body ...))
                (unsafe-fx+ 1 i)))
             v))))]
    [(_ #:length length-expr (for-clause ...) body ...)
     (for_/parts #'(fv #:length length-expr #:fill 0 (for-clause ...) body ...) 
                 orig-stx for_/parts-stx for_/fold/derived-stx wrap-all?)]))

(define-syntax (for/parts stx)
  (for_/parts stx stx #'for/parts #'for/fold/derived #f))

(define-syntax (for*/parts stx)
  (for_/parts stx stx #'for*/parts #'for*/fold/derived #t))
