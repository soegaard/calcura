#lang racket/base
(provide
 vector-index-where              ; Like (index-where lst proc) but for vectors.
 vector-index-where-prefix-ends  ; 
 span-indices                    ; Computes spans of vector where the elements are the same according to a predicate.
 collect-vector)                 ; Collects elements into a vector.
 

;;;
;;; Vector Utilities
;;; 

;; This file contains general utilities for working with Racket vectors.

;;;
;;; Index related
;;;

; (vector-index-where vec proc)
;   Like (index-where lst proc) but for vectors.
(define (vector-index-where proc vec [start 0])
  (for/first ([x (in-vector vec)]
              [i (in-naturals start)]
              #:when (proc x))
    i))

;;;
;;; Prefixes
;;; 

; (vector-index-where-prefix-ends vec proc)
;   The vector `vec` has a prefix of elements that fulfill `proc`.
;   Return the index where the prefix ends.
(define (vector-index-where-prefix-ends proc vec [start 0] [end (vector-length vec)] [step 1])
  (or (for/first ([x (in-vector vec start end step)]
                  [i (in-naturals start)]
                  #:when (not (proc x)))
        (+ start (* (- i start) step)))
      end))


;;;
;;; Partitioning
;;;

; (span-indices vec start same?)
;   Computes spans of `vec` where the elements are the same according to `same?`.
;   The spans are returned as list of pairs of the form (cons span-start span-length).

; > (span-indices (vector 1 1 1  2 2 2 2  3 3 3 3 3) 0 equal?)
; '((0 . 3) (3 . 4) (7 . 5))

(define (span-indices vec start same?)
  (define n (vector-length vec))
  (unless (<= start n)
    (raise-arguments-error 'span-indices 
                           "start must less than or equal to the vector length" "start" start))
  (define (make-span start length)
    (cons start length))

  (cond
    [(= n start)       '()]
    [(= n (+ start 1)) (list (make-span start 1))]
    [else              (let loop ([spans       '()]
                                  [span-start  start]
                                  [span-length 1]
                                  [span-first  (vector-ref vec start)]
                                  [i           (+ start 1)])
                         (cond
                           [(= i n) (reverse (cons (make-span span-start span-length) spans))]
                           [else    (define cur (vector-ref vec i))
                                    (if (same? span-first cur)
                                        ; extend existing span
                                        (loop spans span-start (+ span-length 1) span-first (+ i 1))
                                        ; add existing span and start new
                                        (loop (cons (make-span span-start span-length) spans)
                                              i 1 cur (+ i 1)))]))]))

;;;
;;; Collecting
;;;

(define (grow-vector vec)
  ; double the size
  (define n (vector-length vec))
  (define new-vec (make-vector (* 2 n)))
  (vector-copy! new-vec 0 vec 0 n)
  new-vec)

(define (shrink-vector vec i)
  ; shrink length to `i`
  (define new-vec (make-vector i))
  (vector-copy! new-vec 0 vec 0 i)
  new-vec)

(define (grow-vector/fill vec fill)
  (define n (vector-length vec))
  (define new-vec (make-vector (* 2 n) fill))
  (vector-copy! new-vec 0 vec 0 n)
  new-vec)

(define (grow-init-vector init-vec start fill)
  ; make sure `start` is a valid index 
  (if (< (vector-length init-vec) start)
      (grow-init-vector (grow-vector/fill init-vec fill) start fill)
      init-vec))

(define (collect-vector f
                        #:start  [start          0]
                        #:fill   [fill           0]
                        #:length [initial-length 8]
                        #:into   [initial-vector (make-vector initial-length fill)])
  ; The function `f` takes one arguments:
  ;   - a function `collect` that adds an element to the elements collected so far

  ; Note: The vector passed to `#:into` is only returned as the result,
  ;       if the collected elements happen to fit in the vector.
  ;       That is, think of the #:into option as "*attempt* to collect the
  ;       elements into an existing vector".
  (unless (vector? initial-vector)
    (raise-arguments-error 'collect-vector "expected a vector for #:into" "into-vector" initial-vector))
  (unless (and (exact-integer? initial-length) (>= initial-length 0))
    (raise-arguments-error 'collect-vector "expected a non-negative, exact intege for #:length" "into-length" initial-length))
  (unless (and (exact-integer? start) (>= start 0))
    (raise-arguments-error 'collect-vector "expected a non-negative, exact integer" "start" start))
  
  (define vec (grow-init-vector initial-vector start fill))
  (define n   (vector-length vec))
  (define i   start)
  
  (define (collect x)
    (cond
      [(< i n) (vector-set! vec i x)
               (set! i (+ i 1))]
      [else    (set! vec (grow-vector vec))
               (set! n (* 2 n))
               (collect x)]))

  (define (done)
    (shrink-vector vec i))

  (f collect)
  (done))

;;;
;;; Test
;;;

;; All results are expected to give the result #t. 


#;(begin
  (define (evens vec)
    (collect-vector (λ (collect)
                      (for ([x (in-vector vec)] #:when (even? x))
                        (collect x)))))
  

  (define (evens* vec)
    (collect-vector (λ (collect)
                      (for ([x (in-vector vec)] #:when (even? x))
                        (for ([_ x])
                          (collect x))))))

  (define (make-evens n)
    ; Using `#:length n` has the effect that the vector collected into is never resized.
    (collect-vector #:length n 
                    (λ (collect)
                      (for ([i n])
                        (collect (* 2 i))))))

  (define (make-odds n vec start)
    ; Using `#:into initial-vector` overwrites the elements from start and later
    (collect-vector #:into  vec  
                    #:start start
                    (λ (collect)
                      (for ([i (- n start)])
                        (collect (+ (* 2 i) 1))))))
  

  (list (list 'span-indices (list (equal? (span-indices (vector 1 1 1  2 2 2 2  3 3 3 3 3) 0 equal?)
                                          '((0 . 3) (3 . 4) (7 . 5)))
                                  (equal? (span-indices (vector 1 1 1  2 2 2 2  3 3 3 3 3) 1 equal?)
                                          '((1 . 2) (3 . 4) (7 . 5)))
                                  (equal? (span-indices (vector 1 1 1  2 2 2 2  3 3 3 3 3) 3 equal?)
                                          '((3 . 4) (7 . 5)))
                                  (equal? (span-indices (vector 1 1 1  2 2 2 2  3 3 3 3 3) 4 equal?)
                                          '((4 . 3) (7 . 5)))
                                  (equal? (span-indices (vector 1 1 1) 2 equal?)
                                          '((2 . 1)))
                                  (equal? (span-indices (vector 1 1 1) 3 equal?)
                                          '())))
        
        (list 'evens        (list (equal? (evens (vector 1 2 3 4 5 6 7 8 9 10))
                                         '#(2 4 6 8 10))))
        (list 'evens*       (list (equal? (evens* (vector 1 2 3 4))
                                         '#(2 2 4 4 4 4))))
        (list 'make-evens   (list (equal? (make-evens 4)
                                         '#(0 2 4 6))))
        (list 'make-odss    (list (equal? (make-odds 10 (make-evens 10) 5)
                                          '#(0 2 4 6 8 1 3 5 7 9))))))


