#lang racket/base
;;;
;;; Double Factorial
;;;

; The double factorial of a non-negative integer n,
; is the product of the whole numbers up to n that
; has the same parity as n.

; Thus,
;   6!! = 2 * 4 * 6 = 48
;   5!! = 1 * 3 * 5 = 15

; https://en.wikipedia.org/wiki/Double_factorial

(require racket/format
         racket/math
         math/number-theory
         math/special-functions)

(provide double-factorial)

(define (double-factorial n)
  (cond
    [(= n 0)      1]
    [(integer? n) (let ([n (if (inexact? n) (inexact->exact n) n)])
                    (cond
                      [(< n 0)  (if (even? n)
                                    'ComplexInfinity
                                    (/ (* (expt -1 (/ (- n 1) 2)) n)
                                       (double-factorial (- n))))]
                      [(even? n) (define k (/ n 2))
                                 (* (expt 2 k) (factorial k))]
                      [(odd?  n) (define k (/ (+ n 1) 2))
                                 (/ (factorial n)
                                    (* (expt 2 (- k 1)) (factorial (- k 1))))]))]
    [else
     (error 'double-factorial (~a "got: " n))]
     ; Wikipedia has this formula, but Mathematica disagrees.
     #; (* (sqrt (/ 2 pi))
           (expt 2 (/ n 2))
           (gamma (+ (/ n 2) 1)))))

;;;
;;; Tests
;;;

(list "Double Factorial"
      (and (equal? (double-factorial  0)  1)
           (equal? (double-factorial  1)  1)
           (equal? (double-factorial  2)  2)
           (equal? (double-factorial  3)  3)
           (equal? (double-factorial  4)  8)
           (equal? (double-factorial  5) 15)
           (equal? (double-factorial -1)  1)
           (equal? (double-factorial -2)  'ComplexInfinity)
           (equal? (double-factorial -3)  -1)
           (equal? (double-factorial -4)  'ComplexInfinity)
           (equal? (double-factorial -5) 1/3)))
    

  
    
    
    

