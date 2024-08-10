#lang racket
;;;
;;; Big Float Racket (BFRacket)
;;;

; The goal of this module is to extend Racket with a new number type: bigfloat.

; Importing this module will replace all standard mathematical functions
; with versions that know about bigfloats.


;; 4.3 Numbers

;; All numbers are complex numbers. Some of them are real numbers, and
;; all of the real numbers that can be represented are also rational
;; numbers, except for +inf.0 (positive infinity), +inf.f
;; (single-precision variant, when enabled via read-single-flonum),
;; -inf.0 (negative infinity), -inf.f (single-precision variant, when
;; enabled), +nan.0 (not-a-number), and +nan.f (single-precision variant,
;; when enabled). Among the rational numbers, some are integers, because
;; round applied to the number produces the same number.

;; Changes: Big floats are real numbers.
;;          Some big floats like +inf.bf are not rational.


;; 4.3.1 Number Types


; Bigfloats are numbers
(provide number?)
(define (number? x)
  (or (%number? x)
      (bigfloat? x)))

; All numbers are complex numbers.
(provide complex?)
(define (complex? x)
  (number? x))

; A number is real, if it represent a number on the real number line.
; This flonums, bigfloats, fixnums, bigints and rational numbers are all real.
; Note: Flonums such as +inf.0 are also real numbers.
(provide real?)
(define (real? x)
  (or (%real? x)
      (bigfloat? x)))

(provide rational?)
(define (rational? x)
  (or (%rational? x)
      (bfrational? x)))

(provide integer?)
; Number like 2.0 and 2.0.bf also represent integers.
(define (integer? x)
  (or (%integer?  x)
      (bfinteger? x)))

(provide exact-integer?)
(define (exact-integer? x)
  (or (%exact-integer?  x)
      (bfinteger? x)))

(provide exact-nonnegative-integer?)
(define (exact-nonnegative-integer? x)
  (or (%exact-nonnegative-integer?  x)
      (and (bfinteger? x)
           (bf>= x 0.bf))))

(provide exact-positive-integer?)
(define (exact-positive-integer? x)
  (or (%exact-positive-integer?  x)
      (and (bfinteger? x)
           (bf> x 0.bf))))

; Since bigfloats are exact, inexact-real? is unchanged.
(provide (rename-out [%inexact-real? inexact-real?]))

; Big floats are not fixnums, so fixnum? is unchanged.
(provide (rename-out [%fixnum?        fixnum?]
                     [%flonum?        flonum?]
                     [%double-flonum? double-flonum?]
                     [%single-flonum? single-flonum?]
                     
                     [%single-flonum-available? single-flonum-available?]))

(provide zero?)
(define (zero? x)
  (or (and (%number? x)  (%zero? x))
      (and (bigfloat? x) (bfzero? x))))

(provide positive?)
(define (positive? x)
  (or (and (%number? x)  (%positive? x))
      (and (bigfloat? x) (bfpositive? x))))

(provide negative?)
(define (negative? x)
  (or (and (%number? x)  (%negative? x))
      (and (bigfloat? x) (bfnegative? x))))

(provide even?)
(define (even? x)
  (or (and (%number? x)  (%even? x))
      (and (bigfloat? x) (bfeven? x))))

(provide odd?)
(define (odd? x)
  (or (and (%number? x)  (%odd? x))
      (and (bigfloat? x) (bfodd? x))))


(provide exact?)
(define (exact? x)
  (or (and (%number? x) (%exact? x))
      (bigfloat? x)))

(provide inexact?)
(define (inexact? x)
  (and (%number? x) (%inexact? x)))

(provide inexact->exact)
(define (inexact->exact x)
  (cond
    [(bigfloat? x) (if (bfrational? x)
                       x
                       (error 'inexact->exact (~a "no exact representation for " x)))]
    [else          (%inexact->exact x)]))

(provide exact->inexact)
(define (exact->inexact x)
  (cond
    [(%number? x)  (%exact->inexact x)]
    [(bigfloat? x) (bigfloat->flonum x)]
    [else          (raise-arguments-error 'exact->inexact
                                          "expected a number (bigfloats included)"
                                          "x" x)]))
                                          
(provide (rename-out [%real->single-flonum real->single-flonum]
                     [%real->double-flonum real->double-flonum]))


;; Helpers

(define (any-bigfloat? xs)
  (for/or ([x (in-list xs)])
    (bigfloat? x)))

(define (all-bigfloat? xs)
  (for/and ([x (in-list xs)])
    (bigfloat? x)))

(define (any-inexact? xs)
  (for/or ([x (in-list xs)])
    (inexact? x)))

(define (all-inexact? xs)
  (for/and ([x (in-list xs)])
    (inexact? x)))

(define (to-bf x)
  (if (bigfloat? x)
      x
      (bf x)))


;; 4.3.2 Generic Numerics

; Most Racket numeric operations work on any kind of number.

; If inexact numbers are part of the input, then the result is inexact.
; If there are bigfloats in the input (and no inexact numbers),
; then the result is a bigfloat.


(provide +)
(define +
  (case-lambda
    [()     0]
    [(x)    x]
    [(x y)  (cond
              [(inexact? x)
               (cond
                 [(inexact? y)  (%+ x y)]
                 [(bigfloat? y) (%+ x (bigfloat->flonum y))]
                 [else          (%+ x y)])]
              [(inexact? y)
               (cond                 
                 [(bigfloat? x) (%+ (bigfloat->flonum x) y)]
                 [else          (%+ x y)])]
              ; Now: None of x and y are inexact
              [(bigfloat? x)
               (cond
                 [(bigfloat? y)              (bf+ x y)]
                 [(or (real? y) (string? y)) (bf+ x (bf y))]
                 [else                       (error '+ (~a "number (bigfloats included) expected, got: " y))])]
              [(bigfloat? y)  
               (cond
                 [(or (real? x) (string? x)) (bf+ (bf x) y)]
                 [else                       (error '+ (~a "number (bigfloats included) expected, got: " x))])]
              ; Now: Neither x or y are inexact or big floats.
              [else
               (%+ x y)])]
    [xs
     (cond
       [(any-inexact? xs)  (apply %+  (map exact->inexact xs))] ; todo: flsum ?
       [(any-bigfloat? xs) (apply bf+ (map to-bf xs))]
       [else               (apply %+ xs)])]))

(provide *)
(define *
  (case-lambda
    [()     1]
    [(x)    x]
    [(x y)  (cond
              [(inexact? x)
               (cond
                 [(inexact? y)  (%* x y)]
                 [(bigfloat? y) (%* x (bigfloat->flonum y))]
                 [else          (%* x y)])]
              [(inexact? y)
               (cond                 
                 [(bigfloat? x) (%* (bigfloat->flonum x) y)]
                 [else          (%* x y)])]
              ; Now: None of x and y are inexact
              [(bigfloat? x)
               (cond
                 [(bigfloat? y)              (bf* x y)]
                 [(or (real? y) (string? y)) (bf* x (bf y))]
                 [else                       (error '* (~a "number (bigfloats included) expected, got: " y))])]
              [(bigfloat? y)  
               (cond
                 [(or (real? x) (string? x)) (bf* (bf x) y)]
                 [else                       (error '* (~a "number (bigfloats included) expected, got: " x))])]
              ; Now: Neither x or y are inexact or big floats.
              [else
               (%* x y)])]
    [xs
     (cond
       [(any-inexact? xs)  (apply %*  (map exact->inexact xs))]
       [(any-bigfloat? xs) (apply bf* (map to-bf xs))]
       [else               (apply %* xs)])]))


(provide -)
(define -
  (case-lambda
    [(x)    (if (bigfloat? x) (bf- x) (%- x))]
    [(x y)  (cond
              [(inexact? x)
               (cond
                 [(inexact? y)  (%- x y)]
                 [(bigfloat? y) (%- x (bigfloat->flonum y))]
                 [else          (%- x y)])]
              [(inexact? y)
               (cond                 
                 [(bigfloat? x) (%- (bigfloat->flonum x) y)]
                 [else          (%- x y)])]
              ; Now: None of x and y are inexact
              [(bigfloat? x)
               (cond
                 [(bigfloat? y)              (bf- x y)]
                 [(or (real? y) (string? y)) (bf- x (bf y))]
                 [else                       (error '- (~a "number (bigfloats included) expected, got: " y))])]
              [(bigfloat? y)  
               (cond
                 [(or (real? x) (string? x)) (bf- (bf x) y)]
                 [else                       (error '- (~a "number (bigfloats included) expected, got: " x))])]
              ; Now: Neither x or y are inexact or big floats.
              [else
               (%- x y)])]
    [xs
     (cond
       [(any-inexact? xs)  (apply %-  (map exact->inexact xs))] ; todo: flsum ?
       [(any-bigfloat? xs) (apply bf- (map to-bf xs))]
       [else               (apply %- xs)])]))

(provide /)
(define /
  (case-lambda
    [(x)    (if (bigfloat? x) (bf/ x) (%/ x))]
    [(x y)  (cond
              [(inexact? x)
               (cond
                 [(inexact? y)  (%/ x y)]
                 [(bigfloat? y) (%/ x (bigfloat->flonum y))]
                 [else          (%/ x y)])]
              [(inexact? y)
               (cond                 
                 [(bigfloat? x) (%/ (bigfloat->flonum x) y)]
                 [else          (%/ x y)])]
              ; Now: None of x and y are inexact
              [(bigfloat? x)
               (cond
                 [(bigfloat? y)              (bf/ x y)]
                 [(or (real? y) (string? y)) (bf/ x (bf y))]
                 [else                       (error '/ (~a "number (bigfloats included) expected, got: " y))])]
              [(bigfloat? y)  
               (cond
                 [(or (real? x) (string? x)) (bf/ (bf x) y)]
                 [else                       (error '/ (~a "number (bigfloats included) expected, got: " x))])]
              ; Now: Neither x or y are inexact or big floats.
              [else
               (%/ x y)])]
    [xs
     (cond
       [(any-inexact? xs)  (apply %/  (map exact->inexact xs))] ; todo: flsum ?
       [(any-bigfloat? xs) (apply bf/ (map to-bf xs))]
       [else               (apply %/ xs)])]))


(provide quotient)
(define (quotient n m)
  (unless (and (integer? n) (integer? m))
    (error 'quotient "expected two integers"))
  (let ([N (if (bigfloat? n) (bigfloat->integer n) n)]
        [M (if (bigfloat? m) (bigfloat->integer m) m)])
    (define q (%quotient N M))
    (cond
      [(inexact? q)                         q]
      [(or (bigfloat? n) (bigfloat? m)) (bf q)]
      [else                                 q])))

(provide remainder)
(define (remainder n m)
  (unless (and (integer? n) (integer? m))
    (error 'remainder "expected two integers"))
  (let ([N (if (bigfloat? n) (bigfloat->integer n) n)]
        [M (if (bigfloat? m) (bigfloat->integer m) m)])
    (define r (%remainder N M))
    (cond
      [(inexact? r)                         r]
      [(or (bigfloat? n) (bigfloat? m)) (bf r)]
      [else                                 r])))

(provide quotient/remainder)
(define (quotient/remainder n m)
  (unless (and (integer? n) (integer? m))
    (error 'quotient/remainder "expected two integers"))
  (let ([N (if (bigfloat? n) (bigfloat->integer n) n)]
        [M (if (bigfloat? m) (bigfloat->integer m) m)])
    (define-values (q r) (%quotient/remainder N M))
    (define Q
      (cond
        [(inexact? q)                         q]
        [(or (bigfloat? n) (bigfloat? m)) (bf q)]
        [else                                 q]))
    (define R
      (cond
        [(inexact? r)                         r]
        [(or (bigfloat? n) (bigfloat? m)) (bf r)]
        [else                                 r]))
    (values Q R)))

(provide modulo)
(define (modulo n m)
  (unless (and (integer? n) (integer? m))
    (error 'modulo "expected two integers"))
  (let ([N (if (bigfloat? n) (bigfloat->integer n) n)]
        [M (if (bigfloat? m) (bigfloat->integer m) m)])
    (define r (%modulo N M))
    (cond
      [(inexact? r)                         r]
      [(or (bigfloat? n) (bigfloat? m)) (bf r)]
      [else                                 r])))


; Both flonums and big floats are considered real numbers.
; The form 
;     (define-syn sin %sin bfsin)
; where %sin  is the standard sin function from `racket`
; and   bfsin is the big float version of sine
; defines a function `sin` that handles both floating point and big floats.

(require math/bigfloat math/flonum (prefix-in % racket) (prefix-in % math/base))
(require "core-forms.rkt")

(define-syntax (define-fun stx)
  (syntax-case stx ()
    [(_ name %name bfname _)
     (syntax/loc stx 
       (begin
         (provide name)
         (define (name x)
           ; (displayln (list name x))
           (cond  
             [(%number? x)  (%name x)]
             [(bigfloat? x) (bfname x)]
             [else          (error 'name (~a "expected a number (bigfloat included), got:" x))]))))]))

(define (bfadd1 x) (bf+ x 1.bf))
(define (bfsub1 x) (bf- x 1.bf))

(define-fun add1 %add1 bfadd1 Add1)
(define-fun sub1 %sub1 bfsub1 Sub1)

(define-fun abs  %abs  bfabs  Abs)

(define-fun sgn  %sgn  bfsgn  Sign)

; max
; min
; gcd
; lcm

(define-fun round     %round     bfround      Round)
(define-fun floor     %floor     bffloor      Floor)
(define-fun ceiling   %ceiling   bfceiling    Ceiling)
(define-fun truncate  %truncate  bftruncate   Truncate)  ; find correct name

(provide numerator)
(define (numerator x) ; this follows Maxima and MMA 
  (if (or (number? x) (bigfloat? x))
      (if (or (bigfloat? x) (inexact? x))
          x
          (%numerator x))
      (error 'numerator (~a "number or bigfloat expected, got: " x))))

(provide denominator)
(define (denominator x) ; this follows Maxima and MMA
  (if (or (number? x) (bigfloat? x))
      (if (or (bigfloat? x) (inexact? x))
          1
          (%denominator x))
      (error 'denominator (~a "number or bigfloat expected, got: " x))))

(provide rationalize)
(define (rationalize x tolerance)
  (define X (if (bigfloat? x)
                (bigfloat->rational x)
                x))
  (%rationalize X tolerance))

;;; 4.3.2.2 Number comparison

(define-syntax (define-fun2 stx)
  (syntax-case stx ()
    #;[(_ name %name bfname)
     (syntax/loc stx 
       (define-fun2 name %name bfname name))]
    [(_ name %name bfname calcura-name)
     (syntax/loc stx 
       (begin
         (provide name)
         (define (name x y)
           ; (displayln (list 'name x y))
           (cond  
             [(and (%number? x)  (%number?   y)) (%name  x y)]
             [(and (bigfloat? x) (bigfloat? y))  (bfname x y)]
             [(and (%number? x)  (bigfloat? y))  (name (bf x) y)]
             [(and (bigfloat? x) (%number?   y)) (name x (bf y))]
             [else (error 'name (~a "expected two numbers (including bigfloats), got: " x " , " y))]))))]))

; TODO: nary versions ...
(define-fun2 =  %=  bf=  Equal)       ; aka ==
(define-fun2 >  %>  bf>  Greater) 
(define-fun2 <  %<  bf<  Less)
(define-fun2 >= %>= bf>= GreaterEqual)
(define-fun2 <= %<= bf<= LessEqual)

;;; 4.3.2.3 Powers and Roots

(define-fun sqrt %sqrt bfsqrt Sqrt)

(provide integer-sqrt)
(define (integer-sqrt x)
  (unless (integer? x)
    (error 'integer-sqrt (~a "expected an integer, got: " x)))
  (define X (if (bigfloat? x) (bigfloat->integer x) x))
  (define is (%integer-sqrt X))
  (if (bigfloat? x) (bf is) is))

(provide integer-sqrt/remainder)
(define (integer-sqrt/remainder x)
  (unless (integer? x)
    (error 'integer/remainder-sqrt (~a "expected an integer, got: " x)))
  (define X (if (bigfloat? x) (bigfloat->integer x) x))
  (define-values (is r) (%integer-sqrt/remainder X))
  (define IS (if (and (bigfloat? x) (real? is)) (bf is) is))
  (define R  (if (bigfloat? x) (bf r)  r))
  (values IS R))

(define-fun2 expt %expt bfexpt Power)

(define-fun sqr  %sqr  bfsqr   Sqr)

(define-fun exp %exp bfexp Exp)
(define-fun ln  %log bflog Log)

(provide log)
; (log x)   ; b = 10
; (log b x)
(define (log b [x #f]) ; this doesn't follow Racket
  (let ([b (if x b #f)]
        [x (if x x b)])
    (cond
      [(not b)
       ; single argument: natural logarithm
       (cond
         [(%number?  x) (fllog x)]
         [(bigfloat? x) (bflog x)]
         [else          (log x)])]
      [else
       (cond
         [(and (%number? b) (%number? x))
          (cond [(= b 10) (/ (%log x) (%log 10))]
                [(= b  2) (/ (%log x) (%log  2))]
                [else     (/ (%log x) (%log  b))])]
         [(and (bigfloat? b) (bigfloat? x))
          (cond [(bf= b 10.bf) (bflog10 x)]
                [(bf= b  2.bf) (bflog2 x)]
                [else          (bf/ (bflog x) (bflog b))])]
         [(and (%number? b) (bigfloat? x))
          (bf/ (bflog x)
               (bflog (bf b)))]
         [(and (bigfloat? b) (%number? x))
          (bf/ (bflog (bf x))
               (bflog b))]
         [else (error 'log "expected one or two numbers (including bigfloats)")])])))

;;; 4.3.2.4 Trigonometric Functions

(define-fun sin %sin bfsin Sin)
(define-fun cos %cos bfcos Cos)
(define-fun tan %tan bftan Tan)

(define-fun asin %asin bfasin ArcSin)
(define-fun acos %acos bfacos ArcCos)
(define-fun atan %atan bfatan ArcTan)

;;; Hyperbolic Functions

(define-fun sinh %sinh bfsinh Sinh)
(define-fun cosh %cosh bfcosh Cosh)
(define-fun tanh %tanh bftanh Tanh)

(define-fun asinh %asinh bfasinh ArcSinh)
(define-fun acosh %acosh bfacosh ArcCosh)
(define-fun atanh %atanh bfatanh ArcTanh)



(define-fun infinite? %infinite? bfinfinite?  InfinityQ) ; find correct name: Infinity represents a positive, infinite quantity
(define-fun nan?      %nan?      bfnan?       NaNQ)


; bffrac
; bfrint

(provide max)
(define (max . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap %real? xs)    (apply %max xs)]
    [(andmap bigfloat? xs) (apply bfmax xs)]
    [else
     (for/fold ([m (first xs)])
               ([x (in-list (rest xs))])
       (cond
         [(inexact? m)  (if (bigfloat? x)
                            (%max m (bigfloat->flonum x))
                            (%max m x))]
         [(bigfloat? m) (if (inexact? x)
                            (%max (bigfloat->flonum m) x)
                            (bfmax m (bf x)))]
         [(%number? m)  (if (bigfloat? x)
                            (bfmax (bf m) x)
                            (%max m x))]
         [else 'max "internal error"]))]))

(provide min)
(define (min . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap %real? xs)    (apply %min xs)]
    [(andmap bigfloat? xs) (apply bfmin xs)]
    [else
     (for/fold ([m (first xs)])
               ([x (in-list (rest xs))])
       (cond
         [(inexact? m)  (if (bigfloat? x)
                            (%min m (bigfloat->flonum x))
                            (%min m x))]
         [(bigfloat? m) (if (inexact? x)
                            (%min (bigfloat->flonum m) x)
                            (bfmin m (bf x)))]
         [(%number? m)  (if (bigfloat? x)
                            (bfmin (bf m) x)
                            (%min m x))]
         [else 'min "internal error"]))]))


;; ; Conversion from degrees to radians

;; (define (%deg  r)   (*   (/ pi        180.)      r))
;; (define (bfdeg r) (bf* (bf/ pi.bf (bf 180.)) (bf r)))
;; (define-fun deg %deg bfdeg )


;;;
;;; Tests
;;;

#;(list "+"
      (and  (equal? (+)      0)
            (equal? (+ 1)    1)
            (equal? (+ 1.)   1.)
            (equal? (+ 1.bf) 1.bf)

            (equal? (+ 1. 2.)    3.)
            (equal? (+ 1. 2)     3.)
            (equal? (+ 1. 2.bf)  3.)
            (equal? (+ 1. 2.bf)  3.)

            (equal? (+ 2.   1.)  3.)
            (equal? (+ 2    1.)  3.)
            (equal? (+ 2.bf 1.)  3.)
            (equal? (+ 2.bf 1.)  3.)

            (equal? (+ 1 2.   3)   6.)
            (equal? (+ 1 2.bf 3)   6.bf))
      "*"
      (and  (equal? (*)      1)
            (equal? (* 1)    1)
            (equal? (* 1.)   1.)
            (equal? (* 1.bf) 1.bf)

            (equal? (* 1.   2.)    2.)
            (equal? (* 1.   2)     2.)
            (equal? (* 1.   2.bf)  2.)            
            (equal? (* 1    2.bf)  2.bf)
            (equal? (* 1.bf 2)     2.bf)
            (equal? (* 1.bf 2.bf)  2.bf)
            (equal? (* 1    2)     2)            

            (equal? (* 2.   1.)  2.)
            (equal? (* 2    1.)  2.)
            (equal? (* 2.bf 1.)  2.)
            (equal? (* 2.bf 1.)  2.)

            (equal? (* 1 2.   3)   6.)
            (equal? (* 1 2.bf 3)   6.bf))

      "unary -"
      (and (equal? (- 1.)   -1.)
           (equal? (- 1)    -1)
           (equal? (- 1.bf) -1.bf))
      "binary -"
      (and (equal? (- 2.   1.)   1.)
           (equal? (- 2.   1)    1.)
           (equal? (- 2    1.)   1.)
           (equal? (- 2.bf 1.)   1.)
           (equal? (- 2.   1.bf) 1.)
           (equal? (- 2.bf 1.bf) 1.bf)
           (equal? (- 2.bf 1)    1.bf)
           (equal? (- 2    1.bf) 1.bf)
           (equal? (- 2    1)    1))
      "nary -"
      (and (equal? (- 5.   1.   2.)   2.)
           (equal? (- 5.   1    2.)   2.)
           (equal? (- 5    1.   2.)   2.)
           (equal? (- 5.bf 1.   2.)   2.)
           (equal? (- 5.   1.bf 2.)   2.)
           (equal? (- 5.bf 1.bf 2.)   2.)
           (equal? (- 5.bf 1    2.)   2.)
           (equal? (- 5    1.bf 2.)   2.)
           (equal? (- 5    1    2.)   2.))
      (and (equal? (- 5.   1.   2.bf)   2.)
           (equal? (- 5.   1    2.bf)   2.)
           (equal? (- 5    1.   2.bf)   2.)
           (equal? (- 5.bf 1.   2.bf)   2.)
           (equal? (- 5.   1.bf 2.bf)   2.)
           (equal? (- 5.bf 1.bf 2.bf)   2.bf)
           (equal? (- 5.bf 1    2.bf)   2.bf)
           (equal? (- 5    1.bf 2.bf)   2.bf)
           (equal? (- 5    1    2.bf)   2.bf)
           (equal? (- 5    1    2)      2))
      "max"
      (and (equal? (max 3 5  7.bf) 7.bf)
           (equal? (max 3 5. 7.bf) 7.))
      )
