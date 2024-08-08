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



;; 4.3.2 Generic Numerics
; Most Racket numeric operations work on any kind of number.

(provide +)

(define +
  (case-lambda
    [()     0]
    [(x)    x]
    [(x y)  (cond
              [(bigfloat? x)  
               (cond
                 [(bigfloat? y)              (bf+ x y)]
                 [(or (real? y) (string? y)) (bf+ x (bf y))]
                 [else                       (error '+ (~a "number (bigfloats included) expected, got: " y))])]
              [(bigfloat? y)  
               (cond
                 [(or (real? x) (string? x)) (bf+ (bf x) y)]
                 [else                       (error '+ (~a "number (bigfloats included) expected, got: " x))])]
              [else
               (%+ x y)])]
    [xs (cond
          [(any-inexact? xs)  (apply %+  (map exact->inexact xs))] ; todo: flsum ?
          [(any-bigfloat? xs) (apply bf+ (map bf xs))]
          [else               (apply %+ xs)])]))




; FIX:

; (+ (bf 1) 3)

; And ... fix similar issues for *, -, / etc.

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
    [(_ name %name bfname calcura-name)
     (syntax/loc stx 
       (begin
         (provide name)
         (define (name x)
           ; (displayln (list name x))
           (cond  
             [(%number? x)  (%name x)]
             [(bigfloat? x) (bfname x)]
             [else          (Form 'calcura-name (list x))]))))]))



(define-fun sin %sin bfsin Sin)
(define-fun cos %cos bfcos Cos)
(define-fun tan %tan bftan Tan)

(define-fun asin %asin bfasin ArcSin)
(define-fun acos %acos bfacos ArcCos)
(define-fun atan %atan bfatan ArcTan)

(define-fun sinh %sinh bfsinh Sinh)
(define-fun cosh %cosh bfcosh Cosh)
(define-fun tanh %tanh bftanh Tanh)

(define-fun asinh %asinh bfasinh ArcSinh)
(define-fun acosh %acosh bfacosh ArcCosh)
(define-fun atanh %atanh bfatanh ArcTanh)

(define-fun exp %exp bfexp Exp)
(define-fun ln  %log bflog Log)

(define-fun sqr  %sqr  bfsqr  Sqr)
(define-fun abs  %abs  bfabs  Abs)
(define-fun sgn  %sgn  bfsgn  Sign)
(define-fun sqrt %sqrt bfsqrt Sqrt)

(define-fun infinite? %infinite? bfinfinite?  InfinityQ) ; find correct name: Infinity represents a positive, infinite quantity
(define-fun nan?      %nan?      bfnan?       NaNQ)

(define-fun truncate  %truncate  bftruncate   Truncate)  ; find correct name
(define-fun floor     %floor     bffloor      Floor)
(define-fun ceiling   %ceiling   bfceiling    Ceiling)
(define-fun round     %round     bfround      Round)

; bffrac
; bfrint

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
             [(and (number? x)   (number?   y)) (%name  x y)]
             [(and (bigfloat? x) (bigfloat? y)) (bfname x y)]
             [(and (number? x)   (bigfloat? y)) (name x (bigfloat->flonum y))]
             [(and (bigfloat? x) (number?   y)) (name (bigfloat->flonum x) y)]
             [else (Form 'calcura-name (list x y))]))))]))

(define-fun2 =  %=  bf=  Equal)       ; aka ==
(define-fun2 >  %>  bf>  Greater) 
(define-fun2 <  %<  bf<  Less)
(define-fun2 >= %>= bf>= GreaterEqual)
(define-fun2 <= %<= bf<= LessEqual)

(define-fun2 expt %expt bfexpt Power)

(provide log)
(define (log b [x #f])
  (let ([b (if x b 10)]
        [x (if x x b)])
    (cond
      [(and (number? b) (number? x))
       (cond [(= b 10) (/ (%log x) (%log 10))]
             [(= b  2) (/ (%log x) (%log  2))]
             [else     (/ (%log x) (%log  b))])]
      [(and (bigfloat? b) (bigfloat? x))
       (cond [(bf= b 10.bf) (bflog10 x)]
             [(bf= b  2.bf) (bflog2 x)]
             [else          (bf/ (bflog x) (bflog b))])]
      [(and (number? b) (bigfloat? x))
       (log b (bigfloat->flonum x))]
      [(and (bigfloat? b) (number? x))
       (log (bigfloat->flonum b) x)]
      [else (Form 'Log (list b x))])))

(provide max)
(define (max . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap %real? xs)    (apply %max xs)]
    [(andmap bigfloat? xs) (apply bfmax xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(%real? x)    (%max m x)]
         [(bigfloat? x) (%max m (bigfloat->flonum x))]
         [else (error 'max (~a "number or bigfloat expected, got: " x))]))]))

(provide min)
(define (min . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap %real? xs)    (apply %min xs)]
    [(andmap bigfloat? xs) (apply bfmin xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(%real? x)    (%min m x)]
         [(bigfloat? x) (%min m (bigfloat->flonum x))]
         [else (error 'min (~a "number or bigfloat expected, got: " x))]))]))


(provide *)
(define (* . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap %real? xs)    (apply %* xs)]
    [(andmap bigfloat? xs) (apply bf* xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(%real? x)    (%* m x)]
         [(bigfloat? x) (%* m (bigfloat->flonum x))]
         [else (error '* (~a "number or bigfloat expected, got: " x))]))]))

(provide -)
(define (- . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap %real? xs)    (apply %- xs)]
    [(andmap bigfloat? xs) (apply bf- xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(%real? x)    (%- m x)]
         [(bigfloat? x) (%- m (bigfloat->flonum x))]
         [else (error '- (~a "number or bigfloat expected, got: " x))]))]))

(provide /)
(define (/ . xs)
  (define (->real x) (if (bigfloat? x) (bigfloat->real x) x))
  (cond 
    [(andmap %real? xs)    (apply %/ xs)]
    [(andmap bigfloat? xs) (apply bf/ xs)]
    [else
     (for/fold ([m (->real (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(%real? x)    (%/ m x)]
         [(bigfloat? x) (%/ m (bigfloat->real x))]
         [else (error '/ (~a "number or bigfloat expected, got: " x))]))]))

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


;; ; Conversion from degrees to radians

;; (define (%deg  r)   (*   (/ pi        180.)      r))
;; (define (bfdeg r) (bf* (bf/ pi.bf (bf 180.)) (bf r)))
;; (define-fun deg %deg bfdeg )



