#lang racket
;;;
;;; Floating Point Numbers
;;;

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

; A number is real, if it represent a number on the real number line.
; This flonums, bigfloats, fixnums, bigints and rational numbers are all real.
(provide real?)
(define (real? x)
  (or (%real? x) (bigfloat? x)))

; Bigfloats are numbers
(provide number?)
(define (number? x)
  (or (%number? x)
      (bigfloat? x)))

(provide exact?)
(define (exact? x)
  (or (and (%number? x) (%exact? x))
      (bigfloat? x)))

(provide inexact?)
(define (inexact? x)
  (and (%number? x) (%inexact? x)))


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

(define-fun zero?     %zero?     bfzero?      PossibleZeroQ)
(define-fun positive? %positive? bfpositive?  Positive)
(define-fun negative? %negative? bfnegative?  Negative)
(define-fun integer?  %integer?  bfinteger?   IntegerQ)
(define-fun even?     %even?     bfeven?      EvenQ)
(define-fun odd?      %odd?      bfodd?       OddQ)
(define-fun rational? %rational? bfrational?  RationalQ)
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

(provide +)
(define (+ . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap %real? xs)    (%sum xs)]
    [(andmap bigfloat? xs) (apply bf+ xs)]
    [(null? xs)            0]
    [else
     (for/fold ([m (first xs)]) ([x (in-list (rest xs))])
       (cond
         [(%real? x)    (%+ m x)]
         [(bigfloat? x) (%+ m (bigfloat->flonum x))]
         [else (error '+ (~a "number or bigfloat expected, got: " x))]))]))

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



