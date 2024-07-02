#lang racket/base
(provide match2)

;;;
;;; match2 makes an attempt to share work for equivalent patterns
;;;

;; Careful!  Two patterns are "equivalent" if
;;    (equal? (syntax->datum pat1) (syntax->datum pat2))

;; Consider:
;;   (match* ((list 1 2 3) (list 4 5 6))
;;     [(pat1 pat2) 12]
;;     [(pat1 pat3) 13])
;; Here work can be shared by the two `pat1`.

;; We will implement
;;   (match2 ((list 1 2 3) (list 4 5 6))
;;     [(pat1 pat2) 12]
;;     [(pat1 pat3) 13])
;; which expands to
;;   (let ([val1 (list 1 2 3)]
;;         [val2 (list 4 5 6)])
;;     (match val1
;;        [pat1  (match val2
;;                 [pat2 12]
;;                 [pat3 12])])) 

;; But we will rewrite if two patterns "look" the same.
;;   (equal? (syntax->datum #'one-pat) (syntax->datum #'another-pat))
;; This does not work in general, so be careful.

(require (for-syntax racket/base  
                     racket/list
                     racket/syntax
                     syntax/parse))
(require racket/match)

(define-syntax (match2 stx)
  (define (no-matching-clause)
    (syntax/loc stx
      (error 'match2 "no matching clause for ~a and ~a" val1-expr val2-expr)))  
  (syntax-parse stx
    [(_match2 (val1-expr val2-expr) . clauses)
     (syntax/loc stx
       (let* ([val1 val1-expr]
              [val2 val2-expr]
              [clause-error (λ (v1 v2) (error 'match2 "no matching clause for ~a and ~a" v1 v2))])
         (match2-helper (val1 val2) clause-error . clauses)))]))


(define-syntax (match2-helper stx)
  (define (no-matching-clause v1 v2)
    (syntax/loc stx
      (error 'match2 "no matching clause for ~a and ~a" v1 v2)))  
  (syntax-parse stx
    ; v1 and v2 are identifiers
    [(_ (v1 v2) clause-error)                 (syntax/loc stx (clause-error v1 v2))]
    [(_ (v1 v2) clause-error [(p1 p2) expr])  (syntax/loc stx (match* (v1 v2) [(p1 p2) expr]))]
    
    [(_ (v1 v2) clause-error
        [(p1  p2)  expr]
        [(p1s p2s) exprs] ... . clauses)
     (define is-p1?
       (let ([p1-datum (syntax->datum #'p1)])
         (λ (x)
           (equal? p1-datum x))))
     
     (define-values (p1-pats non-p1-pats)
       (splitf-at (syntax->list #'([(p1s p2s) exprs] ...))
                  (λ (x) ; x = #'[(p1s p2s) exprs]
                    (displayln (syntax->datum (car (syntax->list (car (syntax->list x))))))
                    (is-p1? (syntax->datum (car (syntax->list (car (syntax->list x)))))))))

     (displayln p1-pats)
     
     (with-syntax ([ ([(_p1s p2s) exprs] ...) p1-pats]
                   [ non-p1-pats non-p1-pats])
       (syntax/loc stx
         (match v1
           [p1 (match v2
                 [p2 expr]
                 [p2s exprs]
                 ...
                 [_ (clause-error v1 v2)])]          
           [_
            (match2-helper (v1 v2) clause-error . non-p1-pats)])))]))


; This prints 3 times.
#;(match* (1 2)
  [((app println _) 1) 'A]
  [((app println _) 3) 'B]
  [((app println _) 2) 'C])

#;(begin

; This prints only 1.
(match2 (1 2)
  [((app println _) 1) 'A]
  [((app println _) 3) 'B]
  [((app println _) 2) 'C])

(match2 (1 2)
  [(1 1) 'A]
  [(1 2) 'B]
  [(1 3) 'C])

(match2 (2 3)
  [(1 1) 'A]
  [(1 2) 'B]
  [(1 3) 'C]
  [((and (app println _) 2 x) (and 1 y)) (list x y 'D)]
  [((and (app println _) 2 x) (and 2 y)) (list x y 'E)]
  [((and (app println _) 2 x) (and 3 y)) (list x y 'F)])


(match2 ((vector 1 2 3) (vector 1 2 3))
  [((vector 1 2 3) 1)              'A]
  [((vector 1 2 3) (vector 1 2 2)) 'B]
  [((vector x ...) (vector x ...)) 'C])

)
