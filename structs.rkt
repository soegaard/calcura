#lang racket/base

(provide (struct-out expr)
         (struct-out form))

(struct expr (hc)              #:transparent) ; hc = hash code
(struct form expr (head parts) #:transparent) ; parts = (vector #f element ...)
