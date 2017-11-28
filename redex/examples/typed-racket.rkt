#lang typed/racket

; Poor error message
(define-syntax-rule (of-one f) (f "one"))
(of-one add1)
