#lang racket

(require redex)
(require "../resugar.rkt")

;;   booleans   (TAPL pg.93)
;;   nats       (TAPL pg.93)
;;   lambda     (TAPL pg.103)

;;   pairs      (TAPL pg.126)
;;   tuples     (TAPL pg.128)
;;   records    (TAPL pg.129)
;;   sums       (TAPL pg.132)
;;   lists      (TAPL pg.147)

(define-resugarable-language data-lang
  #:keywords(if true false succ pred iszero zero
                λ thunk let = : ..
                pair fst snd tuple project record dot inl inr case of =>
                calctype
                Bool Num Pair Tuple Sum Record List ->)
  (e ::= ....)
  (v ::= ....
     ; booleans
     true
     false
     ; numbers
     number
     ; lambda
     (λ (x : t) e))
  (t ::= ....
     Bool
     Num
     (t -> t)
     ; pairs
     (Pair t t)
     ; tuples
     (Tuple t*)
     ; sum
     (Sum t t)
     ; record
     (Record tRec)
     ; list
     (List t)))