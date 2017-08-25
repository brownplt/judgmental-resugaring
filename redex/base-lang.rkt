#lang racket

(require redex)
(require "unify.rkt")

(provide base-syntax)


;; ---------------------------------------------------------------------------------------------------
;; base language

(define-language base-syntax
  (e ::=
     (atom x)
     v
     x)
  (v ::= undef)
  (x ::= variable-not-otherwise-mentioned)
  (t ::= x)
  (Γ ::= [(x : t) ...])
  (c ::=
     j
     q
     (assumption any))
  (j ::=  (Γ ⊢ x : t))
  (q ::= (t = t)))
