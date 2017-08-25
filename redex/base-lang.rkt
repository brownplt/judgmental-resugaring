#lang racket

(require redex)
(require "unify.rkt")

(provide base-syntax)

; NOTE:
; type inference is necessary because:
;   (Γ ⊢ (atom a) : A
;   (Γ ⊢ 0 : Nat
;   [A = Nat -> ??]
;   ----------------------
;   (Γ ⊢ ((atom a) 0) : ??)


;; ---------------------------------------------------------------------------------------------------
;; base language

(define-language base-syntax
  (e ::=
     a
     x)
  (t ::= x)
  (Γ ::= [(x : t) ...])
  (a ::= (variable-prefix ~))
  (x ::= variable-not-otherwise-mentioned)
  (c ::=
     j
     q
     (assumption any))
  (j ::=  (Γ ⊢ x : t))
  (q ::= (t = t)))

(caching-enabled? #f)
