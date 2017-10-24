#lang racket

(require redex)

(provide base-syntax)

;; ---------------------------------------------------------------------------------------------------
;; base language

(define-language base-syntax
  (e  ::= s x)
  (e* ::= ϵ a (cons e e*))
  (s  ::= a) ; surface lang
  (s* ::= ϵ a (cons s s*))
  (t  ::= x)
  (t* ::= ϵ x (cons t t*))
  (Γ ::= [(x : t) ...])
  (a ::= (variable-prefix ~))
  (x ::= variable-not-otherwise-mentioned)
  (premise ::=
     premise/judgement
     premise/equation
     (assumption any))
  (premise/judgement ::=  (Γ ⊢ s : t))
  (premise/equation ::= (t = t)))

(caching-enabled? #f)

; NOTE:
; type inference is necessary because:
;   (Γ ⊢ (atom a) : A
;   (Γ ⊢ 0 : Nat
;   [A = Nat -> ??]
;   ----------------------
;   (Γ ⊢ ((atom a) 0) : ??)
