#lang racket

(require redex)

(provide base-syntax)

;; ---------------------------------------------------------------------------------------------------
;; base language

(define-language base-syntax
  (v  ::= unit)
  (vRec ::= ϵ (field x v vRec))
  (e  ::= s x)
  (e* ::= ϵ a (cons e e*))
  (eRec ::= ϵ a (field x e eRec))
  (s  ::= a) ; surface lang
  (s* ::= ϵ a (cons s s*))
  (sRec ::= ϵ a (field x s sRec))
  (t  ::= x)
  (t* ::= ϵ x (cons t t*))
  (tRec ::= ϵ x (field x t tRec))
  (Γ ::= [(x : t) ...])
  (a ::= (variable-prefix ~))
  (x ::= variable-not-otherwise-mentioned)
  (premise ::=
     premise/judgement
     premise/equation
     (assumption any))
  (premise/judgement ::=  (Γ ⊢ s : t))
  (premise/equation ::=
                    (t = t)
                    (t* = t*)
                    (tRec = tRec)))

(caching-enabled? #f)

; NOTE:
; type inference is necessary because:
;   (Γ ⊢ (atom a) : A
;   (Γ ⊢ 0 : Nat
;   [A = Nat -> ??]
;   ----------------------
;   (Γ ⊢ ((atom a) 0) : ??)
