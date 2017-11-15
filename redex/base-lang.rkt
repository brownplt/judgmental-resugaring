#lang racket

(require redex)

(provide base-syntax debug)

;; ---------------------------------------------------------------------------------------------------
;; base language

(define-language base-syntax
  (v  ::= unit)
  (vRec ::= ϵ (field x v vRec))
  (e  ::= s x v
      (calctype e as t in e)
      (calctype* e* as t* in e))
  (e* ::= ϵ a (cons e e*))
  (eRec ::= ϵ a (field x e eRec))
  (s  ::= a) ; surface lang
  (s* ::= ϵ a (cons s s*))
  (sRec ::= ϵ a (field x s sRec))
  (t  ::= x)
  (t* ::= ϵ x (cons t t*))
  (tRec ::= ϵ x (field x t tRec))
  (Γ ::= ϵ x (bind x t Γ) (bind* x* t* Γ))
  (a ::= (variable-prefix ~))
  (x ::= variable-not-otherwise-mentioned)
  (x* ::= ϵ x (cons x x*))
  (premise ::=
     premise/judgement
     premise/equation
     premise/subtype
     (assumption any))
  (premise/judgement ::=  (Γ ⊢ s : t) (Γ ⊢* s : t))
  (premise/equation ::=
                    (t = t)
                    (t* = t*)
                    (Γ = Γ)
                    (tRec = tRec))
  (premise/subtype ::=
                   (t ⋖ t)
                   (t* ⋖ t*)
                   (tRec ⋖ tRec)))

(caching-enabled? #f)

(define-for-syntax debug-enabled? #f)

(define-syntax (debug stx)
  (syntax-case stx ()
    [(debug arg ...)
     (if debug-enabled?
         #'(printf arg ...)
         #'(void))]))

; NOTE:
; type inference is necessary because:
;   (Γ ⊢ (atom a) : A
;   (Γ ⊢ 0 : Nat
;   [A = Nat -> ??]
;   ----------------------
;   (Γ ⊢ ((atom a) 0) : ??)
