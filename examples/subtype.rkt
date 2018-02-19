#lang racket

(require redex)
(require "../sweet-t.rkt")

;;   subtyping  (TAPL pg.212)

(define-resugarable-language subtype-lang
  #:keywords(if true false succ pred iszero zero
                fix as λ unit thunk let = : ⋖ Top in
                calctype
                Bool Nat Unit ->)
  (e ::= ....
     ; booleans
     (if e e e)
     ; nats
     (succ e)
     (pred e)
     (iszero e)
     ; lambda
     (e e)
     (λ (x : t) e))
  (v ::= ....
     ; booleans
     true
     false
     ; nats
     zero
     ; lambda
     (λ (x : t) e))
  (t ::= ....
     Bool
     Nat
     Unit
     (t -> t)
     ; subtyping
     Top)
  (s ::= ....
     (thunk s)
     (let x = s in s)
     (or s s)
     (seq s s)
     (sametype s s)
     (cps s)))


(define-core-type-system subtype-lang
  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (⊢ Γ e_3 t_3)
   (con (t_1 = Bool))
   (con (t_2 = t_3))
   ------ t-if
   (⊢ Γ (if e_1 e_2 e_3) t_3)]

  [------ t-true
   (⊢ Γ true Bool)]

  [------ t-false
   (⊢ Γ false Bool)]

  ; nats
  [(⊢ Γ e t)
   (con (t = Nat))
   ------ t-succ
   (⊢ Γ (succ e) Nat)]

  [(⊢ Γ e t)
   (con (t = Nat))
   ------ t-pred
   (⊢ Γ (pred e) Nat)]

  [(⊢ Γ e t)
   (con (t = Nat))
   ------ t-iszero
   (⊢ Γ (iszero e) Bool)]

  ; lambda
  [(side-condition ,(variable? (term x)))
   (where t (lookup x Γ))
   ------ t-id
   (⊢ Γ x t)]

  [(side-condition ,(variable? (term x)))
   (where #f (lookup x Γ))
   (where x_Γ ,(fresh-type-var-named 'Γ))
   (where x_t (fresh-var))
   (con (Γ = (bind x x_t x_Γ)))
   ------ t-id-bind
   (⊢ Γ x x_t)]

  [(⊢ (bind x t Γ) e t_ret)
   ------ t-lambda
   (⊢ Γ (λ (x : t) e) (t -> t_ret))]

  [(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg)
   (where x_arg (fresh-var))
   (where x_t   (fresh-var))
   (con (t_fun = (x_arg -> x_t)))
   (⋖ t_arg x_arg)
   ------ t-apply
   (⊢ Γ (e_fun e_arg) x_t)])

; subtyping
(define-judgment-form subtype-lang
  #:contract (⋖ t t)
  #:mode     (⋖ I I)
  
  [------ t-sub-top
   (⋖ t Top)]

  [(⋖ t_1 t_1*)
   (⋖ t_2* t_2)
   ------ t-sub-arrow
   (⋖ (t_1* -> t_2*) (t_1 -> t_2))]

  [(con (x ⋖ t))
   ------ t-sub-premise1
   (⋖ x t)]

  [(con (t ⋖ x))
   (side-condition ,(not (redex-match subtype-lang x (term t))))
   ------ t-sub-premise2
   (⋖ t x)])


(define rule_upcast
  (ds-rule "upcast" #:capture()
           (upcast ~a as t)
           ((λ (x : t) x) ~a)))



(view-sugar-type-rules subtype-lang ⊢
  (list rule_upcast))
