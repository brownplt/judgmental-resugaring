#lang racket

(require redex)
(require "../resugar.rkt")

;; Multi-arity lambda example.
;; This extends TAPL lambdas to handle multiple arguments.

(define-resugarable-language multi
  #:keywords(if true false succ pred iszero zero
                λ thunk let = : ..
                calctype
                Bool Num ->)
  (e ::= ....
     ; booleans
     (if e e e)
     ; numbers
     (+ e e)
     ; lambda
     (e e*))
  (v ::= ....
     ; booleans
     true
     false
     ; numbers
     number
     ; lambda
     (λ Γ e)
     (λ param* e))
  (param* ::= ϵ (cons (x : t) param*) (x* : t* ..))
  (t ::= ....
     Bool
     Num
     (t* -> t))
  (s ::= ....
     (let bind* s)
     (ors s*))
  #;(bind* ::= ϵ x (cons (x = s) bind*) (x* = s* ..)))


(define-core-type-system multi

  ; boolean
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

  ; number
  [------ t-num
   (⊢ Γ number Num)]

  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (con (t_1 = Num))
   (con (t_2 = Num))
   ------ t-plus
   (⊢ Γ (+ e_1 e_2) Nat)]

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

  [(⊢ (append Γ_params Γ) e t)
   (env-types Γ_params t*)
   ------ t-lambda
   (⊢ Γ (λ Γ_params e) (t* -> t))]
  
  [(⊢ (bind* x* t* Γ) e t)
   ------ t-lambda*
   (⊢ Γ (λ [x* : t* ..] e) (t* -> t))]
  
  [(⊢ Γ e_fun t_fun)
   (⊢* Γ e*_args t*_args)
   (where x_ret (fresh-var))
   (con (t_fun = (t*_args -> x_ret)))
   ------ t-apply
   (⊢ Γ (e_fun e*_args) x_ret)])


(define-judgment-form multi
  #:contract (env-types Γ t*)
  #:mode     (env-types I O)

  [------ env-types-ϵ
   (env-types ϵ ϵ)]

  [(env-types Γ t*)
   ------ env-types-bind
   (env-types (bind x t Γ) (cons t t*))]

  [(where x_t (fresh-var))
   (con (assumption ('env-types x = x_t)))
   ------ env-types-premise
   (env-types x x_t)])



(define rule_let
  (ds-rule "let" #:capture()
           (let [xs = ~vs ..] ~body)
           (calctype* ~vs as ts in
                      (λ (xs : ts ..) ~body))))

; ellipses example
(define rule_sugar-or-1
  (ds-rule "ors-empty" #:capture()
        (ors (cons ~a ϵ))
        ~a))

(define rule_sugar-or-1-fixed
  (ds-rule "ors-empty-fixed" #:capture()
        (ors (cons ~a ϵ))
        (calctype ~a as Bool in ~a)))

(define rule_sugar-or-2
  (ds-rule "ors-cons" #:capture()
        (ors (cons ~a (cons ~b ~cs)))
        (if ~a true (ors (cons ~b ~cs)))))




(view-sugar-type-rules multi ⊢
  (list rule_sugar-or-1 rule_sugar-or-1-fixed rule_sugar-or-2
        rule_let))
