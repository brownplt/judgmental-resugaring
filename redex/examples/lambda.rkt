#lang racket

(require redex)
(require "../resugar.rkt")

;;   booleans   (TAPL pg.93)
;;   nats       (TAPL pg.93)
;;   lambda     (TAPL pg.103)
;;   unit       (TAPL pg.119)
;;   ascription (TAPL pg.122)
;;   fix        (TAPL pg.144)

(define-resugarable-language lamb
  #:keywords(if true false succ pred iszero zero
                fix as λ unit thunk let = :
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
     (λ (x : t) e)
     ; ascription
     (e as t)
     ; fix
     (fix e))
  (v ::= ....
     ; booleans
     true
     false
     ; nats
     zero
     ; lambda
     (λ (x : t) e)
     ; unit
     unit)
  (t ::= ....
     Bool
     Nat
     Unit
     (t -> t))
  (s ::= ....
     (thunk s)
     (let x = s in s)
     (or s s)
     (seq s s)
     (sametype s s)))


(define-core-type-system lamb
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
   (where x_ret (fresh-var))
   (con (t_fun = (t_arg -> x_ret)))
   ------ t-apply
   (⊢ Γ (e_fun e_arg) x_ret)]

  ; unit
  [------ t-unit
   (⊢ Γ unit Unit)]

  ; ascription
  [(⊢ Γ e t_2)
   (con (t_1 = t_2))
   ------ t-ascribe
   (⊢ Γ (e as t_1) t_1)]

  ; fix
  [(⊢ Γ e t)
   (where x_t (fresh-var))
   (con (t = (x_t -> x_t)))
   ------ t-fix
   (⊢ Γ (fix e) x_t)])



(define rule_thunk
  (ds-rule "thunk" #:capture()
        (thunk ~a)
        (λ (x : Unit) ~a)))

(define rule_let
  (ds-rule "let" #:capture()
        (let x = ~a in ~b)
        (calctype ~a as t in ((λ (x : t) ~b) ~a))))

(define rule_or
  (ds-rule "or" #:capture()
        (or ~a ~b)
        ((λ (x : Bool) (if x x ~b)) ~a)))

(define rule_seq
  (ds-rule "seq" #:capture()
        (seq ~a ~b)
        ((λ (x : Unit) ~b) ~a)))

(define rule_sametype
  (ds-rule "sametype" #:capture()
        (sametype ~a ~b)
        (calctype ~b as x_t in (~a as x_t))))

(define rule_letrec
  (ds-rule "letrec" #:capture()
        (letrec x : ~t = ~a in ~b)
        ((λ (x : ~t) ~b) (fix (λ (x : ~t) ~a)))))









(define (do-resugar rule)
  (Resugared-rule (resugar lamb rule ⊢)))

(show-derivations
 (map do-resugar
      (list rule_letrec rule_thunk rule_let rule_or rule_seq rule_sametype)))

