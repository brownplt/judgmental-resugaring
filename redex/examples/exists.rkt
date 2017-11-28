#lang racket

(require redex)
(require "../resugar.rkt")

;;   existentials (TAPL pg.366)

(define-resugarable-language exists-lang
  #:keywords(if true false succ pred iszero zero
                λ thunk let = : ∃ of as in
                pair fst snd
                calctype
                Bool Num Pair ->)
  (e ::= ....
     ; booleans
     (if e e e)
     ; numbers
     (+ e e)
     ; lambda
     (e e)
     ; let
     (let x = e in e)
     ; pair
     (pair e e)
     (fst e)
     (snd e)
     ; exists
     (pack (t e) as t)
     (unpack e as (∃ x x) in e))
  (v ::= ....
     ; booleans
     true
     false
     ; numbers
     number
     ; lambda
     (λ (x : t) e)
     ; pair
     (pair v v)
     ; exists
     (∃ t v as t))
  (t ::= ....
     Bool
     Num
     (t -> t)
     ; pair
     (Pair t t)
     ; exists
     (∃ x t))
  (s ::= ....
     (let-new-type (x x) of t as x in s)))


(define-core-type-system exists-lang

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

  [(⊢ (bind x t Γ) e t_ret)
   ------ t-lambda
   (⊢ Γ (λ (x : t) e) (t -> t_ret))]

  [(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg)
   (where x_ret (fresh-var))
   (con (t_fun = (t_arg -> x_ret)))
   ------ t-apply
   (⊢ Γ (e_fun e_arg) x_ret)]

  ; let
  [(⊢ Γ e_1 t_1)
   (⊢ (bind x t_1 Γ) e_2 t_2)
   ------ t-let
   (⊢ Γ (let x = e_1 in e_2) t_2)]

  ; pairs
  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   ------ t-pair
   (⊢ Γ (pair e_1 e_2) (Pair t_1 t_2))]

  [(⊢ Γ e t)
   (where x_t1 (fresh-var))
   (where x_t2 (fresh-var))
   (con (t = (Pair x_t1 x_t2)))
   ------ t-fst
   (⊢ Γ (fst e) x_t1)]

  [(⊢ Γ e t)
   (where x_t1 (fresh-var))
   (where x_t2 (fresh-var))
   (con (t = (Pair x_t1 x_t2)))
   ------ t-snd
   (⊢ Γ (snd e) x_t2)]

  ; exists
  [(⊢ Γ e t_e)
   (con (t_e = (substitute t_2 x t)))
   ------ t-pack
   (⊢ Γ (pack (t e) as (∃ x t_2)) (∃ x t_2))]

  [(⊢ Γ e_def t_def)
   (where x_ex (fresh-var))
   (con (t_def = (∃ x_t x_ex)))
   (⊢ (bind x x_ex Γ) e_body t_body)
   ------ t-unpack
   (⊢ Γ (unpack e_def as (∃ x_t x) in e_body) t_body)])


(define-global id (a -> a))

; newtype as a pair
#;(define rule_newtype
  (ds-rule "newtype" #:capture()
        (let-new-type w of T as X in ~body)
        (let (∃ X w) = (∃ T (pair id id) as
          (∃ X (Pair (T -> X) (X -> T)))) in
          ~body)))

; newtype as a record
#;(define rule_newtype
  (ds-rule "newtype" #:capture()
        (let-new-type w of T as X in ~body)
        (let (∃ X w) = (∃ T (record (field wrap id (field unwrap id ϵ))) as
          (∃ X (Record (field wrap (T -> X) (field unwrap (X -> T) ϵ))))) in
          ~body)))

; newtype as bindings
(define rule_newtype 
  (ds-rule "newtype" #:capture()
        (new-type (wrap unwrap) of T as X in ~body)
        (unpack (pack (T (pair id id))
                   as (∃ X (Pair (T -> X) (X -> T))))
             as (∃ X w)
             in  (let wrap = (fst w) in
                   (let unwrap = (snd w) in
                     ~body)))))






(define (do-resugar rule)
  (Resugared-rule (resugar exists-lang rule ⊢)))

(show-derivations
 (map do-resugar
      (list rule_newtype)))
