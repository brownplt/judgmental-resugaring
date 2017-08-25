#lang racket

(require redex)
(require "unify.rkt")
(require "base-lang.rkt")


;; --------------------------------------------------------------------------------------------------- 
;; This file tests type resugaring for a language consisting of:
;;   booleans   (TAPL pg.93)
;;   numbers    (TAPL pg.93)
;;   stlc       (TAPL pg.103)
;;   unit       (TAPL pg.119)
;;   ascription (TAPL pg.122)

(define-extended-language stlc-syntax base-syntax
  (e ::= ....
     v
     (if e e e)
     (succ e)
     (pred e)
     (iszero e)
     (typeof e = t in e)
     (e e)
     (λ (x : t) e)
     (e as t))
  (x ::= variable-not-otherwise-mentioned)
  (v ::=
     true
     false
     n
     unit)
  (n ::=
     0
     (succ n))
  (t ::= ....
     Bool
     Nat
     (t -> t)
     Unit))

(define-metafunction stlc-syntax
  lookup : x Γ -> t
  [(lookup x [(x_1s : t_1s) ... (x : t) (x_2s : t_2s) ...])
   t
   (side-condition (not (member (term x) (term (x_2s ...)))))])

(define-metafunction stlc-syntax
  extend : Γ x t -> Γ
  [(extend [(x_s : t_s) ...] x t)
   [(x_s : t_s) ... (x : t)]])

(define-metafunction stlc-syntax
  fresh-type : -> x
  [(fresh-type)
   ,(fresh-type-var)])


;(define-extended-judgment-form stlc-syntax =>base
(define-judgment-form stlc-syntax
  #:contract (⊢ Γ e t)
  #:mode (⊢ I I O)

  ; booleans
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

  ; stlc
  [(where t (lookup x Γ))
   ------ t-id
   (⊢ Γ x t)]
  
  [(⊢ (extend Γ x t_1) e t_2)
   ------ t-lambda
   (⊢ Γ (λ (x : t_1) e) (t_1 -> t_2))]

  [(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg)
   (where x_t (fresh-type))
   (con (t_fun = (t_arg -> x_t)))
   ------ t-apply
   (⊢ Γ (e_fun e_arg) x_t)]

  ; unit
  [------ t-unit
   (⊢ Γ unit Unit)]

  ; ascription
  [(⊢ Γ e t_2)
   (con (t_1 = t_2))
   ------ t-ascribe
   (⊢ Γ (e as t_1) t_1)]

  ; fixed
  [(where x_t ,(atom-type-var (term x))) ; TODO: safety checks!
   (con (,(unfreshen (term Γ)) ⊢ x : x_t))
   ------ t-atom
   (⊢ Γ (atom x) x_t)]

  ; fixed
  [(⊢ Γ e_1 t_3)
   (con (t_1 = t_3))
   (⊢ Γ e_2 t_2)
   ------ t-typeof
   (⊢ Γ (typeof e_1 = t_1 in e_2) t_2)])

(define-judgment-form stlc-syntax
  #:contract (con c)
  #:mode (con I)
  [------ t-equal
   (con q)]
  [------ t-judge
   (con j)])


;; ---------------------------------------------------------------------------------------------------
;; Resguaring

(define rule_not
  (rule "not" #:fresh()
        (not (atom a))
        (if (atom a) false true)))

(define rule_unless
  (rule "unless" #:fresh()
        (unless (atom a) (atom b) (atom c))
        (if (atom a) (atom c) (atom b))))

(define rule_ifzero
  (rule "ifzero" #:fresh()
        (ifzero (atom a) (atom b) (atom c))
        (if (iszero (atom a)) (atom b) (atom c))))

(define rule_thunk
  (rule "thunk" #:fresh(x)
        (thunk (atom a))
        (λ (x : Nat) (atom a))))

(define rule_let
  (rule "let" #:fresh()
        (let x = (atom a) in (atom b))
        (typeof (atom a) = x_t in ((λ (x : x_t) (atom b)) (atom a)))))

(define rule_or
  (rule "or" #:fresh(x)
        (or (atom a) (atom b))
        ((λ (x : Bool) (if x x (atom b))) (atom a))))

(define rule_seq
  (rule "seq" #:fresh(x)
        (seq (atom a) (atom b))
        ((λ (x : Unit) (atom b)) (atom a))))

(define rule_sametype
  (rule "sametype" #:fresh()
        (sametype (atom a) (atom b))
        (typeof (atom b) = x_t in ((atom a) as x_t))))

(define the-literals (set 'λ ': '+ 'pair '-> 'Pair '= 'in 'Num 'Bool 'true 'false 'Unit 'as)) ; todo

(define (resugar-rule r)
  (resugar r ⊢ the-literals))

(show-derivations
 (map resugar-rule
      (list rule_sametype rule_seq rule_or rule_let rule_not rule_unless rule_ifzero rule_thunk)))
