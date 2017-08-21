#lang racket

(require redex)
(require "unify.rkt")

(provide (all-defined-out))


;; ---------------------------------------------------------------------------------------------------
;; syntax

(define-language the-syntax
  (e ::=
     x
     (λ (p : t) e)
     (e e)
     (pair e e)
     (+ e e)
     (if e e e)
     n)
  (p ::=
     x
     (pair p p))
  (v ::=
     (λ (p : t) e)
     (pair v v)
     n)
  (n ::= number)
  (x ::= variable-not-otherwise-mentioned) ; fixed
  (t ::=
     (t -> t)
     (Pair t t)
     Num
     Bool)
  (Γ ::= [(x : t) ...])) ; fixed

(define-extended-language the-meta-syntax the-syntax ; fixed
  (e ::= ....
     (atom x : x))
  (t ::= ....
     x)
  (c ::=
     j
     q)
  (j ::=  (Γ ⊢ (atom x : x) : t))
  (q ::= (t = t)))


;; ---------------------------------------------------------------------------------------------------
;; typing

(define-metafunction the-meta-syntax
  extend : x t Γ -> Γ
  [(extend x t [(x_s : t_s) ...])
   [(x_s : t_s) ... (x : t)]])

(define-judgment-form the-meta-syntax
  #:contract (ty Γ e t)
  #:mode (ty I I O)
  
  [(con (Γ ⊢ (atom x_1 : x_2) : x_2))
   (side-condition ,(freshless? (term Γ)))
   ------ t-atom
   (ty Γ (atom x_1 : x_2) x_2)]

  [(where Γ_2 ,(unfreshen (term Γ)))
   (side-condition ,(not (freshless? (term Γ))))
   (ty Γ_2 (atom x_1 : x_2) x_2)
   ------ t-fresh
   (ty Γ (atom x_1 : x_2) x_2)]
  
  [------ t-number
   (ty Γ n N)]

  [(where t (lookup x Γ))
   ------ t-id
   (ty Γ x t)]

  [(ty Γ e_1 Num)
   (ty Γ e_2 Num)
   ------ t-plus
   (ty Γ (+ e_1 e_2) Num)]

  [(ty Γ e_1 Bool)
   (ty Γ e_2 t_1)
   (ty Γ e_3 t_2)
   (con (t_1 = t_2))
   ------ t-if
   (ty Γ (if e_1 e_2 e_3) t_1)]
  
  [(ty Γ e_1 t_1)
   (ty Γ e_2 t_2)
   ------ t-pair
   (ty Γ (pair e_1 e_2) (Pair t_1 t_2))]
  
  [(ty Γ e_fun (t_1 -> t_3))
   (ty Γ e_arg t_2)
   (con (t_1 = t_2))
   ------ t-apply
   (ty Γ (e_fun e_arg) t_3)]
  
  [(ty (extend x t Γ) e t_2)
   ------ t-lambda
   (ty Γ (λ (x : t) e) (t -> t_2))])



;; ---------------------------------------------------------------------------------------------------
;; meta-typing

(define-judgment-form the-meta-syntax
  #:contract (con c)
  #:mode (con I)
  [------ t-equal
   (con q)]
  [------ t-judge
   (con j)])


(define rule_let
  (rule "let" #:fresh ()
        (let x : T = (atom a : A) in (atom b : B))
        ((λ (x : T) (atom b : B)) (atom a : A))))
(define rule_thunk
  (rule "thunk" #:fresh (x)
        (thunk (atom a : A))
        (λ (x : Num) (atom a : A))))
(define rule_or
  (rule "or" #:fresh (x)
        (or (atom a : A) (atom b : B))
        (if (atom a : A) (atom a : A) (atom b : B))))
        ;((λ (x : A) (if x x (atom b : B))) (atom a : A))))
(define the-literals (set 'λ ': '+ 'pair '-> 'Pair '= 'in))
(define the-deriv (resugar rule_let ty the-literals))
(show-derivations (list the-deriv))
