#lang racket

(require redex)

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
     n
     (atom x)) ;meta
  (p ::=
     x
     (pair p p))
  (v ::=
     (λ (p : t) e)
     (pair v v)
     n)
  (n ::= number)
  (x ::= variable-not-otherwise-mentioned)
  (t ::=
     (t -> t)
     (Pair t t)
     N
     x) ;meta
  (Γ ::= [(x : t) ...])
  ; meta:
  (φ ::= [c ...])
  (c ::=
     (Γ ⊢ e : t) ; e should be (atom x)?
     (t_1 = t_2)))

;; ---------------------------------------------------------------------------------------------------
;; typing

(define-metafunction the-syntax
  lookup : x Γ -> t
  [(lookup x [(x_1 : t_1) ... (x : t) (x_2 : t_2) ...])
   t
   (side-condition (not (member (term x) (term (x_2 ...)))))])

(define-metafunction the-syntax
  extend : x t Γ -> Γ
  [(extend x t [(x_s : t_s) ...])
   [(x_s : t_s) ... (x : t)]])

; TODO: unification
(define-metafunction the-syntax
  add-eq : t t φ -> φ
  [(add-eq t_1 t_2 [c ...])
   [c ... (t_1 = t_2)]])

; TODO: unification
(define-metafunction the-syntax
  union : φ φ -> φ
  [(union [c_1s ...] [c_2s ...])
   [c_1s ... c_2s ...]])

; TODO: unification
(define-metafunction the-syntax
  add-ty : Γ e t φ -> φ
  [(add-ty Γ e t [c_s ...])
   (c_s ... (Γ ⊢ e : t))])

(define-judgment-form the-syntax
  #:contract (ty Γ e t φ)
  #:mode (ty I I O O)
  
  [------ t-atom
   (ty Γ (atom x) x (add-ty Γ (atom x) x []))]
  
  [------ t-number
   (ty Γ n N [])]

  [(where t (lookup x Γ))
   ------ t-id
   (ty Γ x t [])]

  [(ty Γ e_1 N φ_1)
   (ty Γ e_2 N φ_2)
   ------ t-plus
   (ty Γ (+ e_1 e_2) N (union φ_1 φ_2))]
  
  [(ty Γ e_1 t_1 φ_1)
   (ty Γ e_2 t_2 φ_2)
   ------ t-pair
   (ty Γ (pair e_1 e_2) (Pair t_1 t_2) (union φ_1 φ_2))]
  
  [(ty Γ e_fun (t_1 -> t_3) φ_1)
   (ty Γ e_arg t_2 φ_2)
   ------ t-apply
   (ty Γ (e_fun e_arg) t_3 (add-eq t_2 t_1 (union φ_1 φ_2)))]
  
  [(ty (extend x t Γ) e t_2 φ)
   ------ t-lambda
   (ty Γ (λ (x : t) e) (t -> t_2) φ)])
  




(define-syntax-rule (derive expr)
  (build-derivations (ty [] expr _ _)))
;  (show-derivations (build-derivations (ty [] expr _ _))))

(derive ((λ (x : T) (atom B)) (atom A)))
;(derive (+ (atom A) 1))
;(derive (atom A))

