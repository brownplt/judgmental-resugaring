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
  (φ ::= ([j ...] [q ...]))
  (j ::=  (Γ ⊢ (atom x) : t))
  (q ::= (t = t)))


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

(define-metafunction the-syntax
  lookup-eq : x [q ...] -> t or #f
  [(lookup-eq x [(x_1s = t_1s) ... (x = t) (x_2s = t_2s) ...])
   t]
  [(lookup-eq x [q ...])
   #f])

(define-metafunction the-syntax
  lookup-judge : x [j ...] -> j
  [(lookup-judge x [(Γ_1 ⊢ (atom x_1) : t_1) ...
                    (Γ   ⊢ (atom x)   : t)
                    (Γ_2 ⊢ (atom x_2) : t_2) ...])
   (Γ ⊢ (atom x) : t)])      

(define-metafunction the-syntax
  equate : t t [q ...] -> [q ...]
  [(equate x t [q ...])
   (equate t_2 t [q ...])
   (where t_2 (lookup-eq x [q ...]))]
  [(equate x t [(x_s = t_s) ...])
   ; Maintain the invarient that across eqs, lhs not in rhs, and lhs all distinct.
   ; If we're in this case, then (i) x not in lhs[q ...], (ii) x not in t.
   ; Perform substitutions to also ensure that lhs[q ...] not in t, and x not in rhs[q ...].
   [(x = (subs-eq [(x_s = t_s) ...] t)) (x_s = (subs-eq [(x = t)] t_s)) ...]
   (judgment-holds (not-contains t x))]
  ; symmetric cases
  [(equate t x [q_s ...])
   (equate x t [q_s ...])]
  ; language-specific
  [(equate (t_1 -> t_2) (t_3 -> t_4) [q_s ...])
   (equate t_1 t_3 (equate t_2 t_4 [q_s ...]))]
  [(equate (Pair t_1 t_2) (Pair t_3 t_4) [q_s ...])
   (equate t_1 t_3 (equate t_2 t_4 [q_s ...]))]
  [(equate N N [q_s ...])
   [q_s ...]])

(define-metafunction the-syntax
  subs-eq : [q ...] t -> t
  ; language-specific
  [(subs-eq [q ...] (t_1 -> t_2))
   ((subs-eq [q ...] t_1) -> (subs-eq [q ...] t_2))]
  [(subs-eq [q ...] (Pair t_1 t_2))
   (Pair (subs-eq [q ...] t_1) (subs-eq [q ...] t_2))]
  [(subs-eq [q ...] N)
   N]
  [(subs-eq [(x_1s = t_1s) ... (x = t) (x_2s = t_2s) ...] x)
   t]
  [(subs-eq [q ...] x)
   x])

(define-metafunction the-syntax
  subs-judge : [q ...] j -> j
  [(subs-judge [q ...] (Γ ⊢ (atom x) : t))
   (Γ ⊢ (atom x) : (subs-eq [q ...] t))])

(define-metafunction the-syntax
  add-eq : x t φ -> φ
  [(add-eq x t ([j_s ...] [q_s ...]))
   ([(subs-judge [q_2s ...] j_s) ...] [q_2s ...])
   (where [q_2s ...] (equate x t [q_s ...]))])

(define-metafunction the-syntax
  add-judge : Γ x t φ -> φ
  ; TODO: unification
  [(add-judge Γ x t ([j_s ...] [q_s ...]))
   ([(Γ ⊢ (atom x) : (subs-eq [q_s ...] t)) j_s ...] [q_s ...])])

(define-metafunction the-syntax
  union : φ φ -> φ
  [(union φ ([(Γ ⊢ (atom x) : t) j_s ...] [q_s ...]))
   (union (add-judge Γ x t φ) ([j_s ...] [q_s ...]))]
  [(union φ ([] [q q_s ...]))
   (union (add-eq q φ) ([] [q_s ...]))]
  [(union φ ([] []))
   φ])

; language-specific
(define-judgment-form the-syntax
  #:contract (not-contains t x)
  #:mode (not-contains I I)

  [(not-contains t_1 x)
   (not-contains t_2 x)
   ------ contains-lambda
   (not-contains (t_1 -> t_2) x)]

  [(not-contains t_1 x)
   (not-contains t_2 x)
   ------ contains-pair-1
   (not-contains (Pair t_1 t_2) x)]

  [(side-condition ,(not (symbol=? (term x_1) (term x_2))))
   ------ contains-var
   (not-contains x_1 x_2)])

(define-judgment-form the-syntax
  #:contract (ty Γ e t φ)
  #:mode (ty I I O O)
  
  [------ t-atom
   (ty Γ (atom x) x (add-judge Γ x x ([] [])))]
  
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
  (show-derivations (build-derivations (ty [] expr _ _))))

(derive ((λ (x : T) (atom B)) (atom A)))
;(derive (+ (atom A) 1))
;(derive (atom A))

