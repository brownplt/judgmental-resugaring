#lang racket

(require redex)
(require "unify.rkt")
(require "base-lang.rkt")


;; ---------------------------------------------------------------------------------------------------
;; booleans (TAPL pg.93)
;; numbers  (TAPL pg.93)
;; stlc     (TAPL pg.103)

(define-extended-language stlc-syntax base-syntax
  (e ::= ....
     (if e e e)
     (succ e)
     (pred e)
     (iszero e)
     (typeof e = t in e)
     (e e)
     (λ (x : t) e))
  (x ::= variable-not-otherwise-mentioned)
  (v ::= ....
     true
     false
     nat)
  (n ::=
     0
     (succ n))
  (t ::= ....
     Bool
     Nat
     (t -> t)))

(define-metafunction stlc-syntax
  lookup : x Γ -> t
  [(lookup x [(x_1s : t_1s) ... (x : t) (x_2s : t_2s) ...])
   t
   (side-condition (not (member (term x) (term (x_2s ...)))))])

(define-metafunction stlc-syntax
  extend : Γ x t -> Γ
  [(extend [(x_s : t_s) ...] x t)
   [(x_s : t_s) ... (x : t)]])

;(define-extended-judgment-form stlc-syntax =>base
(define-judgment-form stlc-syntax
  #:contract (=> Γ e t)
  #:mode (=> I I O)

  ; booleans
  [(<= Γ e_1 Bool)
   (=> Γ e_2 t)
   (<= Γ e_3 t)
   ------ t-if
   (=> Γ (if e_1 e_2 e_3) t)]

  [------ t-true
   (=> Γ true Bool)]

  [------ t-false
   (=> Γ false Bool)]

  ; nats
  [(<= Γ e Nat)
   ------ t-succ
   (=> Γ (succ e) Nat)]

  [(<= Γ e Nat)
   ------ t-pred
   (=> Γ (pred e) Nat)]

  [(<= Γ e Nat)
   ------ t-iszero
   (=> Γ (iszero e) Bool)]

  ; stlc
  [(=> (extend Γ x t_1) e t_2)
   ------ t-lambda
   (=> Γ (λ (x : t_1) e) t_2)]

  [(where T1 (fresh-type))
   (where T2 (fresh-type))
   (<= Γ e_fun (T1 -> T2))
   (<= Γ e_arg T1)
   ------ t-apply
   (=> Γ (e_fun e_arg) T2)]

  ; fixed
  [(where x_t ,(atom-type-var (term x))) ; TODO: safety checks!
   (con (,(unfreshen (term Γ)) ⊢ x : x_t))
   ------ t-atom
   (=> Γ (atom x) x_t)]

  ; fixed
  [(=> Γ e_1 t_3)
   (con (t_1 = t_3))
   (=> Γ e_2 t_2)
   ------ t-typeof
   (=> Γ (typeof e_1 = t_1 in e_2) t_2)])

(define the-char (char->integer #\A))
(define (next-char)
  (let ([ch (integer->char the-char)])
    (set! the-char (+ the-char 1))
    ch))
(define-metafunction stlc-syntax
  fresh-type : -> x
  [(fresh-type)
   ,(string->symbol (make-string 1 (next-char)))])


;(define-extended-judgment-form stlc-syntax <=base
(define-judgment-form stlc-syntax
  #:contract (<= Γ e t)
  #:mode (<= I I I)

  ; fixed
  [(=> Γ e t_1)
   (con (t_1 = t_2))
   ------ t-syn
   (<= Γ e t_2)])


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

(define rule_app
  (rule "app" #:fresh()
        (app (atom a) (atom b))
        ((atom a) (atom b))))

#;(define rule_let
  (rule "let" #:fresh()
        (let x = (atom a) in (atom b))
        (typeof (atom b) = T in ((λ (x : T) (atom c)) (atom b)))))

(define the-literals (set 'λ ': '+ 'pair '-> 'Pair '= 'in 'Num 'Bool 'true 'false)) ; todo

(define deriv_not (resugar rule_not => the-literals))
(define deriv_unless (resugar rule_unless => the-literals))
(define deriv_ifzero (resugar rule_ifzero => the-literals))
(define deriv_thunk (resugar rule_thunk => the-literals))
#;(define deriv_let (resugar rule_let => the-literals))

(show-derivations (list deriv_not deriv_unless deriv_ifzero deriv_thunk))

#|
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
        ((λ (x : A) (if x x (atom b : B))) (atom a : A))))
(define the-literals (set 'λ ': '+ 'pair '-> 'Pair '= 'in 'Num 'Bool))
(define deriv_let (resugar rule_let => the-literals))
(define deriv_or (resugar rule_or => the-literals))
(show-derivations (list deriv_let deriv_or))
|#