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
;;   let        (TAPL pg.124) (called let_)
;;   pairs      (TAPL pg.126)
;;   tuples     (TAPL pg.128) -- TODO, subsumes pairs
;;   records    (TAPL pg.129) -- TODO, subsumes tuples? Needs row types?
;;   sums       (TAPL pg.132) (uniq typing on pg. 135 irrelevant w/ T.I.)
;;   fix        (TAPL pg.144)
;;   lists      (TAPL pg.147) -- TODO

;; TODO:
;;   - allow sugars to build on each other

(define-extended-language stlc-syntax base-syntax
  (e ::= ....
     v
     ; booleans
     (if e e e)
     ; numbers
     (succ e)
     (pred e)
     (iszero e)
     ; stlc
     (e e)
     (λ (x : t) e)
     ; ascription
     (e as t)
     ; let
     (let! x = e in e)
     ; pair
     (pair e e)
     (fst e)
     (snd e)
     ; record
     #;(record (x e) ...)
     (dot e x)
     ; sum
     (inl e)
     (inr e)
     (case e of (inl x => e) (inr x => e))
     ; fix
     (fix e)
     (letrec! x : t = e in e)
     ; list
     (cons e e)
     (isnil e)
     (head e)
     (tail e)
     ; builtin
     (calctype e as t in e))
  (x ::= variable-not-otherwise-mentioned)
  (v ::=
     ; booleans
     true
     false
     ; numbers
     n
     ; unit
     unit
     ; pair
     (pair v v)
     ; record
     #;(record (x v) ...)
     ; list
     nil
     (cons v v))
  (n ::=
     0
     (succ n))
  (t ::= ....
     ; booleans
     Bool
     ; numbers
     Nat
     ; unit
     Unit
     ; stlc
     (t -> t)
     ; pairs
     (Pair t t)
     ; record
     #;(Record (x t) ...)
     ; sum
     (Sum t t)
     ; list
     (List t)))

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
  [(side-condition ,(not (string-prefix? (symbol->string (term x)) "~"))) ; exclude atoms
   (where t (lookup x Γ))
   ------ t-id
   (⊢ Γ x t)]
  
  [(⊢ (extend Γ x t_1) e t_2)
   ------ t-lambda
   (⊢ Γ (λ (x : t_1) e) (t_1 -> t_2))]

  [(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg)
   (where x_t ,(fresh-type-var))
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

  ; let
  [(⊢ Γ e_1 t_1)
   (⊢ (extend Γ x t_1) e_2 t_2)
   ------ t-let
   (⊢ Γ (let! x = e_1 in e_2) t_2)]

  ; pairs
  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   ------ t-pair
   (⊢ Γ (pair e_1 e_2) (Pair t_1 t_2))]

  [(⊢ Γ e t)
   (where x_t1 ,(fresh-type-var))
   (where x_t2 ,(fresh-type-var))
   (con (t = (Pair x_t1 x_t2)))
   ------ t-fst
   (⊢ Γ (fst e) x_t1)]

  [(⊢ Γ e t)
   (where x_t1 ,(fresh-type-var))
   (where x_t2 ,(fresh-type-var))
   (con (t = (Pair x_t1 x_t2)))
   ------ t-snd
   (⊢ Γ (snd e) x_t2)]

  ; records
  ; TODO

  ; sums
  [(⊢ Γ e t)
   (where x_t ,(fresh-type-var))
   ------ t-inl
   (⊢ Γ (inl e) (Sum t x_t))]

  [(⊢ Γ e t)
   (where x_t ,(fresh-type-var))
   ------ t-inr
   (⊢ Γ (inr e) (Sum x_t t))]

  [(where x_t1 ,(fresh-type-var))
   (where x_t2 ,(fresh-type-var))
   (⊢ Γ e t)
   (con (t = (Sum x_t1 x_t2)))
   (⊢ (extend Γ x_1 x_t1) e_1 t_1)
   (⊢ (extend Γ x_2 x_t2) e_2 t_2)
   (con (t_1 = t_2))
   ------ t-case
   (⊢ Γ (case e of (inl x_1 => e_1) (inr x_2 => e_2)) t_1)]

  ; fix
  [(⊢ Γ e t)
   (where x_t ,(fresh-type-var))
   (con (t = (x_t -> x_t)))
   ------ t-fix
   (⊢ Γ (fix e) x_t)]

  [(⊢ (extend Γ x t) e_1 t_1)
   (⊢ (extend Γ x t) e_2 t_2)
   (con (t_1 = t))
   ------ t-letrec
   (⊢ Γ (letrec! x : t = e_1 in e_2) t_2)]

  ; list
  [(where x_t ,(fresh-type-var))
   ------ t-nil
   (⊢ Γ nil x_t)]

  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (con (t_2 = (List t_1)))
   ------ t-cons
   (⊢ Γ (cons e_1 e_2) t_2)]

  [(⊢ Γ e t)
   (where x_t ,(fresh-type-var))
   (con (t = (List x_t)))
   ------ t-isnil
   (⊢ Γ (isnil e) Bool)]

  [(⊢ Γ e t)
   (where x_t ,(fresh-type-var))
   (con (t = (List x_t)))
   ------ t-head
   (⊢ Γ (head e) x_t)]

  [(⊢ Γ e t)
   (where x_t ,(fresh-type-var))
   (con (t = (List x_t)))
   ------ t-tail
   (⊢ Γ (tail e) t)]

  ; required for any lang
  [(where x_t ,(atom-type-var (term a))) ; TODO: safety checks!
   (con (,(unfreshen (term Γ)) ⊢ a : x_t))
   ------ t-atom
   (⊢ Γ a x_t)]

  ; required for any lang
  [(⊢ Γ e_1 t_3)
   (con (t_1 = t_3))
   (⊢ Γ e_2 t_2)
   ------ t-calctype
   (⊢ Γ (calctype e_1 as t_1 in e_2) t_2)])

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
        (not ~a)
        (if ~a false true)))

(define rule_unless
  (rule "unless" #:fresh()
        (unless ~a ~b ~c)
        (if ~a ~c ~b)))

(define rule_ifzero
  (rule "ifzero" #:fresh()
        (ifzero ~a ~b ~c)
        (if (iszero ~a) ~b ~c)))

(define rule_thunk
  (rule "thunk" #:fresh(x)
        (thunk ~a)
        (λ (x : Nat) ~a)))

(define rule_let
  (rule "let" #:fresh()
        (let x = ~a in ~b)
        (calctype ~a as t in ((λ (x : t) ~b) ~a))))

(define rule_or
  (rule "or" #:fresh(x)
        (or ~a ~b)
        ((λ (x : Bool) (if x x ~b)) ~a)))

(define rule_seq
  (rule "seq" #:fresh(x)
        (seq ~a ~b)
        ((λ (x : Unit) ~b) ~a)))

(define rule_sametype
  (rule "sametype" #:fresh()
        (sametype ~a ~b)
        (calctype ~b as x_t in (~a as x_t))))

(define rule_let-pair
  (rule "let-pair" #:fresh(p)
        (let-pair x y = ~a in ~b)
        (calctype ~a as (Pair t_1 t_2) in
                  (let! p = ~a in
                        (let! x = (fst p) in
                              (let! y = (snd p) in
                                    ~b))))))

; contrived
(define rule_sum-or
  (rule "sum-or" #:fresh(x)
        (sum-or ~a ~b)
        (case ~a of
          (inl x => ~b)
          (inr x => (inr x)))))

; contrived
(define rule_sum-map
  (rule "sum-map" #:fresh(err)
        (sum-or-else ~a ok ~b)
        (case ~a of
          (inl err => (inl err))
          (inr ok => (inr ~b)))))

(define rule_letrec
  (rule "letrec" #:fresh()
        (letrec x : ~t = ~a in ~b)
        (let! x = (fix (λ (x : ~t) ~a)) in ~b)))

(define rule_for-map
  (rule "for-map" #:fresh(f l)
        (for-map x ~list ~body)
        (calctype ~list as (List elem) in
         (calctype (λ (x : elem) ~body) as (elem -> out) in
                   (letrec! f : ((List elem) -> (List out))
                            = (λ (l : (List elem))
                                (if (isnil l)
                                    nil
                                    (let! x = (head l) in
                                          (cons ~body (f (tail l))))))
                            in (f ~list))))))

(define the-literals (set 'λ ': '+ 'pair '-> 'Pair '= 'in 'Num 'Bool
                          'true 'false 'Unit 'as 'case 'of 'inl 'inr '=>)) ; todo

(define (simply-resugar r)
  (let ([resugared (resugar-rule r ⊢ the-literals)])
    (Resugared-rule resugared)))

(show-derivations
 (map simply-resugar
      (list rule_for-map)
      #;(list rule_for-map rule_sum-map rule_sum-or
            rule_letrec rule_sametype rule_seq rule_or rule_let
            rule_not rule_unless
            rule_ifzero rule_thunk rule_let-pair)))

(define-syntax-rule (test-match x)
  (redex-match stlc-syntax e (term x)))
