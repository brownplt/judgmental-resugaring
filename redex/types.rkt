#lang racket

(require redex)
(require "unify.rkt")
(require "base-lang.rkt")

(provide (all-defined-out))


;; --------------------------------------------------------------------------------------------------- 
;; This file tests type resugaring for a language consisting of:
;;   booleans   (TAPL pg.93)
;;   numbers    (TAPL pg.93)
;;   stlc       (TAPL pg.103)
;;   unit       (TAPL pg.119)
;;   ascription (TAPL pg.122)
;;   let        (TAPL pg.124) (called let_)
;;   pairs      (TAPL pg.126)
;;   tuples     (TAPL pg.128) (subsumes pairs)
;;   records    (TAPL pg.129) -- TODO, subsumes tuples? Needs row types?
;;   sums       (TAPL pg.132) (uniq typing on pg. 135 irrelevant w/ T.I.)
;;   fix        (TAPL pg.144)
;;   lists      (TAPL pg.147)
;;   refs       (TAPL pg.166) -- TODO
;;   errors     (TAPL pg.175) -- TODO (skipping the tiny pre-version)
;;   subtyping  (TAPL pg.186) -- TODO
;;   subty-rec  (TAPL pg.197) -- TODO
;;   subty-bot  (TAPL pg.192) -- TODO
;;   subty-var  (TAPL pg.197) -- TODO
;;   alg-subty  pg. 211, 212, 217

;; TODO:
;;   - allow sugars to build on each other
;; Writing:
;;   - type environment Γ
;;   - globals
;;   - recursive sugars

(define-extended-language stlc-syntax base-syntax
  (e ::= ....
     v
     ; booleans
     (if e e e)
     ; numbers
     (succ e)
     (pred e)
     (iszero e)
     (+ e e) ; added for convenience
     ; stlc
     (apply e ...)
     (λ ((x : t) ...) e)
     ; ascription
     (e as t)
     ; let
     (let! x = e in e)
     ; pair
     (pair e e)
     (fst e)
     (snd e)
     ; tuple
     (tuple e*)
     (project e n)
     ; record
     (record eRec)
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
     ; pair
     (pair v v)
     ; tuple
     (tuple v*)
     ; record
     ;(record (x v) ...)
     ; list
     nil
     (cons v v))
  (v* ::= ϵ (cons v v*)) ; for all langs
  (n ::=
     number
     (variable-prefix n$))
  (t ::= ....
     ; booleans
     Bool
     ; numbers
     Nat
     ; unit
     Unit
     ; stlc
     (t ... -> t)
     ; pairs
     (Pair t t)
     ; tuples
     (Tuple t*)
     ; sum
     (Sum t t)
     ; record
     (Record tRec)
     ; list
     (List t)
     ; subtyping
     Top)
  (s ::= ....
     (hlc s s)
     (ands s*)
     (class x extends x class-body rest)
     (call s x s*)
     (new x s*)
     (cast x s))
  (class-body ::= { class-fields & class-constructor & class-methods })
  (class-fields ::= sRec)
  (class-constructor ::= (constructor ((x : t) ...) {
                           (super x ...)
                           ((x = x) ...)
                         }))
  (class-methods ::= (method ((x : t) ...) -> t { t })))

(define-metafunction stlc-syntax
  lookup : x Γ -> t
  [(lookup x [(x_1s : t_1s) ... (x : t) (x_2s : t_2s) ...])
   t
   (side-condition (not (member (term x) (term (x_2s ...)))))]
  [(lookup x Γ)
   ,(get-global (term x))
   (side-condition (global-exists? (term x)))])

(define-metafunction stlc-syntax
  extend : Γ x t -> Γ
  [(extend [(x_s : t_s) ...] x t)
   [(x_s : t_s) ... (x : t)]])

(define-metafunction stlc-syntax
  append : Γ Γ -> Γ
  [(append [(x_1 : t_1) ...] [(x_2 : t_2) ...])
   [(x_1 : t_1) ... (x_2 : t_2) ...]])


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

  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (con (t_1 = Nat))
   (con (t_2 = Nat))
   ------ t-sum
   (⊢ Γ (+ e_1 e_2) Nat)]

  ; stlc
  [(side-condition ,(not (string-prefix? (symbol->string (term x)) "~"))) ; exclude atoms
   (where t (lookup x Γ))
   ------ t-id
   (⊢ Γ x t)]
  
  #;[(⊢ (extend Γ x t_1) e t_2)
   ------ t-lambda
   (⊢ Γ (λ (x : t_1) e) (t_1 -> t_2))]

  #;[(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg)
   (where x_t ,(fresh-type-var))
   #;(where x_arg ,(fresh-type-var)) ; subtyping
   (con (t_fun = (t_arg -> x_t))) ; subtyping (x_arg vs. t_arg)
   #;(⋖ t_arg x_arg) ; subtyping
   ------ t-apply
   (⊢ Γ (e_fun e_arg) x_t)]

  ; multi-arity functions
  [(⊢ (append Γ [(x : t) ...]) e t_e)
   ------ t-lambda*
   (⊢ Γ (λ ((x : t) ...) e) (t ... -> t_e))]

  [(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg) ...
   (where x_ret ,(fresh-type-var))
   (con (t_fun = (t_arg ... -> x_ret)))
   ------ t-apply*
   (⊢ Γ (apply e_fun e_arg ...) x_ret)]

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

  ; tuples
  [(⊢* Γ e* t*)
   ------ t-tuple
   (⊢ Γ (tuple e*) (Tuple t*))]

  [(⊢ Γ e t_e)
   (where x* ,(fresh-type-var))
   (con (t_e = (Tuple x*)))
   (@t x* n t)
   ------ t-proj
   (⊢ Γ (project e n) t)]

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

  ; record
  [(⊢rec Γ eRec tRec)
   ------ t-rec
   (⊢ Γ (record eRec) (Record tRec))]

  [(⊢ Γ e t_e)
   (where x_rec ,(fresh-type-var))
   (con (t_e = (Record x_rec)))
   (@rec x_rec x t)
   ------ t-dot
   (⊢ Γ (dot e x) t)]

  ; required for any lang
  [(where x_t ,(atom->type-var (term s))) ; TODO: safety checks!
   (con (,(unfreshen (term Γ)) ⊢ s : x_t))
   ------ t-premise
   (⊢ Γ s x_t)]

  ; required for any lang
  [(⊢ Γ e_1 t_3)
   (con (t_1 = t_3))
   (⊢ Γ e_2 t_2)
   ------ t-calctype
   (⊢ Γ (calctype e_1 as t_1 in e_2) t_2)])


; subtyping
(define-judgment-form stlc-syntax
  #:contract (⋖ t t)
  #:mode     (⋖ I I)
  
  [------ t-sub-top
   (⋖ t Top)]

  [(⋖ t_1 t_1*)
   (⋖ t_2* t_2)
   ------ t-sub-arrow
   (⋖ (t_1* -> t_2*) (t_1 -> t_2))]

  [(⋖rec tRec1 tRec2)
   ------ t-sub-record
   (⋖ (Record tRec1) (Record tRec2))]

  [(con (⋖ x t))
   ------ t-sub-premise1
   (⋖ x t)]

  [(con (⋖ t x))
   (side-condition ,(not (redex-match stlc-syntax x (term t))))
   ------ t-sub-premise2
   (⋖ t x)])


(define-judgment-form stlc-syntax
  #:contract (⋖rec tRec tRec)
  #:mode     (⋖rec I I)
  
  [(@rec tRec1 x t1)
   (⋖ t1 t2)
   (⋖rec tRec1 tRec2)
   ------ t-sub-rec
   (⋖rec tRec1 (field x t2 tRec2))]

  [------ t-sub-rec-empty
   (⋖rec ϵ ϵ)]

  [(con (⋖rec tRec x_rec))
   ------ t-sub-rec-premise
   (⋖rec tRec x_rec)])


; required for any lang
(define-judgment-form stlc-syntax
  #:contract (con premise)
  #:mode (con I)
  [------ con-equal
   (con premise/equation)]
  [------ con-subtype
   (con premise/subtype)]
  [------ con-judge
   (con premise/judgement)]
  [------ con-assum
   (con (assumption any))])

; required for any lang
(define-judgment-form stlc-syntax
  #:contract (⊢* Γ e* t*)
  #:mode (⊢* I I O)

  [(⊢ Γ e t)
   (⊢* Γ e* t*)
   ------ t-cons
   (⊢* Γ (cons e e*) (cons t t*))]

  [------ t-empty
   (⊢* Γ ϵ ϵ)]

  [(where x_t* ,(atom->type-var (term a)))
   (con (,(unfreshen (term Γ)) ⊢ a : x_t*))
   ------ t-premise*
   (⊢* Γ a x_t*)])

; required for any lang
(define-judgment-form stlc-syntax
  #:contract (⊢rec Γ eRec tRec)
  #:mode (⊢rec I I O)

  [(⊢ Γ e t)
   (⊢rec Γ eRec tRec)
   ------ t-rec-cons
   (⊢rec Γ (field x e eRec) (field x t tRec))]

  [------ t-rec-empty
   (⊢rec Γ ϵ ϵ)])


; required for any lang
(define-judgment-form stlc-syntax
  #:contract (@rec tRec x t)
  #:mode (@rec I I O)

  [------ t-rec-at-base
   (@rec (field x t tRec) x t)]

  [(@rec tRec x t)
   ------ t-rec-at-recur
   (@rec (field x_2 t_2 tRec) x t)]

  [(where x_t ,(fresh-type-var))
   (con (assumption (x_rec @ x = x_t)))
   ------ t-rec-at-premise
   (@rec x_rec x x_t)])


; required for any lang
(define-judgment-form stlc-syntax
  #:contract (@t t* n t)
  #:mode (@t I I O)

  [------ t-at-zero
   (@t (cons t t*) 0 t)]

  [(side-condition (number? (term n)))
   (side-condition (> (term n) 0))
   (@t t* ,(- (term n) 1) t_n)
   ------ t-at-succ
   (@t (cons t t*) n t_n)]

  [(where y ,(fresh-type-var))
   (con (assumption (x @ n$ = y)))
   ------ t-at-premise
   (@t x n$ y)])

