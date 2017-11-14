#lang racket

(require redex)
(require "unify.rkt")
(require "base-lang.rkt")

(provide (all-defined-out))

;; TODO:
;;   - allow sugars to build on each other
;;   - use syntax 'pack' and 'unpack'
;;   - reverse order of 'bind'

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
;;   records    (TAPL pg.129)
;;   sums       (TAPL pg.132) (uniq typing on pg. 135 irrelevant w/ T.I.)
;;   variants   (TAPL pg.136) -- TODO
;;   fix        (TAPL pg.144)
;;   lists      (TAPL pg.147)
;;   refs       (TAPL pg.166) -- TODO
;;   errors     (TAPL pg.175) (skipping the tiny pre-version)
;; End of Part II - stopping here
;;   subtyping  (TAPL pg.186) -- TODO
;;   subty-rec  (TAPL pg.197) -- TODO
;;   subty-bot  (TAPL pg.192) -- TODO
;;   subty-var  (TAPL pg.197) -- TODO
;;   alg-subty  pg. 211, 212, 217
;;   featherweight-java (TAPL pg.259)
;;   iso-recurs (TAPL pg.276) -- TODO
;;   constraint (TAPL pg.322) -- skip
;;   system F   (TAPL pg.343) -- TODO
;;   existential(TAPL pg.366) -- TODO (mostly done)

;; Potential Resugaring Examples:
;;   encoding existentials (TAPL 24.3 pg.377)

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
     (e e ...)
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
     (link e e) ; renamed to avoid name clash with builtin cons
     (isnil e)
     (head e)
     (tail e)
     ; exception
     (raise e)
     (try e with e)
     ; exists
     (∃ t e as t)
     (let (∃ x x) = e in e)
     ; begin
     (begin e e)
     ; builtin
     (calctype e as t in e))
  (param* ::= ϵ a (cons (x : t) param*))
  (x ::= variable-not-otherwise-mentioned)
  (v ::=
     ; booleans
     true
     false
     ; numbers
     n
     ; strings
     string
     ; stlc
     (λ ((x : t) ...) e)
     ; pair
     (pair v v)
     ; tuple
     (tuple v*)
     ; record
     (record vRec)
     ; list
     nil
     (cons v v)
     ; exists
     (∃ t v as t))
  (v* ::= ϵ (cons v v*)) ; for all langs
  (n ::=
     number
     (variable-prefix n$))
  (t ::= ....
     ; booleans
     Bool
     ; numbers
     Nat
     ; strings
     String
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
     Top
     ; exists
     (∃ x t))
  (s ::= ....
     (hlc s s)
     (ands s*)
     (class x extends x class-body rest)
     (call s x s*)
     (new x s*)
     (cast x s)
     (cps e))
  (class-body ::= { class-fields & class-constructor & class-methods })
  (class-fields ::= sRec)
  (class-constructor ::= (constructor ((x : t) ...) {
                           (super x ...)
                           ((x = x) ...)
                         }))
  (class-methods ::= (method ((x : t) ...) -> t { t })))

(define-metafunction stlc-syntax
  lookup : x Γ -> any ; (t or #f)
  [(lookup x Γ)
   ,(get-global (term x))
   (side-condition (global-exists? (term x)))]
  [(lookup x Γ)
   t
   (where t (lookup-recur x Γ))]
  [(lookup x Γ)
   #f
   (where #f (lookup-recur x Γ))])


(define-metafunction stlc-syntax
  lookup-recur : x Γ -> any ; (t or #f)
  [(lookup-recur x (bind x t Γ)) t]
  [(lookup-recur x (bind x_2 t Γ))
   (lookup-recur x Γ)
   (side-condition (not (equal? (term x) (term x_2))))]
  [(lookup-recur x Γ)
   #f])

(define-metafunction stlc-syntax
  fresh-var : -> x
  [(fresh-var)
   ,(fresh-type-var)])

(define-metafunction stlc-syntax
  append : Γ Γ -> Γ
  [(append (bind x t Γ_1) Γ_2)
   (bind x t (append Γ_1 Γ_2))]
  [(append ϵ Γ)
   Γ])

(define-metafunction stlc-syntax
  bind-each : [(x t) ...] Γ -> Γ
  [(bind-each [] Γ)
   Γ]
  [(bind-each [(x t) (x_s t_s) ...] Γ)
   (bind x t (bind-each [(x_s t_s) ...] Γ))])


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

  ;numbers
  [------ t-num
   (⊢ Γ n Nat)]

  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (con (t_1 = Nat))
   (con (t_2 = Nat))
   ------ t-sum
   (⊢ Γ (+ e_1 e_2) Nat)]

  ; strings

  [------ t-str
   (⊢ Γ string String)]

  ; stlc
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
  
  #;[(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg)
   (where x_t (fresh-var))
   #;(where x_arg (fresh-var)) ; subtyping
   (con (t_fun = (t_arg -> x_t))) ; subtyping (x_arg vs. t_arg)
   #;(⋖ t_arg x_arg) ; subtyping
   ------ t-apply
   (⊢ Γ (e_fun e_arg) x_t)]

  ; multi-arity functions
  [(⊢ (bind-each [(x t) ...] Γ) e t_ret)
   ------ t-lambda
   (⊢ Γ (λ [(x : t) ...] e) (t ... -> t_ret))]

  [(⊢ Γ e_fun t_fun)
   (⊢ Γ e_args t_args) ...
   (where x_ret (fresh-var))
   (con (t_fun = (t_args ... -> x_ret)))
   ------ t-apply
   (⊢ Γ (e_fun e_args ...) x_ret)]

  ; multi-arity functions w/ *
  #;[(⊢ Γ e t_ret)
   ------ t-lambda-empty
   (⊢ Γ (λ* ϵ e) (ϵ ->* t_ret))]

  #;[(⊢ (bind x t Γ) (λ param* e) t_fun)
   (where x_ret (fresh-var))
   (where x_params (fresh-var))
   (con (t_fun = (x_params ->* x_ret)))
   ------ t-lambda-cons
   (⊢ Γ (λ (cons (x : t) param*) e) ((cons t x_params) ->* x_ret))]
  
  #;[(⊢ Γ e_fun t_fun)
   (⊢* Γ e*_args t*_args)
   (where x_ret (fresh-var))
   (con (t_fun = (t*_args -> x_ret)))
   ------ t-apply
   (⊢ Γ (apply e_fun e*_args) x_ret)]

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
   (⊢ (bind x t_1 Γ) e_2 t_2)
   ------ t-let
   (⊢ Γ (let! x = e_1 in e_2) t_2)]

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

  ; tuples
  [(⊢* Γ e* t*)
   ------ t-tuple
   (⊢ Γ (tuple e*) (Tuple t*))]

  [(⊢ Γ e t_e)
   (where x* (fresh-var))
   (con (t_e = (Tuple x*)))
   (@t x* n t)
   ------ t-proj
   (⊢ Γ (project e n) t)]

  ; records
  ; TODO

  ; sums
  [(⊢ Γ e t)
   (where x_t (fresh-var))
   ------ t-inl
   (⊢ Γ (inl e) (Sum t x_t))]

  [(⊢ Γ e t)
   (where x_t (fresh-var))
   ------ t-inr
   (⊢ Γ (inr e) (Sum x_t t))]

  [(where x_t1 (fresh-var))
   (where x_t2 (fresh-var))
   (⊢ Γ e t)
   (con (t = (Sum x_t1 x_t2)))
   (⊢ (bind x_1 x_t1 Γ) e_1 t_1)
   (⊢ (bind x_2 x_t2 Γ) e_2 t_2)
   (con (t_1 = t_2))
   ------ t-case
   (⊢ Γ (case e of (inl x_1 => e_1) (inr x_2 => e_2)) t_1)]

  ; fix
  [(⊢ Γ e t)
   (where x_t (fresh-var))
   (con (t = (x_t -> x_t)))
   ------ t-fix
   (⊢ Γ (fix e) x_t)]

  [(⊢ (bind x t Γ) e_1 t_1)
   (⊢ (bind x t Γ) e_2 t_2)
   (con (t_1 = t))
   ------ t-letrec
   (⊢ Γ (letrec! x : t = e_1 in e_2) t_2)]

  ; list
  [(where x_t (fresh-var))
   ------ t-nil
   (⊢ Γ nil x_t)]

  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (con (t_2 = (List t_1)))
   ------ t-link
   (⊢ Γ (link e_1 e_2) t_2)]

  [(⊢ Γ e t)
   (where x_t (fresh-var))
   (con (t = (List x_t)))
   ------ t-isnil
   (⊢ Γ (isnil e) Bool)]

  [(⊢ Γ e t)
   (where x_t (fresh-var))
   (con (t = (List x_t)))
   ------ t-head
   (⊢ Γ (head e) x_t)]

  [(⊢ Γ e t)
   (where x_t (fresh-var))
   (con (t = (List x_t)))
   ------ t-tail
   (⊢ Γ (tail e) t)]

  ; exceptions

  [(⊢ Γ e t)
   (where x_ret (fresh-var))
   (con (t = String))
   ------ t-raise
   (⊢ Γ (raise e) x_ret)]

  [(⊢ Γ e t)
   (⊢ Γ e_catch t_catch)
   (con (t_catch = (String -> t)))
   ------ t-try
   (⊢ Γ (try e with e_catch) t)]

  ; record
  [(⊢rec Γ eRec tRec)
   ------ t-rec
   (⊢ Γ (record eRec) (Record tRec))]

  [(⊢ Γ e t_e)
   (where x_rec (fresh-var))
   (con (t_e = (Record x_rec)))
   (@rec x_rec x t)
   ------ t-dot
   (⊢ Γ (dot e x) t)]

  ; exists
  [(⊢ Γ e t_e)
   (con (t_e = (substitute t_2 x t)))
   ------ t-pack
   (⊢ Γ (∃ t e as (∃ x t_2)) (∃ x t_2))]

  [(⊢ Γ e_def t_def)
   (where x_ex (fresh-var))
   (con (t_def = (∃ x_t x_ex)))
   (⊢ (bind x x_ex Γ) e_body t_body)
   ------ t-unpack
   (⊢ Γ (let (∃ x_t x) = e_def in e_body) t_body)]

  ; begin
  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   ------ t-begin
   (⊢ Γ (begin e_1 e_2) t_2)]

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

  [(where x_val (fresh-var))
   (where x_rest (fresh-var))
   (con (x_rec = (field x x_val x_rest)))
   ------ t-rec-at-row
   (@rec x_rec x x_val)]

  #;[(where x_t (fresh-var))
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

  [(where y (fresh-var))
   (con (assumption (x @ n$ = y)))
   ------ t-at-premise
   (@t x n$ y)])

