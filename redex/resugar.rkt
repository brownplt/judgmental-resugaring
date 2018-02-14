#lang racket

(require redex)
(require "unify.rkt")
(require "base-lang.rkt")

(provide (all-defined-out)
         ds-rule define-global
         (struct-out Resugared)
         test-match
         global-exists? get-global variable?
         fresh-type-var fresh-type-var-named atom->type-var unfreshen
         apply-rule)

;; TODO:
;;   - allow sugars to build on each other
;;   - use syntax 'pack' and 'unpack'
;;   - reverse order of 'bind'
;;   - in shown derivations, include extension rule at bottom

;; --------------------------------------------------------------------------------------------------- 
;; This file tests type resugaring for a language consisting of:
;;   booleans   (TAPL pg.93)
;;   numbers    (TAPL pg.93)
;;   stlc       (TAPL pg.103)
;;   unit       (TAPL pg.119)
;;   ascription (TAPL pg.122)
;;   let        (TAPL pg.124)
;;   pairs      (TAPL pg.126)
;;   tuples     (TAPL pg.128)
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



(define-syntax-rule (resugar lang rule ⊢)
  (resugar-rule lang rule ⊢))

(define-syntax-rule (define-resugarable-language the-lang #:keywords (kw ...) grammar-ext ...)
  (begin
    (set-language-literals! 'the-lang (set 'kw ...))
    (define-extended-language the-lang base-syntax
      grammar-ext ...)))

(define-syntax (define-core-type-system stx)
  (syntax-case stx ()
    [(define-core-type-system THE_LANG TYPE_RULE ...)

 (datum->syntax stx (syntax->datum #'(begin
    
    (define-judgment-form THE_LANG
      #:contract (⊢ Γ e t)
      #:mode (⊢ I I O)
      TYPE_RULE ...

      [(where x_t ,(atom->type-var (term s))) ; TODO: safety checks!
       (con (,(unfreshen (term Γ)) ⊢ s : x_t))
       ------ t-premise
       (⊢ Γ s x_t)]

      [(⊢ Γ e_1 t_3)
       (con (t_1 = t_3))
       (⊢ Γ e_2 t_2)
       ------ t-calctype
       (⊢ Γ (calctype e_1 as t_1 in e_2) t_2)]

      [(⊢* Γ e*_1 t*_3)
       (con (t*_1 = t*_3))
       (⊢ Γ e_2 t_2)
       ------ t-calctype*
       (⊢ Γ (calctype* e*_1 as t*_1 in e_2) t_2)])
    
    (define-metafunction THE_LANG
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

    (define-metafunction THE_LANG
      lookup-recur : x Γ -> any ; (t or #f)
      [(lookup-recur x (bind x t Γ)) t]
      [(lookup-recur x (bind x_2 t Γ))
       (lookup-recur x Γ)
       (side-condition (not (equal? (term x) (term x_2))))]
      [(lookup-recur x Γ)
       #f])

    (define-metafunction THE_LANG
      fresh-var : -> x
      [(fresh-var)
       ,(fresh-type-var)])

    (define-metafunction THE_LANG
      append : Γ Γ -> Γ
      [(append (bind x t Γ_1) Γ_2)
       (bind x t (append Γ_1 Γ_2))]
      [(append ϵ Γ)
       Γ]
      [(append (bind* x* t* ϵ) Γ)
       (bind* x* t* Γ)])

    #;(define-metafunction THE_LANG
      bind* : x* t* Γ -> Γ
      [(bind* ϵ ϵ Γ) Γ]
      [(bind* (cons x x*) (cons t t*) Γ)
       (bind x t (bind* x* t* Γ))]
      [(bind* x_s x_ts Γ)
       (binds x_s x_ts Γ)])

    (define-judgment-form THE_LANG
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

    (define-judgment-form THE_LANG
      #:contract (⊢* Γ e* t*)
      #:mode (⊢* I I O)

      [(⊢ Γ e t)
       (⊢* Γ e* t*)
       ------ t-cons
       (⊢* Γ (cons e e*) (cons t t*))]

      [------ t-empty
       (⊢* Γ ϵ ϵ)]

      [(where x_t* ,(atom->type-var (term a)))
       (con (,(unfreshen (term Γ)) ⊢* a : x_t*))
       ------ t-premise*
       (⊢* Γ a x_t*)])

    (define-judgment-form THE_LANG
      #:contract (⊢rec Γ eRec tRec)
      #:mode (⊢rec I I O)

      [(⊢ Γ e t)
       (⊢rec Γ eRec tRec)
       ------ t-rec-cons
       (⊢rec Γ (field x e eRec) (field x t tRec))]

      [------ t-rec-empty
       (⊢rec Γ ϵ ϵ)])

    (define-judgment-form THE_LANG
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
       (@rec x_rec x x_val)])

    (define-judgment-form THE_LANG
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
       (@t x n$ y)]))))]))

; for testing
(define-syntax-rule (test-match lang e x)
  (redex-match lang e (term x)))


