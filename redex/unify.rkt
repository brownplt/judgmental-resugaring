#lang racket

(require redex)
(require "base-lang.rkt")

(provide
 ; resugaring
 resugar-rule
 (struct-out Resugared)
 ; desugaring rules
 (rename-out (make-rule rule))
 ; freshness
 fresh-type-var
 atom->type-var
 unfreshen
 ; globals
 define-global
 global-exists?
 get-global)

;; assumption: Redex model does not contain #f

;; ------------------------------------------------------------
;; Desugaring Rules

(define fresh-vars (make-parameter #f))

(define (fresh-binding? binding)
  (member (car binding) (fresh-vars)))

(define (unfreshen Γ)
  (filter (λ (b) (not (fresh-binding? b))) Γ))

(define-struct DsRule (name fresh lhs rhs))

(define (get-fresh-vars captures lhs rhs)
  (set-subtract (get-variables rhs)
                (get-variables lhs)
                captures))

(define-syntax-rule
  (make-rule name #:capture (capture-name ...) lhs rhs)
  (let [[fresh (get-fresh-vars (set 'capture-name ...) (term lhs) (term rhs))]]
    (DsRule name (set->list fresh) (term lhs) (term rhs))))


;; ------------------------------------------------------------
;; Fresh Types

; TODO: no-one will ever need more than 26 type variables, right?
(define the-char (char->integer #\A))

(define (next-char)
  (let ([ch (integer->char the-char)])
    (set! the-char (+ the-char 1))
    ch))

(define (reset-char!)
  (set! the-char (char->integer #\A)))

(define (fresh-type-var)
  (string->symbol (make-string 1 (next-char))))

(define (atom->type-var atom)
  (fresh-type-var))


;; ------------------------------------------------------------
;; Language Literals

(define language-literals (make-parameter (set)))

(define (variable? x)
  (and (symbol? x)
       (not (set-member? (language-literals) x))))

(define (literal? x)
  (and (symbol? x)
       (set-member? (language-literals) x)))

(define (get-variables t)
  (cond
    [(variable? t) (set t)]
    [(literal? t) (set)]
    [(number? t) (set)]
    [(list? t) (foldl set-union (set) (map get-variables t))]
    [else (error 'get-variables "fell off cond ~a" t)]))



;; ------------------------------------------------------------
;; Globals

(define language-globals (make-hash))

(define (global-exists? x)
  (hash-has-key? language-globals x))

(define (get-global x)
  (hash-ref language-globals x))

(define (define-global x type)
  (hash-set! language-globals x type))


;; ------------------------------------------------------------
;; Premises: Judgements, Equations, and Assumptions

(define (display-judgement j)
  (display (format "  ~a ⊢ ~a : ~a\n" (Judgement-env j) (Judgement-id j) (Judgement-type j))))

(define (display-equation eq)
  (display (format "  ~a = ~a\n" (Equation-left eq) (Equation-right eq))))

(define-struct Judgement (env id type))

(define-struct Equation (left right))

(define-struct Assumption (contents))

(define (read-premise p)
  (match p
    [(list a '= b)
     (Equation a b)]
    [(list Γ '⊢ x ': t)
     (Judgement Γ x t)]
    [(list 'assumption contents)
     (Assumption contents)]))

(define (write-premise x eq)
  (cond
    [(and (list? eq) (equal? (car eq) 'ty))
     (match eq
       [(list 'ty Γ e t) (list Γ '⊢ e ': t)]
       [_ (error 'write-premise "fell off match")])]
    [(Judgement? eq)
     (let [[Γ (Judgement-env eq)]
           [x (Judgement-id eq)]
           [t (Judgement-type eq)]]
       (list Γ '⊢ x ': t))]
    [else
     (list x '= eq)]))

(define (get-premises d)
  (when (not (derivation? d))
    (error 'get-premises "expected a derivation, but found ~a" d))
  (cond
    [(eq? (derivation-name d) "t-equal")
     (list (cadr (derivation-term d)))]
    [(eq? (derivation-name d) "t-judge")
     (list (cadr (derivation-term d)))]
    [(eq? (derivation-name d) "t-assum")
     (list (cadr (derivation-term d)))]
    [else
     (apply append (map get-premises (derivation-subs d)))]))


;; ------------------------------------------------------------
;; Unification (data structure)

(define-struct Unification (judgements types assumptions))

(define (display-unification unif)
  (hash-for-each (Unification-judgements unif)
                 (lambda (x j) (display-judgement j)))
  (hash-for-each (Unification-types unif)
                 (lambda (x t) (display (format "  ~a = ~a\n" x t))))
  (map (lambda (x) (display (format "  ~a\n") x))
       (Unification-assumptions unif)))

(define (new-unification)
  (Unification (make-immutable-hash)
               (make-immutable-hash)
               (list)))

(define (insert-judgement unif x j)
  (Unification (hash-set (Unification-judgements unif) x j)
               (Unification-types unif)
               (Unification-assumptions unif)))

(define (insert-type unif x t)
  (Unification (Unification-judgements unif)
               (hash-set (Unification-types unif) x t)
               (Unification-assumptions unif)))

(define (insert-assumption unif assum)
  (Unification (Unification-judgements unif)
               (Unification-types unif)
               (cons assum (Unification-assumptions unif))))

(define (lookup-judgement x unif)
  (hash-lookup (Unification-judgements unif) x))

(define (lookup-type x unif)
  (hash-lookup (Unification-types unif) x))

(define (unification-judgement-list unif)
  (let [[hash (Unification-judgements unif)]]
    (map (lambda (x) (write-premise x (hash-ref hash x)))
         (hash-keys hash))))


;; ------------------------------------------------------------
;; Substitution

(define (replace x t expr)
  (define (recur expr)
    (replace x t expr))
  (cond
    [(variable? expr) (if (equal? expr x) t expr)]
    [(literal? expr)  expr]
    [(list? expr)     (map recur expr)]
    [(Unification? expr)
     (Unification (map-hash recur (Unification-judgements expr))
                  (map-hash recur (Unification-types expr))
                  (map recur (Unification-assumptions expr)))] ; TODO: make robust
    [(Judgement? expr)
     (Judgement (recur (Judgement-env expr))
                (Judgement-id expr)
                (recur (Judgement-type expr)))]
    [else (error 'replace "fell off cond")]))

(define (substitute unif t)
  (define (recur t) (substitute unif t))
  (cond
    [(literal? t) t]
    [(variable? t)
     (match (lookup-type t unif)
       [#f t]
       [t2 t2])]
    [(list? t)
     (map recur t)]
    [(Judgement? t)
     (Judgement (recur (Judgement-env t))
                (Judgement-id t)
                (recur (Judgement-type t)))]
    [else (error 'substitute "fell off cond ~a" t)]))

(define (occurs? x t)
  (define (recur t) (occurs? x t))
  (cond
    [(variable? t) (equal? x t)]
    [(literal? t)  #f]
    [(list? t)     (ormap recur t)]
    [else          (error 'occurs? "fell off cond")]))


;; ------------------------------------------------------------
;; Errors

(define (unification-error x y)
  (error 'unify "Could not unify `~a` with `~a`" x y))

(define (occurs-error x t)
  (error 'unify "Occurs check failure: `~a` occurs in `~a`" x t))

(define (resugar-error rule derivations)
  (error 'derive "Expected exactly one derivation, but found ~a derivations for ~a. In deriation rule: ~a"
         (length derivations)
         (DsRule-name rule)
         (DsRule-rhs rule)))


;; ------------------------------------------------------------
;; Resugaring

(define-struct Resugared (derivation rule))

(define (make-sugar-rule name conclusion unif)
  (let* ([make-assum (lambda (eq) (derivation eq "assume" (list)))]
         [premises (map make-assum (unification-judgement-list unif))]
         [assumptions (map make-assum (Unification-assumptions unif))])
  (derivation (substitute unif conclusion)
              name
              (append premises assumptions))))

(define (found-derivation! deriv)
  (printf "Derivation found!\n~a\n" deriv))

(define (resugar-derivation rule deriv)
  (let* [[premises (map read-premise (get-premises deriv))]
         [unif (unify premises (new-unification))]
         [concl-type (fourth (derivation-term deriv))]
         [concl-env (second (derivation-term deriv))]
         [concl (write-premise #f (Judgement concl-env (DsRule-lhs rule) concl-type))]
         [tyrule (make-sugar-rule (DsRule-name rule) concl unif)]]
    (Resugared deriv tyrule)))

(define-syntax-rule (resugar-rule rule ty literals globals)
  (parameterize ([fresh-vars (DsRule-fresh rule)]
                 [language-literals literals])
    (reset-char!)
    (let [[derivations (build-derivations (ty [] ,(DsRule-rhs rule) _))]]
      (when (not (eq? 1 (length derivations)))
        (resugar-error rule derivations))
      (let [[deriv (first derivations)]]
        (found-derivation! deriv)
        (resugar-derivation rule deriv)))))


;; ------------------------------------------------------------
;; Unification

(define (unify eqs unif)
  (match eqs
    [(list) unif]
    [(cons (Equation x y) eqs)
     (unify eqs (equate x y unif))]
    [(cons (Assumption assum) eqs)
     (unify eqs (insert-assumption unif assum))]
    [(cons (? Judgement? j) eqs)
     (unify eqs (add-judgement j unif))]))

(define (add-judgement j1 unif)
  (let [[x (Judgement-id j1)]]
    (match (lookup-judgement x unif)
      [#f (insert-judgement unif x (substitute unif j1))]
      [j2 (equate-judgements j1 j2 unif)])))

(define (equate-judgements j1 j2 unif)
  (match* [j1 j2]
    [[(Judgement Γ1 x t1) (Judgement Γ2 x t2)]
     (equate-envs Γ1 Γ2 (equate t1 t2 unif))]))

(define (equate-envs Γ1 Γ2 unif)
  ; TODO: A simplification
  (equate Γ1 Γ2 unif))

(define (equate x y unif)
  (match* [x y]
    [[(? variable? x) t]
     ; Maintain the invarient that `subs` is a well-formed substitution:
     ; it does not contain any of its variables in their definitions.
     (let ([t (substitute unif t)])
       (if (occurs? x t)
           (if (variable? t)
               unif
               (occurs-error x t))
           (match (lookup-type x unif)
             [#f (insert-type (replace x t unif) x t)]
             [t2 (equate t2 t unif)])))]
    ; symmetric case
    [[t (? variable? x)]
     (equate x t unif)]
    ;; Potentially language-specific. This may work for now.
    [[(? literal? x) y]
     (when (not (equal? x y))
       (unification-error x y))
     unif]
    ; symmetric case
    [[x (? literal? y)]
     (equate y x unif)]
    ; lists
    [['ϵ 'ϵ]
     unif]
    [[(list x ': xs) (list y ': ys)]
     (equate x y (equate xs ys unif))]
    ; Compound expressions - TODO: not general
    [[(list-rest xs) (list-rest ys)]
     (when (not (equal? (length xs) (length ys)))
       (unification-error xs ys))
     (foldl equate unif xs ys)]
    ; Do not match
    [[_ _]
     (unification-error x y)]))


;; ------------------------------------------------------------
;; Utility

(define (boolean x)
  (if x #t #f))

(define (map-hash f hash)
  (define (update key hash)
    (hash-update hash key f))
  (foldl update hash (hash-keys hash)))

(define (hash-lookup hash key)
  (if (hash-has-key? hash key)
      (hash-ref hash key)
      #f))


;; ------------------------------------------------------------
;; Tests

(module+ test
  (require rackunit)
  
  (define unif1 (equate 'Y 'Y (new-unification)))
  (check-equal? (hash-count (Unification-types unif1)) 0)
  
  (define unif2 (equate 'X 'Y (new-unification)))
  (check-equal? (substitute unif2 (list (list 'X))) (list (list 'Y)))

  (define unif3 (equate 'B 'C (equate 'A (list 'B 'C) (new-unification))))
  (check-equal? (substitute unif3 'B) 'C)
  (check-equal? (substitute unif3 'A) (list 'C 'C))

  (check-equal? (occurs? 'X 'X) true)
  (check-equal? (occurs? 'X '(List X)) true))
