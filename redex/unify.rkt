#lang racket

(require redex)

(provide resugar unfreshen atom-type-var (rename-out (make-rule rule)))

;; assumption: Redex model does not contain #f

(define (atom-type-var atom)
  (string->symbol (string-upcase (symbol->string atom))))

;; ------------------------------------------------------------
;; Desugaring Rules

(define fresh-vars (make-parameter #f))

(define (fresh-binding? binding)
  (boolean (member (car binding) (fresh-vars))))

(define (unfreshen Γ)
  (filter (λ (b) (not (fresh-binding? b))) Γ))

(define-struct ds-rule (name fresh lhs rhs))

(define-syntax-rule (make-rule name #:fresh (fresh-name ...) lhs rhs)
  (ds-rule name (list 'fresh-name ...) (term lhs) (term rhs)))


;; ------------------------------------------------------------
;; Language Literals

(define language-literals (make-parameter #f))

(define (variable? x)
  (and (symbol? x)
       (not (set-member? (language-literals) x))))

(define (literal? x)
  (and (symbol? x)
       (set-member? (language-literals) x)))


;; ------------------------------------------------------------
;; Judgements and Equations

(define (print-judgement j port mode)
  (show (format "  ~a ⊢ ~a : ~a\n" (judgement-env j) (judgement-id j) (judgement-type j))
        port mode))

(define (print-equation eq port mode)
  (show (format "  ~a = ~a\n" (equation-left eq) (equation-right eq))
        port mode))

(define-struct judgement (env id type)
  #:methods gen:custom-write
  [(define write-proc print-judgement)])

(define-struct equation (left right)
  #:methods gen:custom-write
  [(define write-proc print-equation)])

(define (read-eq eq)
  (match eq
    [(list a '= b)
     (equation a b)]
    [(list Γ '⊢ x ': t)
     (judgement Γ x t)]))

(define (write-eq x eq)
  (cond
    [(and (list? eq) (equal? (car eq) 'ty))
     (match eq
       [(list 'ty Γ e t) (list Γ '⊢ e ': t)]
       [_ (raise "write-eq - fell off match")])]
    [(judgement? eq)
     (let [[Γ (judgement-env eq)]
           [x (judgement-id eq)]
           [t (judgement-type eq)]]
       (list Γ '⊢ x ': t))]
    [else
     (list x '= eq)]))

(define (get-constraints d)
  (when (not (derivation? d))
    (error 'get-constraints "expected a derivation, but found ~a" d))
  (cond
    [(eq? (derivation-name d) "t-equal")
     (list (cadr (derivation-term d)))]
    [(eq? (derivation-name d) "t-judge")
     (list (cadr (derivation-term d)))]
    [else
     (apply append (map get-constraints (derivation-subs d)))]))


;; ------------------------------------------------------------
;; Unifications

(define (print-unification unif port mode)
  (hash-for-each (unification-judgements unif)
                 (lambda (x j) (show-recur j port mode)))
  (hash-for-each (unification-types unif)
                 (lambda (x t) (show (format "  ~a = ~a\n" x t) port mode))))

(define-struct unification (judgements types)
  #:methods gen:custom-write
  [(define write-proc print-unification)])

(define (new-unification)
  (unification (make-immutable-hash) (make-immutable-hash)))

(define (insert-judgement unif x j)
  (unification (hash-set (unification-judgements unif) x j)
               (unification-types unif)))

(define (insert-type unif x t)
  (unification (unification-judgements unif)
               (hash-set (unification-types unif) x t)))

(define (lookup-judgement x unif)
  (hash-lookup (unification-judgements unif) x))

(define (lookup-type x unif)
  (hash-lookup (unification-types unif) x))

(define (unification-judgement-list unif)
  (let [[hash (unification-judgements unif)]]
    (map (lambda (x) (write-eq x (hash-ref hash x))) (hash-keys hash))))


;; ------------------------------------------------------------
;; Substitution

(define (replace x t expr)
  (define (recur expr)
    (replace x t expr))
  (cond
    [(variable? expr) (if (equal? expr x) t expr)]
    [(literal? expr)  expr]
    [(list? expr)     (map recur expr)]
    [(unification? expr)
     (unification (map-hash recur (unification-judgements expr))
                  (map-hash recur (unification-types expr)))]
    [(judgement? expr)
     (judgement (recur (judgement-env expr))
                (recur (judgement-id expr))
                (recur (judgement-type expr)))]
    [else (raise "replace - fell off cond")]))

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
    [else (raise "substitute - fell off cond")]))

(define (occurs? x t)
  (define (recur t) (occurs? x t))
  (cond
    [(variable? t) (equal? x t)]
    [(literal? t)  #f]
    [(list? t)     (ormap recur t)]
    [else          (raise "occurs? - fell off cond")]))


;; ------------------------------------------------------------
;; Unification Errors

(define (unification-error x y)
  (error 'unify "Could not unify `~a` with `~a`" x y))

(define (occurs-error x t)
  (error 'unify "Occurs check failure: `~a` occurs in `~a`" x t))


;; ------------------------------------------------------------
;; Resugaring

(define (render-atoms t)
  (cond
    [(literal? t) t]
    [(variable? t) t]
    [(and (list? t) (not (empty? t)) (equal? 'atom (first t)))
     (second t)]
    [(list? t) (map render-atoms t)]
    [else (raise "render-atoms - fell off cond")]))

(define (make-sugar-rule name unif conclusion)
  (derivation (render-atoms (substitute unif conclusion))
              name
              (map (lambda (eq) (derivation eq "assume" (list)))
                   (unification-judgement-list unif))))

(define-syntax-rule (resugar rule ty literals)
  (parameterize ([fresh-vars (ds-rule-fresh rule)])
    (let [[derivations (build-derivations (ty [] ,(ds-rule-rhs rule) _))]]
      (when (not (eq? 1 (length derivations)))
        (error 'derive "Expected exactly one derivation, but found ~a derivations" (length derivations)))
      (let [[deriv (first derivations)]]
        (parameterize [[language-literals literals]]
          (display (get-constraints deriv)) (newline)
          (let* [[unif (unify (map read-eq (get-constraints deriv))
                              (new-unification))]
                 [concl-type (fourth (derivation-term deriv))]
                 [concl-env (second (derivation-term deriv))]
                 [concl (list concl-env '⊢ (term ,(ds-rule-lhs rule)) ': concl-type)]]
            (make-sugar-rule (ds-rule-name rule) unif concl)))))))


;; ------------------------------------------------------------
;; Unification

(define (unify eqs unif)
  (match eqs
    [(list) unif]
    [(cons (equation x y) eqs)
     (unify eqs (equate x y unif))]
    [(cons (? judgement? j) eqs)
     (unify eqs (add-judgement j unif))]))

(define (add-judgement j1 unif)
  (let [[x (judgement-id j1)]]
    (match (lookup-judgement x unif)
      [#f (insert-judgement unif x j1)]
      [j2 (equate-judgements j1 j2 unif)])))

(define (equate-judgements j1 j2 unif)
  (match* [j1 j2]
    [[(judgement Γ1 x t1) (judgement Γ2 x t2)]
     (equate-envs Γ1 Γ2 (equate t1 t2 unif))]))

(define (equate-envs Γ1 Γ2 unif)
  ; TODO: A simplification
  (equate Γ1 Γ2 unif))

(define (equate x y unif)
  (match* [x y]
    [[(? variable? x) t]
     ; Maintain the invarient that `subs` is a well-formed substitution:
     ; it does not contain any of its variables in their definitions.
     (when (and (not (variable? t)) (occurs? x t))
       (occurs-error x t))
     (match (lookup-type x unif)
       [#f (insert-type (replace x t unif) x (substitute unif t))]
       [t2 (equate t2 t unif)])]
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
    ; Compound expressions
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

(define (show x port mode)
  (when mode (write-string x port)))

(define (show-recur x port mode)
  (case mode
    [(#t) (write x)]
    [(#f) (display x)]
    [else (print x port mode)]))


