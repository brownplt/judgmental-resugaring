#lang racket

(require redex)

(provide resugar-rule unfreshen atom-type-var fresh-type-var (rename-out (make-rule rule))
         (struct-out Resugared))

;; assumption: Redex model does not contain #f

;; ------------------------------------------------------------
;; Desugaring Rules

(define fresh-vars (make-parameter #f))

(define (fresh-binding? binding)
  (boolean (member (car binding) (fresh-vars))))

(define (unfreshen Γ)
  (filter (λ (b) (not (fresh-binding? b))) Γ))

(define-struct DsRule (name fresh lhs rhs))

(define-syntax-rule (make-rule name #:fresh (fresh-name ...) lhs rhs)
  (DsRule name (list 'fresh-name ...) (term lhs) (term rhs)))

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

(define (atom-type-var atom)
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


;; ------------------------------------------------------------
;; Judgements and Equations

(define (display-judgement j)
  (display (format "  ~a ⊢ ~a : ~a\n" (judgement-env j) (judgement-id j) (judgement-type j))))

(define (display-equation eq)
  (display (format "  ~a = ~a\n" (equation-left eq) (equation-right eq))))

(define-struct judgement (env id type))

(define-struct equation (left right))

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

(define (display-unification unif)
  (hash-for-each (unification-judgements unif)
                 (lambda (x j) (display-judgement j)))
  (hash-for-each (unification-types unif)
                 (lambda (x t) (display (format "  ~a = ~a\n" x t)))))

(define-struct unification (judgements types))

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
                (judgement-id expr)
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
    [(judgement? t)
     (judgement (recur (judgement-env t))
                (judgement-id t)
                (recur (judgement-type t)))]
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

(define-struct Resugared (derivation rule))

(define (make-sugar-rule name conclusion unif)
  (derivation (substitute unif conclusion)
              name
              (map (lambda (eq) (derivation eq "assume" (list)))
                   (unification-judgement-list unif))))

(define-syntax-rule (resugar-rule rule ty literals)
  (parameterize ([fresh-vars (DsRule-fresh rule)])
    (reset-char!)
    (let [[derivations (build-derivations (ty [] ,(DsRule-rhs rule) _))]]
      (when (not (eq? 1 (length derivations)))
        (display (DsRule-rhs rule)) (newline)
        (error 'derive "Expected exactly one derivation, but found ~a derivations for ~a"
               (length derivations)
               (DsRule-name rule)))
      (let [[deriv (first derivations)]]
        (parameterize [[language-literals literals]]
          (display "Deriv found!") (newline)
          (display deriv) (newline)
          (let* [[unif (unify (map read-eq (get-constraints deriv))
                              (new-unification))]
                 [concl-type (fourth (derivation-term deriv))]
                 [concl-env (second (derivation-term deriv))]
                 [concl (list concl-env '⊢ (term ,(DsRule-lhs rule)) ': concl-type)]]
            (Resugared
             deriv
             (make-sugar-rule (DsRule-name rule) concl unif))))))))


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
      [#f (insert-judgement unif x (substitute unif j1))]
      [j2 (equate-judgements j1 j2 unif)])))

(define (equate-judgements j1 j2 unif)
  (match* [j1 j2]
    [[(judgement Γ1 x t1) (judgement Γ2 x t2)]
     (equate-envs Γ1 Γ2 (equate t1 t2 unif))]))

(define (equate-envs Γ1 Γ2 unif)
  ; TODO: A simplification
  (equate Γ1 Γ2 unif))

(define (equate x y unif)
  (display "equate\n")
  (display x) (newline) (display y) (newline)
  (display-unification unif) (newline)
  (match* [x y]
    [[(? variable? x) t]
     ; Maintain the invarient that `subs` is a well-formed substitution:
     ; it does not contain any of its variables in their definitions.
     (let ([t (substitute unif t)])
       (if (occurs? x t)
           (begin (display "occurs") (newline)
                  (if (variable? t)
                      (begin (display "--var")(newline) unif)
                      (occurs-error x t)))
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


;; ------------------------------------------------------------
;; Tests

(module+ test
  (require rackunit)
  
  (define unif1 (equate 'Y 'Y (new-unification)))
  (check-equal? (hash-count (unification-types unif1)) 0)
  
  (define unif2 (equate 'X 'Y (new-unification)))
  (check-equal? (substitute unif2 (list (list 'X))) (list (list 'Y)))

  (define unif3 (equate 'B 'C (equate 'A (list 'B 'C) (new-unification))))
  (check-equal? (substitute unif3 'B) 'C)
  (check-equal? (substitute unif3 'A) (list 'C 'C))

  (check-equal? (occurs? 'X 'X) true)
  (check-equal? (occurs? 'X '(List X)) true))
















