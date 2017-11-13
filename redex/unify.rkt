#lang racket

(require redex)
(require "base-lang.rkt")

(provide
 ; resugaring
 (rename-out (resugar-rule resugar))
 (struct-out Resugared)
 ; desugaring rules
 (rename-out (make-rule rule))
 ; freshness
 fresh-type-var
 fresh-type-var-named
 atom->type-var
 unfreshen
 ; globals
 define-global
 global-exists?
 get-global
 ; misc
 (rename-out (regular-variable? variable?)))

;; assumption: Redex model does not contain #f

;; ------------------------------------------------------------
;; Desugaring Rules

(define fresh-vars (make-parameter #f))

(define (unfreshen Γ)
  (match Γ
    ['ϵ 'ϵ]
    [(? variable?) Γ]
    [(list 'bind x t Γ)
     (if (member x (fresh-vars))
         (unfreshen Γ)
         (list 'bind x t (unfreshen Γ)))]))

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

(define the-names (make-hash))

(define (next-name-index name)
  (if (hash-has-key? the-names name)
      (let [[i (hash-ref the-names name)]]
        (hash-set! the-names name (+ i 1))
        i)
      (begin
        (hash-set! the-names name 2)
        1)))

(define (next-name name)
  (let [[i (next-name-index name)]]
    (string->symbol (string-append (symbol->string name)
                                   (number->string i)))))

(define (reset-names!)
  (set! the-char (char->integer #\A))
  (set! the-names (make-hash)))

(define (fresh-type-var-named name)
  (next-name name))

(define (fresh-type-var)
  (string->symbol (make-string 1 (next-char))))

(define (atom->type-var atom)
  (fresh-type-var))


;; ------------------------------------------------------------
;; Language Literals

(define language-literals (make-parameter (set)))

(define meta-literals (set 'cons 'field 'bind 'ϵ))

(define (pattern-variable? x)
  (string-prefix? (symbol->string x) "~"))

(define (regular-variable? x)
  (and (variable? x) (not (pattern-variable? x))))

(define (variable? x)
  (and (symbol? x)
       (and (not (set-member? (language-literals) x))
            (not (set-member? meta-literals x)))))

(define (literal? x)
  (and (symbol? x)
       (set-member? (language-literals) x)))

(define (get-variables t)
  (match t
    [(? variable?) (set t)]
    [(? literal?)  (set)]
    [(? number?)   (set)]
    [(? string?)   (set)]
    ['ϵ            (set)]
    [(list 'cons expr exprs)
     (set-union (get-variables expr) (get-variables exprs))]
    [(list 'field x expr exprs)
     (set-union (get-variables expr) (get-variables exprs))]
    [(list 'bind x expr exprs)
     (set-union (get-variables expr) (get-variables exprs))]
    [(? list?)
     (foldl set-union (set) (map get-variables t))]))



;; ------------------------------------------------------------
;; Globals

(define language-globals (make-hash))

(define (global-exists? x)
  (hash-has-key? language-globals x))

(define (get-global x)
  (hash-ref language-globals x))

(define-syntax-rule (define-global x type)
  (hash-set! language-globals 'x (term type)))


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
    [(list '⋖ a b)
     (Assumption (list '⋖ a b))]
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
    [(string-prefix? (derivation-name d) "con-")
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
  (match expr
    [(? variable? expr)
     (if (equal? expr x) t expr)]
    [(? literal? expr)  expr]
    ['ϵ 'ϵ]
    [(list 'cons expr exprs)
     (list 'cons (recur expr) (recur exprs))]
    [(list 'field x expr exprs)
     (list 'field x (recur expr) (recur exprs))]
    [(list 'bind x expr exprs)
     (list 'bind x (recur expr) (recur exprs))]
    [(? list? expr)
     (map recur expr)]
    [(? Unification? expr)
     (Unification (map-hash recur (Unification-judgements expr))
                  (map-hash recur (Unification-types expr))
                  (map recur (Unification-assumptions expr)))] ; TODO: make robust
    [(? Judgement? expr)
     (Judgement (recur (Judgement-env expr))
                (Judgement-id expr)
                (recur (Judgement-type expr)))]
    [_ (error 'replace "fell off match")]))

(define (substitute unif t)
  (define (recur t) (substitute unif t))
  (match t
    [(? literal? t) t]
    [(? variable? t)
     (match (lookup-type t unif)
       [#f t]
       [t2 t2])]
    ['ϵ 'ϵ]
    [(list 'cons t ts)
     (list 'cons (recur t) (recur ts))]
    [(list 'field x t ts)
     (list 'field x (recur t) (recur ts))]
    [(list 'bind x t ts)
     (list 'bind x (recur t) (recur ts))]
    [(list x '⋖ y)
     (list (substitute unif x) '⋖ (substitute unif y))]
    [(? list? t)
     (map recur t)]
    [(? Judgement? t)
     (Judgement (recur (Judgement-env t))
                (Judgement-id t)
                (recur (Judgement-type t)))]
    [_ (error 'substitute "fell off cond ~a" t)]))

(define (occurs? x t)
  (define (recur t) (occurs? x t))
  (match t
    [(? variable? t)      (equal? x t)]
    [(? literal? t)       #f]
    ['ϵ                   #f]
    [(list 'cons t ts)    (or (recur t) (recur ts))]
    [(list 'field _ t ts) (or (recur t) (recur ts))]
    [(list 'bind _ t ts)  (or (recur t) (recur ts))]
    [(? list? t)          (ormap recur t)]
    [else                 (error 'occurs? "fell off match")]))


;; ------------------------------------------------------------
;; Errors

(define (unification-error x y)
  (error 'unify "Could not unify `~a` with `~a`" x y))

(define (occurs-error x t)
  (error 'unify "Occurs check failure: `~a` occurs in `~a`" x t))

(define (resugar-error rule derivations)
  (error 'derive "Expected exactly one derivation, but found ~a derivations for ~a. In deriation rule: ~a.\n\n~a"
         (length derivations)
         (DsRule-name rule)
         (DsRule-rhs rule)
         derivations))


;; ------------------------------------------------------------
;; Resugaring

(define-struct Resugared (derivation rule))

(define (make-sugar-rule name conclusion unif)
  (let* ([make-assum (lambda (eq) (derivation eq "assume" (list)))]
         [premises (map make-assum (unification-judgement-list unif))]
         [assumptions (map (λ (a) (make-assum (substitute unif a)))
                           (Unification-assumptions unif))])
  (derivation (substitute unif conclusion)
              name
              (append premises assumptions))))

(define (found-derivation! deriv)
  #;(show-derivations (list deriv))
  (printf "Derivation found!\n~a\n" deriv))

#;(define (resugar-premise unif premise)
  (let [[premise (substitute unif premise)]]
    (let [[derivs (dynamic-build-derivations premise)]]
      (match (length derivs)
        [0 (list premise)]
        [1 (get-premises (first derivs))]
        [_ (error/ambiguous-premise premise)]))))

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
    (reset-names!)
    (let [[derivations (build-derivations (ty Γ ,(DsRule-rhs rule) _))]]
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
  (printf "~a = ~a\n" x y)
  (define (take-field x rec) ; overloaded for 'bind
    (match rec
      ['ϵ (values #f rec)]
      [(? variable? _) (values #f rec)]
      [(list (or 'field 'bind) y val rest)
       (if (equal? x y)
           (values val rest)
           (let-values [[[val* rec*] (take-field x rest)]]
             (if val*
                 (values val* (list (car rec) y val rec*))
                 (values #f rec))))]))
  
  (define (equate-fields name rec1 rec2 unif) ; overloaded for 'bind
    (printf "~a =r ~a\n" rec1 rec2)
    (define (recur rec1 rec2 um1 um2 unif)
      (printf "  ~a =u ~a & ~a & ~a\n" rec1 rec2 um1 um2)
      (match* [rec1 rec2]
        [[(list (or 'field 'bind) x val1 rec1*) _]
         (let-values [[[val2 rec2] (take-field x rec2)]]
           (if val2
               (equate val1 val2 (recur rec1* rec2 um1 um2 unif))
               (recur rec1* rec2 (list (car rec1) x val1 um1) um2 unif)))]
      [[_ (list (or 'field 'bind) y val2 rec2*)]
       (recur rec1 rec2* um1 (list (car rec2) y val2 um2) unif)]
      [[(or 'ϵ (? variable?)) (or 'ϵ (? variable?))]
       (equate rec1 um2 (equate rec2 um1 unif))]))
    (let [[t (fresh-type-var-named name)]]
      (recur rec1 rec2 t t unif)))

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
    [[(list 'cons x xs) (list 'cons y ys)]
     (equate x y (equate xs ys unif))]
    ; records
    [[(list 'field _ _ _)
      (list 'field _ _ _)]
     (equate-fields 'ρ x y unif)]
    ; environments
    [[(list 'bind _ _ _)
      (list 'bind _ _ _)]
     (equate-fields 'Γ x y unif)]
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

(define-syntax (dynamic-build-derivations stx)
  (syntax-case stx ()
    [(dynamic-build-derivations x)
     (with-syntax [[a (eval-syntax #'x)]]
       #'(build-derivations a))]))



;; ------------------------------------------------------------
;; Tests

(module+ test
  (require test-engine/racket-tests)
  
  (define unif1 (equate 'Y 'Y (new-unification)))
  (check-expect (hash-count (Unification-types unif1)) 0)
  
  (define unif2 (equate 'X 'Y (new-unification)))
  (check-expect (substitute unif2 (list (list 'X))) (list (list 'Y)))

  (define unif3 (equate 'B 'C (equate 'A (list 'B 'C) (new-unification))))
  (check-expect (substitute unif3 'B) 'C)
  (check-expect (substitute unif3 'A) (list 'C 'C))

  (check-expect (occurs? 'X 'X) true)
  (check-expect (occurs? 'X '(List X)) true)

  (check-expect (get-variables '((cons (field x x (field y z r)) (q 3)) w))
                (set 'x 'z 'r 'q 'w))

  (check-expect (replace 'x '(field y 1 ϵ) '(field x y x))
                '(field x y (field y 1 ϵ)))

  (check-expect (occurs? 'x '(cons y (field c z w))) #f)
  (check-expect (occurs? 'y '(cons y (field c z w))) #t)
  (check-expect (occurs? 'z '(cons y (field c z w))) #t)
  (check-expect (occurs? 'w '(cons y (field c z w))) #t)
  
  (define unif4 (equate '(field a X (field b Y row1)) 'd
                        (equate 'd '(field c Z (field b W row2))
                                (new-unification))))
  (check-expect (substitute unif4 '(d row1 row2))
                '((field c Z (field b Y (field a X ρ1)))
                  (field c Z ρ1)
                  (field a X ρ1)))
  
  (define unif5 (equate '(field a X (field b X ϵ))
                        '(field a Y row)
                        (new-unification)))
  (check-expect (substitute unif5 'row)
                '(field b Y ϵ))

  (define unif6 (equate '(field a Y (field b Z ϵ)) 'r
                        (equate '(field a X (field b X ϵ)) 'r
                                (new-unification))))
  (check-expect (substitute unif6 'r)
                '(field a Y (field b Y ϵ)))

  (check-error (equate '(field a X ϵ)
                       '(field a Y (field b Z row))
                       (new-unification)))

  (test))
