#lang racket

(require redex)
(require "unify.rkt")
(require "types.rkt")

;; ---------------------------------------------------------------------------------------------------
;; Desugaring Rules


; capturing example
(define rule_method
  (ds-rule "method" #:capture(this)
        (method (arg : t) ~body)
        (λ ((obj : o)) (λ ((arg : t)) (let this = obj in ~body)))))

; ellipses example
(define rule_ands-empty
  (ds-rule "ands-empty" #:capture()
        (ands (cons ~a ϵ))
        ~a))

(define rule_ands-empty-fixed
  (ds-rule "ands-empty-fixed" #:capture()
        (ands (cons ~a ϵ))
        (calctype ~a as Bool in ~a)))

(define rule_ands-cons
  (ds-rule "ands-cons" #:capture()
        (ands (cons ~a (cons ~b ~cs)))
        (if ~a true (ands (cons ~b ~cs)))))

; exceptions
(define rule_foreach
  (ds-rule "while" #:capture(break)
     (foreach x ~list ~body)
     (letrec! loop : ((List a) (List b) -> (List b)) =
       (λ [(lst : (List a)) (ans : (List b))]
         (if (isnil lst)
             ans
             (try (let! break = (λ [(_ : Unit)] (raise "")) in
                    (let! x = (head lst) in
                      (loop (tail lst) (link ~body ans))))
              with (λ [(_ : String)] ans)))) in
       (loop ~list nil))))

; exists
(define-global id (a -> a))

#;(define rule_newtype ; newtype as a pair
  (ds-rule "newtype" #:capture()
        (let-new-type w of T as X in ~body)
        (let (∃ X w) = (∃ T (pair id id) as
          (∃ X (Pair (T -> X) (X -> T)))) in
          ~body)))

#;(define rule_newtype ; newtype as a record
  (ds-rule "newtype" #:capture()
        (let-new-type w of T as X in ~body)
        (let (∃ X w) = (∃ T (record (field wrap id (field unwrap id ϵ))) as
          (∃ X (Record (field wrap (T -> X) (field unwrap (X -> T) ϵ))))) in
          ~body)))

(define rule_newtype ; newtype as bindings
  (ds-rule "newtype" #:capture()
        (let-new-type (wrap unwrap) of T as X in ~body)
        (let (∃ X w) = (∃ T (pair id id) as
          (∃ X (Pair (T -> X) (X -> T)))) in
          (let! wrap = (fst w) in
            (let! unwrap = (snd w) in
              ~body)))))

; error chaining
(define rule_fail
  (ds-rule "fail" #:capture()
        (fail)
        (raise "%fail")))

(define rule_and-then
  (ds-rule "and-then" #:capture()
        (and-then ~a ~b)
        (begin ~a ~b)))

(define rule_or-else
  (ds-rule "or-else" #:capture()
        (or-else ~a ~b)
        (try ~a with (λ [(err : String)] ~b))))

; cps (https://xavierleroy.org/publi/cps-dargaye-leroy.pdf)
(define rule_cps-var
  (ds-rule "cps-var" #:capture()
        (cps x)
        (calctype x as t in (λ [(k : (t -> Unit))] (k x)))))

(define rule_cps-lambda
  (ds-rule "cps-lambda" #:capture()
        (cps (λ [(x : t)] ~M))
        (calctype (λ [(x : t)] ~M) as (t -> t2) in
          (λ [(k : ((t -> ((t2 -> Unit) -> Unit)) -> Unit))]
            (k (λ [(x : t)] (cps ~M)))))))

(define rule_cps-apply
  (ds-rule "cps-apply" #:capture()
        (cps (~M ~N))
        (calctype ~M as (t1 -> t2) in
          (λ [(k : (t2 -> Unit))]
            ((cps ~M) (λ [(m : (t1 -> ((t2 -> Unit) -> Unit)))]
                        ((cps ~N) (λ [(n : t1)] ((m n) k)))))))))

(define rule_process-stream-1
  (ds-rule "process-stream-1" #:capture()
        (process-stream ϵ)
        false))

(define rule_process-stream-2
  (ds-rule "process-stream-2" #:capture()
        (process-stream (cons (~label -> ~target) ~rest))
        (if (string-eq (head stream) ~label)
            (~target (tail stream))
            ((process-stream ~rest) stream))))

(define rule_process-state
  (ds-rule "process-state" #:capture()
        (process-state ~state)
        (lambda (stream)
          (if (isnil stream)
              true
              (process-stream ~state)))))

(define rule_automaton-1
  (ds-rule "automaton-1" #:capture()
        (automaton ~init-state ϵ)
        ~init-state))

(define rule_automaton-2
  (ds-rule "automaton-2" #:capture()
        (automaton ~init-state (cons (state : ~responses) ~rest))
        (letrec state = (process-state ~responses)
        ~init-state)))


;(define-syntax automaton
;(syntax-rules (:)
;  [( init-state
;    (state : response · · ·)
;    · · ·)
;  (letrec ([state
;    (process-state response · · ·)]
;    · · ·)
;    init-state)]))

;(define-syntax process-state
;(syntax-rules (→)
;[( (label → target) · · ·)
;  (lambda (stream)
;    (cond
;      [(empty? stream) true]
;      [else
;        (case (first stream)
;        [(label) (target (rest stream))]
;        · · ·
;    [else false])]))]))

;[[x]] = λk. k x
;[[λx.M]] = λk. k (λx. [[M]])
;[[M N]] = λk. [[M]] (λm. [[N]] (λn. m n k))

; classes
(define rule_c-new
  (ds-rule "new" #:capture()
        (new C ~args)
        ((dot C construct) ~args)))


#;((     (class x extends x class-body rest)
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




;; ---------------------------------------------------------------------------------------------------
;; Resugaring

; TODO: derive automatically
(define the-literals (set 'λ ': '+ 'pair '-> 'Pair '= 'in
                          'Nat 'Bool 'String
                          'try 'with 'unit 'fix 'if 'cps
                          'true 'false 'Unit 'as 'case 'of 'inl 'inr '=>))

(define (simply-resugar r)
  (let ([resugared (resugar r ⊢ the-literals the-globals)])
    (Resugared-rule resugared)))

(show-derivations
 (map simply-resugar
      (list rule_process-state
            rule_process-stream-1 rule_process-stream-2)
      #;(list rule_fail rule_and-then rule_or-else)
      #;(list rule_cps-var rule_cps-lambda rule_cps-apply)
      #;(list rule_foreach)
      #;(list rule_c-new)
      #;(list rule_newtype)
      #;(list rule_rec-point rule_rec-sum)
      #;(list rule_ands-empty rule_ands-empty-fixed rule_ands-cons)
      #;(list rule_hlc-bind rule_hlc-guard rule_hlc-let)
      #;(list
       rule_method
       rule_hlc-bind rule_hlc-guard rule_hlc-let
       rule_for-map rule_sum-map rule_sum-or
       rule_letrec rule_sametype rule_seq rule_or rule_let
       rule_not rule_unless
       rule_ifzero rule_thunk rule_let-pair)))

(define-syntax-rule (test-match e x)
  (redex-match stlc-syntax e (term x)))