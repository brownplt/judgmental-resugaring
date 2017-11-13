#lang racket

(require redex)
(require "unify.rkt")
(require "types.rkt")

;; ---------------------------------------------------------------------------------------------------
;; Desugaring Rules

(define rule_not
  (rule "not" #:capture()
        (not ~a)
        (if ~a false true)))

(define rule_unless
  (rule "unless" #:capture()
        (unless ~a ~b ~c)
        (if ~a ~c ~b)))

(define rule_ifzero
  (rule "ifzero" #:capture()
        (ifzero ~a ~b ~c)
        (if (iszero ~a) ~b ~c)))

(define rule_thunk
  (rule "thunk" #:capture()
        (thunk ~a)
        (λ ((x : Nat)) ~a)))

(define rule_let
  (rule "let" #:capture()
        (let x = ~a in ~b)
        (calctype ~a as t in ((λ ((x : t)) ~b) ~a))))

(define rule_or
  (rule "or" #:capture()
        (or ~a ~b)
        ((λ ((x : Bool)) (if x x ~b)) ~a)))

(define rule_seq
  (rule "seq" #:capture()
        (seq ~a ~b)
        ((λ ((x : Unit)) ~b) ~a)))

(define rule_sametype
  (rule "sametype" #:capture()
        (sametype ~a ~b)
        (calctype ~b as x_t in (~a as x_t))))

(define rule_let-pair
  (rule "let-pair" #:capture()
        (let-pair x y = ~a in ~b)
        (calctype ~a as (Pair t_1 t_2) in
                  (let! p = ~a in
                        (let! x = (fst p) in
                              (let! y = (snd p) in
                                    ~b))))))

; contrived
(define rule_sum-or
  (rule "sum-or" #:capture()
        (sum-or ~a ~b)
        (case ~a of
          (inl x => ~b)
          (inr x => (inr x)))))

; contrived
(define rule_sum-map
  (rule "sum-map" #:capture()
        (sum-or-else ~a ok ~b)
        (case ~a of
          (inl err => (inl err))
          (inr ok => (inr ~b)))))

(define rule_letrec
  (rule "letrec" #:capture()
        (letrec x : ~t = ~a in ~b)
        (let! x = (fix (λ ((x : ~t)) ~a)) in ~b)))

(define rule_for-map
  (rule "for-map" #:capture()
        (for-map x ~list ~body)
        (calctype ~list as (List elem) in
         (calctype (λ ((x : elem)) ~body) as (elem -> out) in
                   (letrec! f : ((List elem) -> (List out))
                            = (λ ((l : (List elem)))
                                (if (isnil l)
                                    nil
                                    (let! x = (head l) in
                                          (cons ~body (f (tail l))))))
                            in (f ~list))))))

(define rule_tuple2
  (rule "tuple2" #:capture()
        (tuple2 ~a ~b)
        (tuple (cons ~a (cons ~b ϵ)))))

(define rule_my-tuple
  (rule "my-tuple" #:capture()
        (my-tuple ~a)
        (tuple ~a)))

(define rule_my-proj
  (rule "my-proj" #:capture()
        (my-proj ~a)
        (project (tuple ~a) 2)))

;; Haskell List Comprehensions ;;

(define-global concatMap
  ((i -> (List o)) (List i) -> (List o)))

; [e | b, Q] = if b then [e | Q] else []
(define rule_hlc-guard
  (rule "hlc-guard" #:capture()
        (hlc ~e (hlc/guard ~b ~Q))
        (if ~b (hlc ~e ~Q) nil)))

; [e | p <- l, Q] = let ok p = [e | Q]
;                       ok _ = []
;                    in concatMap ok l
; TODO: handle the underscore stuff
(define rule_hlc-bind
  (rule "hlc-bind" #:capture()
        (hlc ~e (hlc/bind x ~l ~Q)) ; [e | x <- l, Q]
        (calctype ~l as (List t) in ; concatMap (\x. [e | Q]) l
                  (concatMap (λ ((x : t)) (hlc ~e ~Q)) ~l))))
 
; [e | let decls, Q] = let decls in [e | Q]
; TODO: this is singleton let
(define rule_hlc-let
  (rule "hlc-let" #:capture()
        (hlc ~e (hlc/let x = ~a in ~Q))
        (let! x = ~a in (hlc ~e ~Q))))

; ellipses example
(define rule_ands-empty
  (rule "ands-empty" #:capture()
        (ands (cons ~a ϵ))
        ~a))

(define rule_ands-empty-fixed
  (rule "ands-empty-fixed" #:capture()
        (ands (cons ~a ϵ))
        (calctype ~a as Bool in ~a)))

(define rule_ands-cons
  (rule "ands-cons" #:capture()
        (ands (cons ~a (cons ~b ~cs)))
        (if ~a true (ands (cons ~b ~cs)))))

; capturing example
(define rule_method
  (rule "method" #:capture(this)
        (method (arg : t) ~body)
        (λ ((obj : o)) (λ ((arg : t)) (let! this = obj in ~body)))))

; records
(define rule_rec-point
  (rule "rec-point" #:capture()
        (rec-point ~a ~b)
        (record (field x ~a (field y ~b ϵ)))))

(define rule_rec-sum
  (rule "rec-sum" #:capture()
        (rec-sum ~rec x y)
        (let! r = ~rec in
              (+ (dot r x)
                 (dot r y)))))

; exceptions
(define rule_while
  (rule "while" #:capture(break)
        (while ~cond ~body)
        ((fix (λ [(loop : (Unit -> Unit))]
                (λ [(_ : Unit)]
                  (try (if ~cond
                           (loop (let! break = (λ [(_ : Unit)] (raise "")) in ~body))
                           unit)
                       with (λ [(err : String)] unit)))))
         unit)))

; exists
(define-global id (a -> a))

#;(define rule_newtype ; newtype as a pair
  (rule "newtype" #:capture()
        (let-new-type w of T as X in ~body)
        (let (∃ X w) = (∃ T (pair id id) as
          (∃ X (Pair (T -> X) (X -> T)))) in
          ~body)))

(define rule_newtype ; newtype as a record
  (rule "newtype" #:capture()
        (let-new-type w of T as X in ~body)
        (let (∃ X w) = (∃ T (record (field wrap id (field unwrap id ϵ))) as
          (∃ X (Record (field wrap (T -> X) (field unwrap (X -> T) ϵ))))) in
          ~body)))

; classes
(define rule_c-new
  (rule "new" #:capture()
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
(define the-literals (set 'λ ': '+ 'pair '-> 'Pair '= 'in 'Nat 'Bool
                          'try 'with 'unit 'fix 'if
                          'true 'false 'Unit 'as 'case 'of 'inl 'inr '=>))

(define (simply-resugar r)
  (let ([resugared (resugar r ⊢ the-literals the-globals)])
    (Resugared-derivation resugared)))

(show-derivations
 (map simply-resugar
      #;(list rule_while)
      #;(list rule_c-new)
      #;(list rule_newtype)
      #;(list rule_myapp)
      #;(list rule_rec-point rule_rec-sum)
      #;(list rule_ands-empty rule_ands-empty-fixed rule_ands-cons)
      (list rule_hlc-bind rule_hlc-guard rule_hlc-let)
      #;(list
       rule_method
       rule_hlc-bind rule_hlc-guard rule_hlc-let
       rule_for-map rule_sum-map rule_sum-or
       rule_letrec rule_sametype rule_seq rule_or rule_let
       rule_not rule_unless
       rule_ifzero rule_thunk rule_let-pair)))

(define-syntax-rule (test-match e x)
  (redex-match stlc-syntax e (term x)))