#lang racket

(require redex)
(require "../resugar.rkt")

;;   booleans   (TAPL pg.93)
;;   nats       (TAPL pg.93)
;;   lambda     (TAPL pg.103)

;;   pairs      (TAPL pg.126)
;;   tuples     (TAPL pg.128)
;;   records    (TAPL pg.129)
;;   sums       (TAPL pg.132)
;;   lists      (TAPL pg.147)

(define-resugarable-language data-lang
  #:keywords(if true false succ pred iszero zero
                λ thunk let = : in
                pair fst snd tuple project record dot inl inr case of =>
                link isnil head tail
                calctype
                Bool Num Pair Tuple Sum Record List ->)
  (e ::= ....
     ; booleans
     (if e e e)
     ; numbers
     (+ e e)
     ; strings
     (string-eq e e)
     ; lambda
     (e e)
     ; let
     (let x = e in e)
     (letrec x : t = e in e)
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
     ; list
     (link e e) ; renamed to avoid name clash with builtin cons
     (isnil e)
     (head e)
     (tail e)
     ; exception
     (raise e)
     (try e with e))
  (v ::= ....
     ; booleans
     true
     false
     ; numbers
     number
     ; strings
     string
     ; lambda
     (λ (x : t) e)
     ; list
     nil
     (link v v))
  (t ::= ....
     Bool
     Num
     String
     (t -> t)
     ; pairs
     (Pair t t)
     ; tuples
     (Tuple t*)
     ; sum
     (Sum t t)
     ; record
     (Record tRec)
     ; list
     (List t))
  (s ::= ....
     (hlc s s)))


(define-core-type-system data-lang

  ; boolean
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

  ; number
  [------ t-num
   (⊢ Γ number Num)]

  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (con (t_1 = Num))
   (con (t_2 = Num))
   ------ t-plus
   (⊢ Γ (+ e_1 e_2) Nat)]

  ; string
  [------ t-str
   (⊢ Γ string String)]

  [(⊢ Γ e_1 t_1)
   (⊢ Γ e_2 t_2)
   (con (t_1 = String))
   (con (t_2 = String))
   ------ t-string-eq
   (⊢ Γ (string-eq e_1 e_2) Bool)]

  ; lambda
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

  [(⊢ (bind x t Γ) e t_ret)
   ------ t-lambda
   (⊢ Γ (λ (x : t) e) (t -> t_ret))]

  [(⊢ Γ e_fun t_fun)
   (⊢ Γ e_arg t_arg)
   (where x_ret (fresh-var))
   (con (t_fun = (t_arg -> x_ret)))
   ------ t-apply
   (⊢ Γ (e_fun e_arg) x_ret)]

  ; let
  [(⊢ Γ e_1 t_1)
   (⊢ (bind x t_1 Γ) e_2 t_2)
   ------ t-let
   (⊢ Γ (let x = e_1 in e_2) t_2)]

  ; letrec
  [(⊢ (bind x t Γ) e_1 t_1)
   (⊢ (bind x t Γ) e_2 t_2)
   (con (t_1 = t))
   ------ t-letrec
   (⊢ Γ (letrec x : t = e_1 in e_2) t_2)]

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
  [(⊢rec Γ eRec tRec)
   ------ t-rec
   (⊢ Γ (record eRec) (Record tRec))]

  [(⊢ Γ e t_e)
   (where x_rec (fresh-var))
   (con (t_e = (Record x_rec)))
   (@rec x_rec x t)
   ------ t-dot
   (⊢ Γ (dot e x) t)]

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
   (⊢ Γ (try e with e_catch) t)])



; pairs
(define rule_let-pair
  (ds-rule "let-pair" #:capture()
        (let-pair x y = ~a in ~b)
        (calctype ~a as (Pair t_1 t_2) in
                  (let p = ~a in
                        (let x = (fst p) in
                              (let y = (snd p) in
                                    ~b))))))
; tuple
(define rule_tuple2
  (ds-rule "tuple2" #:capture()
        (tuple2 ~a ~b)
        (tuple (cons ~a (cons ~b ϵ)))))

; records
(define rule_rec-point
  (ds-rule "rec-point" #:capture()
        (rec-point ~a ~b)
        (record (field x ~a (field y ~b ϵ)))))

(define rule_rec-sum
  (ds-rule "rec-sum" #:capture()
        (rec-sum ~rec x y)
        (let r = ~rec in
              (+ (dot r x)
                 (dot r y)))))

; sum
(define rule_and-then
  (ds-rule "and-then" #:capture()
        (and-then ~a ~b)
        (case ~a of
          (inl x => ~b)
          (inr x => (inr x)))))

(define rule_or-else
  (ds-rule "sum-map" #:capture()
        (or-else ~a ok ~b)
        (case ~a of
          (inl err => (inl err))
          (inr ok => (inr ~b)))))

(define rule_for-map
  (ds-rule "for-map" #:capture()
        (for-map x ~list ~body)
        (calctype ~list as (List elem) in
          (calctype (λ (x : elem) ~body) as (elem -> out) in
                    (letrec f : ((List elem) -> (List out))
                             = (λ (l : (List elem))
                                 (if (isnil l)
                                     nil
                                     (let x = (head l) in
                                           (link ~body (f (tail l))))))
                            in (f ~list))))))


;; Haskell List Comprehensions ;;

(define-global concatMap
  ((i -> (List o)) -> ((List i) -> (List o))))

; [e | b, Q] = if b then [e | Q] else []
(define rule_hlc-guard
  (ds-rule "hlc-guard" #:capture()
        (hlc ~e (hlc/guard ~b ~Q))
        (if ~b (hlc ~e ~Q) nil)))

; [e | p <- l, Q] = let ok p = [e | Q]
;                       ok _ = []
;                    in concatMap ok l
; (ignoring _ because the binding cannot fail in our core)
(define rule_hlc-gen
  (ds-rule "hlc-gen" #:capture()
        (hlc ~e (hlc/gen x ~l ~Q)) ; [e | x <- l, Q]
        (calctype ~l as (List t) in ; concatMap (\x. [e | Q]) l
                  ((concatMap (λ (x : t) (hlc ~e ~Q))) ~l))))
 
; [e | let decls, Q] = let decls in [e | Q]
(define rule_hlc-let
  (ds-rule "hlc-let" #:capture()
        (hlc ~e (hlc/let x = ~a in ~Q))
        (let x = ~a in (hlc ~e ~Q))))


; functional foreach loop
(define rule_foreach
  (ds-rule "while" #:capture(break)
     (foreach x ~list ~body)
     (letrec loop : ((List a) -> ((List b) -> (List b))) =
       (λ (lst : (List a))
         (λ (ans : (List b))
           (if (isnil lst)
               ans
               (try (let break = (λ (_ : Unit) (raise "")) in
                      (let x = (head lst) in
                      ((loop (tail lst)) (link ~body ans))))
                with (λ (_ : String) ans))))) in
       ((loop ~list) nil))))








(define (do-resugar rule)
  (Resugared-rule (resugar data-lang rule ⊢)))

(show-derivations
 (map do-resugar
      (list rule_foreach)
      #;(list rule_foreach rule_for-map rule_let-pair rule_tuple2 rule_rec-point rule_rec-sum
            rule_and-then rule_or-else
            rule_hlc-guard rule_hlc-gen rule_hlc-let)))

