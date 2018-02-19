#lang racket

(require redex)
(require "../sweet-t.rkt")

;;   booleans   (TAPL pg.93)
;;   nats       (TAPL pg.93)
;;   unit       (TAPL pg.119)

(define-resugarable-language arith
  #:keywords(if true false succ pred iszero zero unit
                Bool Nat Unit)
  (e ::= ....
     ; booleans
     (if e e e)
     ; nats
     (succ e)
     (pred e)
     (iszero e))
  (v ::= ....
     ; booleans
     true
     false
     ; nats
     zero
     ; unit
     unit)
  (t ::= ....
     Bool
     Nat
     Unit)
  (s ::= ....
     (not s)
     (unless s s s)
     (ifzero s s s)))


(define-core-type-system arith

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

  ; unit
  [------ t-unit
   (⊢ Γ unit Unit)])


(define rule_and
  (ds-rule "and" #:capture()
           (and ~a ~b)
           (if ~a ~b false)))

(define rule_not
  (ds-rule "not" #:capture()
           (not ~a)
           (if ~a false true)))

(define rule_unless
  (ds-rule "unless" #:capture()
           (unless ~a ~b)
           (if ~a unit ~b)))

(define rule_ifzero
  (ds-rule "ifzero" #:capture()
           (ifzero ~a ~b ~c)
           (if (iszero ~a) ~b ~c)))




(module+ test
  (require test-engine/racket-tests)

  (check-expect (Resugared-rule (resugar arith rule_not ⊢))
                (derivation '(Γ ⊢ (not ~a) : Bool) "not"
                            (list (derivation '(Γ ⊢ ~a : Bool) "assume" '()))))
  
  (test))

(view-sugar-type-rules arith ⊢
  (list rule_not rule_and rule_unless rule_ifzero))
