#lang racket

(require redex)
(require "../resugar.rkt")

;;   booleans   (TAPL pg.93)
;;   nats       (TAPL pg.93)

(define-resugarable-language arith
  #:keywords(if true false succ pred iszero zero
                Bool Nat)
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
     zero)
  (t ::= ....
     Bool
     Nat)
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
   (⊢ Γ (iszero e) Bool)])






(define (do-resugar rule)
  (Resugared-rule (resugar arith rule ⊢)))


(module+ test
  (require test-engine/racket-tests)

  (check-expect (do-resugar rule_not)
                (derivation '(Γ ⊢ (not ~a) : Bool) "not"
                            (list (derivation '(Γ ⊢ ~a : Bool) "assume" '()))))
  
  (test))


(show-derivations
 (map do-resugar
      (list rule_not rule_unless rule_ifzero)))
