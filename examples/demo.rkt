#lang racket

(require redex)
(require "../sweet-t.rkt")

;; This is a super-simple resugaring demo to demonstrate the API.

(define-resugarable-language demo
  #:keywords(if true false Bool)
  (e ::= ....
     (if e e e))
  (v ::= ....
     true
     false)
  (t ::= ....
     Bool)
  (s ::= ....
     (not s)))

(define-core-type-system demo
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
   (⊢ Γ false Bool)])

(define rule_not
  (ds-rule "not" #:capture()
           (not ~a)
           (if ~a false true)))

(view-sugar-type-rules demo ⊢ (list rule_not))
