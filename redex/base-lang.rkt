#lang racket

(require redex)

(provide base-syntax ellipsis-var?)

; NOTE:
; type inference is necessary because:
;   (Γ ⊢ (atom a) : A
;   (Γ ⊢ 0 : Nat
;   [A = Nat -> ??]
;   ----------------------
;   (Γ ⊢ ((atom a) 0) : ??)


;; ---------------------------------------------------------------------------------------------------
;; base language

(define-language base-syntax
  (e ::=
     s
     x)
  (s ::= ; surface lang
     a)
  (e★ ::=
      a★
      (★ e ...)
      (★ e ... a★))
  (s★ ::=
      a★
      (★ s ...)
      (★ e ... a★))
  (t ::= x)
  (t★ ::=
      x★
      (★ t ...)
      (★ t ... x★))
  (Γ ::= [(x : t) ...])
  (a ::= (variable-prefix ~))
  (a★ ::= (variable-prefix ~★))
  (x★ ::= (variable-prefix ★))
  (x ::= variable-not-otherwise-mentioned)
  (c ::=
     j
     q
     (assumption any))
  (j ::=  (Γ ⊢ s : t))
  (q ::= (t = t)))

(caching-enabled? #f)


;; for handling 'ellipses' ;;

(define (ellipsis-var? x)
  (or (redex-match base-syntax x★ x)
      (redex-match base-syntax a★ x)))

(define (elliptic? l)
  (and (list? l)
       (not (empty? l))
       (equal? '★ (car l))))

(define (split-ellipsis l)
  (let ([l (cdr l)])
    (if (empty? l)
        empty
        (let ([head (take l (- (length l) 1))]
              [tail (last l)])
          (if (ellipsis-var? tail)
              (values head tail)
              (values l #f))))))

(module+ test
  (require rackunit)

  (define a (term (★ x y z)))
  (define b (term (★ (+ 1 2) ★x)))
  (define c (term (★ ~★x)))

  (check-equal? (elliptic? (term (x ★ y))) #f)
  (check-equal? (elliptic? (term (+ 1 2))) #f)
  (check-equal? (elliptic? (term z)) #f)
  (check-equal? (elliptic? (term x★)) #f)
  (check-equal? (elliptic? a) #t)
  (check-equal? (elliptic? b) #t)
  (check-equal? (elliptic? c) #t)
  (let-values [[[p1 q1] (split-ellipsis a)]
               [[p2 q2] (split-ellipsis b)]
               [[p3 q3] (split-ellipsis c)]]
    (check-equal? (list p1 q1) (list (term (x y z)) #f))
    (check-equal? (list p2 q2) (list (term ((+ 1 2))) (term ★x)))
    (check-equal? (list p3 q3) (list (term ()) (term ~★x))))
  )

