#lang racket

; Some sanity tests for the 'foreach' desugaring

(define-syntax-rule (break) (raise "")) ; it's hard to capture a var in Racket
(define-syntax-rule (try body handler)
  (with-handlers
      [[(λ (exn) true) handler]]
    body))

(define-syntax foreach
  (syntax-rules (break)
    [(foreach x ~list ~body)
     (letrec [[loop
       (λ (lst)
         (λ (ans)
           (if (empty? lst)
               ans
               (try
                (let [[x (first lst)]]
                  ((loop (rest lst)) (cons ~body ans)))
                (λ (_) ans)))))]]
       (reverse ((loop ~list) empty)))]))

(display (foreach x (list 1 2 3 4)
                  (if (equal? x 3)
                      (break)
                      (* x x))))