#lang racket

(require redex)
(require "resugar.rkt")

(define-resugarable-language
  (v ::= ....
     string))