#lang sicp

(#%require "util.rkt")
(#%require "symbolic-deriv.rkt")

(define (deriv exp var)
  (cond ((number? exp) 0)
        ((variable? exp)
         (if (same-variable? exp var)
           1
           0))
        (else ((get 'deriv (operator exp))
               (operands exp)
               var))))

(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(put 'deriv '+
     (lambda (operands var)
       (make-sum (deriv (car operands) var)
                 (deriv (cadr operands) var))))

(put 'deriv '*
     (lambda (operands var)
       (make-sum
         (make-product
           (car operands)
           (deriv (cadr operands) var))
         (make-product
           (deriv (car operands) var)
           (cadr operands)))))

(put 'deriv '**
     (lambda (operands var)
      (make-product
       (cadr operands)
       (make-exponentiation (car operands)
        (dec (cadr operands))))))
