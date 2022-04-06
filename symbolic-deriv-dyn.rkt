#lang sicp

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

(define table '())

(define (put op type item)
  (set! table (cons (list op type item) table)))

(define (get op type)
  (define (inner table-prime)
    (cond ((null? table) (error "lookup failed"))
          ((and (equal? op (caar table-prime))
                (equal? type (cadar table-prime)))
           (caddar table-prime))
          (else (inner (cdr table-prime)))))
  (inner table))

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
