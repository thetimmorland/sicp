#lang sicp

(#%require "util.rkt")

(#%require (only racket/base
                 print-as-expression
                 print-pair-curly-braces
                 print-mpair-curly-braces))
(print-as-expression      #f)
(print-pair-curly-braces  #t)
(print-mpair-curly-braces #f)

(define (queens board-size)
  (define (queen-cols k)
    (if (= k 0)
      (list empty-board)
      (filter
        (lambda (positions)
          (safe? k positions))
        (flatmap
          (lambda (rest-of-queens)
            (map (lambda (new-row)
                   (adjoin-position
                     new-row
                     k
                     rest-of-queens))
                 (enumerate-interval
                   1
                   board-size)))
          (queen-cols (- k 1))))))
  (queen-cols board-size))

(define (make-pos row col) (cons row col))
(define (pos-row pos) (car pos))
(define (pos-col pos) (cdr pos))

(define empty-board nil)

(define (adjoin-position new-row k rest-of-queens)
  (cons (make-pos new-row k) rest-of-queens))

(define (safe? k positions)
  (accumulate
    (lambda (a b) (and a b))
    true
    (map (lambda (queen) (not (sees? queen
                                     (car positions))))
         (cdr positions))))

(define (sees? pos-a pos-b)
  (or
    (= (pos-row pos-a) (pos-row pos-b))
    (= (pos-col pos-a) (pos-col pos-b))
    (and (= (horiz-dist pos-a pos-b)
            (vert-dist pos-a pos-b)))))

(define (horiz-dist pos-a pos-b)
  (abs (- (pos-col pos-a) (pos-col pos-b))))

(define (vert-dist pos-a pos-b)
  (abs (- (pos-row pos-a) (pos-row pos-b))))
