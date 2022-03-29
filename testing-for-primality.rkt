#lang sicp

(define (square x) (* x x))

(define (smallest-divisor n)
  (find-divisor n 2))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) 
         n)
        ((divides? test-divisor n) 
         test-divisor)
        (else (find-divisor 
               n 
               (next-divisor test-divisor)))))

(define (next-divisor n)
  ; (+ n 1)
  (if (= n 2)
   (+ n 1)
   (+ n 2))) 

(define (divides? a b)
  (= (remainder b a) 0))

(define (prime? n)
  (= n (smallest-divisor n)))

(define (expmod base exp m)
  (cond ((= exp 0) 1)
        ((even? exp)
         (remainder 
          (square (expmod base (/ exp 2) m))
          m))
        (else
         (remainder 
          (* base (expmod base (- exp 1) m))
          m))))

(define (fermat-test n)
  (define (try-it a)
    (= (expmod a n n) a))
  (try-it (+ 1 (random (- n 1)))))

(define (fast-prime? n times)
  (cond ((= times 0) true)
        ((fermat-test n) 
         (fast-prime? n (- times 1)))
        (else false)))

(define (timed-prime-test n)
  (start-prime-test n (runtime)))

(define (start-prime-test n start-time)
  ; (let ((is-prime (prime? n))))
  (let ((is-prime (fast-prime? n 4)))
      (if is-prime (report-prime n (- (runtime) start-time)))
      is-prime))

(define (report-prime n elapsed-time)
  (display "Found Prime: ")
  (display n)
  (display " in ") 
  (display elapsed-time)
  (display " us.\n"))

(define (search-for-primes n num)
  (if (> num 0)
    (search-for-primes
      (+ n 2)
      (if (timed-prime-test n)
        (dec num)
        num))))

(define (report-search-for-primes n num)
  (display "Finding first ")
  (display num)
  (display " primes >= ")
  (display n)
  (display ".\n")
  (search-for-primes n num))

(define (main)
  (report-search-for-primes 199 3)
  (report-search-for-primes 1999 3)
  (report-search-for-primes 19999 3))
