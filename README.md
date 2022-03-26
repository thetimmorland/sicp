# Structure and Interpretation of Computer Programs

https://sarabander.github.io/sicp

## Exercise 1.1

```
> 10
10
> (+ 5 3 4)
12
> (- 9 1)
8
> (/ 6 2)
3
> (+ (* 2 4) (- 4 6))
6
> (define a 3)
> (define b (+ a 1))
> (+ a b (* a b))
19
> (= a b)
#f
> (if (and (> b a) (< b (* a b)))
      b
      a)
4
> (cond ((= a 4) 6)
        ((= b 4) (+ 6 7 a))
        (else 25))
16
> (+ 2 (if (> b a) b a))
6
> (* (cond ((> a b) a)
           ((< a b) b)
           (else -1))
     (+ a 1))
16
```

## Exercise 1.2

```
(/ (+ 4
      (- 2
         3
         (+ 6
            (/ 4 5))))
   (* 3
      (- 6 2)
      (- 2 7)))
```

## Exercise 1.3

```
(define (sum-of-squares a b)
  (+ (* a a) (* b b)))

(define (f a b c)
  (cond ((and (< a b) (< a c)) (sum-of-squares b c)) ; a is smallest
        ((and (< b a) (< b c)) (sum-of-squares a c)) ; b is smallest
        (else (sum-of-squares a b))))                ; c is smallest
```

## Exercise 1.4

The procedure can be described as: Add b to a if b is greater than zero, otherwise subtract b from a.

## Exercise 1.5

An interpreter which uses applicative-order evaluation will run out of memory trying to expand `(p)`, while an interpreter which uses normal-order evaluation will never evaluate `(p)` since `(= x 0)` is `#t`.

## Exercise 1.6

When calling `new-if` the then-clause and else-clause are both evaluated regardless of the predicate resulting in infinite recursion. The regular `if` expression does not have this problem because it only evaluates one of the clauses, depending on the predicate. 

## Exercise 1.7

For very small numbers `good-enough?` will return `#t` even if the error is very large proportionally to the actual answer.

For very large numbers the act of squaring `x` will result in a very low precision number which will not satisfy `(< (abs (- (square guess) x)) 0.001))`.

```
(define (good-enough guess last-guess x)
  (< (abs (- guess last-guess)) (/ x 1000))
```

## Exercise 1.8

```
(define (square x) (* x x))
(define (abs x) (if (> x 0) x (- x)))

(define (cube-root x)
  (cube-root-iter 0 1.0 x))

(define (cube-root-iter last-guess guess x)
  (cond ((good-enough? last-guess guess) guess)
        (else (cube-root-iter guess (improve-guess guess x) x))))

(define (improve-guess guess x)
  (/ (+ (/ x (square guess))
        (* 2 guess))
     3))

(define (good-enough? guess last-guess)
  (< (abs (- guess last-guess)) 0.001))
```

## Exercise 1.9

### Procedure A

```
(+ 4 5)
(inc (+ 3 5))
(inc (inc (+ 2 5)))
(inc (inc (inc (+ 1 5))))
(inc (inc (inc (inc (+ 0 5)))))
(inc (inc (inc (inc 5))))
9
```

This process is recursive.

### Procedure B

```
(+ 4 5)
(+ 3 6)
(+ 2 7)
(+ 1 8)
(+ 0 9)
9
```

This process is iterative.

## Exercise 1.10

```
> (define (A x y)
    (cond ((= y 0) 0)
          ((= x 0) (* 2 y))
          ((= y 1) 2)
          (else (A (- x 1)
                   (A x (- y 1))))))
> (A 1 10)
(A 0 (A 1 9))
(A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 1))))))))))
(* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 2)))))))))
(expt 2 10)
1024
> (A 2 4)
(A 1 (A 2 3))
(A 1 (A 1 (A 1 (A 1 1))))
(expt 2 (expt 2 (expt 2 2))))
65536
> (A 3 3)
(A 2 (A 3 2))
(A 2 (A 2 (A 2 1)))
(A 2 (A 2 2))
(A 2 4)
(expt 2 (expt 2 (expt 2 2)))
65536
```

```
(define (f n) (A 0 n)) ; 2n
(define (g n) (A 1 n)) ; 2^n
(define (h n) (A 2 n)) ; 2^2^2... n times
```

## Exercise 1.11

```
(define (f n)
  (if (< n 3)
      n
      (+ (f (- n 1))
         (* 2 (f (- n 2)))
         (* 3 (f (- n 3))))))
```

```
(define (f n)
  (define (f-i a b c count)
    (cond ((< n 3) n)
          ((<= count 0) a)
          (else (f-i (+ a (* 2 b) (* 3 c)) a b (- count 1)))))
  (f-i 2 1 0 (- n 2)))
```

## Exercise 1.12

```
(define (pascal x y)
  (if (or (= x 0) (= x y))
      1
      (+ (pascal (dec x) (dec y))
         (pascal x (dec y)))))
```

## Exercise 1.13

Proof: Fib(n) is the closest integer to phi^n/sqrt(5).

```
Show Fib(n) = (phi^n - psi^n) / sqrt(5) where
  phi = (1 + sqrt(5)) / 2
  psi = (1 - sqrt(5)) / 2

Base Cases
  Fib(0) = 0
  (phi^0 - psi^0) / sqrt(5) = 0 / sqrt(5) = 0

  Fib(1) = 1
  (phi^1 - psi^1) / sqrt(5) = sqrt(5) / sqrt(5) = 1

Inductive Case
  Fib(n + 2) = Fib(n + 1) + Fib(n)

  (phi^n+2 - psi^n+2) / sqrt(5)
    = ((phi^n-1 - psi^n-1) / sqrt(5)) + ((phi^n - psi^n) / sqrt(5)) = 

  phi^n+2 - psi^n+2
    = phi^n+1 + phi^n - psi^n+1 + phi^n
    = phi^n(phi + 1) - psi^n(psi + 1)
    = phi^n(phi^2) - psi^n(phi^2) // because of definition of golden ratio x^2=x+1
    = phi^n+2 - psi^n+2
```

## Exercise 1.14

```
(define (cc amount kinds-of-coins)
  (cond ((= amount 0) 1)
        ((or (< amount 0) 
             (= kinds-of-coins 0)) 
         0)
        (else 
         (+ (cc amount (- kinds-of-coins 1))
            (cc (- amount (first-denomination 
                           kinds-of-coins))
                kinds-of-coins)))))

(define (first-denomination kinds-of-coins)
  (cond ((= kinds-of-coins 1) 1)
        ((= kinds-of-coins 2) 5)
        ((= kinds-of-coins 3) 10)
        ((= kinds-of-coins 4) 25)
        ((= kinds-of-coins 5) 50)))

(+
  (+
    (+
      (+
        (cc 11 1)         ; 1
        (+
          (cc 6 1)        ; 1
          (+
            (cc 1 1)      ; 1
            (cc -4 2))))  ; 0
      (cc 1 3))           ; 1
    (cc -14 4))           ; 0
  (cc -39 5))             ; 0
```

Space complexity: O(n) because average height of call tree is dominated by the expansion of `(cc n 1)`.

Time complexity: O(n^kinds-of-coins) because `(cc n 1)` is O(n) and `(cc n 2)` is O(n^2) etc...

## Exercise 1.15

```
(define (cube x) (* x x x))
(define (p x) (- (* 3 x) (* 4 (cube x))))
(define (sine angle)
   (if (not (> (abs angle) 0.1))
       angle
       (p (sine (/ angle 3.0)))))
```

`(sine a)` repeatedly divides it's argument by three until it is less than 0.1, so the following can be used to caluculate how many times `p` is evaluated:

```
> (ceiling (log (/ 12.5 0.01) 3))
7.0
```

The order of growth for `(sine a)` in both time and space is O(log a).

## Exercise 1.6

```
(define (fast-expt b n)
  ;; invariant: ab^n is constant
  (define (fast-expt-i a b n)
    (cond ((= n 0)
           a)
          ((even? n)
           (fast-expt-i a (square b) (/ n 2)))
          (else
           (fast-expt-i (* a b) b (dec n)))))
  (fast-expt-i 1 b n))
```

## Exercise 1.17

```
(define (double x) (* x 2))
(define (half x) (/ x 2))
(define (* a b)
  (cond ((= b 0)
         0)
        ((even? b)
         (* (double a) (half b)))
        (else
         (+ a (* a (dec b))))))
```

## Exercise 1.18

```
(define (double x) (* x 2))
(define (half x) (/ x 2))
(define (* a b)
  ;; invariant: a * b is constant
  (cond ((= b 0)
         0)
        ((even? b)
         (* (double a) (half b)))
        (else
         (* (+ a b) (dec b)))))
```

## Exercise 1.19

```
Tpq = a <- bq + aq + ap
      b <- bp + aq

Tpq^2 = a <- (bp + aq)q + (bq + aq + ap)q + (bq + aq + ap)p
        b <- (bp + aq)p + (bq + aq + ap)q

Using transform for b:

(bp + aq)p + (bq + aq + ap)q = bp^2 + bq^2 + aq^2 + 2paq
                             = b(p^2 + q^2) + a(q^2 + 2pq)

Therefore p' = p^2 + q^2
      and q' = q^2 + 2pq
```

```
(define (fib n)
  (fib-iter 1 0 0 1 n))

(define (fib-iter a b p q count)
  (cond ((= count 0) 
         b)
        ((even? count)
         (fib-iter a
                   b
                   (+ (* p p) (* q q))
                   (+ (* q q) (* 2 p q))
                   (/ count 2)))
        (else 
         (fib-iter (+ (* b q) 
                      (* a q) 
                      (* a p))
                   (+ (* b p) 
                      (* a q))
                   p
                   q
                   (- count 1)))))
```

## Exercise 1.20

```
(define (gcd a b)
  (if (= b 0)
      a
      (gcd b (remainder a b))))

;; normal-order, ??? remainder ops
;; note that remainder ops will be evaluated to check if-condition
(gcd 206 40)
(gcd 40 (remainder 206 40))                                
(gcd (remainder 206 40) (remainder 40 (remainder 206 40)))
(gcd (remainder 40 (remainder 206 40))
     (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))
;; etc...

;; applicative-order, four remainder ops
(gcd 206 40)
(gcd 40 (remainder 206 40))
(gcd 40 6)
(gcd 6 (remainder 40 6))
(gcd 6 4)
(gcd 4 (remainder 6 4))
(gcd 4 2)
(gcd 2 (remainder 4 2))
(gcd 2 0)
2
```

## Exercises 1.21 and 1.22

```
Finding first 3 primes >= 199.
Found Prime: 199 in 7 us.
Found Prime: 211 in 0 us.
Found Prime: 223 in 1 us.
Finding first 3 primes >= 1999.
Found Prime: 1999 in 4 us.
Found Prime: 2003 in 3 us.
Found Prime: 2011 in 2 us.
Finding first 3 primes >= 19999.
Found Prime: 20011 in 6 us.
Found Prime: 20021 in 7 us.
Found Prime: 20023 in 10 us.

199:   avg 1 ~= sqrt(1)
1999:  avg 3 ~= sqrt(10)
19999: avg 8 ~= sqrt(100)
```

As shown in the averages above the observed runtimes are roughly `O(sqrt(n))`


## Exercise 1.23

```
Finding first 3 primes >= 199.
Found Prime: 199 in 7 us.
Found Prime: 211 in 0 us.
Found Prime: 223 in 0 us.
Finding first 3 primes >= 1999.
Found Prime: 1999 in 1 us.
Found Prime: 2003 in 1 us.
Found Prime: 2011 in 3 us.
Finding first 3 primes >= 19999.
Found Prime: 20011 in 3 us.
Found Prime: 20021 in 3 us.
Found Prime: 20023 in 4 us.

199:   avg 0 ~= sqrt(0)
1999:  avg 1 ~= sqrt(1)
19999: avg 3 ~= sqrt(10)
```

This change roughly halved the runtime of the algorithm and the averages are still roughly `O(sqrt(n))`.

## Exercise 1.24

```
Found Prime: 199 in 15 us.
Found Prime: 211 in 3 us.
Found Prime: 223 in 3 us.
Finding first 3 primes >= 1999.
Found Prime: 1999 in 10 us.
Found Prime: 2003 in 6 us.
Found Prime: 2011 in 5 us.
Finding first 3 primes >= 19999.
Found Prime: 20011 in 6 us.
Found Prime: 20021 in 4 us.
Found Prime: 20023 in 12 us.
```

The time to test primes near 1000000 should be 6/3 = 2 times the time to test primes near 1000. My data roughly aligns with this.

## Exercise 1.25

This implementation of `expmod` would involve computing very large exponents which would take conciderably longer.

## Exercise 1.26

With this change, `expmod` becomes `O(n^2)`. When used within the once `O(log n)` `fast-prime?` the result is `fast-prime` becomes `O(n)`.

## Exercise 1.27

```
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

(define (carmichael-i? n a)
  (cond
    ((= a 0)
     true)
    ((= (expmod a n n) a)
     (carmichael-i? n (dec a)))
    (else
     false)))

(define (carmichael? n)
  (carmichael-i? n (dec n)))

(carmichael? 561)  ; #t
(carmichael? 1105) ; #t
(carmichael? 1729) ; #t
(carmichael? 2465) ; #t
```

## Exercise 1.28

```
 (define (miller-rabin n) 
   (miller-rabin-test (- n 1) n)) 

(define (miller-rabin-test a n) 
  (cond ((= a 0)
         true) 
        ((= (expmod a (- n 1) n) 1)
         (miller-rabin-test (- a 1) n)) 
        (else
          false))) 

(define (expmod base exp m) 
  (cond ((= exp 0) 1) 
        ((even? exp) 
         (let ((x (expmod base (/ exp 2) m))) 
           (if (non-trivial-sqrt? x m)
             0
             (remainder (square x) m)))) 
        (else 
          (remainder
            (* base (expmod base (- exp 1) m)) m)))) 

(define (non-trivial-sqrt? n m) 
  (cond ((= n 1)
         false) 
        ((= n (- m 1))
         false) 
        (else
          (= (remainder (square n) m) 1)))) 
```

## Exercise 1.29

```
(define (cube x) (* x x x))

(define (sum term a next b)
  (if (> a b)
      0
      (+ (term a)
         (sum term (next a) next b))))

(define (integral f a b dx)
  (define (add-dx x) (+ x dx))
  (* (sum f (+ a (/ dx 2.0)) add-dx b) 
     dx))

(define (simp f a b n)
  (define h (/ (- b a) n))
  (define (scalar k)
    (cond ((or (= k 0) (= k n)) 1)
          ((even? k) 4)
          (else 2)))
  (define (y k)
    (f (+ a (* k h))))
  (define (simp-term k)
    (* (scalar k) (y k)))
  (* (/ h 3)
     (sum simp-term 0 inc n)))

(integral cube 0 1 0.001)
(simp cube 0 1 100)
```

## Exercise 1.30

```
(define (sum term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (+ (term a) result))))
  (iter a 0))
```

## Exercise 1.31

```
(define (product term a next b)
  (if (> a b)
    1
    (* (term a)
       (product term (next a) next b))))

(define (product-iter term a next b)
  (define (iter a result)
    (if (> a b)
      result
      (iter (inc a)
            (* result (term a)))))
  (iter a 1))

(define (factorial n)
  (product identity 1 inc n))

(define (aprox-pi n)
  (* 4
     (/ (product upper-term 0 inc n)
        (product lower-term 0 inc n))))

(define (upper-term n)
  ;; 2, 4, 4, 6, 6, 8...
  (if (= n 0)
    2
    (+ 4
       (* 2
          (floor (/ (- n 1)
                    2))))))

(define (lower-term n)
  ;; 3, 3, 5, 5, 7, 7...
  (+ 3
     (* 2
        (floor (/ n 2)))))
```

## Exercise 1.32

```
(define (accumulate combiner null-value term a next b)
  (if (> a b)
    null-value
    (combiner (term a)
              (accumulate combiner null-value term (next a) next b))))

(define (accumulate-iter combiner null-value term a next b)
  (define (iter a result)
    (if (> a b)
      result
      (iter (next a)
            (combiner (term a) result))))
  (iter a null-value))
      
(define (sum term a next b)
  (accumulate + 0 term a next b))

(define (product term a next b)
  (accumulate * 1 term a next b))
```

## Exercise 1.33

```
(define (filter-accumulate filter combiner null-value term a next b)
  (if (> a b)
    null-value
    (combiner (if (filter a)
                (term a)
                null-value)
              (filter-accumulate
                filter
                combiner
                null-value
                term
                (next a)
                next
                b))))

(define (sum-of-prime-squares a b)
  (filter-accumulate prime? + 0 square a inc b))

(define (sum-of-relative-primes n)
  (define (filter x)
    (= (gcd x n) 1))
  (filter-accumulate prime? + 0 square 1 inc (dec n)))
```

## Exercise 1.34

```
(f f) ;; reduces to
(f 2) ;; reduces to
(2 2) ;; error
```

## Exercise 1.35

```
a and b are the golden ratio iff (a + b) / a = a / b
phi = a + b / a
    = a / a + b / a
    = 1 + b / a
    = 1 + 1 / phi
```

```
(fixed-point (lambda (x) (+ 1 (/ 1 x))) 1.0) ;; 1.6180327868852458
```

## Exercise 1.36

```
(fixed-point (lambda (x) (/ (log 1000) (log x))) 2) ;; 35 steps
(fixed-point (lambda (x) (/ (+ x (/ (log 1000) (log x))) 2)) 2) ;; 10 steps
```
