# Structure and Interpretation of Computer Programs

https://sarabander.github.io/sicp

Note: the following snippet will make racket print lists and pairs more nicely.

```
(#%require (only racket/base
                 print-as-expression
                 print-pair-curly-braces
                 print-mpair-curly-braces))
(print-as-expression      #f)
(print-pair-curly-braces  #t)
(print-mpair-curly-braces #f)
```

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

`(sine a)` repeatedly divides it's argument by three until it is less than 0.1, so the following can be used to calculate how many times `p` is evaluated:

```
> (ceiling (log (/ 12.5 0.01) 3))
7.0
```

The order of growth for `(sine a)` in both time and space is O(log a).

## Exercise 1.16

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

This implementation of `expmod` would involve computing very large exponents which would take considerably longer.

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

## Exercise 1.37

```
(define (cont-frac n d k)
  (define (inner i)
    (if (> i k)
      0
      (/ (n i)
         (+ (d i)
            (inner (inc i))))))
  (inner 1))

(define (cont-frac n d k)
  (define (iter i result)
    (if (= i 0)
      result
      (iter (dec i)
            (/ (n i)
               (+ (d i)
                  result)))))
  (iter k 0))


(cont-frac (lambda (i) 1.0)
           (lambda (i) 1.0)
           11)
```

Using `cont-frac` with `k` = 11 produces 1/phi accurate to four decimal places.

## Exercise 1.38

```
(define (n i)
  (if (= (modulo (+ i 1) 3) 0)
    (* (/ (+ i 1) 3) 2)
    1))

(+ 2 (cont-frac (lambda (i) 1.0)
                n
                100))
```

## Exercise 1.39

```
(define (tan-cf x k)
   (cont-frac (lambda (i) (- (if (= x 1)
                               x
                               (* x x))))
              (lambda (i) (- 1 (* i 2)))
              k))
```

## Exercise 1.40

```
(define (cubic a b c)
  (lambda (x) (+ (cube x)
                 (* a (square x))
                 (* b x)
                 c)))
```

## Exercise 1.41

```
(define (double f)
  (lambda (x) (f (f x))))

(((double (double double)) inc) 5) ; 21
```

## Exercise 1.42

```
(define (compose f g)
  (lambda (x) (f (g x))))
```

## Exercise 1.43

```
(define (repeated f n)
  (if (= n 0)
    identity
    (compose f
             (repeated f (dec n)))))
```

## Exercise 1.44

```
(define (smooth f)
  (lambda (x) (/ (+ (f (- x dx))
                    (f x)
                    (f (+ x dx)))
                 3)))

(define (n-smooth f n)
  (repeated smooth n) f)
```

## Exercise 1.45

```
(define (nth-root n x)
  (fixed-point ((repeated average-damp
                          (ceiling (/ n 2.0)))
                (lambda (y) (/ x
                               (expt y (- n 1)))))
               1.0))
```

## Exercise 1.46

```
(define (iterative-improve good-enough? improve)
  (define (inner x)
    (if (good-enough? x)
      x
      (inner (improve x))))
  inner)
      

(define (sqrt x)
  ((iterative-improve
    (lambda (guess) (< (abs (- (square guess) x)) 0.001))
    (lambda (guess) (average guess (/ x guess))))
   x))
    
(define (fixed-point f x)
  (define tolerance 0.00001)
  (define (close-enough? v1 v2)
    (< (abs (- v1 v2)) 
       tolerance))
  ((iterative-improve
     (lambda (guess) (close-enough? guess (f guess)))
     f)
   x))
```

## Exercise 2.1

```
(define (make-rat n d)
  (if (negative? d)
      (make-rat (- n) (- d))
      (let ((g (gcd n d)))
        (cons (/ n g) 
              (/ d g)))))
```

## Exercise 2.2

```
(define make-segment cons)
(define start-segment car)
(define end-segment cdr)

(define make-point cons)
(define x-point car)
(define y-point cdr)

(define (midpoint-segment seg)
  (make-point
    (average (x-point (start-segment seg))
             (x-point (end-segment seg)))
    (average (y-point (start-segment seg))
             (y-point (end-segment seg)))))

(define (print-point p)
  (newline)
  (display "(")
  (display (x-point p))
  (display ",")
  (display (y-point p))
  (display ")"))

(print-point
  (midpoint-segment
    (make-segment (make-point 0 0)
                  (make-point 1 1))))
```

## Exercise 2.3

```
;; model rectangle in a plain as two points
;;   1. the position of the bottom-left corner
;;   2. the position of the top right corner relative to the bottom-left corner
(define make-rect cons)
(define origin-rect car)
(define dimensions-rect cdr)

(define (perimeter-rect rect)
  (let ((dimensions (dimensions-rect rect)))
    (* 2
       (+ (x-point dimensions)
          (y-point dimensions)))))

(define (area-rect rect)
  (let ((dimensions (dimensions-rect rect)))
    (* (x-point dimensions)
       (y-point dimensions))))
```

## Exercise 2.4

```
(cons (car 0 1))
((lambda (m) (m 0 1) (lambda (p q) p))
((lambda (p q) p) 0 1)
0)
```

## Exercise 2.5

```
(define (cons a b) (* (expt 2 a) (expt 3 b)))

(define (car p)
  (if (= (modulo p 2) 0)
    (inc (car (/ p 2)))
    0))

(define (cdr p)
  (if (= (modulo p 3) 0)
    (inc (cdr (/ p 3)))
    0))
```

## Exercise 2.6

```
;; applies f to x one time
(define one
  (lambda (f)
    (lambda (x)
      (f x))))

;; applies f to x two times
(define two
  (lambda (f)
    (lambda (x)
      (f (f x)))))

;; compose (a f) with (b f) 
(define (add a b)
  (lambda (f)
    (lambda (x)
      ((a f) ((b f) x)))))

(((add one two) inc) 0) ; 3
```

## Exercises 2.7 and 2.8

See `interval-arithmetic.scm`.

## Exercise 2.9

For addition, the width of the result will always be the sum of the widths of the two arguments. This can be seen from the definition for addition, which produces a new interval which is the sum of the lower bounds added to the sum of the upper bounds. Addition results in the same change regardless of what is being added to, so only the widths matter, not the position of the intervals. Since subtraction is defined in terms of addition this property holds for it as well.

For multiplication the resulting interval will be different depending on the positions of the intervals. This is due to the property of multiplication scaling larger numbers more. Since division is defined in terms of multiplication this property holds for it as well.

## Exercise 2.10

See `interval-arithmetic.scm`.

## Exercise 2.11

Skipped.

## Exercise 2.12

See `interval-arithmetic.scm`.

## Exercise 2.13

Experimentation below shows that for small percentage tolerances the resulting tolerance after multiplication is approximately equal to the sum of the two original tolerances.

```
> (percent
    (mul-interval
      (make-center-percent 1.0 1.0)
      (make-center-percent 1.0 1.0)))
1.999800019998002
> (percent
    (mul-interval
      (make-center-percent 1.0 2.0)
      (make-center-percent 1.0 1.0)))
2.9994001199760074
```

## Exercises 2.14 and 2.15

Dividing a number by itself should always yield 1, however our interval arithmetic package is unable two tell if two intervals are the same (in the identity sense). For this reason it is better to use formulas which do not repeat the same variable, multiple times.

## Exercise 2.16

Skipped.

## Exercise 2.17

```
(define (last-pair l)
  (if (null? (cdr l))
    l
    (last-pair (cdr l))))
```

## Exercise 2.18

```
(define (reverse l)
  (define (inner l-a l-b)
    (if (null? l-a)
      l-b
      (inner (cdr l-a)
             (cons (car l-a)
                   l-b))))
  (inner l nil))
```

## Exercise 2.19

```
(define no-more? null?)
(define except-first-denomination cdr)
(define first-denomination car)
```

## Exercise 2.20

```
(define (filter p l)
  (if (null? l)
    nil
    (let ((head (car l))
          (tail (cdr l)))
      (if (p (car l))
       (cons head (filter p tail))
       (filter p tail)))))

(define (same-parity . x)
  (filter
    (if (even? (car x))
      even?
      odd?)
    x))
```

## Exercise 2.21

```
(define (square-list items)
  (if (null? items)
      nil
      (cons (square (car items)) (square-list (cdr items)))))

(define (square-list items)
  (map square items))
```

## Exercise 2.22

`cons` lists can only be built in a single direction, from the bottom up. Therefore an iterative process which `cdr`s down a list will end up placing the first element it processes onto the bottom of the resulting list. One solution to this problem is to apply `reverse` to the final list.

## Exercise 2.23

```
(define (for-each p l)
  (if (null? l)
    nil
    (begin
      (p (car l))
      (for-each p (cdr l)))))
```

## Exercise 2.24

```
[2, .] -> [3, .] -> [4, /]
```

## Exercise 2.25

```
(car (cdr (car (cdr (cdr (list 1 3 (list 5 7) 9))))))
(car (car (list (list 7))))
(car (cdr (cdr (cdr (cdr (cdr (cdr (list 1 2 3 4 5 6 7))))))))
```

## Exercise 2.26

```
> (define x (list 1 2 3))
> (define y (list 4 5 6))
> (append x y)
(1 2 3 4 5 6)
> (cons x y)
((1 2 3) (4 5 6))
> (list x y)
((1 2 3) (4 5 6))
```

# Exercise 2.27

```
(define (deep-reverse l)
  (if (list? l)
    (reverse (map deep-reverse l))
    l))
```

# Exercise 2.28

```
(define (fringe t)
  (cond ((not (list? t)) (list t))
        ((null? t) t)
        (else
          (append (fringe (car t))
                  (fringe (cdr t))))))
```

## Exercise 2.29

```
(define (make-mobile left right)
  (list left right))
(define mobile? list?)
(define left-branch car)
(define (right-branch m) (car (cdr m)))

(define (make-branch length structure)
  (list length structure))
(define branch-length car)
(define (branch-structure b) (car (cdr b)))

;; Mobile -> Number
;; return the total weight of a mobile `m`
(define (total-weight m)
  (+ (branch-weight (left-branch m))
     (branch-weight (right-branch m))))

;; Branch -> Number
;; return the weight of a branch `b`
(define (branch-weight b)
  (let ((s (branch-structure b)))
    (if (mobile? s)
      (total-weight s)
      s)))

;; Mobile -> Bool
;; check if a mobile `m` is balanced
(define (balanced? m)
  (if (not (mobile? m))
    true
    (and
      (= (branch-torque (left-branch m))
         (branch-torque (right-branch m)))
      (balanced? (branch-structure (left-branch m)))
      (balanced? (branch-structure (right-branch m))))))

;; Branch -> Number
;; compute the torque of branch `b`
(define (branch-torque b)
  (* (branch-length b)
     (branch-weight b)))
```

We only have to change the selectors and the predicate `mobile?` if we change the representations of our data.

## Exercise 2.32

```
(define (square-tree tree)
  (cond ((null? tree) nil)
        ((not (pair? tree)) (square tree))
        (else
         (cons (square-tree (car tree))
               (square-tree (cdr tree))))))

(define (square-tree tree)
  (cond ((null? tree) nil)
        ((not (pair? tree)) (square tree))
        (else (map square-tree tree))))
```

## Exercise 2.31

```
(define (tree-map f tree)
  (cond ((null? tree) nil)
        ((not (pair? tree)) (f tree))
        (else
         (cons (tree-map f (car tree))
               (tree-map f (cdr tree))))))
```

## Exercise 2.32

```
(define (subsets s)
  (if (null? s)
      (list nil)
      (let ((rest (subsets (cdr s))))
        (append rest (map (lambda (x) (cons (car s) x))
                          rest)))))
```

The subsets of a null set are just the null set ({}). This represents our base case. If we add another element `a` to our set, the subsets become {} and {a}. This is equivalent to `(map (lambda (x) (cons a x)) (subsets null))`. This pattern holds as we continue to add elements to the set.

## Exercise 2.33

```
(define (map p sequence)
  (accumulate (lambda (x y) (cons (p x) y))
              nil sequence))

(define (append seq1 seq2)
  (accumulate cons seq2 seq1))

(define (length sequence)
  (accumulate (lambda (x y) (inc y)) 0 sequence))
```

## Exercise 2.34

```
(define
  (horner-eval x coefficient-sequence)
  (accumulate
   (lambda (this-coeff higher-terms)
     (+ (* higher-terms x) this-coeff))
   0
   coefficient-sequence))
```

## Exercise 2.35

```
(define (count-leaves t)
  (accumulate + 0 (map (lambda (x)
                         (cond ((null? x) 0)
                               ((pair? x) (count-leaves x))
                               (else 1)))
                       t)))
```

## Exercise 2.36

```
(define (accumulate-n op init seqs)
  (if (null? (car seqs))
      nil
      (cons (accumulate op init (map car seqs))
            (accumulate-n op init (map cdr seqs)))))
```

## Exercise 2.37

```
(define (matrix-*-vector m v)
  (map (lambda (row) (dot-product v row))
       m))

(define (transpose mat)
  (accumulate-n cons nil mat))

(define (matrix-*-matrix m n)
  (let ((cols (transpose n)))
    (map (lambda (row) (matrix-*-vector cols row)) m)))
```

## Exercise 2.38

```
(fold-right / 1 (list 1 2 3))      ; (/ 1 3 2 1)
(fold-left  / 1 (list 1 2 3))      ; (/ 1 1 2 3)
(fold-right list nil (list 1 2 3)) ; (list 1 2 3 nil)
(fold-left  list nil (list 1 2 3)) ; (list 3 2 1 nil)
```

`op` must be commutative.

## Exercise 2.39

```
(define (my-reverse sequence)
  (fold-right
    (lambda (x y) (append x (list y))) nil sequence))

(define (my-reverse sequence)
  (fold-left
    (lambda (x y) (cons y x)) nil sequence))
```

## Exercise 2.40

```
(define (unique-pairs n)
  (flatmap
    (lambda (i)
      (map (lambda (j) (list j i))
           (enumerate-interval 1 (dec i))))
    (enumerate-interval 1 n)))
```

## Exercise 2.41

```
(define (unique-tuples n m)
  (define (iter result m)
    (if (= m 0)
      result
      (iter (flatmap prepend-smaller result)
            (dec m))))
    (iter (map list (enumerate-interval 1 n))
          (dec m)))

(define (prepend-smaller lst)
  (map (lambda (i)
         (append (list i) lst))
       (enumerate-interval 1 (dec (car lst)))))

(define (triple-sum n s)
  (filter
    (lambda (triple) (= s (accumulate + 0 triple)))
    (unique-tuples n 3)))
```

## Exercise 2.42

See `eight-queens.rkt`

## Exercise 2.43

Louis's implementation revaluates `queen-cols` once for each row in the board. because of this his program find a solution in time `Tn` where `n` is the number of rows in the board.

## Exercise 2.53

```
> (list 'a 'b 'c)
(a b c)
> (list (list 'george))
((george))
> (list 'a 'b 'c)
(a b c)
> (list (list 'george))
((george))
> (cdr '((x1 x2) (y1 y2)))
((y1 y2))
> (cadr '((x1 x2) (y1 y2)))
(y1 y2)
> (pair? (car '(a short list)))
#f
> (memq 'red '((red shoes) (blue socks)))
#f
> (memq 'red '(red shoes blue socks))
(red shoes blue socks)
```

## Exercise 2.54

```
(define (equal? a b)
  (if (and (pair? a) (pair? b))
    (and (equal? (car a) (car b))
         (equal? (cdr a) (cdr b)))
    (eq? a b)))
```

## Exercise 2.55

```
'x  is the same as (quote x)
''x is the same as (quote (quote x))
(car (quote (quote x))) returns the head of the list which is quote
```

## Exercise 2.56

See `symbolic-deriv.rkt`

## Exercise 2.57

See `symbolic-deriv.rkt`

## Exercise 2.58

See `symbolic-deriv-infix.rkt`

## Exercise 2.59

```
(define (union-set set1 set2)
  (cond ((null? set1) set2)
        ((element-of-set? (car set1) set2)
         (union-set (cdr set1) set2))
        (else (cons (car set1)
                    (union-set (cdr set1)
                               set2)))))
```

## Exercise 2.60

```
;; Still O(n), however sets are now larger
(define (element-of-set? x set)
  (cond ((null? set) false)
        ((equal? x (car set)) true)
        (else (element-of-set? x (cdr set)))))

;; O(1)
(define (adjoin-set x set)
  (cons x set))

;; Still O(n)
(define (intersection-set set1 set2)
  (cond ((null? set1) '())
        ((element-of-set? (car set1) set2)
         (cons (car set1)
               (intersection-set (cdr set1)
                                 set2)))
        (else (intersection-set (cdr set1)
                                 set2))))

;; O(n)
(define (union-set set1 set2)
  (append set1 set2))
```

This reperesentation may be preferable on systems with large amounts of memory where adjoin-set and union-set are common operations.

## Exercise 2.61

```
(define (adjoin-set set1 set2)
  (cond ((null? set1) set2)
        ((null? set2) set1)
        (else (let ((x1 (car set1)) (x2 (car set2)))
                (cond ((= x1 x2)
                       (cons x1 (adjoin-set
                                  (cdr set1)
                                  (cdr set2))))
                      ((< x1 x2)
                       (cons x1 (adjoin-set
                                  (cdr set1)
                                  set2)))
                      ((< x2 x1)
                       (cons x2 (adjoin-set
                                  set1
                                  (cdr set2)))))))))
```

# Exercise 2.62

```
(define (union-set set1 set2)
  (cond ((null? set1) '())
        ((null? set2) '())
        (else (let ((x1 (car set1)) (x2 (car set2)))
                (cond ((= x1 x2)
                       (cons x1 (union-set
                                  (cdr set1)
                                  (cdr set2))))
                      ((< x1 x2)
                       (union-set
                         (cdr set1)
                         set2))
                      ((< x2 x1)
                       (union-set
                         set1
                         (cdr set2))))))))
```

## Exercise 2.63

1. Both procedures perform an in-order traversal (left, center, right) to construct a list from the bottom up. Therefore they both produce the same list.

2. The first procedure is O(n log n) since it performs an O(n) append once per level of the tree. The second procedure is O(n) since it performs a O(1) cons once per entry in the tree.

## Exercise 2.64

### Question 1

Partial tree works by dividing the problem of constructing the tree into three subproblems:

1. Constructing the left side from the first floor((n - 1) / 2) elements
2. Constructing the center from the next elment
3. Constructing the right side from the next n - (size(left side) + 1) elements

```
   5
 /   \
1     9
 \   / \
  3 7   11
```

### Question 2

```
T(n) = 2T(n/2) + O(1)
     = O(n)
```

## Exercise 2.65

```
(define (union-set-tree set1 set2)
  (list->tree (union-set (tree->list set1) (tree->list set2))))

(define (intersection-set-tree set1 set2)
  (list->tree (intersection-set (tree->list set1) (tree->list set2))))
```

## Exercise 2.66

```
(define (lookup given-key set-of-records)
  (define (lookup given-key set-of-records)
    (if (null? set-of-records)
      false
      (let (current-key (key (entry set-of-records)))
        (cond ((= given-key current-key)
               (entry set-of-records))
              ((< given-key current-key)
               (lookup given-key (left-branch set-of-records))
              (else
               (lookup given-key (right-branch set-of-records)))))))))
```

## Exercise 2.67

```
> (decode sample-message sample-tree)
(A D A B B C A)
```

## Exercise 2.68

See `huffman-encoding.rkt`

## Exercise 2.69

See `huffman-encoding.rkt`

## Exercise 2.70

```
> (length (encode
            '(
              GET A JOB
              SHA NA NA NA NA NA NA NA NA
              GET A JOB
              SHA NA NA NA NA NA NA NA NA
              WAH YIP YIP YIP YIP
              YIP YIP YIP YIP YIP
              SHA BOOM
              )
            (generate-huffman-tree
              '(
                (A    2)    (NA  16)
                (BOOM 1)    (SHA  3)
                (GET  2)    (YIP  9)
                (JOB  2)    (WAH  1)
                )
              )))
84
```

Huffman encoding requires 84 bits vs 89 * 8 = 712 bits for Ascii encoding.

## Exercise 2.71

```
             {a b c d e} 31
             /            \
         {a b c d} 15     e 16
         /          \
     {a b c} 7      d 8
     /       \
  {a b} 3    c 4
  /    \
a 1    b 2
```

1. 1 bit is required to encode the most frequent symbol.
2. n - 1 bits are required to encode the least frequent symbol.

## Exercise 2.72

The time to search for a symbol in the tree is proportional to the number of bits required to encode the symbol. For the most frequent symbol this is constant, for the least frequent symbol this is proportional to the number of other symbols.

1. Most frequent symbol: O(1)
2. Least frequent symbol: O(n)

## Exercise 2.73

### Part 1

Instead of checking if an expression is a sum, product, or exponent we lookup the derivative procedure for the given operator and apply it to the operands. This cannot be done for `number?` and `variable` because they are represented by primitive so they are not tagged with a symbol to dispatch on.

### Part 2 / 3

See `symbolic-deriv-dyn.rkt`

### Part 4

Procedures would need to be installed with `(put 'op 'deriv (lambda (operands var) ...))`

## Exercise 2.74

```
(define (type x)
  (car x))

(define (get-record personnel-file)
  ((get 'get-record (type personnel-file))
   personnel-file))

(define (get-salary personnel-file)
  ((get 'get-salary (type personnel-file))
   personnel-file))

  (define (get-name personnel-file)
    ((get 'get-employee-name (type personnel-file))
     personnel-file))

(define (find-employee-record records name)
  (cond ((null? records) (error "search failed"))
        ((equal name (get-name (car records))) (car records))
        (else (find-employee-record (cdr records) name))))
```

Each division's records must be structured so that `type` works, and each division must install `get-record`, `get-salary`, and `get-employee-name` for their record types. These conditions must be met when a new company is acquired.

## Exercise 2.75

```
(define (make-from-mag-angle m a)
  (lambda (op)
    (cond ((eq? op 'real-part) (* m (cos a)))
          ((eq? op 'imag-part) (* m (sin a)))
          ((eq? op 'magnitude) m)
          ((eq? op 'angle) a)
          (else (error "unknown op")))))
```

## Exercise 2.76

### Explicit dispatch

- all generic procedures which directly access a type's structure must be modified to support new types
- no existing procedures need to be modified to add additional operations

### Data directed

- the table must be modified to support additional types
- the table must be modified to support additional procedures

### Message passing

- no exiting code needs to be modified to add additional types
- each type must be modified to add additional procedures

### Summary

All of these strategies are similar, the differences begin in where the edits need to occur when the sytem is extended. Message passing / data directed systems are best when type are added frequently, and explicit dispatch is best when procedures are added frequently.

## Exercise 2.77

This works because it performs a two stage dispatch which recursively calls magnitude on the contents of z.

```
(magnitude z)
(apply-generic 'magnitude z)
((get 'magnitude '(complex)) (contents z))
(magnitude (contents z))
(apply-generic 'magnitude (contents z))
((get 'magnitude '(polar)) (contents (contents z)))
```

## Exercise 2.78

```
(define (attach-tag type-tag contents)
  (if (number? contents)
    contents
    (cons type-tag contents)))

(define (type-tag datum)
  (cond ((number? datum) 'scheme-number)
        ((pair? datum)
         (cdr datum))
        (else (error "Bad tagged datum: 
                     CONTENTS" datum))))

(define (contents datum)
  (cond ((number? datum) datum)
        ((pair? datum)
         (cdr datum))
        (else (error "Bad tagged datum: 
                     CONTENTS" datum))))
```

## Exercise 2.79

```
(define (equ? a b)
 (apply-generic '= a b))

(put '= '(scheme-number scheme-number) =)
```

## Exercise 2.80

```
(define (=zero? x)
 (apply-generic '=zero? x))

(put '=zero? '(scheme-number) zero?)
```

## Exercise 2.81

1. In all scenarios the first argument will be coerced in an infinite loop due to the recursive nature of `apply-generic`.
2. Louis is incorrect, apply-generic should work as is.

```
(define (apply-generic op . args)
  (let ((type-tags (map type-tag args)))
    (let ((proc (get op type-tags)))
      (if proc
          (apply proc (map contents args))
          (if (and (= (length args) 2)
                   (not (eq? (car type-tags) (cadr type-tags))))
              (let ((type1 (car type-tags))
                    (type2 (cadr type-tags))
                    (a1 (car args))
                    (a2 (cadr args)))
                (let ((t1->t2 
                       (get-coercion type1
                                     type2))
                      (t2->t1 
                       (get-coercion type2 
                                     type1)))
                  (cond (t1->t2
                         (apply-generic 
                          op (t1->t2 a1) a2))
                        (t2->t1
                         (apply-generic 
                          op a1 (t2->t1 a2)))
                        (else
                         (error 
                          "No method for 
                           these types"
                          (list 
                           op 
                           type-tags))))))
              (error 
               "No method for these types"
               (list op type-tags)))))))
```

## Exercise 2.82

```
(define (apply-generic op . args)
  (let ((type-tags (map type-tag args)))
    (let ((proc (get op type-tags)))
      (if proc
        (apply proc (map contents args))
        (cocerce-generic op args)))))

(define (cocerce-generic op args)
  (car (memf identity
             (filter-map
               (lambda (args) (member #f args))
               (lambda (args)
                 (let ((proc (get op (map type-tags args))))
                   (if proc
                     (apply proc (map contents args))
                     #f)))
               (map (lambda (x) (try-coerce (car x) (cadr x)))
                    (product args))))))

(define (try-coerce a1 a2)
  (let ((t1 (type-tag a1))
        (t2 (type-tag a2)))
    (if (eq? t1 t2)
      a1
      (let ((t1->t2 (get-coercion t1 t2)))
        (if t1->t2
          (t1-t2 a1)
          #f)))))
```

## Exercise 2.83

```
(define (raise x) (apply-generic 'raise x))
(put 'raise '(integer) (lambda (x) (make-rat x 1)))
(put 'raise '(rat) (lambda (x) (make-real (/ (numer x) (denom x)))))
(put 'raise '(real) (lambda (x) (make-imag x 0)))
```

## Exercise 3.1

```
(define (make-accumulator x)
  (lambda (y)
    (set! x (+ x y))
    x))
```

## Exercise 3.2

```
(define (make-monitored f)
  (let ((n 0))
    (lambda (x)
      (if (eq? x 'how-many-calls)
        n
        (begin (set! n (inc n))
               (f x))))))
```

## Exercise 3.3

```
(define (make-account amount passwd)
  (lambda (passwd-prime msg)
    (cond ((not (eq? passwd-prime passwd))
           (lambda (x) "invalid password"))
          ((eq? msg 'withdrawl)
           (lambda (amount-prime)
             (if (<= amount-prime amount)
               (begin
                 (set! amount (- amount amount-prime))
                 amount)
               "insufficient funds")))
          (else (lambda (x) "unknown operation")))))
```

## Exercise 3.4

```
(define (make-account amount passwd)
  (define (withdrawl amount-prime)
    (if (<= amount-prime amount)
      (begin
        (set! amount (- amount amount-prime))
        amount)
      "insufficient funds"))
  (let ((num-incorrect-passwds 0))
    (lambda (passwd-prime msg)
      (if (not (eq? passwd-prime passwd))
        (begin
          (set num-incorrect-passwds (inc num-incorrect-passwds))
          (if (> num-incorrect-passwds 7) (call-the-cops))
          (lambda (x) "invalid password"))
        (begin
          (set num-incorrect-passwds 0)
          (cond ((eq? msg 'withdrawl) withdrawl)
                (else (lambda (x) "unknown operation"))))))))
```

## Exercise 3.5

```
(define (estimate-integral p x1 x2 y1 y2)
  (monte-carlo 1000
               (lambda ()
                 (p (+ x1 (random (- x2 x1)))
                    (+ y1 (random (- y2 y1)))))))

(* 4.0 (estimate-integral (lambda (x y)
                            (< (+ (square x) (square y)) 1.0))
                          -1.0 1.0 -1.0 1.0))
```

## Exercise 3.6

```
(define rand
  (let ((x random-init))
    (lambda (msg)
      (cond ((eq? msg 'generate)
             (begin (set! x (rand-update x)) x))
            ((eq? msg 'reset)
             (begin (set! x random-init) "rand reset"))))))
```

## Exercise 3.7

```
(define (make-joint acc acc-pass new-pass)
  (lambda (pass msg)
    (if (not (eq? pass new-pass))
      (lambda (_) "invalid password")
      (acc acc-pass msg))))

```

## Exercise 3.8

```
(define y false)
(define (f x)
  (if (or y (= x 0))
    (begin (set! y true)
           0)
    x))
```

## Exercise 3.12

```
> (car x)
'(a b)

> (cdr x)
'(b c d)
```
