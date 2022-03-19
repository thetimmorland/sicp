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
