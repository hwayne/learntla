+++
title = "Expressions"
weight = 0
+++

### Operators

```tla
Add(a,b) == a + b

Apply(Op(_,_), a) == Op(a, 3)
Apply(Add, 5) = 8

RECURSIVE IsOdd(_)

IsOdd(n) == CASE n = 1 -> TRUE
              [] n = 0 -> FALSE
              [] OTHER -> ~IsOdd(n-1)

IsOdd(3) = TRUE
```

### Expressions

```tla
AddOrMult(a, b, add) == IF add
                        THEN a + b
                        ELSE a * b
AddOrMult(4, 6, TRUE) = AddOrMult(2, 5, FALSE)

SubtractSquares(a, b) == 
  LET sum  == a + b
      diff == a - b
  IN sum * diff
SubtractSquares(6, 4) = 20 

Bool(bool) ==
  LET op1 == LET op2 == LET op3 ==
      IF bool
      THEN TRUE ELSE 
      FALSE IN 
      op3 IN op2
  IN op1
Bool(TRUE) = TRUE
Bool(FALSE) = FALSE
```

### Logic

```tla
(\E x \in {1, 2, 3} : x > 2) = TRUE
(CHOOSE x \in {1, 2, 3} : x > 2) = 3
(CHOOSE x \in {1, 2, 3} : x <= 2) = \* 1 or 2, arbitrary

(\A x \in {1, 2, 3} : x > 4) = FALSE
(CHOOSE x \in {1, 2, 3} : x > 4) = \* error

EvenSquare(n) ==
  /\ n % 2 = 0
  /\ \E x \in 1..n : x*x = n

EvenSquareOrOdd(n) ==
  \/ /\ n % 2 = 0
     /\ \E x \in 1..n : x*x = n
  \/ n % 2 = 1

EvenSquareOrOddNonsquare(n) ==
  (\E x \in 1..n : x*x = n) <=> (n % 2 = 0)
```
