+++
title = "Sets"
weight = 1
+++

First, a few helper operators:

```tla
Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == Pick(S)
                              IN SetReduce(Op, S \ {s}, Op(s, value)) 

```

Note that `SetReduce` only works for commutative operators. You will have to define a separate operator if you want to reduce over a function.

If you're concerned about accidentally passing in a noncommutative operator, we can make a 'safe' reduce that fails iff any given step is not commutative.

```tla
EXTENDS TLC

SetReduce(Op(_, _), S, value) == 
  IF S = {} THEN value
  ELSE LET s == Pick(S)
       IN IF Op(s, value) = Op(value, s)
       THEN SetReduce(Op, S \ {s}, Op(s, value)) 
       ELSE Assert(FALSE, "oh no")
```

### Sum of a set

```tla
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)
```

### Min and Max

Two different ways to do it.

```tla
Max(S) == CHOOSE x \in S: 
            \A y \in S: 
              y <= x

Min(S) == CHOOSE x \in S: 
            \A y \in S \ {x}: 
              y > x
```
