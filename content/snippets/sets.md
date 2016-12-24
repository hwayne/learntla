+++
title = "Sets"
weight = 1
draft = true
+++

### Sum of a set

This is gawdawful
```
Sum(Set) == LET FSum[S \in SUBSET Set] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE + FSum[S \ {elt}]
          IN  FSum[Set]
```

### Min and Max

### Set Compositon

```
S ** n = [1..n -> S]
S ** n = UNION {[1..m -> S] : m \in 1..n}
```
