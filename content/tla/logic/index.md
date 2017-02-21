+++
title = "Logic"
weight = 20
+++

In this section, we'll introduce the basics of propositional logic. Even if you're unfamiliar with the idea, you've almost certainly used it in programming before. 

### `\E`

`\E` means "exists". We write `\E x \in S : P(x)` to say "there is at least one x in the set such that P(x) is true." It's the equivalent of a python `any()` or a Ruby `any?`. If we wanted to check that a set had an even  number in it, we could write `HasEvenNumber(S) == \E x \in S : IsEven(x)`

`~\E` is the opposite: it says that there are no such elements. `\E x \in {}: Foo` is always false, since there are no elements in `{}`.

{{% q %}}
Assuming `Sum(S)` returns the sum of the elements of S, write an operator that, for a given set of integers S and integer N, returns if there are N elements in S that sum to 0. eg

```tla
SumsToZero({1, 2, -7, 4, 11}, 2) = FALSE
SumsToZero({1, 2, -7, 4, 11}, 4) = TRUE
SumsToZero({1, 2, -7, 4, 11}, 5) = FALSE
```

{{% ans sum %}}
```tla
SumsToZero(S, N) == \E s \in SUBSET S:
                      /\\ Cardinality(s) = N
                      /\\ Sum(s) = 0
```
{{% /ans %}}
{{%/q %}}
### `\A`

`\A` means "all". We write `\A x \in S : P(x)` to say "For every x in the set, P(x) is true." If we wanted to check that a set had no odd numbers in it, we could write `OnlyEvenNumbers(S) == \A x \in S : IsEven(x)`. If there are only even numbers, `HasEvenNumber` is true. Otherwise it's false. Simple.

`~\A` is the opposite: it says that there is at least one element where P(x) is false. `\A x \in {}: Foo` is always true, since there are no elements in `{}`, so all zero elements pass the test.

{{% notice warning %}}
`\A x \in {}: FALSE` is still true!
{{% /notice %}}

{{% q %}}
Given a set and an operator, determine whether the operator is commutative over _all_ elements in the set.

{{% ans abelian %}}
```tla
IsCommutative(Op, S) == \A x \in S : 
                          \A y \in S : Op(x,y) = Op(y,x)
```
Alternatively, we could put them on the same line:
```tla
IsCommutative(Op, S) == \A x \in S, y \in S : Op(x,y) = Op(y,x)`
```
{{% /ans %}}
{{%/q %}}

### `=>` and `<=>`

`P => Q` means "If P is true, then Q must also be true." Note that P can be false and Q can be true, or both can be false. It's equivalent to writing `~P \/ Q`, which is how TLC interprets it.

`P <=> Q` means "Either both P and Q are true or both are false." It's equivalent to writing `(~P /\ ~Q) \/ (P /\ Q)`. `P <=> ~Q` is P XOR Q.

{{% q %}}
Without looking back at the introduction, write an operator that returns the maximum number of a set.

{{% ans max %}}
```tla
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
```
{{% /ans %}}
{{%/q %}}
