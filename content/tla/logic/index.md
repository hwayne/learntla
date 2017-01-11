+++
title = "Logic"
weight = 20
+++

In this section, we'll introduce the basics of propositional logic. Even if you're unfamiliar with the idea, you've almost certainly used it in programming before. 

### `\E`

`\E` means "exists". We write `\E x \in S : P(x)` to say "there is at least one x in the set such that P(x) is true." It's the equivalent of a python `any()` or a Ruby `any?`. If we wanted to check that a set had an even  number in it, we could write `HasEvenNumber(S) == \E x \in S : IsEven(x)`

`~\E` is the opposite: it says that there are no such elements. `\E x \in {}: Foo` is always false, since there are no elements in `{}`.

### `\A`

`\A` means "all". We write `\A x \in S : P(x)` to say "For every x in the set, P(x) is true." If we wanted to check that a set had no odd numbers in it, we could write `OnlyEvenNumbers(S) == \A x \in S : IsEven(x)`. If there are only even numbers, `HasEvenNumber` is true. Otherwise it's false. Simple.

`~\A` is the opposite: it says that there is at least one element where P(x) is false. `\A x \in {}: Foo` is always true, since there are no elements in `{}`.

{{% notice warning %}}
`\A x \in {}: FALSE` is still true!
{{% /notice %}}

### `=>` and `<=>`

`P => Q` means "If P is true, then Q must also be true." Note that P can be false and Q can be true, or both can be false. It's equivalent to writing `~P \/ Q`, which is how TLC interprets it.

`P <=> Q` means "Either both P and Q are true or both are false." It's equivalent to writing `(~P /\ ~Q) \/ (P /\ Q)`. `P <=> ~Q` is P XOR Q.

## Examples

You can specify surprisingly complex properties with just those three additional operators. To demonstrate this, let's burn through some common whiteboard interview problems.

_Find the largest element in the set._

```
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
\* Or
Max(S) == CHOOSE x \in S : \A y \in S \ {x} : y < x
```

"Choose an element of a set where all other elements are smaller than it."

_Here's a list of numbers, do any two add up to N?_

```
IsTwo(Seq, N) == \E x, y \in 1..Len(Seq) : x # y /\ Seq[x] + Seq[y] = N
```

"Are there two different numbers that correspond to the points in the sequence that add up to N."

_Do any THREE add up to N?_

```
IsThree(Seq, N) == \E x, y, z \in 1..Len(Seq) : Cardinality({x, y, z}) = 3 /\ Seq[x] + Seq[y] + Seq[z] = N
```

To make this a little nicer we show that `x # y # z` by saying "If we throw them all into a set, the set should be size three." Otherwise, one of them was a duplicate.

_[That annoying stock problem]_

TODO CLEANUP

```
BestSell(Prices) == CHOOSE <<min, max>> \in 1..Len(Prices) \X 1..Len(Prices) :
                      /\ max >= min
                      /\ \A a, b \in 1..Len(Prices) : 
                        a <= b 
                        => Prices[b] - Prices[a] <= Prices[min] - Prices[max]
```

[Explain]

_Given lists of numbers A and B, determine if one is a rotation of the other. Eg 1, 2, 3, 4 is a rotation of 2, 3, 4, 1_

```
IsRotation(Seq1, Seq2) == LET len == Len(Seq2)
                          IN /\ Len(Seq1) = len
                             /\ \E x \in 1..len :
                                \A n \in 1..len : Seq1[((n+x)%len)+1] = Seq2[n]
\* Or

IsRotation(Seq1, Seq2) == LET AllRotations(S) ==
                              { [ n \in 1..Len(S) |-> S[((n+x)%Len(S))+1]] : x \in 1..Len(S) } 
                          IN Seq1 \in AllRotations(Seq2)
```

"Here's what it means to be a rotation. Does Se1 match that definition?" [Dislike this]

[PlusCal Example?]
