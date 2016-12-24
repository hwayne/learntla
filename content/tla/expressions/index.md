+++
title = "Set [Thingy]"
weight = 2
draft = true
+++

Often, when we have a set of things, we're interested in how those things relate to each other and the set itself. For example, "Given this set of [], are any broken?" Additionally, we often want to choose things out of a set with specific properties, for example "the smallest element". In order to do this, we'll introduce three new set operators. For all these examples, let's assume we've already written the following operator:

`IsEven(x) == x % 2 = 0`

### \E

`\E` means "exists". We write `\E x \in S : P(x)` to say "there is at least one x in the set such that P(x) is true." If we wanted to check that a set had an even  number in it, we could write `HasEvenNumber(S) == \E x \in S : IsEven(x)`. If there are any even numbers, `HasEvenNumber` is true. Otherwise it's false. Simple.

`~\E` is the opposite: it says that there are no such elements. `\E x \in {}: Foo` is always false, since there are no elements in `{}`.

### \A

`\A` means "all". We write `\A x \in S : P(x)` to say "For every x in the set,P(x) is true." If we wanted to check that a set had an even number in it, we could write `OnlyEvenNumbers(S) == \A x \in S : IsEven(x)`. If there are only even numbers, `HasEvenNumber` is true. Otherwise it's false. Simple.

`~\A` is the opposite: it says that there is at least one element where P(x) is false. `\A x \in {}: Foo` is always true, since there are no elements in `{}`.

{{% notice warning %}}
`\A x \in {}: FALSE` is still true!
{{% /notice %}}

### CHOOSE

`CHOOSE` means exactly that. We write `CHOOSE x \in S : P(x)` to say "Throw me whatever x is in S for which P(x) is true". For example, we could write `AnEvenNumber(s) : CHOOSE x \in S : IsEven(x)` to mean "I want an even number." 

If there are multiple elements that satisfy the CHOOSE, TLC will create a separate behavior for each element. If there are no elements that satisfy the CHOOSE, TLC will raise an error. That's because there's a problem in your spec. If the set is infinite, TLC will raise an error. That's because TLC can't choose from an infinite sets. There still may be a problem with your spec.

## Composing Set Operators

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
