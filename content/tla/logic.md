+++
title = "Logic"
weight = 20
+++

In this section, we'll introduce the basics of propositional logic. Even if you're unfamiliar with the idea, you've almost certainly used it in programming before.

### `\E`

`\E` means "exists". We write `\E x \in S : P(x)` to say "there is at least one x in the set `S` such that P(x) is true." It's the equivalent of a python `any()` or a Ruby `any?`. If we wanted to check that a set had an even  number in it, we could write `HasEvenNumber(S) == \E x \in S : IsEven(x)`

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

`\A` means "all". We write `\A x \in S : P(x)` to say "For every x in the set, P(x) is true." If we wanted to check that a set had no odd numbers in it, we could write `OnlyEvenNumbers(S) == \A x \in S : IsEven(x)`. If there are only even numbers, `OnlyEvenNumbers` is true. Otherwise it's false. Simple.

`~\A` is the opposite: it says that there is at least one element where P(x) is false. `\A x \in {}: Foo` is always true, since there are no elements in `{}`, so all zero elements pass the test.

{{% notice warning %}}
`\A x \in {}: FALSE` is still true!
{{% /notice %}}

{{% q %}}
Given a set and an operator, determine whether the operator is commutative over _all_ elements in the set.

{{% ans abelian %}}
```tla
IsCommutative(Op(_,_), S) == \A x \in S :
                          \A y \in S : Op(x,y) = Op(y,x)
```
Alternatively, we could put them on the same line:
```tla
IsCommutative(Op(_,_), S) == \A x \in S, y \in S : Op(x,y) = Op(y,x)`
```
{{% /ans %}}
{{%/q %}}

### `=>` and `<=>`

`P => Q` means "If P is true, then Q must also be true." Note that P can be false and Q can be true, or both can be false. It's equivalent to writing `~P \/ Q`, which is how TLC interprets it.

`P <=> Q` means "Either both P and Q are true or both are false." It's equivalent to writing `(~P /\ ~Q) \/ (P /\ Q)`. `P <=> ~Q` is P XOR Q.

{{% notice tip %}}
When `P` and `Q` are booleans, `P <=> Q` is equal to `P = Q`. when `P` and `Q` are not booleans, `P <=> Q` is a TLC error. This means TLC will catch it if you accidentally didn't use booleans
{{% /notice %}}

{{% q %}}
Without looking back at the introduction, write an operator that returns the maximum number of a set.

{{% ans max %}}
```tla
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
```
{{% /ans %}}
{{% /q %}}

Both `=>` and `<=>` follow the same precedence rules as logical junctions. In other words, TLC interprets

```
/\ A
/\ B
  => C
```

as `A /\ (B => C)`, whereas 

```
/\ A
/\ B
=> C
```

Is `(A /\ B) => C`.

### CHOOSE

While we introduced the CHOOSE operator back in sets, it really comes into its own when we add the logical operators. Many quantified properties, such as "the largest x such that P", can be expressed as "the x where all larger elements don't have P" or "the x where all of the other elements with P are smaller". For example, what is the largest prime in a set S?

```tla
IsPrime(x) == x > 1 /\ ~\E d \in 2..(x-1) : x % d = 0

LargestPrime(S) == CHOOSE x \in S:
                    /\ IsPrime(x)
                    /\ \A y \in S:
                        IsPrime(y) => y <= x
                    \* or y > x => ~IsPrime(y)
```

{{% q %}}
A prime number p is a _twin prime_ if p-2 is prime or p+2 is prime. Find the largest twin prime in S.
{{% ans twin %}}

```tla
IsTwinPrime(x) == /\\ IsPrime(x)
                  /\\ \/ IsPrime(x + 2)
                     \/ IsPrime(x - 2)

LargestTwinPrime(S) == CHOOSE x \in S:
                    /\\ IsTwinPrime(x)
                    /\\ \A y \in S: IsTwinPrime(y) => y <= x
                    \* or y > x => ~ IsTwinPrime(y)
```                    
{{% /ans %}}

Now return the largest pair of twin primes, ordered by value. Assume that S may be missing numbers and, if one of the twin primes is missing, the pair is invalid. For example, the largest pair in `{3, 5, 13}` is `<<3, 5>>`, not `<<5, 13>>`.

{{% ans twinpair %}}
```tla
LargestTwinPair(S) == CHOOSE <<x, y>> \in S \X S:
                         /\\ IsPrime(x)
                         /\\ IsPrime(y)
                         /\\ x = y - 2
                         /\\ \A <<w, z>> \in S \X S:
                            /\\ IsPrime(z)
                            /\\ IsPrime(w)
                            /\\ w = z - 2
                            => z < y
```
{{% /ans %}}
{{% /q %}}

{{% q %}}

Given `stockprices` is a tuple of positive integers representing the value of a stock at a given time of day, write an operator that determines the maximum profit you could make by buying and selling a single stock. Assume for this problem that you cannot short; you must buy before you sell.

{{< ans profit >}}
```tla
MaxProfit(stockprices) ==
    LET sp == stockprices \* clean it up a bit
        TimePair == (1..Len(sp)) \X (1..Len(sp))
        Profit[p \in TimePair] == sp[p[2]] - sp[p[1]]
        best == CHOOSE best \in TimePair :
            /\ best[2] > best[1] \* Buy after sell
            /\ Profit[best] > 0 \* Make money plz
            /\ \A worse \in TimePair :
                worse[2] > worse[1] => Profit[best] >= Profit[worse]
    IN Profit[best]
```

Note this will crash if there is no possible pair, which is preferrable to paying trading fees twice on a zero-dollar profit.

{{< /ans >}}
{{% /q %}}
