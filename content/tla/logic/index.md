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

[[ TODO examples ]]
