+++
title = "Sets, Tuples, and Structures"
weight = 7
+++


In the last sequence we saw how we could model complicated behavior with PlusCal. We also saw that it could get a little unwieldy. In this section we'll introduce a couple of extra types, as well as some information on how to use them.

## Types

### Sets

[TALK ABOUT MULTIPLE SELECT]
You've seen sets before. `{1, 2}` is a set. `1..N` is the set of all numbers between 1 and 2.

Is there a convenient shorthand to say "the set of all odd numbers under 100"? We can do this with _set constructors_, the map and filter analogs of a set.

First, we can filter a set with `{x \in S: P(x)}`, which is the set of all x \in S where P(x) is true. Some examples:

- `{x \in 1..100 : x % 2 = 1}`
- `{x \in S : x \in Z \/ x >= 5}`
- `{x \in S : FALSE}`

We can also map with `{F(x) : x \in S}`. `{x * 2 : x \in 1..3}` is the set `{2, 4, 6}`.

Finally, there are extra operations for working with sets:

logic | token | `TRUE` | `FALSE`
------|--------|--------|--------
in set|  `\in` | `1 \in {1, 2}` | `1 \in {{1}, 2}` 
not in set | `\notin` | `1 \notin {}` | `{1} \notin {{1}}`
is subset | `\subseteq` | `{1, 2} \subseteq {1, 2, 3}` | `{1, 2} \subseteq {1, 3}`

token | operation | example
-------|-----------|--------
`\cup`, `\union` | Set Union | `{1, 2} \cup {2, 3} = {1, 2, 3}`
`\cap`, `\intersect` | Set Intersection | `{1, 2} \cap {2, 3} = {2}`
`S1 \ S2` | The elements in S1 not in S2 | `{1, 2} \ {2, 3} = {1}, {2, 3} \ {1, 2} = {3}`
`SUBSET S` | The set of all subsets of S | `SUBSET {1, 2} = {{}, {1}, {2}, {1, 2}}`
`UNION S` | Flatten set of sets | `UNION {{1}, {1, 2}, {5}} = {1, 2, 5}`

### Tuples

[TODO DOMAIN]

Tuples are pretty much what you think they are. They have an ordering and everything. You specify them with `<<>>` and they are 1-indexed.

{{% notice warning %}}
Did I mention they're 1-indexed? They're 1-indexed.
{{% /notice %}}

```
x = <<4, 5, 6>>;
x[1] + x[2] + x[3] = 15;
```

If you add `EXTENDS Sequences` to your spec, they also do double duty as sequences, which adds some more functionality. None of these operations will mutate the sequence. If you want to pop the head, for example, you have to do `seq := Tail(seq)`.

token | operation | example
------|-----------|--------
Head | First element | `Head(<<1, 2>>) = 1`
Tail | Sequence aside from head | `Tail(<<1, 2>>) = <<2>>`
Append | Add element to end of sequence | `Append(<<1>>, 2) = <<1, 2>>`
`\o` | Combine two sequences | `<<1>> \o <<2>> = <<1, 2>>`
Len | Length of sequence | `Len(<<1, 2>>) = 2`

{{% notice info %}}
If the value is undefined (for example, `Tail(<<1>>)`), the model crashes. This is a Good Thing- better you know something is wrong with the model than get bad results.
{{% /notice %}}

### Structures

Structures are hashes. They have keys and values. You specify them as `[key |-> value]` and query them with either `[key]` or `.key`. Both are legal and valid.

```
x = [a |-> 1, b |-> {2, 3}];
x.a = 1;
x["b"] = {2, 3};
```

Aside from that, there's one extra trick structures have. Instead of `key |-> value`, you can do `key : set`. In that case, instead of a structure you get the set of all structures which have, for each given key, a value in the set.

```
x = [a |-> 1, b : {2, 3}];
x = { [a |-> 1, b |-> 2], [a |-> 1, b -> 3] }
```

Neat, huh? It's pretty neat.


{{% notice info %}}
Aside from sets, sequences, and structures, there's a fourth complex type: functions. They're a little more complicated, so I cover them in a couple of chapters. Feel free to [skip ahead] if you want.
{{% /notice %}}

{{% notice note %}}
The above is a blatant lie. There's actually only two complex types: sets and functions. Tuples and structures are just functions with some syntactic sugar.
{{% /notice %}}

### Type Composition

Any type can be squeezed inside any other type.

```
x = [a |-> {<<>>, <<1, 2, 3>>, <<3, 2, 1>>}, b |-> <<[a |-> 0]>>];
x.b[1].a; \* 0
```

There's nothing technically _stopping_ you from writing a sequence with alternating 1's and sets of structures, but that will end very badly, so please don't do that.

## Example

_Solve the Tower of Hanoi._

Quick refresher on the [rules](https://www.cs.sfu.ca/~tamaras/recursion/Rules_Towers_Hanoi.html). This kind of problem flips TLA+ on its head. Instead of checking if our solution has no problems, we're checking that our problem has a solution! A common way to do this is to turn the spec inside out: we say the spec is "valid" if the solution is unreachable. Then TLC will flag it as an "error" and show us the steps required to reproduce the solution.

(Improve this code it's the worst)

{{% code hanoi %}}
