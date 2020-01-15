+++
title = "Sets"
weight = 4
+++

You've seen sets before. `{1, 2}` is a set. `1..N` is the set of all numbers between 1 and N. `x \in S` checks whether S contains x, unless you use it in a PlusCal `variables` statement or a `with` (where it creates new behaviors). Like everything else, you can nest them: `{{{}}}` is a set containing a set containing an empty set.

Often, we're interested in some transformation of the set, such as "the set of male participants under 60" or "The owners of the pets." In this section we'll cover three ways to transform a set and how they are combined.

### Filtering

We can filter a set with `{x \in S: P(x)}`, which is the set of all x \in S where P(x) is true. For example, `{x \in 1..8 : x % 2 = 1}` is the set `{1, 3, 5, 7}`. P must return a boolean, so `{ x \in 1..4 : x * x }` raises an error.

If S is a set of tuples, you can filter on some relationship between the elements of the tuple by instead using `<<...>> \in S`. If you want the set of ordered pairs, you could do `{<<x, y>> \in S \X S : x >= y}`.

As always, you can nest filters, and `{x \in {y \in S : P(y)} : Q(x)}` will filter on the filtered list. Generally, though, `{x \in S: P(x) /\ Q(x)}` is easier to understand.


### Mapping

`{P(x): x \in S}` applies P to every element in the set. `{ x * x : x \in 1..4 }` is the set `{1, 4, 9, 16}`. `{ x % 2 = 1:x \in 1..8 }` is the set `{TRUE, FALSE}`. 

You can also write `{P(x, y, ...) : x \in S, y \in T, ...}`. `{ x + y : x \in 0..9, y \in { y * 10 : y \in 0..9} }` is the first hundred numbers, in case you wanted to obfuscate `0..99`.

{{% q %}}
Given `DOMAIN Tuple` is the set of numbers `Tuple` is defined over, write an operator that gives you the values of the Tuple, ie the range.

{{% ans range %}}
`Range(T) == { T[x] : x \in DOMAIN T }`
{{% /ans %}}

This is a useful enough operator that I'll assume it's available for all other examples and exercises.
{{%/q %}}

### CHOOSE

`CHOOSE x \in S : P(x)` is some x where P(x) is true. `CHOOSE x \in 1..8 : x % 2 = 1` will be one of 1, 3, 5, 7. TLC does _not_ branch here; while the number it chooses is arbitrary, it will _always_ return that number. This is similar to how CASE statements work: `CHOOSE x \in S : TRUE` is _some_ element of S, but TLC won't check all of them.

TLC assumes that you always intend for there to be at least one element to choose. If there aren't any (trivial example: `CHOOSE x \in S : FALSE`), it will consider this a problem in your spec and raise an error. TLC will also raise if S is infinite because TLC can't evaluate P on an infinite number of elements. There still may be a problem with your spec, though, and it's a good idea to try it on a finite subset.


## Set Operators

Finally, there are extra operations for working with sets:

logic | operator | `TRUE` | `FALSE`
------|--------|--------|--------
in set|  `\in` | `1 \in {1, 2}` | `1 \in {{1}, 2}` 
not in set | `\notin` | `1 \notin {}` | `{1} \notin {{1}}`
is subset | `\subseteq` | `{1, 2} \subseteq {1, 2, 3}` | `{1, 2} \subseteq {1, 3}`


{{% q %}}
Write an operator that takes two sets S1 and S2 and determines if the double of every element in S1 is an element of S2.

{{% ans double %}}
`IsDoubleSubset(S1, S2) == {x * 2 : x \in S1} \subseteq S2`.
If you wanted to check both ways (doubles of S2 are in S1), you could write two expressions with `\\/`.
{{% /ans %}}
{{%/q %}}

operator | operation | example
-------|-----------|--------
`\union` | Set Union | `{1, 2} \union {2, 3} = {1, 2, 3}`
`\intersect` | Set Intersection | `{1, 2} \intersect {2, 3} = {2}`
`S1 \ S2` | The elements in S1 not in S2 | `{1, 2} \ {2, 3} = {1}`, `{2, 3} \ {1, 2} = {3}`
`SUBSET S` | The set of all subsets of S | `SUBSET {1, 2} = {{}, {1}, {2}, {1, 2}}`
`UNION S` | Flatten set of sets | `UNION {{1}, {1, 2}, {5}} = {1, 2, 5}`

{{% q %}}
Given a sequence of sets, write an operator that determines if a given element is found in any of the sequence's sets. IE `Op("a", <<{"b", "c"}, {"a", "c"}>>) = TRUE`.

{{% ans setrange %}}
`InSeqSets(elem, Seq) == elem \in UNION Range(Seq)`
{{% /ans %}}
{{%/q %}}
If you add `EXTENDS FiniteSets`, you also get the following operators:

operator | operation
-------|-------
IsFiniteSet(S) | TRUE iff S is finite
Cardinality(S) | Number of elements of S, if S is finite

{{% q %}}
Given a set, write an operator that returns all subsets of length two. IE `Op(1..3) = {{1, 2}, {1, 3}, {2, 3}}`.

{{% ans twos %}}
`Op(S) == { subset \in SUBSET S : Cardinality(subset) = 2 }`
{{% /ans %}}
{{%/q %}}
