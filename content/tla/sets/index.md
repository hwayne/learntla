+++
title = "Sets"
weight = 3
+++

You've seen sets before. `{1, 2}` is a set. `1..N` is the set of all numbers between 1 and N. `x \in S` checks whether S contains x, unless you use it in a PlusCal `variables` statement or a `with` (where it creates new behaviors). Like everything else, you can nest them: `{{{}}}` is a set containing a set containing an empty set.

Often, we're interested in some transformation of the set, such as "the set of male participants under 60" or "The owners of the pets." In this section we'll cover three ways to transform a set and how they are combined.

### Filtering

We can filter a set with `{x \in S: P(x)}`, which is the set of all x \in S where P(x) is true. For example, `{x \in 1..8 : x % 2 = 1}` is the set `{1, 3, 5, 7}`. `x \in S : FALSE}` is always the empty set.

### Mapping

### CHOOSE

`CHOOSE` pulls . We write `CHOOSE x \in S : P(x)` to say "Throw me whatever x is in S for which P(x) is true". For example, we could write `AnEvenNumber(s) : CHOOSE x \in S : IsEven(x)` to mean "I want an even number." 

If there are multiple elements that satisfy the CHOOSE, TLC will create a separate behavior for each element. If there are no elements that satisfy the CHOOSE, TLC will raise an error. That's because there's a problem in your spec. If the set is infinite, TLC will raise an error. That's because TLC can't choose from an infinite sets. There still may be a problem with your spec.

{{% notice tip %}}
A common pattern is `CHOOSE x \in S : TRUE` to grab an arbitrary element, like using `\in` in a PlusCal variable declaration.
{{% /notice %}}

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

[[Something about run the following in the expression evaluator.]]
