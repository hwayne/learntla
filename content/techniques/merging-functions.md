+++
title = "Merging Functions"
weight = 1.5
+++

In addition to general debugging tools, extending TLC adds two function operators:

* `a :> b` is the function `[x \in {a} |-> b]`, or the function that maps a to b.
* `f1 @@ f2` merges both functions into a new one with the same domain and values. If some element is in both domains, it uses f1.

`@@` in particular is a great tool for simplifying PlusCal specs. As a toy example, imagine we have a sequence of digits and want to count the number of occurrences of each digit. Here's one way to write that:

```tla
EXTENDS TLC, Integers, Sequences, FiniteSets

Digits == 0..9
Count(seq) ==
  [x \in Digits |-> Cardinality({y \in DOMAIN seq: seq[y] = x})]

(* --algorithm counter

variables seq \in [1..5 -> Digits],
     counter = [x \in Digits |-> 0],
     pos = 1;

begin
  while pos <= Len(seq) do
    counter[seq[pos]] := counter[seq[pos]] + 1;
    pos := pos + 1;
  end while;
  assert counter = Count(seq);
end algorithm; *)
```

That works, but what if instead of a sequence of digits, it was a sequence of sets of digits? The solution gets a little messy (and the state space is much larger):

```tla
Digits == 0..2
Count(seq) ==
  [x \in Digits |-> Cardinality({y \in DOMAIN seq: x \in seq[y]})]

(* --algorithm counter

variables seq \in [1..5 -> SUBSET Digits],
     counter = [x \in Digits |-> 0],
     pos = 1;

begin
  while pos <= Len(seq) do
    counter := [ 
      x \in Digits |->
      IF x \in seq[pos] 
      THEN counter[x] + 1
      ELSE counter[x]
     ];
    pos := pos + 1;
  end while;
  assert counter = Count(seq);
end algorithm; *)
```

With `@@`, we can make the assignment much cleaner:

```tla
counter := [x \in seq[pos] |-> counter[x] + 1] @@ counter;
```