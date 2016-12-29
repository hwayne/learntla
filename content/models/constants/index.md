+++
title = "Constants"
weight = 5
draft = true
+++

Imagine we have the following dummy program:

```
M == 5
N == 4
(* --algorithm foo
process \in 1..M
*);
```

We want to test the invariant works for all numbers 1-N and up to M processes. This means there are [N] initial states and [N*M!] timelines. Doable for a pretty high number of processes- even 6 processes is just 720*N states to check.

Now what if each process has two steps? 6 processes jumps to over 7 million! For M processes with L steps, the number of behaviors is N*(ML)!/(L!^M), aka out of hand _extremely_ quickly. We know our models may take a while to run, but we still want them to finish before we die.

There's a number of optimizations we can do: reduce the number of labels, reducing branch points, etc. At some extent, though, it starts making sense to reduce the scope of the model: instead of checking everything on everything, test that the behaviors are correct for a restricted set of starting states and the the starting states are correct for a restricted set of behaviors. We verify our invariants hold in a variety of restricted subsets of the total behavior and informally link them, so as to make the model checking tolerable.

To start, instead of simply defining the bounds, we put them in as _constants_:

```

CONSTANTS M

(*
```

If we now try to run this, the model will fail, because M is not defined:

[screenshot]

When we click "edit", we have three options. The latter two, _model value_ and _set of model values_, we'll learn in the next section. Right now we're interested in "ordinary assignment". In there, we can assign an arbitrary value to N: `1`, `<<"a", "b", "c">>`, `[1..10 -> {x \in {1, 2, 3} : x > 2]`, etc.

[more]
