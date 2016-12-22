+++
title = "[Basic TLA+]"
weight = 0
+++

Up until now we've been working almost exclusively in PlusCal. That's been enough to write interesting specs. Now it's time to dive into TLA+, which will dramatically increase the breadth and specificity of the systems we can model.

The key difference between TLA+ and programming languages is that TLA+ is a mathematically descriptive, not prescriptive. Lamport designed TLA+ to easily describe any system, even impossible or nonsensical ones. For example,

```
Primes == {n \in N: /\ n > 1 /\ ~\E i \in 2..n : n % i = 0}
GoldbachCounters == {n \in N: /\ n > 2 /\ n % 2 = 0 /\ \A p1, p2 \in Primes : p1 + p2 # n}
```

`GoldbachCounters` is the set of all counterexamples to the [Goldbach Conjecture](https://en.wikipedia.org/wiki/Goldbach's_conjecture). Do any exist? Who knows? But you can easily define that set in TLA+. And we can just as easily write a function that only exists if the `GoldbachCounters` is nonempty.

As a consequence of this, we can't actually _run_ TLA+. Nor can we model check _all_ of it: doing so would break the Halting Problem! But we can check a fairly large subsystem of it, more than enough to [do cool stuff.]

Unfortunately for our purposes
 
Point of note: we're going to be almost completely ignoring the "temporal" part of "Temporal Logic of Actions". As a simple heuristic, we're never, _ever_ going to be talking about "primed and unprimed operators", which make up like 95% of Specifying Systems. At it's core, TLA+ is a beautiful way to elegantly express the temporal properties of a complicated system. For our uses, TLA+ is a way of writing better PlusCal specs. Sacriligious? Probably. Easier? Yup.

## Stuff

A TLA+ operator is like a function.

That's a _massive_ oversimplification, but it's an ok intuition for our scope. Throw in some arguments, get some output. Some examples:

```
IsFooEmpty == foo = {}
IsBarInFoo(bar) == bar \in foo
IsBarInBaz(bar, baz) == bar \in baz
```

Etc etc etc.

Considered a core expession, use in invariants
Has to come after the translation
Recursion?
Let In
