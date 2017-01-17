+++
title = "TLA+"
weight = 0
+++

Now that we have our PlusCal scaffold, it's time to dive into TLA+. TLA+ is a mathematical description language. Instead of saying how to find the value you want, you instead say the properties of what you want. For example, the largest element of a set is `CHOOSE x \in S : \A y \in S : y <= x`. That's not an algorithm. It's just "the number that's bigger than the other numbers." 

This gives us incredible specification power. Complex properties and invariants can be expressed in just a few lines. For example, is a given set of vectors linearly independent?

``` tla
IsIndependent(Vectors) == 
  \A coeff \in [Vectors -> Int] :
    LET result == VectorSum({Scale(v, coeff[v]) : v \in Vectors})
    IN Magnitude(result) = 0 => Magnitude(coefficients) = 0
```

It does depend on you having a couple helper operators (and _technically_ won't run in TLC due to the infinite size of `Int`), but they're fairly easy to write. And that is a direct definition of linear independence. Doing that in an actual programming language would require to you implement a proper algorithm.

{{% notice note %}}
A consequence of its descriptiveness is it's possible to build uncheckable models. It's easy, for example, to define the set of all universal turing machines that halt. If you feed that into TLC, though, it will throw an error back. In this case we have a problem because there are an infinite number of integers and TLC can't handle that. But we could make it work over, say, `-100..100`.
{{% /notice %}}

Getting a head for using TLA+ can be a little intimidating, so let's dive in.

Point of note: we're going to be almost completely ignoring the "temporal" part of "Temporal Logic of Actions". As a simple heuristic, we're never, _ever_ going to be talking about "primed and unprimed operators", which make up like 95% of Specifying Systems. At it's core, TLA+ is a beautiful way to elegantly express the temporal properties of a complicated system. For our uses, TLA+ is a way of writing better PlusCal specs. Sacriligious? Probably. Easier? Yup.
