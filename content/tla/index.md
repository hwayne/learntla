+++
title = "TLA+"
weight = 0
+++

Now that we have our PlusCal scaffold, it's time to dive into TLA+. TLA+ is a mathematical description language. Instead of saying how to find the value you want, you instead say the properties of what you want. For example, the largest element of a set is `CHOOSE x \in S : \A y \in S : y <= x }`. That's not an algorithm. It's just "the number that's bigger than the other numbers." 

This gives us incredible specification power. Incredibly complex algorithms and invariants can be expressed in just a few lines. For example, given a set of vendors V and items I and prices P, how do you specificy all possible prices such that you can't arbitrage any item?

``` tla
ValidMarkets == LET Markets == [V \X I -> [buy : P, sell : P]]
                IN {m \in Markets : 
                    \A item \in I, vendors \in V \X V:
                      m[<<vendors[1], item>>].buy <= m[<<vendors[2], item>>].sell
                   }
```

{{% notice note %}}
A consequence of its descriptiveness is it's possible to build uncheckable models. It's easy, for example, to define the set of all universal turing machines that halt. If you feed that into TLC, though, it will throw an error back. Generally, avoid using infinite sets and you'll probably be fine.
{{% /notice %}}

Let's dive in.

Point of note: we're going to be almost completely ignoring the "temporal" part of "Temporal Logic of Actions". As a simple heuristic, we're never, _ever_ going to be talking about "primed and unprimed operators", which make up like 95% of Specifying Systems. At it's core, TLA+ is a beautiful way to elegantly express the temporal properties of a complicated system. For our uses, TLA+ is a way of writing better PlusCal specs. Sacriligious? Probably. Easier? Yup.
