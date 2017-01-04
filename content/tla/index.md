+++
title = "TLA+"
weight = 0
+++

Up until now we've been able to model fairly simple systems and discover some subtle bugs in them. We're still fairly limited, however, in what we're able to do. In practical problems we tend to be interested in are far more complicated and require some concepts we can't yet implement. For example, how do you test the invariant "at most one element in the sequence can be a duplicate" or "the largest and smallest element must be within a certain distance of each other"? We don't even have a way yet of specifying "the largest element".

For this, we need TLA+.

TLA+ is a mathematical description language. Instead of saying how to find the value you want, you instead say the properties of what you want. For example, the largest element of a set is `CHOOSE x \in S : \A y \in S : y <= x }`. That's not an algorithm. It's just "the number that's bigger than the other numbers."

[A consequence of its descriptiveness is it's possible to build uncheckable models. It's easy, for example, to define the set of all universal turing machines that halt. If you feed that into TLC, though, it will throw an error back. Generally, avoid using infinite sets and you'll probably be fine.]

TLA+ gives us incredible specification power. Not only can we specify complex invariants with it, we can also weave it into our PlusCal code. We can specify per-process flags with `Flags == [pc -> Bool]`. We can []. We can []. PlusCal makes using TLA+ much easier, but TLA+ is what makes PlusCal worthwhile in the first place. The more we understand it, the stronger our PlusCal specifications can be. Let's get started.

Point of note: we're going to be almost completely ignoring the "temporal" part of "Temporal Logic of Actions". As a simple heuristic, we're never, _ever_ going to be talking about "primed and unprimed operators", which make up like 95% of Specifying Systems. At it's core, TLA+ is a beautiful way to elegantly express the temporal properties of a complicated system. For our uses, TLA+ is a way of writing better PlusCal specs. Sacriligious? Probably. Easier? Yup.
