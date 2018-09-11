+++
title = "TLA+"
weight = 200
+++

Now that we have our PlusCal scaffold, it's time to learn TLA+ proper. TLA+ is a mathematical description language. Instead of saying how to find the value you want, you instead say the properties of what you want. For example, the largest element of a set is `CHOOSE x \in S : \A y \in S : y <= x`. That's not an algorithm. It's just "the number that's bigger than the other numbers." 

This gives us incredible specification power. Complex properties and invariants can be expressed in just a few lines. On the downside, it can also be very intimidating. It's also possible to accidentally build uncheckable models. It's easy, for example, to define the set of all universal turing machines that halt. If you feed that into TLC, though, it will throw an error back. There's a bit of an art to writing TLA+ specs. Let's get started.

Point of note: we're going to be almost completely ignoring the "temporal" part of "Temporal Logic of Actions". As a simple heuristic, we're never, _ever_ going to be talking about "primed and unprimed operators", which make up like 95% of _Specifying Systems._ At it's core, TLA+ is a beautiful way to elegantly express the temporal properties of a complicated system. For our uses, TLA+ is a way of writing better PlusCal specs. Sacrilegious? Probably. Easier? Yup.
