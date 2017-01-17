+++
title = "About TLA+"
weight = 1
+++

TLA+ is a specification language. Whereas programming languages are designed to build systems, specification languages are about making blueprints. You first design your system in TLA+, make sure it works, and then build it in another language.

So if you have to rewrite everything anyway, why bother? Because TLA+ is focused on specification, it can model much more complex behavior than mocks and unit tests can. For example, imagine if as part of your system your variable can be in one of three states, you are using it to call one of two third party APIs, and each call can succeed, fail, or 404. That’s already six mocks in your unit tests, and if you wanted comprehensive integration tests you’re looking at 18 tests! Or you could model it in TLA+:

```
with var \in {"a", "b", "c"}, api \in {api1, api2} do
 either 
  api.call(var); 
 or 
  api.fail(var)
 or 
  api.four_oh_four;
 end either;
end with;
```

Those 9 lines are enough for TLA+ to test all 18 paths and make sure all of them work as intended.

TLA+ is especially good for handling concurrency. In that same system, imagine if those calls changed state, and you had three workers making them. How can you check that there’s no race conditions- that with just the right workers making just the right calls in just the right order, everything won’t crash? This is a nightmare to test in the system itself, because creating the initial conditions is extremely difficult. With TLA+, though, it’s trivial.

```
process call_maker \in {1, 2, 3}
begin
  \* code
end process;
```

If the algorithm has one "race condition" point, there are now over 500,000 possible behaviors, and TLA+ will check every single one. Might take a while, but it will check them.

Finally, TLA+ prevents you from handwaving things away. If it can reach a place where it doesn’t understand the blueprint, it will consider that an error. This means you create a comprehensive design that provides a deeper understanding into the system you're building.

That said, TLA+ is not a panacea. First of all, it’s slow. Simple models can take seconds or minutes and complex ones can take hours or days. Second, it can’t check everything it can specify: for example, it cannot handle real numbers or infinite sets. Third, it can only check what you ask it to check; it gives you confidence but not certainty. Most importantly, though, it can’t tell you anything about your implementation. You still need to test your code.

So, to summarize: TLA+ __does not__ replace unit tests, integration tests, or code reviews, but it __does__ help you find complex bugs in your design as well as more clearly understand what you're designing. I think those are definitely worth the investment.
