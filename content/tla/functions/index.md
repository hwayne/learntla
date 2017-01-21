+++
title = "Functions"
weight = 40
+++

Beyond the basic four types in TLA+ (number, string, boolean, model value), there are two 'complex' types. The first we've already used - that's the set. The other is the function. Functions form the basis of all the 'practical' complex types, so we're going to spend some time on them. Fortunately, the theory is pretty simple.

The word 'function' can cause a lot of misunderstanding. They are not similar to functions in other languages- that's operators. Instead, functions are closer in nature to hashes or dictionaries, except that you can choose to programmatically determine the value from the key. There are two ways to define a function:

* `Function == [s \in S |-> foo]`
* `Function[s \in S] == foo`

Here, `foo` can be any equation, and can be dependent on `s`. Other than that, you have near-complete freedom. For example, you can use an infinite set:

`Doubles == [n \in Nat |-> 2 * n]`

Or multiple variables:

`Sum == [x, y \in S |-> x + y]`

You call a function with f[x], just like tuples and structs do. That's because tuples and structs _are_ functions! Specifically, tuples are just functions where the domain is 1..n. One consequence of this is that TLA+ is essentially structurally subtyped. If you write `Squares == [n \in 1..100 |-> n * n]`, then `Squares` is also by definition a tuple, and you can use sequence operators on it.

Similarly, you can write `DOMAIN F` to get the set of values F is defined on.

{{% notice info %}}
So, what exactly is the difference between functions and operators? There's a few important difference, but here's the practical ones. You can't have a set of operators. Functions can't express certain actions that operators can. Finally, you can't use functions as invariants. A good rule of thumb is that if you want to manipulate it as part of your algorithm, prefer functions. Otherwise, prefer operators.
{{% /notice %}}

[[ TODO exercise: Range of function ]]
## Function Sets

Imagine you are trying to model some sort of flag, like a concurrency lock, on multiple processes. Or you're writing a trading algorithm and match people to what they're interested in. Or any case where you know that a set of things has an initial value but you're not sure what initial value. Or you need to test arbitrary sequences. It'd be helpful to say "generate all functions with these properties" so we can harden our algorithm against them. The syntax for that is

`SetOfFunctions == [A -> B]`

That generates every function which maps an element of A to an element of B. A and B must be sets, or more specifically expressions that evaluate to sets.

**`|->` and `->` are different.** This is going to mess you up at least once. Use `|->` when you want one function that maps the domain to a specific range. Use `->` when you want the set of functions that maps the domain to the range. 

```
S == {1, 2}
[s \in S |-> S] = [1 |-> {1, 2}, 2 |-> {1, 2}]
[S -> S] = {[1 |-> 1, 2 |-> 1], [1 |-> 1, 2 |-> 2], [1 |-> 2, 2 |-> 1], [1 |-> 2, 2 |-> 2]} 
```

Since each side is a set, you can use normal set expressions on them.
