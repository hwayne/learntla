+++
title = "Functions"
weight = 40
+++

Beyond the basic four types in TLA+ (number, string, boolean, model value), there are two 'complex' types. The first we've already used - that's the set. The other is the function. Functions form the basis of all the 'practical' complex types, so we're going to spend some time on them. Fortunately, the theory is pretty simple.

The word 'function' can cause a lot of misunderstanding. They are not similar to functions in other languages- that's operators. Instead, functions are closer in nature to hashes or dictionaries, except that you can choose to programmatically determine the value from the key. There are two ways to define a function:

`Function == [s \in S |-> foo]`

Here, foo can be any equation, and can be dependent on s. Other than that, you have complete-near freedom. For example, you can use an infinite set:

`Doubles == [n \in Nat |-> 2 * n]`

Or multiple variables:

`Sum == [x, y \in S |-> x + y]`

You call a function with f[x]. [], not (). () are for operators.

{{% notice info %}}
So, what exactly is the difference between functions and operators? There's a few important difference, but here's the practical ones. You can't have a set of operators. Functions can't express certain actions that operators can. Finally, you can't use functions as invariants. A good rule of thumb is that if you want to manipulate it as part of your algorithm, prefer functions. Otherwise, prefer operators.
{{% /notice %}}

### Sequences and Structs

You might have noticed that functions use `[]` just like tuples and structs do. That's because tuples and structs _are_ functions! Specifically, tuples are just functions where the domain is 1..N. One consequence of this is that TLA+ is essentially structurally subtyped. If you write `Squares == [n \in 1..100 |-> n * n]`, then `Squares` is also by definition a tuple, and you can use sequence operators on it.

## Function Sets

Yes, you can have a set of functions. Yes, it's a super useful tool. Yes, it's bonkers.

Imagine you are trying to model some sort of flag, like a lock or whatever, on multiple processes. Or you're writing a trading algorithm and match people to what they're interested in. [[That'd be a good example.]] Or any case where you know that a set of things has an initial value but you're not sure what initial value. Or you need to test arbitrary sequences. It'd be helpful to say “generate all functions with these properties” so we can harden our algorithm against them. The syntax for that is

`SetOfFunctions == [A -> B]`

That generates every function which maps an element of A to an element of B. You can use normal set operations on either set if you want.

{{% notice warning %}}
WARNING: |-> and -> are different! This is going to mess you up at least once. Use |-> when you want one function that maps the domain to a specific range. Use -> when you want the set of functions that maps the domain to the range. 
{{% /notice %}}

[TIP: If you want every element of A to map to a subset of B (trading), you can do [A -> SUBSET B]. Examples.]


## Example

Write a program that returns the minimum amount of change in pennies, nickels, dimes, and quarters.

This is a fairly standard interview question. The trick is that the simple way to solve it, a greedy algorithm, fails for the general case. Let's implement it in PlusCal and see how the general case breaks down.

```
Coins == {"p", "n", "d", "q"}
CoinValue == [p |-> 1, n |-> 5, d |-> 10, q |-> 25]
CV == CoinValue
IsExactChange(cents, coins) == CV["p"]*coins["p"] + CV["n"]*coins["n"] + CV["d"]*coins["d"] + CV["q"]*coins["q"] = cents 
ExactChangeSet(cents) == {c \in [Coins -> 0..20] : IsExactChange(cents, c)}
SmallestExactChange(cents) == CHOOSE s \in ExactChangeSet(cents) : \A y \in ExactChangeSet(cents) : Sum(y) >= Sum(s)
```

Let's walk through each piece. `Sum(f)` is a snippet from [here]. `CoinValue` is the relative worth of each coin (American coins), CV is a shorthand for that, and `IsExactChange` checks if a bag of coins is worth the change. So far, everything is fairly straightforward.

Things get more interesting with `ExactChangeSet`. As always, the easiest way to read it is inside-out. The first part is the inner piece, `[Coins -> ...]`. It's our first set of functions! __Remember that -> means set of functions.__ So that expands to `[0 0 0 0], [0 0 0 1], ... [20 20 20 19], [20 20 20 20]`. There's no particular reason why I capped it at 20. After that, we filter on `IsExactChange`, leaving us with only the set of collections of coins that add up to exactly our number.

Finally, we have `SmallestExactChange`. Compared to the others, it's a doozy. The `CHOOSE s` tells us it will be _some_ exact change set. Specifically, the one with the fewest number of coins (`Sum(s)`). The fewest number of coins is defined by that every other number is _more_ than it, which gives us the filter: choose the bag such that every single bag of change has as many or more coins. We could also do `ExactChangeSet(cents) / {s}` to replace the `Sum(y) >= Sum(s)` with `Sum(y) > Sum(s)`, but e, more characters.

The greedy algorithm is “subtract quarters until you can't anymore, then subtract dimes, then nickels, then pennies”.

{{% code change %}}

And we can see this works for any number between 1 and 100 cents.

This is where the interviewer generally throws in the twist: what if you had different denominations of coins? The algorithm breaks down if you have, for example, pennies, nickels, and 7-cent coins; it would give you four coins for ten where two nickels would work.

[Updated algorithm]

This is usually where the interviewer is satisfied and the problem ends. The base case works, the edge case works, and our algorithm is solid. But we're modeling, not programming, so we have a higher standard of rigour. Let's first confirm our algorithm works for _every_ choice of change:
asdasda


For certain values of coins, the “minimum change” is ill-defined! 21 cents is 10+10+1 or 7+7+7. Both are three coins. Which is the minimum? We'd have to define a tie-breaker. 

What if we try a range of coin values?

...

The minimum change might not exist. [6 cents is impossible with 5,7]

Exercises: Stingy change machine (returns the least amount it 'can'), change machine with finite money 

