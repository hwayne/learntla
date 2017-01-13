+++
title = "Operators"
weight = 1
+++

An operator is a thing that does a thing. It's what programmers might refer to as a function. You use a `==` for them.

```
Five == 5
Five + 5 \* 10
```

You can also give them arguments.

```
IsFive(x) == x = 5
```

Or multiple arguments.

```
SumWithFive(a, b) == a + b + 5
```

You can use them anywhere you use any other expression.

```
{ Five, SumWithFive(Five, Five) } \* { 5, 15 }
```

Operators can't recursively call themselves unless you [foo]:

[BAR]

Simple.

## Integrating with PlusCal

There are generally three ways to use operators with pluscal:

### Generic Helpers

Anything that doesn't specifically reference your variables, like `IsEmpty(Set) == Set = {}`. The best place to put this are _before_ the `--algorithm` line, and your PlusCal code can use it like any other expression.

### Invariants

Something you want to check in a model, like `HasMoneyLeft == money > 0`. TLA+ parses top down; if you want to reference a variable in your operator, it has to come after the TLA+ definition. So your invariant has to go _after_ the `\* END TRANSLATION` block.


### PlusCal Helpers

A helper operator that uses PlusCal variables, like `CanGamble == money > 25`. You can't put it above the `--algorithm`, because it needs to know about the PlusCal variables, and you can't put it below the `end algorithm`, because PlusCal needs to know about the operator. To work around this edge case, PlusCal adds an additional structure called `define`:

```
define
  Foo(bar) == baz
  \* ...
end define
```

Your `define` block must come before the `begin`.

Here's an example with all three use cases.

[[ TODO ]]
