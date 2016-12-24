+++
title = "[Operators]"
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
MakeSeq(a, b) == <<a, b, Five>>
```

You can use them anywhere you use any other expression.

```
{x \in 1..10 : IsFive(x)} = {5}
```

Operators can't recursively call themselves unless you [foo]:

So, how do we use them! A few different ways!

### Generic Helper Operators

You can put them _before_ the PlusCal algorithm to use them as helpers, for example if you need to define a set filter a lot:

[example]

Operators defined this way can't reference the variables in the pluscal algorithm itself. If you want them to be able to, you have to put them in a _define_ block:

[example]

### Invariants

You know how in our models we've been testing, say, `pos \in board`? Instead we could define `InBoard == pos \in board` and put that after the translation, which makes writing models easier and more elegant.

[example]

## Example
