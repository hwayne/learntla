+++
title = "Operators"
weight = 1
+++

An operator is a thing that does a thing. It's what programmers might refer to as a "pure function". You use a `==` to define them.

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

{{% notice tip %}}
Remember, you can use the "No Behavior Spec" option in your TLC model to test various operators and cases.
{{% /notice %}}

{{% q %}}
Write an operator that tests if two numbers are not equal.

{{% ans neq %}}
`Neq(a,b) == a /= b` works, as does `Neq(a,b) == ~(a = b)`.
{{% /ans %}}
{{%/q %}}

Operators and expressions do not "mutate" variable, just return values. If you want to update the value of something in PlusCal, you must make an assignment with `:=`.

### Higher-Order Operators

You can write operators that take other operators if you use a special syntax:

``` tla
Sum(a, b) == a + b
Do(op(_,_), a, b) == op(a, b)

Do(Sum, 1, 2) = 3
```

You can also make operators recursive if you specify them with the `RECURSIVE` keyword before invocation:

``` tla
RECURSIVE SetReduce(_, _, _)

SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == CHOOSE s \in S: TRUE
                                   IN SetReduce(Op, S \ {s}, Op(s, value)) 

CandlesOnChannukah == SetReduce(Sum, 2..9, 0) \* 44
```

{{% q %}}
Write an operator that determines whether a second operator is commutative over two given numbers. An operator is commutative if `f(a,b) = f(b,a)`.

{{% ans commutative %}}
`IsCommutative(f(_, _), a, b) == f(a, b) = f(b, a)`
{{% /ans %}}
{{%/q %}}

## Integrating with PlusCal

If your operator doesn't reference any PlusCal variables (such as `IsEmpty(S) == S = {}`), you can put it above the start of the PlusCal algorithm and it will be usable like any other expression.

If your operator _does_ reference any PlusCal variables (such as `HasMoneyLeft == money > 0`), it has to appear in or after the algorithm. The first way to do this is to put it after the TLA+ translation. This is simple, but it also means the PlusCal can't call the operator. Fine for invariants, less-fine for conditionals. To place the operator directly in your code, you can use a  `define` block:

```
define
  Foo(bar) == baz
  \* ...
end define
```

Your `define` block must come before the `begin`.
