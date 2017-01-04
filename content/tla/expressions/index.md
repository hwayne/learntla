+++
title = "Expressions"
weight = 2
+++

We've been implicitly using _expressions_ up until now; we just haven't clarified them. Doing so it useful, because will help us interview our TLA+ and PlusCal. For our purposes, an expression is __anything that follows a `==`, `=`, `:=`, or `\in`__. All expressions are valid TLA+ and can leverage anything in TLA+. For example, let's say we had the following PlusCal code:

[FIXME]
```
Foo == 1..10
(* --algorithm foo
variables a \in Foo, b = a = 0;
begin
  b := CHOOSE x \in Foo : x # a;
end algorithm; *)
```

Some things to note here:

* In the initial variable setup, we were able to define be a boolean on "is a zero". The first `=` was assignment that started the expression, the second one was an equality check. While you don't need to, it's recommended to wrap the expression here in (), so as to make it clear that the `=` is semantically overloaded.
* In the algorithm itself, we were able to assign b based on a `CHOOSE` operation. We could just as easily do `b := CHOOSE x \in SUBSET Foo: TRUE` to grab an arbitrary subset.

{{% notice tip %}}
One nice reason to inline `CHOOSE` is to replace a `with`, which can't make procedure calls or use while loops.
{{% /notice %}}

* A third thing after I make the algorithm better, this is not the editing phase

Beyond that, there are ways of increasing the complexity of an expression. Let's examine them.

### LET-IN

Any expression can use LET-IN to add local operators and definitions to just that expression alone.

```
LET IsEven(x) == x % 2 = 0
IN  IsEven(5)

LET IsEven(x) == x % 2 = 0
    Five == 5
IN  IsEven(Five)

LET IsEven(x) == LET Zero == 2
                 IN  x % Zero = Zero
    Five == 5
IN  IsEven(Five)
```

The whitespace is nonsignificant: we can write `LET IsEven(x) == x % 2 = 0 Five == 5 IN IsEven(Five)` and it will correctly parse it as two separate operators in the LET.

{{% notice info %}}
Please use newlines. _Please_.
{{% /notice %}}

### IF-THEN-ELSE

C'mon, you know this one.

```
IsEven(x) == IF x % 2 = 0 
             THEN TRUE
             ELSE FALSE
```

As before, alignment doesn't matter, but you should align them anyway unless you really hate your coworkers.

### CASE 

Case is _mostly_ how you'd expect it to act, with one subtle difference.

```
CASE x = 1 -> TRUE
[] x = 2 -> TRUE
[] x = 3 -> 7
OTHER -> FALSE
```

OTHER is the default. If none of the cases match and you leave out an OTHER, TLC considers that an error. If _more than one match_, though, you [HIT A BUG IN TLC]

{{% notice warning %}}
**THIS IS BROKEN PAGE 298**
{{% /notice %}}

## Nesting

Of course you can.

[Example]
