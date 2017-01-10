+++
title = "Expressions"
weight = 2
+++

We've been implicitly using _expressions_ up until now; we just haven't clarified them. For our purposes, an expression is __anything that follows a `==`, `=`, `:=`, or `\in`__. As we'll see [[TODO]]. in this section we'll cover some general expression modifiers.

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

The whitespace does not matter: we can write `LET IsEven(x) == x % 2 = 0 Five == 5 IN IsEven(Five)` and it will correctly parse it as two separate operators in the LET. 

{{% notice info %}}
Please use newlines. _Please_.
{{% /notice %}}

### IF-THEN-ELSE

This is exactly what you expect it to be.

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

OTHER is the default. If none of the cases match and you leave out an OTHER, TLC considers that an error. If _more than one match_, though, TLC will pick one for you and _not_ branch. Sometimes that's what you want, sometimes it isn't. Depends on your use case, really.

## Nesting

Of course you can.

[Example]
