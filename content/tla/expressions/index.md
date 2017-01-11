+++
title = "Expressions"
weight = 2
+++

We've been implicitly using _expressions_ up until now; we just haven't clarified them. For our purposes, an expression is __anything that follows a `==`, `=`, `:=`, or `\in`__. In this section we'll cover some general expression modifiers.

### `/\` and `\/`

We've used these for a while now: /\ is and, \/ is or. We can join expressions with them. The one sublety is that this is the _only_ case where TLA+ is whitespace sensitive. If you start a line with an indented [[]], TLA+ considers that the start of a subclause. For example,

```
/\ TRUE
 \/ TRUE
/\ FALSE \* (T \/ T) /\ F

/\ TRUE
 \/ TRUE
 \/ FALSE \* (T /\ (T \/ F))

\/ TRUE
\/ TRUE
 /\ FALSE \* T \/ (T /\ F)
```

Etc. As a general rule of thumb:

* If two logical operators are on the same level of indentation, they are part of the same level of expression.
* If a logical operator is on a higher level of indentation, it's part of the previous operator statement.
* Use only one type of operator per level of indentation.

Generally if you mess this up the spec will crash, so you're unlikely to get a logic bug through this.

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
