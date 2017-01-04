+++
title = "Temp"
weight = 30
+++

Introducing logical operators _should_ be a ten-line section, but because there's some wonky indentation rules I'd like emphasize them in detail. **Conjunction and disjunction are the only places in TLA+ where indentation matters.**

### /\ and \/

We've already been using `/\` and `\/`. The former is "and", the latter is "or". `TRUE /\ FALSE = FALSE`, etc.

So, why bring them up again? There's special rules if you want to write a multiline conjugation. What's the value of the following?

```
TRUE
\/ TRUE
/\ FALSE
```

Trick question, that's an error. TLA+ reads that as `TRUE /\ TRUE \/ FALSE`, which has a precedence issue, so it crashes unless you add parenthesis. You actually have to write it like this:

```
\/ TRUE
\/ TRUE
/\ FALSE
```

To get `(T \/ T) /\ F`, which is false, or

```
/\ TRUE
\/ TRUE
/\ FALSE
```

Which is _also_ an error, because you can't alternate operators like that. But we can write

```
/\ TRUE
 \/ TRUE
/\ FALSE
```

To get `(T \/ T) /\ F`, or 

```
/\ TRUE
 \/ TRUE
 \/ FALSE
```

To get `(T /\ (T \/ F))`, or

```
\/ TRUE
\/ TRUE
 /\ FALSE
```

To get `T \/ (T /\ F)`, etc.

Confused at all? No worries if so, since it's pretty confusing. Here's a quick rule of thumb:

* If two logical operators are on the same level of indentation, they are part of the same level of expression.
* If a logical operator is on a higher level of indentation, it's part of the previous previous operator statement.
* For comprehensibility's sake, use only one type of operator per level of indentation.

Why is this important to know, versus leaving it all on the same line? Because often you will want to combine simple logic with more complicated expressions. For example, the archetypical definition of the greatest common denominator is

```
GCD (x,y) ==  CHOOSE gcd \in 1..x:
                /\ x % gcd = 0
                /\ y % gcd = 0
                /\ \A j \in (gcd+1)..x:
                  \/ x % j # 0
                  \/ y % j # 0
```

The gcd divides both x and y, and every number bigger doesn't divide x or doesn't divide y (or both). It's important to have a sense of how the indentation works. FOrtunately, if you make a mistake you're much more likely to get a crash than a bad spec.

## =>

I have no idea where to put this so I'm just throwing it here for the rough draft(s). `=>` is the final logical operator we haven't introduced yet. "P => Q" means "If P is true, then Q must also be true". While it's sometimes useful for expressing properties, it's not necessary: "P => Q" is equivalent to "~P \/ Q", or "Either Q is true or P is false (or both)". If that doesn't seem intuitive to you, take a few minutes to play with it.

[[Stuff on de morgan's laws, etc]]
