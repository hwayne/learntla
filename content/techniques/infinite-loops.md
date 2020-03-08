+++
title = "Infinite Loops"
weight = 11
+++

Infinite loops are useful to model, as they are a great way of representing things like cronjobs or worker pools. You can add infinite loops in the same way as any other language, by using `while` or `goto`.

```tla
process whileprocess = "while"
begin While:
  while TRUE do
    skip
  end while
end process

process gotoprocess = "goto"
begin Goto:
  skip;
  goto Goto;
end process;
```

There are two specific problems with using infinite loops in TLA+. The first is that if the infinite loop produces a state change, TLC might try to check an infinite state space. The second is that it makes checking termination harder: your program is done when everything _but_ the infinite loop has terminated.

### State Space Restriction

If we try to check the following spec, TLC will run out of memory:

```
variable x = 0;
begin Adder:
  while TRUE do
    x := x + 1;
  end while
end algorithm;
```

There's an infinite number of possible states here: `x = 1`, `x = 2`, etc. The naive way of fixing this would be to add a time counter:

```
variable x = 0, time = 0;
begin Adder:
  while time < 10 do
    x := x + 1;
    time := time + 1;
  end while
end algorithm;
```

However, this can quickly get untenable. Another options is to use the regular loops and switch to a depth-first search. This lets you force the model to terminate in a finite number of steps.
![](../img/depth-first.png)

The last option is to use a state constraint. A state constraint is a formula restricting the possible states: When a state does not comply with the constraint, model will finish running.
![](../img/state-constraint.png)

One pitfall with depth-first search and state constraint is that your model might have an error, but you don't reach it in the specified time.
