+++
title = "Labels"
weight = 2
+++

### Valid Labels

Since labels represent steps, single moments of time, there are some rules on how you have to place them.

- The first line in a process has to have a label. That includes the first `begin` if it's a single-process algorithm.

```
begin
Foo:
  skip;
```

- A label must come before a `while` statement.

```
Foo:
  while FALSE do
    skip;
  end while;
```

- A label must come right after a `call`, `return`, or `goto`. 

```
A:
  skip;
B:
  goto A;
Foo: \* this one is necessary even if it's never reached
  skip;
```

- If you have a control statement, such as `if` or `either`, and one possible branch has a label in it, then the whole control structure must be followed with a label.

```
either 
  A: 
    skip;
or 
  skip;
end either;
Foo: \* Necessary because of the A label
```

- You can not put labels in a `with` statement.

```
with x \in {1, 2} do
  Foo: \* INVALID
    skip
end with;
```

- You cannot assign to any given variable more than once in a label.

```
Foo:
  x := 1;
  q := 2; \* VALID

Bar:
  x := 1;
  x := 2; \* INVALID
```

Sometimes this can cause issues: for example, switching two variables, or assigning to different records of the same structure. In these cases you can use `||` to chain assignments: `x := y || y := x;`

### Optimization

Every label specifies a branch point in your system: any process with an available label can run as the next step. For N processes with M sequential labels the total number of behaviors is `(MN)!/M!^N`, not counting initial states or nondeterministic labels (`either` or `with`). The more labels you have, the more exact your concurrency testing. The fewer labels you have, the faster your model will run. As always, there are tradeoffs.