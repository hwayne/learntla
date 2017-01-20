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

### ENABLED

Labels are converted into "Actions" by the PlusCal translator. I think actions are a bit out of scope for this guide, but there's one consequence of this we can find useful: we can 'apply' operators to Labels. The main one we're interested in is `ENABLED`. For a label `A`, `ENABLED A` means "this specific action can happen in the next step. For example, if we wanted to ensure that we don't download a file if a specific flag is set, we can write the invariant as `no_download_flag => ~ENABLED A`.
