+++
title = "Processes"
weight = 1
+++

When writing a concurrent system, the PlusCal code is a little different.
```
---- MODULE module_name ----
\* TLA+ code

(* --algorithm algorithm_name
variables GLOBAL VARIABLES
process process_name = foo
variables local_variables
begin
\* pluscal code 
end process
process process_group \in bar
variables local_variables
begin
\* pluscal code 
end process
end algorithm; *)
====
```

Instead of having a single `begin` block, we have a separate one per process. The process must be set equal to something. If set equal to a single variable, you will run one process. If instead you use `\in`, the model will create one process for each element in the set. Regardless of what the process 'equals', you can refer to it in the code with `self`. e.g

```
process foo = "bar"
begin
  print self; \* prints "bar"
end process
```

When there are multiple processes, TLC can choose not only choose the initial conditions for each process, it can also choose _which_ process executes in the next step. For example:

```
variables x = 0;
process one = 1
begin
  A:
    x := x - 1;
  B:
    x := x * 3;
end process

process two = 2
begin
  C:
    x := x + 1;
  D:
    assert x # 0;
end process
```

This will fail, as the sequence `C -> A -> B -> D` sets x as `0 + 1 -> 1 - 1 -> 0 * 3 -> 0 # 0`.

What if we __don’t__ want a process to always run? We only want workers to run if there are jobs in the queue. We only want to hit an API if we need more data. We can stop a process from running with await:

```
process one = 1
begin
  A:
    x := x - 1;
  B:
    x := x * 3;
end process

process two = 2
begin
  C:
    await x < -1;
    x := x + 1;
  D:
    assert x # 0;
end process
```

In this case, the entire C step is blocked until the `await` is true. So the only path that can happen is `A -> B -> C -> D`, which is valid.

A troubling problem here: if we can say “don’t run this step unless X is true”, can we have a situation where we can’t run any steps? For example, if we instead did `await x > 1`, we'd be able to do `A -> B` and then get stuck. This is called a deadlock. This is almost certainly a serious bug and TLC will flag this as an error in your algorithm. Try not to have deadlocks.

EXAMPLE

