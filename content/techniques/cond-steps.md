+++
title = "Conditional Steps"
+++

Sometimes you may want to combine `either` with labels, so that branching steps are possible. For example:

```
either
  Push:
    \* code
or
  Pop:
    \* code
end either
After:
    \* code
```

However, you may also want some steps to only be possible in certain cases. For example, we might want that we can only pop a non-empty stack. Here are two ways of doing that:

```
either
  Push:
    \* code
or
  if stack_not_empty() then
    Pop:
      \* code
  end if
end either
After:
    \* code
```

```
either
  Push:
    \* code
or
  await stack_not_empty()
  Pop:
    \* code
end either
After:
    \* code
```

While the both will prevent you from running `Pop` if `stack_not_empty` is false, they mean different things for the rest of your system. Here's how TLC interprets each of them:

* _If Case_: TLC can run either the first or second branch. In the second branch, it checks the conditional, sees that the conditional is false, and then jumps to the end of the if block. So on reaching the `either`, TLC checks two behaviors: "go to `Push`" or "skip to `After`".
* _Await Case_: In order run the second branch, `stack_not_empty` must be true. Since it's false, the second branch can't run, meaning only the first branch is possible. So there is only one possible behavior: "go to `Push`".

In other words, in the `if` spec, depending on the state of the stack, there are three possible behaviors: `Push->After`, `Pop->After`, and `After`. In the `await` spec, there's only `Push->After` and `Pop->After`. Generally, the latter is what you want, so you should use `await` in this case unless you're sure that the skipping the `either` is something you want.

One thing that **does not** work is putting the `await` in `Pop`:

```
either
  Push:
    \* code
or
  Pop:
    await stack_not_empty()
    \* code
end either
After:
    \* code
```
This is because there's nothing stopping TLC from _reaching_ Pop; the `await` only matters afterwards. In this case, if the stack is empty, there's no way for TLC to run the `Pop` step and no other processes to run instead, so this is a deadlock.

All of this, of course, assumes this is a single-process system. In a multiprocess system, other processes may potentially alter the stack, so `Pop` is not an automatic deadlock.

## Conditional Processes

We can also guard a process in the same way:

```tla
await condition;
call process;
```

Similar to above, we can't put the `await` inside the process.. So we have to have an `await` every time we want to call the process, which is error prone. While we can't avoid this, we can ensure that we raise an error if we miss the guard:

```tla
process p()
begin
 P:
   assert condition;
   \* code
end
```
We still need to manually include the `await` statements, but if we forget the assertion fails and spec is broken.