+++
title = "Procedures and Macros"
weight = 2
+++

If you have multiple processes, you might eventually want to share code between them. Since we’re engineers we want to keep things DRY, and the simplest way to do that is with macros and procedures.

### Macros

Macros are the general catch-all code inliner. You define them with

```
macro Name(var1, ...)
begin
 \* stuff
end macro;
```

And call them with `Name(value1, ...)`. Simple. There's just a few caveats you have to keep in mind:

1. A macro is shorthand code, not its own process. So they can't have labels, multiple assignments, while loops, etc. 
1. This happens inline.

Macros must be defined after any `define` block and before any processes.

### Procedures

Procedures are a little more difficult to both write and use. In return, though, you get two benefits. One, a procedure can have internal variables. Two, you can have labels in them.

```
procedure Name(arg1, ...)
variables var1 = ... \* This cannot be \in, only =
begin
  Label:
  \* stuff
  return;
end procedure;
```

The return just ends the procedure. If your procedure never reaches it, then it's an error. It won't return any value (really, nothing does). If you passed in a variable as `arg1` and then mutate `arg1`, the variable will remain unchanged even after the `return`.

In order to call a procedure, you have to explicitly use `call Name(val1, ...);`, and the following line must be a label or a `return` (if you called it from another procedure).

{{% notice warning %}}
 If you want to use procedures you _must_ `EXTEND Sequences`.
{{% /notice %}}

Procedures must be defined after any macros and before any processes.

{{% notice info %}}
So when should you use which? Macros are faster and less complicated. If you can use them, use them. Use procedures when you have multiple separate processes that can do the same actions.
{{% /notice %}}

### Order of operations

PlusCal enforces a strict ordering of its blocks. The `define` block has to come before any macros, which has to come before any procedures, which has to come before any processes.

## Example

Here's what our dining philosophers algorithm looks like if we use procedures and macros:

```tla
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NumPhilosophers, NULL
ASSUME NumPhilosophers > 0
NP == NumPhilosophers

(* --algorithm dining_philosophers

variables forks = [fork \in 1..NP |-> NULL]

define
  LeftFork(p) == p
  RightFork(p) == IF p = NP THEN 1 ELSE p + 1

  HeldForks(p) ==
    { x \in {LeftFork(p), RightFork(p)}: forks[x] = p}

  AvailableForks(p) ==
    { x \in {LeftFork(p), RightFork(p)}: forks[x] = NULL}
end define;

macro set_fork(fork, val) begin
    forks[fork] := val;
end macro;

macro take_a_fork() begin
  with fork \in AvailableForks(self) do
       set_fork(fork, self);
  end with;
end macro;

macro drop_a_fork() begin
  await AvailableForks(self) = {};
  with fork \in HeldForks(self) do
    set_fork(fork, NULL);
  end with;
end macro;

procedure attempt_eat() begin
 Eat:
  if Cardinality(HeldForks(self)) = 2 then
    hungry := FALSE;
    forks[LeftFork(self)] := NULL ||
    forks[RightFork(self)] := NULL;
  end if;
  return;
end procedure;

process philosopher \in 1..NP
variables hungry = TRUE;
begin P:
  while hungry do
    either
      take_a_fork();
    or
      drop_a_fork();
    end either;
    call attempt_eat(); 
  end while;
end process;
end algorithm; *)
```

Note that we didn't have to define `self` or `hungry` in the macros and procedures: it's automatically equivalent to the calling processes's corresponding variables.

Now change `call attempt_eat()` to `call attempt_eat(hungry)` and the procedure to the following:

```tla
procedure attempt_eat(h)
begin
 Eat:
  if Cardinality(HeldForks(self)) = 2 then
    h := FALSE;
    forks[LeftFork(self)] := NULL ||
    forks[RightFork(self)] := NULL;
  end if;
  return;
end procedure;
```

From our understanding of procedures, even if this procedure updates `h`, `hungry` will remain `TRUE`. However, if we try to run it, we hit a gotcha with procedures: it will tell us we're missing a label before `return`. To explain what's going on here, we need to leak the abstraction a little. `return` resets `h` for us. Since we're also setting `h := FALSE`, this means that in the `Eat` label we'd be updating `h` twice: once inside the if block and once in the `return`. TLA+ does not allow us to update twice in a label, so we'd need to add a new one before the `return`. Procedures can behave in surprising ways, which is another reason to use macros if you have the option.
