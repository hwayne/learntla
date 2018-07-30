+++
title = "Processes"
weight = 1
+++

Our old code ran everything in a single process- that’s the begin block. If we wanted have several things happen simultaneously, we use multiple processes. We set it up like this:

{{% code processes %}}

All processes must be assigned a value. There are two ways to do this. First, you can say `process = foo`, which will create one copy of that process. Or you could say `process \in bar`, in which case it will create one copy of that process for each element in `bar`. So if you write `process \in {1, 3, 5}`, you have three copies of that process running your behavior. 

Process values are used to select which process to run, so all processes in a behavior *must* be comparable and *should* be unique. If you write `process = 1`, you can’t have a second defined as `process bar = 'bar'` because 1 and ‘bar’ are not comparable. Additionally, you shouldn't have a second process also defined as `process = 1` because when `1` is selected the first process will always run and the second process will always be ignored.

This is a case where model values and model sets can be very useful, since every model value is comparable to everything else (it's unequal to everything except itself).

You can get a process’s value with `self`:

```tla
process foo = "bar"
begin
  print self; \* prints "bar"
end process
```

Variables declared outside of a process have global scope: any process can read and modify them. Variables declared in a process scope are local to _that process_. So if you have multiple processes defined in a set, each one will have it’s own private variable scope. If you use `\in` for the variables, TLC will create one state for each combination of initial states in each process. For example:

{{% code in %}}

TLC can choose in which order to run the possible steps, where each step corresponds to all of the code in one label of one process. If any of these paths breaks an invariant, then TLC raise it as usual.

{{% code fail1 %}}

This will fail, as the sequence `C -> A -> B -> D` sets x as `0 + 1 -> 1 - 1 -> 0 * 3 -> 0 /= 0`.

If there are multiple instances of the same process, TLC advances them one at a time.

{{% code fail2 %}}

This fails on the path `A[1] -> B[1] -> A[2] -> A[3] -> C[1]`.

### Await

Is there a way to prevent a step from running? We can do this with `await`:

{{% code pass1 %}}

In this case, the entire C step is blocked until the `await` is true. So the only path that can happen is `A -> B -> C -> D`, which is valid.

A troubling problem here: if we can say "don’t run this step unless X is true", can we have a situation where we can’t run any steps? For example, if we instead did `await x > 1`, we'd be able to do `A -> B` and then get stuck. This is called a _deadlock_. This is almost certainly a serious bug and TLC will flag this as an error in your algorithm.

If a deadlock is _not_ an error in your system, then you can disable that check in the model.

## Example

Let's model a very simple deadlock system: the "Dining Philosophers" problem. We set it up as follows:

* There are N philosophers sitting around a circular table.
* Between every two philosophers is a fork, with N forks in all.
* A philosopher needs to pick up both adjacent forks to eat. As soon as they finish eating, they put down both forks.
* A philosopher can only pick up one fork at a time.
* If a philosopher picks up a fork and does not have a second, they will hold the first fork while waiting for the second.

In less poetic terms, each process shares two resources with two other processes, one for each 'adjacent' one. Here's the equivalent PlusCal model:

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
process philosopher \in 1..NP
variables hungry = TRUE;
begin P:
  while hungry do
    with fork \in AvailableForks(self) do
      forks[fork] := self;
    end with;
    Eat:
      if Cardinality(HeldForks(self)) = 2 then
        hungry := FALSE;
        forks[LeftFork(self)] := NULL ||
        forks[RightFork(self)] := NULL;
      end if;
  end while;
end process;
end algorithm; *)
```

If we set `NumPhilosophers` to 1, this works. If we set it to 2, though, the model deadlocks. Each philosopher can pick up their left fork, leading to a case where every philosopher has exactly one fork and no others are available. Since each will only release their fork once they eat, and since they need two forks to eat, the entire system stalls out. We can 'fix' this by providing a timeout, but that can lead to a 'livelock' problem, which we'll cover in the next chapter. However, it _does_ fix the deadlock, so let's put that down here:

```tla
process philosopher \in 1..NP
variables hungry = TRUE;
begin P:
  while hungry do
    either
     with fork \in AvailableForks(self) do
       forks[fork] := self;
     end with;
    or
     await AvailableForks(self) = {};
     with fork \in HeldForks(self) do
      forks[fork] := NULL;
     end with;
    end either;
    Eat:
      if Cardinality(HeldForks(self)) = 2 then
        hungry := FALSE;
        forks[LeftFork(self)] := NULL ||
        forks[RightFork(self)] := NULL;
      end if;
  end while;
end process;
```
