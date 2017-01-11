+++
title = "Processes"
weight = 1
+++

Our old code ran everything in a single process- that’s the begin block. If we wanted have several things happen simultaneously, we use multiple processes. We set it up like this:

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

All processes must be assigned a value. There are two ways to do this. First, you can say "process = foo", which will create one copy of that process. Or you could say "process \in bar", in which case it will create one copy of that process for each element in bar. So if you write `process \in {1, 3, 5}`, you have three copies of that process running your behavior. 

All processes in a behavior must be comparable. So if you write "process = 1", you can’t have a second defined as "process bar = ‘bar’". 1 and ‘bar’ are not comparable. This is a case where model values can be very useful, since every model value is comparable to everything else (it's unequal to everything except itself)

You can get a process’s value with "self":

```
process foo = "bar"
begin
  print self; \* prints "bar"
end process
```

Variables declared outside of a process have global scope: any process can read and modify them. Variables declared in a process scope are local to _that process_. So if you have multiple processes defined in a set, each one will have it’s own private variable scope. If you use `\in` for the variables, TLC will create one state for each combination of initial states in each process. For example:

```
process p \in 1..3
variable x \in 1..4
begin
A:
skip
end process;
```

There are three processes, each with one of four possible values for x, so there are 4^3 = 64 different initial states. Since TLC can run the processes in any order, each initial state has 3! = 6 possible behaviors, so there are 384 total behaviors for this spec. In reality, TLC is usually smart enough to realize that some behaviors are redundant, so the actual number checked will be a lot lower. [[this is slightly off]]


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

### Await

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

### Deadlocks

A troubling problem here: if we can say "don’t run this step unless X is true", can we have a situation where we can’t run any steps? For example, if we instead did `await x > 1`, we'd be able to do `A -> B` and then get stuck. This is called a deadlock. This is almost certainly a serious bug and TLC will flag this as an error in your algorithm.

If a deadlock is _not_ an error in your system, then you can disable that check in the model.

[[ TODO EXAMPLE ]]

