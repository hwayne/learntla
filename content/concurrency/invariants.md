+++
title = "Concurrent Invariants"
weight = 3.5
+++

Sometimes, we want to enforce invariants _between_ processes. For example, only one thread may have a lock at the same time, or the total values across all processes must be less than a certain threshold. Here's one example:

``` tla
process foo \in 1..2
variable x \in 1..2
begin
  Skip:
    skip
end process
```

How do we assert the variant "the sum of x between the two processes is not 4?" With a single process algorithm, we could write `x # 4`. But to do the same with multiple processes, we have to let the PlusCal abstraction leak.

When we translate an algorithm, TLA+ will create all of the corresponding variables. When we have multiple processes, TLA+ will instead create a function with a domain on the process identifiers and the range the actual values of x per process. So instead of having for example `x \in 1..2`, we instead have `x == [ProcSet -> 1..2]`. So in this case, the appropriate invariant is `x[1] + x[2] # 4`.
