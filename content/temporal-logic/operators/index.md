+++
title = "Temporal Operators"
weight = 1
+++

## Liveness

Whenever we write invariants, we're saying "for an arbitrary state, this will never happen." And this has been very useful. But there's a trivial system that matches _any_ such case: make sure the initial conditions are correct and then do nothing at all. Safety only tells us something that's true of any moment in any behavior. Sometimes, we want to ask a question about the behavior itself. Most often this is "will this eventually do what we want?" Will the trade eventually happen? Does every thread at some point get priority? Does our algorithm _finish_?

We call these properties "Liveness". And to answer these questions, we use the following new operators.

### []

`[]` is probably the most important operator and the one we're least likely to use. `[]` means _always_: `[]P` means that P is true for all states.

Basically, an invariant. When you put `P` in the invariant box, TLC interprets that as the temporal property `[]P`. The only difference is that TLC is hyper-optimized to handle invariants, so the entire invariants box is basically a convenience thing. So while `[]` implicitly powers all of our invariants, we almost never need to write it explicitly.

### <>

`<>` means _eventually_: `<>P` means that for every possible behavior, at least one state has P as true. For example, the following code is wrong under the temporal property `<>(x = 1)`

```
(* --algorithm example
variables x = 3
begin
  while x > 0 do
  with decrement \in {1, 2} do
    x := x - decrement
  end with;
  end while;
end algorithm; *)
```

[TODO check this]. There exists one timeline where x never passes through 1: "x = 3 -> x = 2 -> x = 0". So it's not true that 'eventually, x is 1'. As long as every behavior has at least one state satisfying the statement, an eventually is true.

### ~>

`~>` means _leads to_: `P ~> Q` implies that if P ever becomes true, at some point afterwards Q must be true. For example:

```
(* --algorithm example
variables x = 4, decrement \in {1, 2}
begin
  while x > 0 do
    x := x - decrement
  end while;
end algorithm; *)
```

As with before, `<>(x = 1)` is not true: we can do `4 -> 2 -> 0`. But the temporal property `(x = 3) ~> (x = 1)` is _true_: there's no way to pass through 3 without also passing through 1.

[adjust this for stuttering]

### <>[]

`<>[]` means _stays as_: `<>[]P` says that at some point P becomes true and then **stays** true. If your program terminates, the final state has to have P as true. [more]

