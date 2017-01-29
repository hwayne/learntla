+++
title = "Behaviors"
weight = 4
+++

So far we've seen the basics of PlusCal as well as how to run a model. We've also seen that if our starting variables are specified as belonging to a set, it expands the state space that TLC can search. This takes us most of the way to writing useful specifications. The last step is to add divergent _behaviors_: allow the system to do different things at a given step. In a single process PlusCal algorithm, there are two simple ways to introduce concurrency: a `with` statement and an `either` statement.

### Either
`either` looks a lot like a basic if statement. The syntax is as follows: 

```
either
  skip;
or
  skip;
or
  skip;
end either;
```

The important thing is that TLC will run _every_ branch. When it encounters an either, it creates a separate behavior and executes a different branch for each one. For example, given:

``` tla
variables x = 3, i = 2;
begin
while i > 0 do
  either A: x := x + 2 or B: x := x * 2 end either
  i := i - 1
end while
```

The inner loop will happen twice. Each time the model can either add two or double x, meaning that there's four possible end results:

```
     3
  5     6
7  10 8  12
```

### With

`with` does the same thing, except instead of creating a new behavior for each possible branch, it creates a behavior for each element in the set. In this case, we have three possible behaviors:

```
with a \in {1, 2, 3} do
  x := x + a
end with;
```

This creates a separate timeline for each element in the set.

```
 a=1 a=2 a=3
 x+1 x+2 x+3
```

## Example

_Specify a system with three flags that can be on or off._

Right now we're a little limited in what we can practically do, but we can already start constructing simple patterns. Here's one way to write this in PlusCal:

{{% code gates %}}

`BOOLEAN` is a TLA+ builtin and is equal to the set `{TRUE, FALSE}`. As you can see, every step this picks a single flag and either sets it to true or false. Fairly simple.

To give a better sense of where we're going, here's how we could write it instead, once we're more comfortable with the language:

{{% code gates2 %}}


