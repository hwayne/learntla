+++
title = "[Behaviors]"
weight = 4
+++

So far we've seen the basics of PlusCal as well as how to run a model. We've also seen that if our starting variables are specified as belonging to a set, it expands the state space that TLC can search. This takes up most of the way to writing useful specifications. The last step is to add divergent _behaviors_: allow the system to do different things at a given step. In a single process PlusCal algorithm, there are two simple ways to introduce concurrency: a `with` statement and an `either` statement.

### Either
`Either` looks a lot like a basic if statement. The syntax is as follows: 

```
either
  skip;
or
  skip;
or
  skip;
end either;
```

The important thing is that TLC will run _every_ branch. When it encounters an either, it creates a separate state and executes a different branch for each one. For example, given:

```
variables x = 3, i = 2;
begin
while i > 0 do
  either x := x + 2 or x := x * 2 end either
  i := i - 1
end while
```

The inner loop will happen twice. Each time the model can either add two or double x, meaning that there's four possible end results:

MAKE THIS A DRAWING
```
     3
  5     6
7  10 8  12
```

### With

[Maybe avoid this entirely?]
```
with a \in {1, 2, 3} do
  x := x + a
end with;
```

This creates a separate timeline for each element in the set.

## Example

[Example]
