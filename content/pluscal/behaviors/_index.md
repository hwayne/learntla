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
  either 
    x := x + 2;
  or 
    x := x * 2;
  end either;
  i := i - 1;
end while
```

The inner loop will happen twice. Each time the model can either add two or double x, meaning that there's four possible end results:

{{<mermaid>}}
graph TD;
A[3] --> B[5]
A    --> C[6]
B    --> BB[7]
B    --> BC[10]
C    --> CB[8]
C    --> CC[12]
{{< /mermaid >}}

{{% q %}}
Will the following code pass or fail?

```
either
  assert TRUE;
or
  assert FALSE;
end either;
```

{{% ans either %}}
Fail, as the second branch can fail. Since a spec only passes if every behavior passes, one behavior failing means the entire spec is broken.
{{% /ans %}}
{{%/q %}}

### With

`with` does the same thing, except instead of creating a new behavior for each possible branch, it creates a behavior for each element in the set. In this case, we have three possible behaviors:

```
with a \in {1, 2, 3} do
  x := x + a
end with;
```

This creates a separate timeline for each element in the set.

{{<mermaid>}}
graph LR;
e["end with"];
with ---x1(x+1);
with ---x2(x+2);
with ---x3(x+3);
x1 --- e; x2 --- e; x3 --- e; 
{{< /mermaid >}}

## Example

_Specify a system with three flags that can be on or off, as well as can change the state of a flag._

Right now we're a little limited in what we can practically do, but we can already start constructing simple patterns. Here's one way to write this in PlusCal:

{{% code gates %}}

This isn't the most optimal way of writing it, but I wanted to showcase both `with` and `either` here. You could probably use just the `either`. `BOOLEAN` is a TLA+ builtin and is equal to the set `{TRUE, FALSE}`. As you can see, every step this picks a single flag and either sets it to true or false. Fairly simple, if cumbersome.

{{% q %}}
How many possible _behaviors_ are there after three loop iterations? Keep in mind that distinct behaviors can have the same end state.

{{% ans 3havior %}}
There are 8 initial states. On each loop, the model chooses one of three values and takes one of two actions with it, for a total of 6 paths per loop. So after three loops there are 8*6^3 ~ 1800 behaviors. However, there are only 8 possible current states: most of the behaviors lead to a duplicate outcome.
{{% /ans %}}
{{%/q %}}

To give a better sense of where we're going, here's how we could write it instead, once we're more comfortable with the language:

{{% code gates2 %}}

The `flags \in [1..3 -> BOOLEAN]` bit is called a [function set](/tla/functions). We'll be covering it later.
