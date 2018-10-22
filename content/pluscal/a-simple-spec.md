+++
title = "A Simple Spec"
weight = 2
+++

TLA+ started as a notation, and the model checker, TLC, only came out 5 years later. As it was never intended to be run, there's some assumptions of it being a read document instead of being runnable code. That means that there's a little bit of boilerplate we'll need to get through first.

In order for TLC to analyze a spec, it **must** have the following format:

``` tla
---- MODULE module_name ----
\* TLA+ code

(* --algorithm algorithm_name
begin
\* PlusCal code
end algorithm; *)
====
```

TLC will only analyze the code between the `----` beginning and the `====` end. Anything outside of those boundaries is ignored. `module_name` **must** be the same as the filename, while `algorithm_name` can be whatever you want. `\*` is a line comment and `(*` is a block comment. Note we're putting our algorithm in a comment. If you don't put it in a comment, you'll get a syntax error, because PlusCal isn't TLA+.

{{% notice note %}}
PlusCal came out fifteen years after TLA+ did. TLC is supposed to perfectly follow the semantics of TLA+, and since PlusCal is a completely different style it can't be fit into the same schema. Behind the scenes, we transpile the PlusCal to raw TLA+, and the `--algorithm` in comments is there to let the PlusCal translator know what it's supposed to be translating.
{{% /notice %}}

You can only have one PlusCal algorithm per file. 

{{% notice tip %}}
If you need to alternate between two versions of a pluscal algorithm, you disable one by adding a space to make `-- algorithm` in one. Then it's just a regular comment.
{{% /notice %}}


As for the PlusCal itself, here's the layout of a basic single process algorithm:

```
variables x = 1, y \in {3, 4}, z = {3, 4};
begin
  \* your code here
end algorithm;
```

In the `variables` block, `=` is the initial assignment. Everywhere else, `=` is the equality check and `:=` is assignment. If I wrote `variables x = 1, y = x = 2`, x would be initialized to `1`. Then, since `x` already had an initial assignment, `y = x = 2` would be parsed as assigning the _comparison_ `1 = 2` to `y`. This would lead to `y` initially being `FALSE`.

You might have noticed the `y \in {3, 4}`. That's set notation. It means that for the purposes of this algorithm, y can be 3 **or** 4. When you check the model, TLC will make sure it works for __all__ possible values of y. It will first test that nothing fails with `y = 3`, and then test that nothing fails with `y = 4`. 

Contrast `y \in {3, 4}` with `z = {3, 4}`, which means that z is the **set** {3, 4}. Any sort of data structure can be assigned to a variable in TLA+.

{{% notice note %}}
Since TLA+ is a specification language, it was designed to output really nice documents. That's why we use TeX like `\in` and `\union` and such. Fun fact: Leslie Lamport, the inventor of TLA+, also invented LaTeX! Another fun fact: we won't be talking about outputting specifications in any way whatsoever. Cool stuff, but not _immediately_ relevant to model checking.
{{% /notice %}}

Let's get Hello World out of the way.

``` tla
EXTENDS TLC

(* --algorithm hello_world
variable s \in {"Hello", "World!"};
begin
  A:
    print s;
end algorithm; *)
```

The `EXTENDS` is the `#include` analog for TLA+. `TLC` is a module that adds `print` and `assert`. `print` is, incidentally, the only IO possible with TLA+ and is provided for debugging purposes.

The only thing that may be unusual here is the `A:`. That is called a _label_. TLC treats labels as the "steps" in a specification; everything in the label happens at once. It's only between labels that the model can check invariants and switch processes. Also, you can't assign to the same variable twice in the same label. For the most part, it isn't too useful here. But it will be pretty important later.

{{% notice warning %}}
If you leave the `A:` out, your PlusCal will still transpile. For single process apps, it usually doesn't matter where we put the labels, so TLC will infer them. For the most part it's fine to leave them out in single process apps, but you should keep them in mind. For multiprocess algorithms, labels are extremely important and we always have to add them ourselves.
{{% /notice %}}

I assume that you're familiar with other programming languages. To make modeling more familiar, PlusCal has similar constructs. The semantics are fairly obvious, so here's what they look like. Assume all variables have been initialized before and we're in a `begin` block.

### Logic Operators

logic | operator | `TRUE` | `FALSE`
------|--------|--------|-------
equal | `=` | `1 = 1` | `1 = 2`
not equal | `/=` | `1 /= 2` | `1 /= 1`
and | `/\` | `TRUE /\ TRUE` | `TRUE /\ FALSE`
or | `\/` | `FALSE \/ TRUE` | `FALSE \/ FALSE`
not | `~` | `~FALSE` | `~TRUE`

### If

``` 
if x = 5 then
  skip;
elsif x = 6 then
  skip;
else
  skip;
end if;
```

### While

```
x := 5;
while x > 0 do
  x := x - 1;
end while;
```

This is the only form of looping.

### Goto

```
A:
  if TRUE then goto B else goto C endif;
B:
  skip;
C:
  skip;
```

Goto considered useful in PlusCal.
