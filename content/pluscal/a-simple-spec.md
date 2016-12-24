+++
title = "A simple spec"
weight = 2
+++

TLA+ started as a notation, and the model checker, TLC, only came out 5 years later. As it was never intended to be run, there's some assumptions of it being a design document vs being a specification language. That means that there's a little bit of boilerplate bwe'll need to get through first.

In order for TLC to analyze a spec, it **must** have the following format:

```
---- MODULE module_name ----
\* TLA+ code

(* --algorithm algorithm_name
begin
\* PlusCal code end algorithm; *)
====
```

TLC will only analyze the code between the `----` beginning and the `====` end. Anything outside of those boundaries is ignored. `module_name` **must** be the same as the filename, while `algorithm_name` can be whatever you want. `\*` is a line comment and `(*` is a block comment. Note we're putting our algorithm in a comment. If you don't put it in a comment, you'll get a syntax error, because PlusCal isn't TLA+.

{{% notice note %}}
This might seem a little odd to you. It's this way because of backwards compatibility. TLA+ came out in 1994. TLC came out in 1999. PlusCal came out in 2009. TLC is supposed to perfectly follow the semantics of TLA+, and since PlusCal is a completely different style it can't be fit into the same schema. Behind the scenes, the TLC toolbox actually uses three separate tools for model checking: the `--algorithm` in comments is there to let the PlusCal translator know what it's supposed to be translating.
{{% /notice %}}

[question, can you have two algorithms in one file?]

As for the PlusCal itself, here's the layout of a basic single process algorithm:

```
variables x = 1, y = {2}, z \in {3, 4};
begin
  \* your code here
end algorithm;
```

[talk about extends Naturals]
For the variables block (and only the variables block)[more], `=` is assignment. Everywhere else, `=` is the equality check and `:=` is assignment.

You might have notices the `z \in {3, 4}`. That's set notation. It means that for the purposes of this algorithm, z can be 3 **or** 4. `z = {3, 4}`, on the other hand, means that z is the **set** {3, 4}. You'll find yourself using both quite a lot.

{{% notice note %}}
Since TLA+ is a specification language, it was designed to output really nice documents. That's why we use TeX like `\in` and `\union` and stuff. Fun fact: Leslie Lamport, the inventor of TLA+, also invented LaTeX! Another fun fact: we won't be talking about outputting as a specification in any way whatsoever. Cool stuff, but not _immediately_ relevant to model checking.
{{% /notice %}}

Let's get Hello World out of the way.

```
EXTENDS TLC

(* --algorithm hello_world
variable s \in {"Hello", "World!"};
begin
  A:
    print s;
end algorithm; *)
```

The `EXTENDS` is the `#include` analog for TLA+. `TLC` is a module that adds `print` and `assert`. `print` is, incidentally, the only IO possible with TLA+.

The only thing that is different here is the `A:`. That is called a _label_. TLC treats labels as the "steps" in a specification; everything in the label happens at once. It's only between labels that the model can check invariants and switch processes. Also, you can't assign to the same variable twice in the same label. For the most part, it isn't too useful here. But it will be pretty important later.


{{% notice warning %}}
If you leave the `A:` out, your PlusCal will still transpile. This is because the TLC can infer the labels in a single process app. **Do not get into this habit.** You'll want to feel comfortable with them by the time we start concurrency. [this is bad]
{{% /notice %}}

I assume that you're familiar with other programming languages. Be make modeling more familiar, PlusCal has a bunch of similar constructs. The semantics are fairly obvious, so here's what they look like. Assume all variables have been initialized before and we're in a `begin` block.

### Logic Operators

logic | token | `TRUE` | `FALSE`
------|--------|--------|-------
equal | `=` | `1 = 1` | `1 = 2`
not equal | `#` | `1 # 2` | `1 # 1`
and | `\/` | `TRUE \/ TRUE` | `TRUE \/ FALSE`
or | `/\` | `FALSE /\ TRUE` | `FALSE /\ FALSE`
not | `~` | `~FALSE` | `~TRUE`

### If

``` 
if x = 5 then
  skip;
elsif x = 6 then
  skip;
else
  skip;
endif;
```

### While

```
x := 5;
while x > 0 do
  x := x - 1;
end while;
```

### Goto

```
A:
  if TRUE then goto B else goto C endif;
B:
  skip;
C:
  skip;
```


