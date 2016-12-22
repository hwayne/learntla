+++
title = "Labels"
weight = 2
+++

Now you see why labels are so critical: they determine when your system can switch between processes. In this section we'll talk a little more about the requirements of labels, as well as where you can and cannot put them.

Labels represent moments of time. Everything in the label happens at once.
The label rules:

- The first line in a process has to have a label. That includes the first `begin` if it's a single-process algorithm.
- Put a label before a `while`.
- On the line after `call`, `return`, `goto`, or a control statement that also has a label in it.
- You can't put labels in a `with` statement.

{{% notice tip %}}
Generally, using `with` is an antipattern: there's often a more efficient or intuitive way to express your algorithm without with. One way is to drop down into the TLA+. Instead of writing `with x \in Set`, we can write `x := CHOOSE s \in Set: TRUE`. We'll cover `CHOOSE` and TLA+ in the next chapter.
{{% /notice %}}

Beyond that, there's one rule that's a little more complicated: you can only assign to a variable __once__ in a given label. That's because, as mentioned above, labels are moments of time. A variable can't change twice between two instants, because that doesn't make sense. There are some cases where this can get annoying; for example, switching two variables. In these cases you can use `||` to chain assignments: `x := y || y := x;`
