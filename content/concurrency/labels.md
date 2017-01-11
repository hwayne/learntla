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

Beyond that, there's one rule that's a little more complicated: you can only assign to a variable __once__ in a given label. That's because, as mentioned above, labels are moments of time. A variable can't change twice between two instants, because that doesn't make sense. There are some cases where this can get annoying; for example, switching two variables. In these cases you can use `||` to chain assignments: `x := y || y := x;`

### ENABLED

Labels are converted into "Actions" by the PlusCal translator. I think actions are a bit out of scope for this guide, but there's one consequence of this we can find useful: we can 'apply' operators to Labels. The main one we're interested in is `ENABLED`. For a label `A`, `ENABLED A` means "this specific action can happen in the next step. For example, if we wanted to ensure that we don't download a file if a specific flag is set, we can write the invariant as `no_download_flag => ~ENABLED A`.
