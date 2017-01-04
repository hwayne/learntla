+++
title = "PlusCal"
weight = 0
+++

PlusCal is a tool for working with TLA+: it adds a pseudocode-like interface to the specs, making them easier for programmers to understand. While not every interesting spec can be written with PlusCal, quite a few can, and it's a great entry point into modelling. All of the specs we'll write over the course of this guide will run with PlusCal at the core.

```
\* TLA+

Init == /\ x = 1
Next == /\ x = 1 /\ x' = x + 1
Spec == Init /\ [][Next]_x

\* PlusCal

x = 1;
x := x + 1;
```

One note: PlusCal was invented over 10 years after TLA+ was. A consequence of this is that TLC (the TLA+ model checker) doesn't understand PlusCal. Instead, the Toolbox IDE can automatically transpile PlusCal to TLA+.

This section will focus on single process systems.
