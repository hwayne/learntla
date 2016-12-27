+++
title = "Using Temporal Properties"
weight = 2
+++

Most often, you're not interested in checking temporal properties. In the cases you are, you can often express what you want through invariants. [Something about ENABLED]. Sometimes, though, you don't have any other option. Here are some things to watch out for.

[[Editing note: this _definitely_ doesn't make sense without the chapter on writing models]]

### Liveness is Slow

It's easy to check that reachable states satisfy invariants. But to check liveness, _how you reach those states_ also matters. If a thousand routes lead through state S, that's 1000 routes that need to be checked for liveness and only one state that needs to be checked for safety. So liveness is intrinsically much, _much_ slower than checking invariants.

### Temporal Properties are Very Slow

The Toolbox has a number of optimizations to make it easier to check invariants: multithreading, model symmetry sets, cloud computing, etc. These all assume, though, that we only care about individual states. None of these apply to temporal properties. So it's even slower to check than you'd think at first.

An especially important one to watch out for are symmetric models. TLC can check them for temporal properties. _However_, the symmetry properties can provide false negatives: it can say that your spec satisfies the properties when it actually doesn't.

### Stuttering and Fairness

TODO

## Recommendations

* Use separate models for invariants and temporal properties.
* Use smaller sets of model values to check liveness than safety. 
* Consider testing the same temporal property among several models with different setups.
* Do not use symmetric model sets.
