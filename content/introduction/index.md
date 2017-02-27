+++
title = "Introduction"
weight = 0
+++

### What is TLA+?

TLA+ is a _formal specification language_. Instead of writing code, you write a description of what the code should accomplish and what your abstract algorithm is. Then you can verify that your specification matches your expectations. Think of it like unit tests, except on your designs instead of the code.

### How could I use it?

People normally think of formal specification as a difficult tool for only critical systems, there are many cases where a few hours of TLA+ can find critical bugs before you've written any code. Some examples:

* Two jobs edit the same database record, except one makes a call to a laggy server that either returns a value immediately, after a few seconds, or times out. Can you guarantee that under no bizarre race conditions will the record ever get updated 'wrong'?
* Will a given change the caching system make it possible for a critical system to receive the wrong information?
* Will your maze generator ever make an impossible map?

### What's an example?

TK 

### How do I learn?

Here.