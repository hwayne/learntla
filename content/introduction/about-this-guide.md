+++
title = "About This Guide"
weight = 3
+++

So why write a guide when the [canonical book](https://research.microsoft.com/en-us/um/people/lamport/tla/book.html) is freely available online? This is aimed at a slightly different audience. _Specifying Systems_ is a comprehensive work that covers the total power of TLA+, down to proving that the logic is mathematically consistent.  And you can do fantastic things with that power.

However, that power comes at a cost: TLA+ is also very _complicated_, and I've found that often scares people away. And while you can do fantastic things with 100% of TLA+, you can do _damn good_ things with 40% of it. You don't need to know about machine closure or except-syntax to check that your API won't crash if you POST twice in a row. _Specifying Systems_ is aimed at people building critical systems; this guide is aimed at software developers in startups who want to catch edge cases before they hurt a customer.

So, this guide. I'll be focusing on the bare minimum required to get you up and running as fast as possible as well as some intermediate techniques to improve your models. This approach will ignore or skim over the vast majority of TLA+ in order to make that small chunk easier to learn. This doesn't mean the other parts boring, difficult, or useless. Far from it. But they're outside the scope of this guide.

If you want a more comprehensive guide to TLA+, I'd recommend reading Specifying Systems and the [PlusCal manual](https://research.microsoft.com/en-us/um/people/lamport/tla/pluscal.html).


This guide assumes you’re comfortable with programming and testing. Some experience with first order logic ("P => Q") is useful but unnecessary; we’ll be covering those topics as needed. You should have the TLA+ toolbox installed as well as access to the PlusCal and Specifying Systems pdfs.

The guide is divided as follows:

* Introduction to PlusCal introduces basic PlusCal syntax and model checking, as well as basic set operations.
* Concurrent PlusCal teaches how to simulate several systems or algorithms interacting in a shared world.
* [[TLA+ teaches you about, um, TLA+.]]
* Modelling goes into more detail on how to test your specifications and how to make your checks more performant.
* Temporal Logic provides an extremely brief overview of how to check invariants dependent on the entire timeline as well as the associated pitfalls with this.
* Miscellaneous covers basics that don’t find into the other categories, like instances and binary operators.

When following the core chapters, I recommend experimenting with the examples.

In addition, there are three reference chapters. None of these introduce anything novel and critical but instead are written to help you use TLA+ in practice.  [[None of these are here yet!]]

* Examples contains practical problems, how to model the invariants, and how to build the appropriate specifications.
* Snippets provides operators for common use cases, such as finding the sum of a set, and descriptions of how they work.
* Reference is a glossary, syntax guide, and list of common gotchas.

Tooltips show side information that may be interesting but is unrelated to the basic ideas. Info boxes provide clarification. Tip boxes provide comprehension or optimization advice. Warnings tell you about pitfalls.
