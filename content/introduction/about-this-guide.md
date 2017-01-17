+++
title = "About This Guide"
weight = 3
+++

So why write a guide when the [canonical book](https://research.microsoft.com/en-us/um/people/lamport/tla/book.html) is freely available online? This is aimed at a slightly different audience. _Specifying Systems_ is a comprehensive work that covers the total power of TLA+, down to proving that the logic is mathematically consistent.  And you can do fantastic things with that power.

However, that power comes at a cost: TLA+ is also very _complicated_, and I've found that often scares people away. And while you can do fantastic things with 100% of TLA+, you can do _damn good_ things with 40% of it. You don't need to know about machine closure or except-syntax to check that your API won't crash if you POST twice in a row. _Specifying Systems_ is aimed at people building critical systems; this guide is aimed at software developers in startups who want to catch edge cases before they hurt a customer.

So, this guide. I'll be focusing on the bare minimum required to get you up and running as fast as possible as well as some intermediate techniques to improve your models. This approach will ignore or skim over the vast majority of TLA+ in order to make that small chunk easier to learn. This doesn't mean the other parts boring, difficult, or useless. Far from it. But they're outside the scope of this guide.

If you want a more comprehensive guide to TLA+, I'd recommend reading Specifying Systems and the [PlusCal manual](https://research.microsoft.com/en-us/um/people/lamport/tla/pluscal.html). In fact, I'd recommend downloading both to use as a reference while reading this guide.
