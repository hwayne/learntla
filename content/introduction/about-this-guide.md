+++
title = "About This Guide"
weight = 3
+++

This guide focuses on the bare minimum required to get you up and running as fast as possible as well as some intermediate techniques to improve your models. This approach will ignore or skim over the vast majority of TLA+ in order to make that small chunk easier to learn. This doesn't mean the other parts boring, difficult, or useless. Far from it. But they're outside the scope of this guide.

I'm assuming you have the following background:

* __You're an experienced programmer.__ This is not an introduction to programming, and TLA+ is not a user-friendly tool.
* __You're familiar with testing.__ If you haven't used unit tests before, that'll be a lot more useful than learning this.
* __You know some math.__ TLA+ borrows heavily from mathematical structures and syntax. If you've heard of de Morgan's laws, know what a set is, and can understand what `(P => Q) => (~Q => ~P)` means, you're fine. Otherwise, this should still be accessible but might be a little less intuitive.

__You need to download the [TLA+ Toolbox](http://lamport.azurewebsites.net/tla/toolbox.html#downloading).__ You should also have access to the following resources:

* [The PlusCal Manual](https://research.microsoft.com/en-us/um/people/lamport/tla/pluscal.html): PlusCal is the algorithmic interface to TLA+. We'll be covering everything about it in this guide, but it's nice to have a complete grammar reference.
* [The TLA+ Cheat Sheet](http://lamport.azurewebsites.net/tla/summary-standalone.pdf): Exactly what it sounds like. Includes syntax for things out of this guide's scope.
* [Specifying Systems](https://research.microsoft.com/en-us/um/people/lamport/tla/book.html): _Specifying Systems_ was written by Leslie Lamport, the inventor of TLA+, and remains the most comprehensive book on the subject. It's a lot more advanced than this guide is, but you should know it exists.