+++
title = "Next Steps"
weight = 0
+++

TK Delete all of this

In a relative sense, we've only covered a small portion of TLA+. I tried to keep this condensed to the parts I personally find most useful, which meant most of TLA+ was left out. After all, we spent more time on functions than _all_ of temporal logic. And we haven't even touched entire topics, like interface refinement, or the proof system, or even what 'temporal logic' means!

To be honest, I don't think I'm the right person to teach those things. I still consider myself a beginner: if you read everything in this guide, you probably now know as much as I do. If you want to learn more, you'll have to dive in. So let's talk about what to read next.

### Documentation

There's four sources you should probably start with.

* [Specifying Systems](https://research.microsoft.com/en-us/um/people/lamport/tla/book.html): I recommended that you download a copy in the introduction, for checking things that aren't clear in this guide. _Specifying Systems_ is a (near) complete reference the core TLA+. There's also the [TLA+ Hyperbook](https://research.microsoft.com/en-us/um/people/lamport/tla/hyperbook.html), which is a work in progress but more comprehensive it what it currently covers.

* [TLA+2](https://research.microsoft.com/en-us/um/people/lamport/tla/tla2.html): Since _Specifying Systems_ came out Lamport updated the TLA+ language, adding lambda functions and a proof system. This document provides an overview of those changes.

* [PlusCal Manual](https://research.microsoft.com/en-us/um/people/lamport/tla/pluscal.html): Contains a complete specification of PlusCal, including some corners I did not talk about. Note there are two syntaxes for PlusCal: p-syntax, which we've been using, and c-syntax, which overloads `{}` to replace "do" and "end".

* [TLA+ Proof System](https://tla.msr-inria.inria.fr/tlaps/content/Documentation/Tutorial/The_example.html): If you're interested in TLA+ proofs, this is the most comprehensive source.

### Other Articles

* [TLA+ in Distributed Systems Class](http://muratbuffalo.blogspot.com/2015/01/my-experience-with-using-tla-in.html): Murat uses TLA+ as a teaching tool and has some discussions on some of his experiences with that. He has [several](http://muratbuffalo.blogspot.com/search/label/tla) posts on TLA+ and they're all solid.

* [Lamport's TLA+ for Spec Testing (and why you're not using it)](https://www.linkedin.com/pulse/lamports-tla-spec-testing-why-youre-using-nira-amit): Real-world use case of ensuring trading bots don't do bad things.
