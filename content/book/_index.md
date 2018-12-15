+++
title = "Book"
weight = 800
+++


I am delighted to announce that my book, [Practical TLA+](https://www.apress.com/us/book/9781484238288), is now available! 

_Practical TLA+_ is the spiritual sequel to _Learn TLA+_. It's designed for the same audience, people who are unfamiliar with formal methods but could benefit from using it at work. Part two is where the book really shines: it's all about _using_ TLA+. It covers all sorts of different approaches, techniques, and pitfalls to writing specs. Everything from fleshing out abstract specs to modeling adversarial agents to why you always want a `TypeInvariant`.

The book is also designed to be _accessible_. My technical editor and I went through the book together, line by line, making sure every explanation was clear and every step was explained. On average, we spent a half hour on each page. I honestly believe this is the best introduction to TLA+ available.

Of course, you're already at a free, beginner-focused resource for TLA+, one I'm still incredibly proud of. I think it's worth talking about how the two resources relate to each other.

### FAQ

**What makes this different from _Learn TLA+_?**

_Practical TLA+_ is much more comprehensive. It covers the same material with greater depth, properly explains temporal logic, and actually talks about the module system. More importantly, it focuses much more on how to _use_ TLA+. The second half of the book is packed with applications, techniques, and large scale examples. To give a sense of scale, the last two proper chapters are each about a single spec. Those two chapters combined are about as long as _the entirety_ of _Learn TLA+_.

Most importantly, I wrote _Learn TLA+_ as I was, well, _learning_ TLA+. I wrote _Practical TLA+_ with two more years of experience with writing specs, teaching people, and communicating the ideas. I think it shows in the quality of the text.

On the other hand, _Learn TLA+_ is free and has exercises in it. Tradeoffs!

**What's happening to _Learn TLA+_?**

_Learn TLA+_ will always be freely available online. In fact, I'm planning two more big updates to it. The first will clean up any confusing parts and correct any technical errors. I'm about halfway through that and hope to have it finished relatively soon. The second will be adding the option to switch between P-syntax (the current style) and C-syntax. That's a little further out. 

Past that I plan to let _Learn TLA+_ stand on its own. I will still be reviewing pull requests, of course, if people want to [contribute fixes or additions](https://github.com/hwayne/learntla). Ultimately I see it being a shared project of the community. I wrote it because I believe free, online documentation is critical to the success of any project, and _Learn TLA+_ will stay that way.

**If I've already read _Learn TLA+_, how should I read _Practical TLA+_?**

Read the introduction so you know how to set up the PT module. Chapter 1 uses the same introductory example here and can be skipped. Chapters 2, 3, and 5 cover similar ground as the website, but more carefully and with more detail. Skim these if you feel comfortable with the basics. Chapter 4 is new material: in addition to constants and model values, it also has using multiple modules in a project and parameterization. Chapter 6 is a much better treatment of temporal logic than the site currently has.

Chapters 7-12 are entirely new material.
