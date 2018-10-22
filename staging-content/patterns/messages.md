+++
title = "Messages"
weight = 1
hidden = true
+++

A common question when starting with PlusCal is how to implement message queues. While you rarely have to test that your queue works, you often use them to pass information around your system, and often bugs can appear in the communication layer. So it's useful to know how to simulate them.

Let's start by making a simple FIFO queue.

```tla
variable queue = <<>>

macro push(queue, message)
begin
  queue := Append(queue, message);
end macro

macro pop(queue, receiver)
begin
  receiver := Head(queue);
  queue := Tail(queue);
end macro
```

## Message Queues

The simplest message queue is our above implementation: put the server and client on separate processes and you're done. In some cases you can even do away with the pushing and pick an already-filled queue as a starting state. 

### Finite Queues

If you want a queue to have a maximum size, you should add that as a checked invariant: `QueueSizeInvariant(queue, size) == Len(queue) <= size`. Even if that's not the focus of your system, it's a good sanity check to ensure that the system follows your assumptions. As for implementation, you have to determine what happens when you try to push to a full queue? Does it block until there's space or drop the message?

```tla
macro blocking_push(queue, message)
begin
  await Len(queue) < max_queue_size \* could be an operator or function
  queue := Append(queue, message);
end macro
```

```tla
macro nonblocking_push(queue, message)
begin
  if Len(queue) < max_queue_size then
    queue := Append(queue, message);
  end if;
end macro
```

### Multiple Clients

If multiple clients are using the same queue, just have each process refer to the same global.

```tla
variables queue = <<>>

process client \in some_set
variable message = Null
begin
  Poll:
    await queue /= <<>>;
    message := pop(queue, message);
end process;
```

### Duplicate messages

Two common cases of messages are "the server accidentally pushes the same message twice" and "the client fails to delete the pulled message". The former case is doable with `queue \o <<message, message>>`. The latter is doable with an either statement:

```tla
macro broken_pop(queue, receiver)
begin
  receiver := Head(queue);
  either
    queue := Tail(queue);
  or
    skip;
  end either;
end macro
```

## Publish/Subscribe

In a pub/sub system, the server pushes the same message to multiple clients. Instead of a single queue, we can assign one queue to each process.

```tla
variable queue = <<>>,
         subscribers = 1..3,
         sub_queues = [s \in subscribers |-> <<>>];

macro publish(message)
  sub_queues := [ s \in subscribers |-> Append(sub_queues[s], message)];
begin
end macro;

process sub \in subscribers
begin
\* sub_queues[self] is appropriate queue
end process;
```

Sometimes we cannot guarantee that every receiver will receive every message. We can simulate that by pushing to only a subset of the receivers.

```tla
macro lossy_publish(message)
begin
  with to_receive \in SUBSET DOMAIN sub_queues do
    sub_queues := [ s \in subscribers |-> 
                      IF s \in to_receive
                      THEN Append(sub_queues[s], message)
                      ELSE sub_queues[s]
                  ];
end macro;
```

---

---
title: "Practical TLA+ Now Available"
date: "2018-10-17"
categories:
  - Programming
tags:
  - TLA+
  - Formal Methods
draft: true

---

I am delighted to announce that my book, [Practical TLA+](https://www.apress.com/us/book/9781484238288), is now available! When I stumbled into TLA+ in 2016 I had no idea it would so define my passions, my values, and my career. I _definitely_ didn't think I'd be writing a book. But 11 months and 220 pages later, here we are! This is the largest project I've ever done and I'm incredibly excited to share it with you all.

g
_Practical TLA+_ is designed to take you from a complete outsider in formal methods to a happy user at your day-to-day job. The first six chapters cover most of the syntax and semantics, which by itself would be a solid introduction to TLA+. But part two is where the book really shines: it's all about _using_ TLA+. It covers all sorts of different approaches, techniques, and pitfalls to writing specs. Everything from fleshing out abstract specs to modeling adversarial agents to why you always want a `TypeInvariant`.

The book is also designed to be _accessible_. My technical editor and I went through the book together, line by line, making sure every explanation was clear and every step was explained. On average, we spent a half hour on each page. I honestly believe this is the best introduction to TLA+ available.

### FAQ

**What makes this different from [_Learn TLA+_](http://learntla.com/)?**

_Practical TLA+_ is much more comprehensive. It covers the same material with greater depth, properly explains temporal logic, and actually talks about the module system. More importantly, it focuses much more on how to _use_ TLA+. The second half of the book is packed with applications, techniques, and large scale examples. To give a sense of scale, the last two proper chapters are each about a single spec. Those two chapters combined are about as long as _the entirety_ of _Learn TLA+_.

Most importantly, I wrote _Learn TLA+_ as I was, well, _learning_ TLA+. I wrote _Practical TLA+_ with two more years of experience with writing specs, teaching people, and communicating the ideas. I think it shows in the quality of the text.

On the other hand, _Learn TLA+_ is free and has exercises in it. Tradeoffs!

**What's happening to _Learn TLA+_?**

Nothing. _Learn TLA+_ will always be freely available online. I'll be fixing some of the factual errors in it and prolly writing a C-syntax version of the guide but otherwise I'll be leaving it alone. I will still be reviewing pull requests, of course, if people want to [contribute fixes or additions](https://github.com/hwayne/learntla). Ultimately I see it being a shared project of the community. I wrote it because I believe free, online documentation is critical to the success of any project, and _Learn TLA+_ will stay that way.

**Now what?**

I [made workshops](/consulting) for TLA+ and Alloy and am currently looking for clients. If think you might be interested, [please contact me](mailto:consulting@hillelwayne.com).

My next major project will likely be writing a free online [Alloy](http://alloytools.org/) guide. There's already an [amazing book](https://mitpress.mit.edu/books/software-abstractions) for Alloy but I believe the lack of friction-free documentation is limiting adoption.
