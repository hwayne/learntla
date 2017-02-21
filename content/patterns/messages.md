+++
title = "Messages"
weight = 1
draft = true
+++

A common question when starting with PlusCal is how to implement message queues. While you rarely have to test that your queue works, you often use them to pass information around your system, and often bugs can appear in the communication layer. So it's useful to know how to simulate them. Here's a few examples.

Let's start with a couple of data structures: queues and stacks.

### A FIFO Queue

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

### A LIFO Stack

Same pop mechanism, different push mechanism.

```tla
macro push(stack, message)
begin
  stack := <<message>> \o stack;
end macro
```

## Polling


## Pushing
