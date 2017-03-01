+++
title = "Messages"
weight = 1
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
    await queue # <<>>;
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
