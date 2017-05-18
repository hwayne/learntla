+++
title = "Using Model Values"
weight = 2
+++

When should you be using model values instead of strings and numbers? The main advantage of model values is they compare false to everything but themselves. If `M` is a model value, `M = 0`, `M = "0"`, and `M = {0}` are all false. In contrast, `0 = "0"` isn't false. It's an _error in your spec_.

In theory, you'll never want to compare two incomparables. In practice, we sometimes need to work around limitations in TLA+. As a good rule of thumb, if you're not directly processing strings as part of your system, **prefer model values to strings**.

### Processes

How do we represent N clients and one server? The following way seems reasonable, but it fails:

```tla
process clients \in 1..N
process server = 1
```

The problem here is that each process must be assigned to a separate value, and 1 is used twice. We could instead assign `server = 0`, but that just hides the problem. We might try to use a string instead, like this:

```tla
process clients \in 1..N
process server = "server"
```

But this also fails: 1 and "server" are not comparable. However, if we instead use a model value for server, it's valid:

```tla
process clients \in 1..N
process server = Server
```

### Sets

If a value could be true, false, or unknown, how do we best represent it? For two of those we'd want to use booleans, however "unknown" is a string and can't be compare to booleans. Instead, we can write `{TRUE, FALSE, UNKNOWN}` and make `UNKNOWN` a model value.

This is especially important when working with functions. A function's domain must be a set, and all elements in a set must be comparable to each other. So you can't have a function that mixes strings and numbers, but you can have one that mixes strings and model values.

## Sets of Model Values

What about model sets? They're obviously useful in cases where we're using numbers just to distinguish processes. For example, the ideal way to write the server-client proccesses would be

```tla
process clients \in Clients
process server = Server
```

Where `Clients = {c1, c2, ...}`. Why is this better than numbers? Aside from being easier to understand, it means you can make the set symmetrical. This, as mentioned before, makes your specs take considerably less time to run. This is true even outside of processes. For example, given the following simple algorithm:

```tla
begin
  with x \in S do
    skip;
  end with;
```

If `S = {1, 2, 3}`, then TLC will check three behaviors. If `S = {s1, s2, s3}` _and_ `S` is symmetric, TLC will check only one behavior and infer the rest. In cases where this is a safe assumption (no liveness tests), it's a good optimization.