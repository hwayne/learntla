+++
title = "Example: Rate Limiting"
weight = 7
+++

## The Problem

As part of your project, you need to call a third party API. There are two types of calls you need to make:

1. A GET for a collection of objects. Each call will return some results and, potentially, a pagination token.
1. A GET for a single object, followed by, if necessary, a PUT to update it.

There is a known rate limit of N calls per unit of time on this API, and you do not want to exceed this. The first type may make an arbitrary number of calls, but it's less critical and you are comfortable waiting between calls. For the second, it will make either 1 or 2 calls; however, being higher priority, you want to _immediately_ update the object if necessary. With these constraints in mind, how do you guarantee you never exceed the rate limit?

### Initial Design

We start with the minimum possible case.

{{% code init %}}

Since most of the business logic is irrelevant to our use case, we simply leave it out. `get_collection` makes an arbitrary number of calls, represented by the `either goto`. Every time TLC reaches that branch point it will explore both branches, so we know this can be an arbitrary number of calls. Similarly, the `get_put` makes either one or two calls in a transaction. Finally, every time the `made_calls` changes we check that we haven't gone over the maximum.

If we run this, we'll get an error: the assert fails pretty trivially. We can fix this by adding a check in the macro, so that we only make a call if we have enough rate left. One fix is this:

{{% code if_macro %}}

Which makes the call fail silently if it would take us past the limit.

### Deadlocks

Our solution works, but misses the business case: we don't want to not make the calls, we want to _wait_ on them until the rate limit refreshes. We can simulate that with an _await_:

{{% code await_macro %}}

If we run this, though, we get a deadlock. That's because all of our processes are waiting for the limit to refresh, which we never actually coded. Here's one way of doing this:

{{% code limit_process %}}

If we add that, the spec passes as normal.

### Asynchronous Workers

Let's add a complication: all of the processes are running on different workers, so they don't automatically know the number of calls made. In order to avoid going past the limit, we need to share that information, which takes time. One way we can do this is by having each process query a central cache that only move forward if there's enough calls remaining. One representation would be

{{% code with_delay %}}

When we run this, we see it fails, as between the get and the request another process can make a call. If we want to resolve this we need some form of locking or priority. This will work, but it also explodes the diameter. Every process needs to wait on every other process, even when there's plenty of calls to go around. We should instead look for a more optimized way of handling this issue.

### Semaphores

One solution we can use is to reserve calls: when a process checks that there are calls remaining, it reserves N calls that are considered made in our cache but not in the API endpoint. Then, once we make the appropriate calls, we return the necessary reserves.

{{% code with_reserves %}}
