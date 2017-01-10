+++
title = "Concurrency"
weight = 0
+++

[[ TODO fix whole chapter ]]

The last chapter covered modeling simple, single-process systems in PlusCal. This section will cover _concurrent systems_: ones where multiple processes, sharing a global state, run simultaneously. As a simple example of a concurrent system, you have one model and three different kinds of jobs that can affect the state of that model, all running in an asynchronous worker pool. How do you guarantee that just the right ordering of run jobs doesn’t cause data to somehow break?

Reasoning about concurrent systems gets intractable quickly, which is why we get a model checker to reason about it for us.
