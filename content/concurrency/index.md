+++
title = "Concurrent PlusCal"
weight = 0
+++

The last chapter covered modeling simple, single-process systems in PlusCal. This section will cover _concurrent systems_: ones where multiple processes, sharing a global state, run simultaneously. The processes don't need to run the same code or even run by the same company. As a web dev, here are some of the concurrent systems I've run into:

* Server sending jobs to multiple workers
* Interacting with an unstable third party API
* Parallelizing a web scraper
* Processing cached data when the data 'in the wild' can be changing

Reasoning about concurrent systems gets intractable quickly, which is why we get a model checker to reason about it for us.
