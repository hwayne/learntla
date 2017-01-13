+++
title = "Example: Arbitrage"
weight = 20
+++

Back in our introduction to TLA+ [[ TODO ]] we showed a simple example of something TLA+ can specify: a market of people who can buy and sell items. We'll begin by turning that into a full specification:

{{% code market %}}

We don't care about deadlock, so we can uncheck that as a thing to check and add `NoArbitrage` as an invariant. Try making a model with 2 items, 2 vendors, a max price of 6, and a max actions of 5. Run the model to confirm there are no problems. Finally, add a third vendor and compare the runtimes. [[ TODO is symmetry safe here? ]]

One variant we can make: Right now it doesn't matter how many different types of items you have, because none of the items interact with each other. So it makes sense to test this with only one item.

[[ TODO etc ]]

### Trades

We can be reasonably confident there are no arbitrage opportunities here. What if we make the specification a little more complex? In addition to having buying items, let's imagine that you can also barter; you can convert some items into other items. To keep the system simple we'll assume you 'lose' quantity here: if you trade away N items, you can get at most N-1 back.

``` tla
ValidTrades == LET Trades == [SUBSET I -> SUBSET I]
               IN { T \in Trades : 
                    \A s \in DOMAIN T :
                      Cardinality(s) > Cardinality(T[s]) \* Fix
                      }
```

This requires us to extend FiniteSets. Note there are some weird cases here: for example, you can trade an item for nothing. However, these are all strictly bad options, so it's only an optimization problem. A big optimization problem, it turns out; With three items, `Trades` is has approximately 16 million elements. So instead we want to do a preoptimization of only mapping sets to individual items. [[ TODO ASSUME statements and stuff ]]

``` tla
ValidTrades == [{ i \in SUBSET I : Cardinality(i) > 1} -> I]
```
Here's the full code, along with the ability to trade:

{{% code trade %}}

In this one, we're less interested in arbitrage between vendors as we are between trading. If we run the model, it will pass. Looking back, we have a problem with our model: since there are only two items available, all trades will just cause you to lose an item. We can prevent that kind of error by adding a guard on trades

[[ TODO ]]

So we need to run this with at least three items. Since vendor arbitrage doesn't matter, we can drop to one vendor to speed up our checks. When we rerun, we get a spec failure:

[[ TODO Talk about challenge extending ]]

