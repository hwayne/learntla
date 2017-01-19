+++
title = "Example: Arbitrage"
weight = 20
+++

Consider a situation where a buyer has access to some number of vendors who buy and sell the same set of items. While each vendor has the exact same inventory, they each buy and sell for a different price; buying at a lower price than they sell, of course. Is there a potential for arbitrage?

To start, we need to specify the data structure we use. The simplest way is to say that for each combination of vendor and item, they have a buy price and a sell price. That suggests a function that maps `Vendor \X Item` tuples to some `[buy |-> X , sell |-> Y]` structure. To provide variance we instead use `[buy : P, sell : P]`; remember, that's the set of all such structures. So each "Market" is a set of vendors and items, and how much they buy and sell that item for each pair.

```
ValidMarkets == [V \X I -> [buy : P, sell : P]]
```

[[ TODO first order arbitrage ]]
{{% code market %}}

We don't care about deadlock, so we can uncheck that as a thing to check and add `NoArbitrage` as an invariant. Try making a model with 2 items, 2 vendors, a max price of 6, and a max actions of 5. Run the model to confirm there are no problems. Finally, add a third vendor and compare the runtimes.

One variant we can make: Right now it doesn't matter how many different types of items you have, because none of the items interact with each other. So it makes sense to test this with only one item. That speeds things up considerably.

[[ TODO etc ]]

### Trades

We can be reasonably confident there are no arbitrage opportunities here. What if we make the specification a little more complex? In addition to having buying items, let's imagine that you can also barter; you can convert some items into other items. To keep the system simple we'll assume you 'lose' quantity here: if you trade away N items, you can get at most N-1 back.

``` tla
ValidTrades == LET Trades == [SUBSET I -> SUBSET I]
               IN { T \in Trades : 
                    \A s \in DOMAIN T :
                      Cardinality(s) > Cardinality(T[s])
                      }
```

This requires us to extend FiniteSets. Note there are some weird cases here: for example, you can trade an item for nothing. However, these are all strictly bad options, so it's only an optimization problem. A big optimization problem, it turns out; With three items, `Trades` is has approximately 16 million elements. So instead we want to do a preoptimization of only mapping sets to individual items.

``` tla
ValidTrades == [{ i \in SUBSET I : Cardinality(i) > 1} -> I]
```
Here's the full code, along with the ability to trade:

{{% code trade %}}

In this one, we're less interested in arbitrage between vendors as we are between trading. If we run the model, it will pass. Looking back, we have a problem with our model: since there are only two items available, all trades will just cause you to lose an item. We can prevent that kind of error by adding a guard on trades:

``` tla
ASSUME ValidTrades # {}
```

So we need to run this with at least three items. Since vendor arbitrage doesn't matter, we can drop to one vendor to speed up our checks. When we rerun, we get a spec failure:

![](img/failure.png)

What happens if the buyer can buy two cheap items and trade for a third expensive item, which they sell back. That's arbitrage for you. Besides the spec failure, there's a couple of interesting points of note. The first is that the smallest error in the spec required four actions on the part of the buyer. If we capped `MaxActions` at 3, we would not have detected the bug. The other is that, at least on my laptop, it took almost two minutes to find the error. If I remove the invariant check, it will take six minutes to explore the whole state space. We can reduce the time by making `Items` a symmetry set, in which case TLC finds the error in a little over 20 seconds. Symmetry sets can be very beneficial, and this is a case where it doesn't change the rigor of your spec.
