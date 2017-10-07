+++
title = "Introduction"
weight = 1
+++

{{% notice note %}}
*If you want a video introduction, come watch my [Strange Loop talk](https://www.youtube.com/watch?v=_9B__0S21y8) on TLA+!*
{{% /notice %}}
### What is TLA+?

TLA+ is a _formal specification language_. It's a tool to design systems and algorithms, then programmatically verify that those systems don't have critical bugs. It's the software equivalent of a blueprint.

### Why should I use it?

Here's a simple TLA+ specification, representing people trading unique items. Can you find the bug?

```tla
People == {"alice", "bob"}
Items == {"ore", "sheep", "brick"}
(* --algorithm trade
variable owner_of \in [Items -> People]

process giveitem \in 1..3 \* up to three possible trades made
variables item \in Items, 
          owner = owner_of[item], 
          to \in People,
          origin_of_trade \in People
begin Give:
    if origin_of_trade = owner then 
        owner_of[item] := to;
    end if;
end process;
end algorithm; *)
```

Since we check that the owner of an item is the one trading it away. So we should be safe against scams, right? But if we run the model checker, we find that's not true: Alice could trade an item to _herself_ and, before that process finishes running, resolve a parallel trade giving that same item to Bob. Then the first trade resolves and Alice gets the item back. Our algorithm fails for race conditions, and we know this because TLA+ explored every possible state and timeline.

There's a few different ways of fixing this. But does our fix work for more than two people? In TLA+, checking that is as simple as `People == {"alice", "bob", "eve"}`. Does it work if we can trade multiple items at once? `variable items \in SUBSET Items`. What about if there's multiple sheep, ore, and bricks? `amount_owned = [People \X Items -> 0..5]`. What if three people are all trading 1 ore and 1 sheep with each of the other players while Eve also trades Alice 0 brick? If it's in the possible state space, TLA+ will check it.

### Is it hard to use?

Formal methods have a reputation for being difficult to the point where they're only worth it for critical systems. This means that all of the guides are written under the assumption that the reader is working on a critical system, where they have to know TLA+ inside and out to make absolutely that their system won't accidentally _kill people_.

If a dangerous bug to you is "somebody dies", then yes, formal methods are hard. If a dangerous bug to you is "nobody dies but our customers get really mad and we have to spend two weeks tracking down and fixing the bug", then the small subset of TLA+ you'll need is actually pretty easy to learn. Just find a beginner-friendly guide and you're all set.

### Where's a beginner-friendly guide?

HEY
