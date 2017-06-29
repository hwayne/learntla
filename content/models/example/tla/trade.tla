---- MODULE market ----
EXTENDS Integers, FiniteSets
CONSTANTS Items, MaxPrice, Vendors, MaxActions

I == Items
V == Vendors
P == 1..MaxPrice

ValidMarkets == LET Markets == [V \X I -> [buy : P, sell : P]]
                IN {m \in Markets :
                    \A item \in I, vendors \in V \X V:
                      m[<<vendors[1], item>>].buy <= m[<<vendors[2], item>>].sell
                   }

ValidTrades == [{ i \in SUBSET I : Cardinality(i) > 1} -> I]

(* --algorithm market
variables market \in ValidMarkets,
          trades \in ValidTrades,
          backpack = {}, \* items we have
          actions = 0,
          profit = 0;

begin
  Act:
    while actions < MaxActions do
      either
        Buy:
          with v \in V, i \in Items \ backpack do
          profit := profit - market[<<v, i>>].sell;
          backpack := backpack \union {i};
          end with;
      or
        Sell:
          with v \in V, i \in backpack do
            profit := profit + market[<<v, i>>].buy;
            backpack := backpack \ {i};
          end with;
      or
        Trade:
          with items \in (SUBSET backpack) \intersect (DOMAIN trades) do
            backpack := (backpack \ items) \union {trades[items]};
          end with;
      end either;
      Loop:
        actions := actions + 1;
    end while;
end algorithm; *)

\* Translation

NoArbitrage == profit <= 0
====
