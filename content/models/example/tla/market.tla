---- MODULE market ----
EXTENDS Integers
CONSTANTS Items, MaxPrice, Vendors, MaxActions

I == Items
V == Vendors
P == 1..MaxPrice

ValidMarkets == LET Markets == [V \X I -> [buy : P, sell : P]]
                IN {m \in Markets : 
                    \A item \in I, vendors \in V \X V:
                      m[<<vendors[1], item>>].buy <= m[<<vendors[2], item>>].sell
                   }

(* --algorithm market
variables market \in ValidMarkets, 
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
      end either;
      Loop:
        actions := actions + 1;
    end while;
end algorithm; *)

\* Translation

NoArbitrage == profit <= 0
====
