EXTENDS Integers, TLC, Sequences

Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE f[elt] + DSum[S \ {elt}]
          IN  DSum[DOMAIN f]

Coins == {"p", "n", "d", "q"}
CoinValue == [p |-> 1, n |-> 7, d |-> 10, q |-> 99]
CV == CoinValue \* DOMAIN CoinValue?
IsExactChange(cents, coins) == CV["p"]*coins["p"] + CV["n"]*coins["n"] + CV["d"]*coins["d"] + CV["q"]*coins["q"] = cents 
ExactChangeSet(cents) == {c \in [Coins -> 0..20] : IsExactChange(cents, c)}
SmallestExactChange(cents) == CHOOSE s \in ExactChangeSet(cents) : \A y \in ExactChangeSet(cents) : Sum(y) >= Sum(s)

(* --algorithm coins
variables coins = [p |-> 0, n |-> 0, d |-> 0, q |-> 0], change \in 10..100,
  order_value = <<"q", "d", "n", "p">>, change_left = change;

begin
  A:
    while ~IsExactChange(change, coins) do
      CoinLoop:
        while change_left >= CV[Head(order_value)] do
          coins[Head(order_value)] := coins[Head(order_value)] + 1;
          change_left := change_left - CV[Head(order_value)];
        end while;
        order_value := Tail(order_value)
    end while;
    assert coins = SmallestExactChange(change);
end algorithm; *)

