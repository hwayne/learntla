---- MODULE api ---- 
EXTENDS Integers, TLC
(* --algorithm api
variables made_calls = 0, max_calls \in 5..10;

macro make_calls(n)
begin
  made_calls := made_calls + n;
  assert made_calls <= max_calls;
end macro;

process get_collection = 0
begin 
  Request:
    make_calls(1);
    either goto Request or skip end either;
end process;

process get_put \in 1..3
begin
  Call:
    with c \in {1, 2} do
      make_calls(c)
    end with;
end process;

end algorithm; *)
====
