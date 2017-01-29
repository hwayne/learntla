EXTENDS Integers, TLC
(* --algorithm api
variables made_calls = 0, max_calls \in 5..10;

macro make_calls(n)
begin
    made_calls := made_calls + n;
    assert made_calls <= max_calls;
end macro;

process reset_limit = -1
begin
  Reset:
    while TRUE do
      made_calls := 0;
    end while
end process


process get_collection = 0
variable gc_local = 0;
begin 
  GCGetCalls:
    await made_calls <= max_calls - 1;
    gc_local := made_calls;
  Request:
    make_calls(1);
    either goto GCGetCalls 
    or skip 
    end either;
end process;

process get_put \in 1..3
variable gp_local = 0;
begin
  GPGetCalls:
    await made_calls <= max_calls - 2;
  Call:
    with c \in {1, 2} do
      make_calls(c)
    end with;
end process;

end algorithm; *)
