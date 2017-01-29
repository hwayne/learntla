---- MODULE api ----
EXTENDS Integers, TLC
(* --algorithm api
variables made_calls = 0, max_calls \in 5..10, reserved_calls = 0;


macro make_calls(n) begin
  made_calls := made_calls + n;
  assert made_calls <= max_calls;
end macro;


macro reserve(n) begin
  await made_calls + reserved_calls + n <= max_calls;
  reserved_calls := reserved_calls + n;
end macro

process reset_limit = -1
begin
  Reset:
    while TRUE do
      made_calls := 0;
    end while
end process

process get_collection = 0
begin
  GCGetCalls:
    reserve(1);
  Request:
    make_calls(1);
    reserved_calls := reserved_calls - 1;
    either goto GCGetCalls 
    or skip 
    end either;
end process;

process get_put \in 1..3
begin
  GPGetCalls:
    reserve(2);  
  Call:
    with c \in {1, 2} do
      make_calls(c)
    end with;
    reserved_calls := reserved_calls - 2;
end process;

end algorithm; *)
