(* --algorithm foo
variables x = 0;
process cycle \in 1..3
begin
  A:
    x := x + 1;
  B:
    x := 0;
  C:
    assert x /= 2;
end process
end algorithm; *)
