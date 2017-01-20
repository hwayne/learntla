variables x = 0;
process one = 1
begin
  A:
    x := x - 1;
  B:
    x := x * 3;
end process

process two = 2
begin
  C:
    x := x + 1;
  D:
    assert x # 0;
end process
