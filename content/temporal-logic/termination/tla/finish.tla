EXTENDS TLC, Integers
variable x = 0
begin
  while x < 10 do
    either
       x := x + 1;
    or
       skip;
end either;
end while
