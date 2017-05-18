EXTENDS TLC, Integers

(* --algorithm counter
variable x = 0;

fair process counter = "counter"
begin Count:
  while x < 10 do
    x := x + 1;
  end while;
end process;

end algorithm; *)