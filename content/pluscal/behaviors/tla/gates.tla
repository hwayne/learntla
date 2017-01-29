---- MODULE flags ----
EXTENDS TLC, Integers
(* --algorithm flags
variables f1 \in BOOLEAN, f2 \in BOOLEAN, f3 \in BOOLEAN
begin
  while TRUE do
    with f \in {f1, f2, f3} do
      either
        f := TRUE;
      or
        f := FALSE;
      end either;
    end with;
  end while;
end algorithm; *)

====
