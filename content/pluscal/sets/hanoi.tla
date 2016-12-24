EXTENDS TLC, Tuples, Integers

Headish(seq) == IF DOMAIN seq = {} 
                THEN 99
                ELSE Head(seq)
(* --algorithm towers
variables tower = <<<<1, 2, 3>>, <<>>, <<>>>>;
begin
while TRUE do
    assert tower[3] # <<1, 2, 3>>;

    with x \in DOMAIN tower, y \in (DOMAIN tower) \ {x} do
        if (Len(tower[x]) # 0)
        /\ (Head(tower[x]) < Headish(tower[y])) then
            tower[x] := Tail(tower[x]) ||
            tower[y] := <<Head(tower[x])>> \o tower[y];
        end if;
    end with;
end while;
end algorithm; *)

