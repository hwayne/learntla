CONSTANTS TSIZE, TSPACES

FullTower[n \in 1..TSIZE] == n \* <<1, 2, 3, ...>>
Board[n \in 1..TSPACES] == IF n = 1 THEN FullTower ELSE <<>>  
              
(* --algorithm hanoi
variables tower = Board;

define 
  D == DOMAIN tower
end define;

begin
while TRUE do
  assert tower[TSPACES] # <<1, 2, 3>>;
  \* rest is the same
