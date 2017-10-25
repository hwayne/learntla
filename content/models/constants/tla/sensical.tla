IsSensical(state) ==  /\ Len(state) = TSPACES \* Correct spaces
                      /\ \A tower \in DOMAIN state: \* Numbers do not exceed TSIZE
                         \A disc \in DOMAIN state[tower]:
                            state[tower][disc] \in 1..TSIZE
                      /\ \A n \in 1..TSIZE : \* All numbers appear
                         \E tower \in DOMAIN state:
                            \E disc \in DOMAIN state[tower]:
                               n = state[tower][disc] 
\* ...

ASSUME IsSensical(SOLUTION)
