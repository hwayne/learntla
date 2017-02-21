IsSensical(state) == /\ Len(state) = TSPACES \* Correct spaces
                     /\ \A n \in 1..TSIZE : \* All numbers appear
                        \E tower \in DOMAIN state:
                            \E disc \in DOMAIN state[tower]:
                                n = state[tower][disc] 

\* ...

ASSUME IsSensical(SOLUTION)
