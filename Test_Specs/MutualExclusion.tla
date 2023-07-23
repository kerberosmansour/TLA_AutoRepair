---- MODULE MutualExclusion ----

EXTENDS Naturals

CONSTANTS Processes
ASSUME Processes = {1, 2}


VARIABLES state

(* Initial state *)
Init == state = [p \in Processes |-> "n"]

(* The next state action for process p *)
ProcNext(p) ==
    /\ state[p] = "n"
    /\ state' = [state EXCEPT ![p] = "t"]
    \/ /\ state[p] = "t"
       /\ IF \E q \in Processes \ {p} : state[q] = "c"
          THEN state' = [state EXCEPT ![p] = "t"]
          ELSE state' = [state EXCEPT ![p] = "c"]
    \/ /\ state[p] = "c"
       /\ state' = [state EXCEPT ![p] = "n"]

(* The next state action for the entire system *)
Next == \E p \in Processes : ProcNext(p)

(* The specification *)
Spec == Init /\ [][Next]_state

(* Property to check: No two processes can be in the critical section at the same time *)
NoTwoInCritical == ~\E p, q \in Processes : p # q /\ state[p] = "c" /\ state[q] = "c"

=============================================================================