----------------------------- MODULE SpecComplex -----------------------------

EXTENDS Naturals, Sequences

VARIABLES queue, process

Init == queue = <<>> /\ process = [i \in 1..3 |-> "idle"]

Enqueue ==
    /\ Len(queue) < 5
    /\ queue' = Append(queue, 1)
    /\ UNCHANGED process

Dequeue ==
    /\ \E i \in DOMAIN process:
        /\ process[i] = "idle"
        /\ Len(queue) > 0
        /\ process' = [process EXCEPT ![i] = "busy"]
        /\ queue' = Tail(queue)

Next ==
    \/ Enqueue
    \/ Dequeue

Invariant ==
    /\ Len(queue) <= 5
    /\ \A i \in DOMAIN process: process[i] \in {"idle", "busy"}

SPECIFICATION Init /\ [][Next]_<<queue, process>>
=============================================================================