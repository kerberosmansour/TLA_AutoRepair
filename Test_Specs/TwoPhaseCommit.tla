------------------------- MODULE TwoPhaseCommit -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES RM \* Set of resource managers. You can overwrite this value in the model configuration file.

VARIABLES rmState, tmState, tmPrepared, tmCommitted, tmAborted

TypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
          /\ tmState \in {"init", "prepare", "commit", "abort"}
          /\ tmPrepared \subseteq RM
          /\ tmCommitted \subseteq RM
          /\ tmAborted \subseteq RM

Init == /\ rmState = [r \in RM |-> "working"]
        /\ tmState = "init"
        /\ tmPrepared = {}
        /\ tmCommitted = {}
        /\ tmAborted = {}

\* Transition definitions
Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
              /\ UNCHANGED <<tmState, tmPrepared, tmCommitted, tmAborted>>

Abort(r) == /\ rmState[r] = "prepared"
            /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
            /\ UNCHANGED <<tmState, tmPrepared, tmCommitted, tmAborted>>

Commit(r) == /\ rmState[r] = "prepared"
             /\ rmState' = [rmState EXCEPT ![r] = "committed"]
             /\ UNCHANGED <<tmState, tmPrepared, tmCommitted, tmAborted>>

TmPrepare == /\ tmState = "init"
             /\ tmState' = "prepare"
             /\ UNCHANGED <<rmState, tmPrepared, tmCommitted, tmAborted>>

TmCommit == /\ tmState = "prepare"
            /\ tmPrepared = RM \ tmAborted
            /\ tmState' = "commit"
            /\ UNCHANGED <<rmState, tmPrepared, tmCommitted, tmAborted>>

TmAbort == /\ tmState = "prepare"
           /\ tmAborted /= {}
           /\ tmState' = "abort"
           /\ UNCHANGED <<rmState, tmPrepared, tmCommitted, tmAborted>>

Next == \/ \E r \in RM : Prepare(r)
            \/ \E s \in RM : Abort(s)
           \/ \E t \in RM : Commit(t)
         \/ TmPrepare
         \/ TmCommit
         \/ TmAbort

Invariant == TypeOK

=============================================================================
