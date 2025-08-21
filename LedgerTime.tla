----------------------------- MODULE LedgerTime -----------------------------

(***************************************************************************)
(* Helper module for time.                                                 *)
(***************************************************************************)

EXTENDS Naturals

VARIABLES
    Time,
    TimeBounds,
    NextChangingTimePoints
    
CONSTANT
    MAX_TIME
    
vars == <<Time, TimeBounds, NextChangingTimePoints>>
    
AdvanceLedgerTime ==
    /\ Time < MAX_TIME
    /\ Time' \in {i \in NextChangingTimePoints \cup {MAX_TIME} :
                            /\ i > Time
                            /\ \A bound \in TimeBounds : bound >= Time => i <= bound
                    }

Init ==
    Time \in 1..MAX_TIME

Next == AdvanceLedgerTime

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

=============================================================================
