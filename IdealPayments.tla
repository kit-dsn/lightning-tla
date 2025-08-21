--------------------------- MODULE IdealPayments ---------------------------

(***************************************************************************)
(* Specification that restricts payments between users: A payment can only *)
(* be marked as processed at the sender of the payment if it already has   *)
(* been marked as processed by the payment's receiver.                     *)
(***************************************************************************)

EXTENDS Integers
VARIABLE Payments
CONSTANTS UserIds, Numbers

Init ==
    /\ \A user \in UserIds :
        Payments[user] \in SUBSET [amount: Numbers,
             sender: UserIds, receiver: UserIds, id: Numbers,
             state: {"NEW", "ABORTED", "PROCESSED"}]
Pay ==
    /\ \A user \in UserIds :
        \/ UNCHANGED Payments[user]
        \/ \E P \in SUBSET {p \in Payments[user] : p.state = "NEW"} : 
            /\ \E r \in [P -> {"ABORTED", "PROCESSED"}] :
                /\ \A p \in P :
                    (r[p] = "PROCESSED" /\ p.sender = user)
                        => \E rp \in Payments'[p.receiver] :
                                rp.id = p.id /\ rp.state = "PROCESSED"
                /\ Payments[user]' = (Payments[user] \ P)
                                        \cup {[p EXCEPT !.state = r[p]] : p \in P}

Spec == Init /\ [][Pay]_Payments
=============================================================================
