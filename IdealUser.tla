----------------------------- MODULE IdealUser -----------------------------

(***************************************************************************)
(* Specification of actions that change a user's state.  Does not depend   *)
(* on other user's.                                                        *)
(***************************************************************************)

EXTENDS Integers, SumAmounts
VARIABLES BlockchainBalance, ChannelBalance,
    Payments, Honest
CONSTANTS UserIds, UserId, InitialPayments, Numbers
ASSUME Numbers \subseteq Int

Init ==
    /\ BlockchainBalance \in Numbers
    /\ ChannelBalance = 0
    /\ Payments = {pmt \in InitialPayments :
                pmt.sender = UserId \/ pmt.receiver = UserId}
    /\ Payments \in SUBSET [amount: Numbers,
                             sender: UserIds, receiver: UserIds, id: Numbers,
                             state: {"NEW", "ABORTED", "PROCESSED"} ]
    /\ Honest \in {TRUE, FALSE}

Deposit ==
    /\ \E amount \in 1..BlockchainBalance :
        /\ BlockchainBalance' = BlockchainBalance - amount
        /\ ChannelBalance' = ChannelBalance + amount
        /\ ChannelBalance' \in Numbers
    /\ UNCHANGED <<Payments, Honest>>
    
Pay ==
    /\ \E P \in SUBSET {pmt \in Payments : pmt.state = "NEW"} :
          \E r \in [P -> {"ABORTED", "PROCESSED"}] :
            /\ Payments' = (Payments \ P)
                                \cup {[p EXCEPT !.state = r[p]] : p \in P}
            /\ LET PP == {p \in P : r[p] = "PROCESSED"}
                   rBal == SumAmounts({p \in PP : p.receiver = UserId})
                   sBal == SumAmounts({p \in PP : p.sender = UserId})
               IN
                    /\ ChannelBalance - sBal >= 0
                    /\ ChannelBalance' = ChannelBalance + rBal - sBal
                    /\ ChannelBalance' >= 0
    /\ UNCHANGED <<Honest, BlockchainBalance>>

Withdraw ==
    /\ BlockchainBalance' \in Numbers
    /\ BlockchainBalance' >= BlockchainBalance
    /\ \E amount \in 0..ChannelBalance :
        /\ ChannelBalance' = ChannelBalance - amount
        /\ Honest => BlockchainBalance' >=
                        BlockchainBalance + amount
    /\ UNCHANGED <<Payments, Honest>>
    
Next ==
    \/ Deposit \/ Pay \/ Withdraw
vars == <<BlockchainBalance, ChannelBalance,
                Payments, Honest>>
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ChannelBalance > 0 /\ Honest /\ Withdraw)   \* Finally, all honest users withdraw their balance.
    \* No other liveness: payments need not be processed and dishonest users might not cheat and be punished
=============================================================================
