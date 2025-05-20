------------------------- MODULE AbstractionHelpers -------------------------

EXTENDS Integers, Naturals, FiniteSets, Sequences, SumAmounts, TLC

CONSTANTS AllSigHashLock, SingleSigHashLock

AllHTLCs(ChannelAliceVars, ChannelBobVars) ==
    ChannelAliceVars.IncomingHTLCs \cup ChannelAliceVars.OutgoingHTLCs \cup ChannelBobVars.IncomingHTLCs \cup ChannelBobVars.OutgoingHTLCs

SeqToSet(seq) ==
  { seq[i] : i \in DOMAIN seq }


IsOpenState(ChannelAliceState, ChannelBobState) ==
    \/ ChannelAliceState \in {"open-funding-pub", "open-new-key-sent", "open-new-key-received"}
    \/ ChannelBobState \in {"open-funding-pub", "open-new-key-sent", "open-new-key-received"}
IsReadyState(ChannelAliceState, ChannelBobState) ==
    /\ ChannelAliceState = "rev-keys-exchanged"
    /\ ChannelBobState = "rev-keys-exchanged"
IsClosedState(ChannelAliceState, ChannelBobState) ==
    ChannelAliceState = "closed" /\ ChannelBobState = "closed"
IsClosingStateAfterCommitHelper(Vars, OtherVars, HTLCHistory, OtherHTLCHistory, LedgerTx) ==
    /\ \A htlc \in Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs :
                htlc.state = "NEW" =>
                    /\ \E otherHTLC \in OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs :
                        /\ otherHTLC.hash = htlc.hash
                        /\ otherHTLC.state # "NEW"
    /\ \A htlc \in Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs :
                htlc.state \in {"NEW", "SENT-COMMIT", "RECV-COMMIT", "PENDING-COMMIT"} =>
                    /\ ~\E tx \in LedgerTx : \E output \in tx.outputs :
                            \E condition \in output.conditions :
                                /\ condition.type = AllSigHashLock
                                /\ htlc.hash = condition.data.hash
    /\ \A htlc \in Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs :
                htlc.state = "ABORTED" =>
                    ~\E otherHTLC \in OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs :
                        /\ otherHTLC.hash = htlc.hash
                        /\  \/ otherHTLC.state = "NEW"
                            \/ otherHTLC.punished
    /\  \/ Vars.HaveCheated
        \/ OtherVars.HaveCheated
        \/ \A htlc \in Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs :
                htlc.state \in {"COMMITTED", "OFF-TIMEDOUT"} /\ htlc.punished = FALSE =>
                    \A otherHTLC \in OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs :
                        otherHTLC.hash = htlc.hash /\ (otherHTLC.state = "PUNISHED" \/ otherHTLC.punished) 
                            =>  /\ \E oHtlcHist \in OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs :
                                    /\ oHtlcHist.hash = htlc.hash
                                    /\ oHtlcHist.reason = "ON-CHAIN-PUNISHED"
                                    /\ oHtlcHist.state \in {"COMMITTED", "OFF-TIMEDOUT", "FULFILLED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE", "PERSISTED"}

IsClosingStateAfterCommit(ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx) ==
    /\ ChannelAliceState \in {"closing", "closed"}
    /\ ChannelBobState \in {"closing", "closed"}
    /\  \/ ~ \E htlc \in AllHTLCs(ChannelAliceVars, ChannelBobVars) : htlc.state \in {"SENT-COMMIT", "RECV-COMMIT", "PENDING-COMMIT"}
        \/  /\ ChannelAliceVars.HaveCheated \/ ChannelAliceDetailVars.HavePunished
            /\ ChannelBobVars.HaveCheated \/ ChannelBobDetailVars.HavePunished
    /\  \/ \E htlcHist \in ChannelAliceHTLCHistory.IncomingHTLCs \cup ChannelAliceHTLCHistory.OutgoingHTLCs \cup ChannelBobHTLCHistory.IncomingHTLCs \cup ChannelBobHTLCHistory.OutgoingHTLCs : 
                htlcHist.afterOnChainCommit = TRUE
        \/  /\ IsClosingStateAfterCommitHelper(ChannelAliceVars, ChannelBobVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx)
            /\ IsClosingStateAfterCommitHelper(ChannelBobVars, ChannelAliceVars, ChannelBobHTLCHistory, ChannelAliceHTLCHistory, LedgerTx)
    /\ ~IsClosedState(ChannelAliceState, ChannelBobState)
IsClosingStateAfterFulfill(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory) ==
    /\ IsClosingStateAfterCommit(ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx)
    /\  /\  \E htlc \in ChannelAliceHTLCHistory.IncomingHTLCs \cup ChannelAliceHTLCHistory.OutgoingHTLCs :
                /\ htlc.reason \in {"ON-CHAIN-PERSISTED"}
                /\ \E bobHTLC \in ChannelBobHTLCHistory.IncomingHTLCs \cup ChannelBobHTLCHistory.OutgoingHTLCs :
                    /\ bobHTLC.hash = htlc.hash
                    /\ bobHTLC.reason \in {"ON-CHAIN-PERSISTED"}
                    /\  \/  /\ ~htlc.afterHavePunished
                            /\ ~bobHTLC.afterHavePunished
                        \/  \E tx \in LedgerTx :
                                /\ \E input \in tx.inputs : 
                                    /\ "preimage" \in DOMAIN input.witness
                                    /\ htlc.hash = input.witness.preimage
                                /\ \A output \in tx.outputs :
                                    /\ Cardinality(output.conditions) = 1
    /\ ~IsClosedState(ChannelAliceState, ChannelBobState)
IsPreClosingState(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory) ==
    /\  \/ ChannelAliceState \in {"closing", "closed"}
        \/ ChannelBobState \in {"closing", "closed"}
    /\ ~IsClosingStateAfterCommit(ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx)
    /\ ~IsClosingStateAfterFulfill(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
    /\ ~IsClosedState(ChannelAliceState, ChannelBobState)
IsOpeningState(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory) ==
    /\ \/ ChannelAliceState \in {"open-sent-accept-channel", "open-sent-open-channel", "open-funding-created", "open-sent-commit", "open-sent-commit-funder", "open-recv-commit"}
       \/ ChannelBobState \in {"open-sent-accept-channel", "open-sent-open-channel", "open-funding-created", "open-sent-commit", "open-sent-commit-funder", "open-recv-commit"}
    /\ ~IsOpenState(ChannelAliceState, ChannelBobState)
    /\ ~IsClosedState(ChannelAliceState, ChannelBobState)
    /\ ~IsPreClosingState(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
    /\ ~IsClosingStateAfterCommit(ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx)
    /\ ~IsClosingStateAfterFulfill(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
IsUpdatingState(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory) ==
    /\ ~IsClosingStateAfterCommit(ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx)
    /\ ~IsClosingStateAfterFulfill(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
    /\ ~IsPreClosingState(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
    /\ LET updatingStates == {"update-commitment-signed", "update-commitment-received", "update-commitment-signed-received"}
       IN \/ ChannelAliceState \in updatingStates
          \/ ChannelBobState \in updatingStates 

HTLCMutuallyOffChainPersisted(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages) ==
    \/ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason = "OFF-CHAIN-PERSISTED"
        /\ ~\E newerHtlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                /\ newerHtlcHist.hash = htlcHist.hash
                /\ newerHtlcHist.index > htlcHist.index
                /\ newerHtlcHist.reason # "FINALLY-PUNISHED"
    \/  /\  \/ htlcData.state = "SENT-REMOVE"
            \/  /\ htlcData.state = "PUNISHED"
                /\ \E htlcHist \in HTLCHistory.OutgoingHTLCs :
                    /\ htlcHist.hash = htlcData.hash
                    /\ htlcHist.reason = "ON-CHAIN-PUNISHED"
                    /\ htlcHist.state = "SENT-REMOVE"
        /\ \E oHtlcHist \in OtherHTLCHistory.IncomingHTLCs :
                            /\ oHtlcHist.hash = htlcData.hash
                            /\ oHtlcHist.reason = "OFF-CHAIN-PERSISTED"
        /\  \/ \E msg \in SeqToSet(Messages) : msg.recipient = MyName /\ msg.type = "RevokeAndAck"
            \/ htlcData.hash \in DetailVars.AbortedMustBePunishedHTLCs
    \/  /\ htlcData.state = "PERSISTED"
        /\ \E oHtlcHist \in OtherHTLCHistory.IncomingHTLCs :
                /\ oHtlcHist.hash = htlcData.hash
                /\ oHtlcHist.reason = "OFF-CHAIN-PERSISTED"
                
HTLCMutuallyOffChainTimedout(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages) ==
    \/ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason = "OFF-CHAIN-TIMEDOUT"
        /\ ~htlcHist.afterClosingTimeSet
        /\ ~\E newerHtlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                /\ newerHtlcHist.hash = htlcHist.hash
                /\ newerHtlcHist.index > htlcHist.index
                /\ newerHtlcHist.reason # "FINALLY-PUNISHED"
        /\  \/ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
                /\ oHtlcHist.hash = htlcData.hash
                /\ oHtlcHist.reason = "OFF-CHAIN-TIMEDOUT"
                /\ ~oHtlcHist.afterClosingTimeSet
                /\ ~\E newerHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
                        /\ newerHtlcHist.hash = oHtlcHist.hash
                        /\ newerHtlcHist.index > oHtlcHist.index
                        /\ newerHtlcHist.reason # "FINALLY-PUNISHED"
                
HTLCMutuallyOnChainPersisted(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx) ==
    /\  \/ htlcData.state = "PERSISTED"
        \/  /\ htlcData.state = "PUNISHED"
            /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                /\ htlcHist.hash = htlcData.hash
                /\ htlcHist.reason = "FINALLY-PUNISHED"
                /\ htlcHist.state = "PERSISTED"
    /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
        /\ ~(htlcHist.state \in {"PENDING-REMOVE", "RECV-REMOVE", "PUNISHED"})
        /\ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
            /\ oHtlcHist.hash = htlcData.hash
            /\ oHtlcHist.reason = "ON-CHAIN-PERSISTED"
            /\ ~(oHtlcHist.state \in {"PENDING-REMOVE", "RECV-REMOVE", "PUNISHED"})
            /\ \/ htlcHist.state \notin {"FULFILLED", "SENT-REMOVE"}
               \/ oHtlcHist.state \notin {"FULFILLED", "SENT-REMOVE"}
    
HTLCWillBePunished(htlcData, LedgerTx, ChannelAliceDetailVars, AliceInventory, BobInventory, Messages, UserA, UserB, AllSignatures) ==
    /\ \E ctx \in LedgerTx : 
        /\ \E input \in ctx.inputs :
            input.parentId = ChannelAliceDetailVars.fundingTxId
        /\ \E htlcTx \in LedgerTx :
            /\ \E input \in htlcTx.inputs :
                /\ input.parentId = ctx.id
                /\ "preimage" \in DOMAIN input.witness
                /\ htlcData.hash = input.witness.preimage
            /\ \E output \in htlcTx.outputs :
                \E condition \in output.conditions :
                    /\ condition.type = AllSignatures
                    /\  \/ condition.data.keys \in SUBSET(AliceInventory.keys \cup { msg.data.rSecretKey : msg \in {msg \in SeqToSet(Messages) : msg.recipient = UserA}})
                        \/ condition.data.keys \in SUBSET(BobInventory.keys \cup { msg.data.rSecretKey : msg \in {msg \in SeqToSet(Messages) : msg.recipient = UserB}})
    
HTLCMutuallyOnChainPersistedAfterFulfill(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, AliceInventory, BobInventory, Messages, UserA, UserB, AllSignatures) ==
    /\  \/ htlcData.state = "PERSISTED"
        \/  /\ htlcData.state = "PUNISHED"
            /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                /\ htlcHist.hash = htlcData.hash
                /\ htlcHist.reason = "FINALLY-PUNISHED"
                /\ htlcHist.state = "PERSISTED"
    /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
        /\ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
            /\ oHtlcHist.hash = htlcData.hash
            /\ oHtlcHist.reason = "ON-CHAIN-PERSISTED"
    /\ ~HTLCWillBePunished(htlcData, LedgerTx, ChannelAliceDetailVars, AliceInventory, BobInventory, Messages, UserA, UserB, AllSignatures)
    /\ IsClosingStateAfterFulfill(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory)

HTLCMutuallyOnChainFulfilled(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars) ==
    /\  \/ htlcData.state = "PERSISTED"
        \/  /\ htlcData.state = "PUNISHED"
            /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                /\ htlcHist.hash = htlcData.hash
                /\ htlcHist.reason = "FINALLY-PUNISHED"
                /\ htlcHist.state = "PERSISTED"
    /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
        /\  \/ ~(htlcHist.state \in {"PENDING-REMOVE", "RECV-REMOVE", "PUNISHED"})
            \/ ~htlcHist.fulfilled
        /\ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
            /\ oHtlcHist.hash = htlcData.hash
            /\ oHtlcHist.reason = "ON-CHAIN-PERSISTED"
            /\  \/ ~(oHtlcHist.state \in {"PENDING-REMOVE", "RECV-REMOVE", "PUNISHED"})
                \/ ~oHtlcHist.fulfilled
            /\  \/  /\ ~htlcHist.afterHavePunished
                    /\ ~oHtlcHist.afterHavePunished
                \/ \E tx \in LedgerTx :
                    /\ \E input \in tx.inputs : 
                        /\ "preimage" \in DOMAIN input.witness
                        /\ htlcData.hash = input.witness.preimage
                    /\ \A output \in tx.outputs :
                        /\ Cardinality(output.conditions) = 1
    /\ IsClosingStateAfterFulfill(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory)

HTLCMutuallyOnChainCommitted(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, LedgerTx) ==
    /\ \/ htlcData.state = "COMMITTED"
       \/ htlcData.state = "TIMEDOUT"
       \/ htlcData.state = "PERSISTED"
       \/   /\ htlcData.state = "PUNISHED"
            /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                /\ htlcHist.hash = htlcData.hash
                /\ htlcHist.reason = "FINALLY-PUNISHED"
                /\ htlcHist.state \in {"COMMITTED", "TIMEDOUT", "PERSISTED"}
    /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason \in {"ON-CHAIN-COMMITTED", "COMMITTED", "ON-CHAIN-TIMEDOUT"}
        /\ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
            /\ oHtlcHist.hash = htlcData.hash
            /\ oHtlcHist.reason \in {"ON-CHAIN-COMMITTED", "COMMITTED", "ON-CHAIN-TIMEDOUT"}
            /\ "ON-CHAIN-COMMITTED" \in {htlcHist.reason, oHtlcHist.reason}
    /\ ChannelAliceState \in {"closing", "closed"}
    /\ ChannelBobState \in {"closing", "closed"}
    /\ IsClosingStateAfterCommit(ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)

HTLCMutuallyOffChainCommitted(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory) ==
    /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason \in {"COMMITTED"}
        /\ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
            /\ oHtlcHist.hash = htlcData.hash
            /\ oHtlcHist.reason \in {"COMMITTED"}
            
HTLCWasOffChainThenOnChainFulfilled(htlcData, HTLCHistory, OtherHTLCHistory, MyName, Messages) ==
    /\ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
        /\ oHtlcHist.hash = htlcData.hash
        /\ oHtlcHist.reason = "ON-CHAIN-PERSISTED"
        /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
            /\ htlcHist.hash = htlcData.hash
            /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
            /\  \/ oHtlcHist.fulfilled
                \/ htlcHist.fulfilled
    /\ ~\E msg \in SeqToSet(Messages) :
        /\ msg.recipient = MyName
        /\ msg.type = "HTLCPreimage"
        /\ msg.data.preimage = htlcData.hash
        
HTLCWasOnChainFulfilledBeforeOnChainCommit(htlc, Vars, HTLCHistory, OtherHTLCHistory) ==
    /\ htlc.fulfilled
    /\  \/  /\ htlc \in Vars.OutgoingHTLCs
            /\ \E htlcHist \in HTLCHistory.OutgoingHTLCs :
                /\ htlcHist.hash = htlc.hash
                /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
                /\ htlcHist.fulfilled = FALSE
            /\ \E oHtlcHist \in OtherHTLCHistory.IncomingHTLCs :
                /\ oHtlcHist.hash = htlc.hash
                /\ oHtlcHist.reason = "ON-CHAIN-PERSISTED"
        \/  /\ htlc \in Vars.IncomingHTLCs
            /\ \E htlcHist \in HTLCHistory.IncomingHTLCs :
                /\ htlcHist.hash = htlc.hash
                /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
                /\ htlcHist.fulfilled = FALSE
            /\ \E oHtlcHist \in OtherHTLCHistory.OutgoingHTLCs :
                /\ oHtlcHist.hash = htlc.hash
                /\ oHtlcHist.reason = "ON-CHAIN-PERSISTED"
        
OnChainFullfilledHTLCsBeforeCommit(Vars, HTLCHistory, OtherHTLCHistory) ==
    {htlc \in Vars.OutgoingHTLCs : HTLCWasOnChainFulfilledBeforeOnChainCommit(htlc, Vars, HTLCHistory, OtherHTLCHistory)}

RECURSIVE HTLCWasAddedDuringThisUpdate(_, _, _, _, _, _, _, _, _, _, _, _, _)
HTLCWasAddedDuringThisUpdate(htlc, DetailVars, OtherDetailVars, Vars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, MyName, OtherName, Messages, LedgerTx) ==
    /\ ~HTLCMutuallyOffChainCommitted(htlc, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory)
    /\ LET htlcState == IF htlc.state = "PUNISHED"
                        THEN (CHOOSE htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs : htlcHist.hash = htlc.hash /\ htlcHist.reason = "FINALLY-PUNISHED").state
                        ELSE htlc.state
       IN \/ htlcState \in {"SENT-COMMIT", "RECV-COMMIT", "PENDING-COMMIT"}
          \/    /\ htlcState \in {"COMMITTED", "FULFILLED", "PERSISTED", "TIMEDOUT"}
                /\ Cardinality({otherHtlc \in (OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs \cup OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
                        /\ otherHtlc.hash = htlc.hash
                        /\ otherHtlc.state \notin {"COMMITTED", "OFF-TIMEDOUT"}
                        /\ ~otherHtlc.state \in {"FULFILLED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE", "PERSISTED", "TIMEDOUT", "PUNISHED"}
                        /\ "reason" \in DOMAIN otherHtlc => otherHtlc.reason # "COMMITTED"
                       }) > 0
                /\ ~\E htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs :
                    /\ htlcHist.hash = htlc.hash
                    /\  \/ htlcHist.reason \in {"ON-CHAIN-COMMITTED", "ON-CHAIN-TIMEDOUT"}
                        \/  /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
                            /\ htlcHist.afterHavePunished = TRUE
          \/    /\ htlcState = "COMMITTED"
                /\ Cardinality({htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                        /\ htlcHist.hash = htlc.hash
                        /\ \/ /\ htlcHist.reason = "ON-CHAIN-COMMITTED"
                           \/ /\ htlcHist.reason = "ON-CHAIN-TIMEDOUT"
                        /\  \/ ~\E otherHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
                                /\ otherHtlcHist.hash = htlc.hash
                                /\ otherHtlcHist.reason \in {"ON-CHAIN-COMMITTED", "ON-CHAIN-TIMEDOUT"}
                            \/ ~IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                        /\  \/ ~\E otherHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
                                /\ otherHtlcHist.hash = htlc.hash
                                /\ otherHtlcHist.reason \in {"COMMITTED"}
                            \/ ~\E myHtlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                                /\ myHtlcHist.hash = htlc.hash
                                /\ myHtlcHist.reason \in {"COMMITTED"}
                       }) > 0
          \/ 
                /\ htlcState = "PERSISTED"
                /\ \E  htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                                /\ htlcHist.hash = htlc.hash
                                /\ htlcHist.reason \in {"ON-CHAIN-PERSISTED"}
                /\ ~IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                /\ ~HTLCMutuallyOffChainCommitted(htlc, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory)
                /\ ~HTLCWasOnChainFulfilledBeforeOnChainCommit(htlc, Vars, HTLCHistory, OtherHTLCHistory)
    /\ ~HTLCMutuallyOnChainFulfilled(htlc, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, MyPCState, OtherPCState, Vars, OtherVars)
    /\ ~HTLCMutuallyOnChainCommitted(htlc, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, MyPCState, OtherPCState, Vars, OtherVars, LedgerTx)
    
HTLCAddedAndPersistedDuringThisUpdate(htlcData, DetailVars, OtherDetailVars, Vars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, MyName, OtherName, Messages, LedgerTx) ==
    /\  \/ htlcData.state = "PERSISTED"
        \/  /\ htlcData.state = "PUNISHED"
            /\ \E htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs :
                /\ htlcHist.hash = htlcData.hash
                /\ htlcHist.reason = "ON-CHAIN-PUNISHED"
                /\ htlcHist.state = "PERSISTED"
    /\ ~\E htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs :
        /\ htlcHist.hash = htlcData.hash
        /\ htlcHist.reason = "ON-CHAIN-COMMITTED"
    /\ LET htlcHists == { htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs :
                                    /\ htlcHist.hash = htlcData.hash
                                    /\ ~htlcHist.reason \in {"COMMITTED"}
                                    /\ htlcHist.state # "PUNISHED"
                                    /\ htlcHist.state # "PERSISTED"
                                    /\ ("reason" \in DOMAIN htlcData => htlcHist.reason # "ON-CHAIN-PUNISHED")
                        }
           htlcHist == CHOOSE h \in htlcHists : \A oH \in htlcHists : h.index >= oH.index
       IN HTLCWasAddedDuringThisUpdate(htlcHist, DetailVars, OtherDetailVars, Vars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, MyName, OtherName, Messages, LedgerTx)
    /\ ~IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
        
HTLCWasPersistedDuringThisUpdate(htlc, DetailVars, OtherDetailVars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory) ==
    \/ htlc.state \in {"SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}
    \/  /\  \/ htlc.state = "PERSISTED"
            \/ htlc.state = "TIMEDOUT"
            \/  /\ htlc.state = "PUNISHED"
                /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                    /\ htlcHist.hash = htlc.hash
                    /\ htlcHist.reason = "FINALLY-PUNISHED"
                    /\ htlcHist.state = "PERSISTED"
        /\ \E otherHtlc \in (OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs) :
                        /\ otherHtlc.hash = htlc.hash
                        /\  \/ /\ otherHtlc.state # "PERSISTED"
                               /\ otherHtlc.state = "PUNISHED" => ~ (\E otherHTLCHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) : otherHTLCHist.hash = otherHtlc.hash /\ otherHTLCHist.state = "PERSISTED") 
                            \/ /\ \E htlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
                                    /\ htlcHist.hash = htlc.hash
                                    /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
                                    /\ htlcHist.state \in {"FULFILLED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}
                                    /\ htlcHist.fulfilled
                            \/  /\ \E otherHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) : \* such an HTLC will be punished
                                    /\ otherHtlcHist.hash = htlc.hash
                                    /\ otherHtlcHist.reason = "ON-CHAIN-TIMEDOUT"
                            \/  /\ \E otherHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) : \* such an HTLC will be punished
                                    /\ otherHtlcHist.hash = htlc.hash
                                    /\ otherHtlcHist.reason = "ON-CHAIN-PERSISTED"
                                    /\ otherHtlcHist.timedout
                                    /\ otherHtlcHist.afterHavePunished \/ OtherVars.HaveCheated
                            \/  /\ \E oHtlcHist \in (OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs) :
                                    /\ oHtlcHist.hash = htlc.hash
                                    /\ oHtlcHist.reason \in {"ON-CHAIN-PERSISTED", "OFF-CHAIN-PERSISTED"}
                                    /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                                        /\ htlcHist.hash = htlc.hash
                                        /\ htlcHist.reason \in {"ON-CHAIN-PERSISTED", "OFF-CHAIN-PERSISTED"}
                                        /\  \/  /\ "OFF-CHAIN-PERSISTED" \in {htlcHist.reason, oHtlcHist.reason}
                                                /\ \/ "ON-CHAIN-PERSISTED" \in {htlcHist.reason, oHtlcHist.reason} \* if both are off-chain that this was an update
                                                   \/ htlcHist.afterOnChainCommit = TRUE \/ oHtlcHist.afterOnChainCommit = TRUE
                                            \/  /\ {htlcHist.reason, oHtlcHist.reason} = {"ON-CHAIN-PERSISTED"}
                                                /\ "COMMITTED" \in {htlcHist.state, oHtlcHist.state}
                                                /\  /\ htlcHist.afterHavePunished \/ oHtlcHist.afterHavePunished 

IncomingHTLCsFulfilledDuringClosing(DetailVars, Vars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, LedgerTx, Payments, ChannelAliceState, ChannelBobState) ==
    {htlc \in HTLCHistory.IncomingHTLCs : /\ htlc.reason = "ON-CHAIN-PERSISTED"
                                          /\ ~htlc.fulfilled
                                          /\ ~\E pmt \in Payments : pmt.id = htlc.id
                                          /\ ~\E tx \in LedgerTx : \E input \in tx.inputs :
                                                /\ "preimage" \in DOMAIN input.witness
                                                /\ input.witness.preimage = htlc.hash
                                          /\ ~\E htlcData \in Vars.IncomingHTLCs :
                                                /\ htlcData.hash = htlc.hash
                                                /\  \/ HTLCMutuallyOnChainFulfilled(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, ChannelAliceState, ChannelBobState, Vars, OtherVars)
                                                    \/ HTLCWasOnChainFulfilledBeforeOnChainCommit(htlcData, Vars, HTLCHistory, OtherHTLCHistory)
    }
OutgoingHTLCsFulfilledDuringClosing(DetailVars, Vars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, LedgerTx, ChannelAliceState, ChannelBobState) ==
    {htlc \in HTLCHistory.OutgoingHTLCs : /\ htlc.reason = "ON-CHAIN-PERSISTED"
                                          /\ ~htlc.fulfilled
                                          /\ htlc.state = "PUNISHED" => ~\E htlcHist \in HTLCHistory.OutgoingHTLCs : 
                                                        /\ htlcHist.hash = htlc.hash
                                                        /\ htlcHist.reason = "ON-CHAIN-PUNISHED"
                                                        /\ htlcHist.state \in {"SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE","FULFILLED"}
                                          /\ ~\E htlcData \in Vars.OutgoingHTLCs :
                                                /\ htlcData.hash = htlc.hash
                                                /\ HTLCMutuallyOnChainFulfilled(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, ChannelAliceState, ChannelBobState, Vars, OtherVars)
     }
OutgoingHTLCsTimedoutDuringClosing(DetailVars, Vars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, ChannelAliceState, ChannelBobState, LedgerTx) ==
    {htlc \in HTLCHistory.OutgoingHTLCs : /\    \/ htlc.reason \in {"ON-CHAIN-TIMEDOUT"}
                                                \/  /\ htlc.reason = "OFF-CHAIN-TIMEDOUT"
                                                    /\ htlc.afterClosingTimeSet
                                          /\    \/  /\ htlc.state \in {"COMMITTED", "OFF-TIMEDOUT"}
                                                    /\  \/ HTLCMutuallyOnChainCommitted(htlc, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, ChannelAliceState, ChannelBobState, Vars, OtherVars, LedgerTx)
                                                        \/ HTLCMutuallyOffChainCommitted(htlc, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory)
                                                \/  /\ htlc.state \in {"FULFILLED", "PENDING-REMOVE", "SENT-REMOVE", "RECV-REMOVE"}
                                          /\ ~\E oHtlc \in Vars.OutgoingHTLCs :
                                                /\ oHtlc.hash = htlc.hash
                                                /\ oHtlc.state = "PERSISTED"
                                                /\ oHtlc.punished = FALSE
                                          /\ ~\E oHtlc \in HTLCHistory.OutgoingHTLCs :
                                                /\ oHtlc.hash = htlc.hash
                                                /\ oHtlc.state = "PERSISTED"
                                                /\ oHtlc.punished = FALSE
                                                /\ oHtlc.reason = "FINALLY-PUNISHED"
    }
IncomingHTLCsTimedoutDuringClosing(DetailVars, Vars, OtherDetailVars, HTLCHistory, OtherHTLCHistory) ==
    {htlc \in HTLCHistory.IncomingHTLCs : /\ htlc.reason = "ON-CHAIN-TIMEDOUT"
                                          /\ htlc.fulfilled
                                          /\ ~\E htlcHist \in HTLCHistory.IncomingHTLCs :
                                                /\ htlcHist.hash = htlc.hash
                                                /\ htlcHist.index > htlc.index
                                                /\ htlcHist.reason # "FINALLY-PUNISHED"
    }

HTLCsPunishedByMeDuringClosing(PreimageInventory, Vars, DetailVars, HTLCHistory) ==
    {htlcHist \in HTLCHistory.IncomingHTLCs :
        /\ htlcHist.latestCommitmentTXId = DetailVars.LatestCommitTransactionId
        /\ htlcHist.state # "NEW"
        /\ htlcHist.reason = "ON-CHAIN-PUNISHED"
        /\ \E htlc \in Vars.IncomingHTLCs : htlc.hash = htlcHist.hash /\ htlc.punished
        /\ ~Vars.HaveCheated
        /\ ~(htlcHist.hash \in PreimageInventory /\ htlcHist.hash \in Vars.OtherKnownPreimages)
        /\ ~\E oHtlcHist \in HTLCHistory.IncomingHTLCs : oHtlcHist.hash = htlcHist.hash /\ oHtlcHist.index > htlcHist.index /\ oHtlcHist.reason = "OFF-CHAIN-PERSISTED"
        }
    \cup
    {htlcHist \in HTLCHistory.OutgoingHTLCs :
        /\ htlcHist.latestCommitmentTXId = DetailVars.LatestCommitTransactionId
        /\ htlcHist.state # "NEW"
        /\ htlcHist.reason = "ON-CHAIN-PUNISHED"
        /\ \E htlc \in Vars.OutgoingHTLCs : htlc.hash = htlcHist.hash /\ htlc.punished
        /\ ~Vars.HaveCheated
        /\ ~\E oHtlcHist \in HTLCHistory.OutgoingHTLCs : oHtlcHist.hash = htlcHist.hash /\ oHtlcHist.index > htlcHist.index /\ oHtlcHist.reason = "OFF-CHAIN-PERSISTED"
        }
HTLCsPunishedByOtherDuringClosing(PreimageInventory, Vars, DetailVars, HTLCHistory) ==
    {htlc \in HTLCHistory.IncomingHTLCs :
        /\ htlc.latestCommitmentTXId = DetailVars.LatestCommitTransactionId
        /\ htlc.reason = "ON-CHAIN-PUNISHED"
        /\ Vars.HaveCheated
        /\ (htlc.hash \in PreimageInventory /\ htlc.hash \in Vars.OtherKnownPreimages)
        }
    \cup
    {htlcHist \in HTLCHistory.OutgoingHTLCs :
        /\ htlcHist.latestCommitmentTXId = DetailVars.LatestCommitTransactionId
        /\ htlcHist.state \in {"TIMEDOUT"}
        /\ htlcHist.reason = "ON-CHAIN-PUNISHED"
        /\ \E htlc \in Vars.OutgoingHTLCs : htlc.hash = htlcHist.hash /\ htlc.punished
        /\ Vars.HaveCheated }
        
OffChainThenOnChainFulfilledHTLCs(OtherHTLCHistory, MyName, Messages) ==
    {htlc.hash : htlc \in {htlc \in OtherHTLCHistory.IncomingHTLCs :
                /\ htlc.reason = "ON-CHAIN-PERSISTED"
                /\ htlc.state \in {"FULFILLED", "RECV-REMOVE", "PENDING-REMOVE", "SENT-REMOVE"}
                /\ htlc.fulfilled
                /\ ~\E msg \in SeqToSet(Messages) : msg.recipient = MyName /\ msg.type = "HTLCPreimage" /\ msg.data.preimage = htlc.hash}}
                
RECURSIVE RefinementMappingForHTLCData(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _)
RefinementMappingForHTLCData(htlcData, MyName, OtherName, PreimageInventory, Payments, Vars, DetailVars, OtherDetailVars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, Messages, LedgerTx, ChannelAliceDetailVars, AliceInventory, BobInventory, UserA, UserB, AllSignatures) ==
    [htlcData EXCEPT !.state = IF \/ /\ HTLCWasAddedDuringThisUpdate([htlcData EXCEPT !.state = IF htlcData.punished THEN "PUNISHED" ELSE @], DetailVars, OtherDetailVars, Vars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, MyName, OtherName, Messages, LedgerTx)
                                     /\ ~ ( /\ \E htlc \in Vars.IncomingHTLCs :
                                                /\ htlc.hash = htlcData.hash /\ htlc.fulfilled
                                                /\ \E tx \in LedgerTx : \E input \in tx.inputs :
                                                    /\ "preimage" \in DOMAIN input.witness
                                                    /\ input.witness.preimage = htlc.hash
                                           )
                                  \/ /\ @ \in {"ABORTED"}
                                     /\ \/ ~IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                                        \/ "reason" \in DOMAIN htlcData /\ htlcData.reason = "ON-CHAIN-PUNISHED"
                                        \/  /\ OtherDetailVars.HavePunished \/ OtherVars.HaveCheated
                                            /\ \E htlc \in OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs :
                                                    /\ htlc.hash = htlcData.hash
                                                    /\ htlc.state # "ABORTED"
                                        \/ \E oHtlcHist \in OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs :
                                            /\ oHtlcHist.hash = htlcData.hash
                                            /\ oHtlcHist.reason \in {"COMMITTED"}
                               THEN IF  /\ IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                                        /\  \/ ~\E htlc \in OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs :
                                                    /\ htlc.hash = htlcData.hash
                                            \/ Vars.HaveCheated \/ OtherVars.HaveCheated
                                        /\ ~\E tx \in LedgerTx : \E output \in tx.outputs :
                                                \E condition \in output.conditions :
                                                    /\ condition.type \in {AllSigHashLock, SingleSigHashLock}
                                                    /\ htlcData.hash = condition.data.hash
                                    THEN
                                        "ABORTED"
                                    ELSE "NEW"
                               ELSE IF /\ @ \in {"PERSISTED", "TIMEDOUT", "PUNISHED"} \/ htlcData.punished 
                                       /\ ~ HTLCMutuallyOnChainFulfilled(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, MyPCState, OtherPCState, Vars, OtherVars)
                                       /\ ~ HTLCMutuallyOffChainPersisted(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages)
                                       /\ ~ HTLCMutuallyOffChainTimedout(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages)
                                       /\ @ = "PERSISTED" =>
                                            ~IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                                       /\ @ = "PUNISHED" /\ (\E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                                            /\ htlcHist.hash = htlcData.hash
                                            /\ htlcHist.reason = "FINALLY-PUNISHED"
                                            /\ htlcHist.state = "PERSISTED")  =>
                                                ~IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                                       /\ "reason" \in DOMAIN htlcData => htlcData.reason = "FINALLY-PUNISHED" \/ htlcData.reason = "ON-CHAIN-PUNISHED"
                                       /\ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                                                /\ htlcHist.hash = htlcData.hash
                                                /\ ~htlcHist.reason \in {"COMMITTED", "OFF-CHAIN-PERSISTED"}
                                                /\ htlcHist.state # "PUNISHED"
                                                /\ "reason" \in DOMAIN htlcData => htlcHist.reason # "ON-CHAIN-PUNISHED"
                                    THEN IF /\  \/ HTLCWasOffChainThenOnChainFulfilled(htlcData, HTLCHistory, OtherHTLCHistory, MyName, Messages)
                                                \/ HTLCWasOnChainFulfilledBeforeOnChainCommit(htlcData, Vars, HTLCHistory, OtherHTLCHistory)
                                         THEN
                                            "PERSISTED"
                                         ELSE 
                                         LET htlcHists == { htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs : htlcHist.hash = htlcData.hash /\ ~htlcHist.reason \in {"COMMITTED", "OFF-CHAIN-PERSISTED"} /\ htlcHist.state # "PUNISHED" /\ ("reason" \in DOMAIN htlcData => htlcHist.reason # "FINALLY-PUNISHED")}
                                             htlcHist == CHOOSE h \in htlcHists : \A oH \in htlcHists : oH.reason = "FINALLY-PUNISHED2" \/ h.index >= oH.index
                                             state == RefinementMappingForHTLCData(htlcHist, MyName, OtherName, PreimageInventory, Payments, Vars, DetailVars, OtherDetailVars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, Messages, LedgerTx, ChannelAliceDetailVars, AliceInventory, BobInventory, UserA, UserB, AllSignatures).state
                                         IN
                                            IF state = "COMMITTED" /\ htlcData.timedout
                                            THEN "OFF-TIMEDOUT"
                                            ELSE IF /\ state \in {"COMMITTED", "FULFILLED", "OFF-TIMEDOUT"}
                                                    /\ \E htlc \in Vars.IncomingHTLCs :
                                                        /\ htlc.hash = htlcData.hash /\ htlc.fulfilled
                                                        /\ \E tx \in LedgerTx : \E input \in tx.inputs :
                                                            /\ "preimage" \in DOMAIN input.witness
                                                            /\ input.witness.preimage = htlc.hash
                                            THEN "PERSISTED"
                                            ELSE state
                               ELSE IF /\ HTLCWasPersistedDuringThisUpdate(htlcData, DetailVars, OtherDetailVars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory)
                                       /\ ~ HTLCMutuallyOnChainFulfilled(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, MyPCState, OtherPCState, Vars, OtherVars)
                                       /\ ~ HTLCMutuallyOffChainPersisted(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages)
                                       /\ ~ HTLCMutuallyOffChainTimedout(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages)
                                       /\ ~ HTLCMutuallyOnChainPersistedAfterFulfill(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, MyPCState, OtherPCState, Vars, OtherVars, ChannelAliceDetailVars, AliceInventory, BobInventory, Messages, UserA, UserB, AllSignatures)
                                    THEN IF /\  \/ HTLCWasOffChainThenOnChainFulfilled(htlcData, HTLCHistory, OtherHTLCHistory, MyName, Messages)
                                                \/ HTLCWasOnChainFulfilledBeforeOnChainCommit(htlcData, Vars, HTLCHistory, OtherHTLCHistory)
                                                \/  /\ \E htlc \in Vars.IncomingHTLCs :
                                                        /\ htlc.hash = htlcData.hash /\ htlc.fulfilled
                                                        /\ \E tx \in LedgerTx : \E input \in tx.inputs :
                                                            /\ "preimage" \in DOMAIN input.witness
                                                            /\ input.witness.preimage = htlc.hash
                                         THEN
                                            "PERSISTED"
                                         ELSE IF /\ HTLCMutuallyOnChainPersisted(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, MyPCState, OtherPCState, Vars, OtherVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                                                 /\ IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                                         THEN
                                            IF  \/ (CHOOSE htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) : htlcHist.hash = htlcData.hash /\ htlcHist.reason = "ON-CHAIN-PERSISTED").timedout
                                                \/ \E htlc \in Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs : htlc.hash = htlcData.hash /\ htlc.state = "PERSISTED" /\ htlc.timedout
                                                \/ \E htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs : htlcHist.hash = htlcData.hash /\ htlcHist.state = "PERSISTED" /\ htlcHist.reason = "FINALLY-PUNISHED" /\ htlcHist.timedout
                                            THEN
                                                "OFF-TIMEDOUT"
                                            ELSE "COMMITTED"
                                         ELSE
                                            LET isOnChainPersisted == \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) : htlcHist.hash = htlcData.hash /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
                                                htlcHists == {htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) : htlcHist.hash = htlcData.hash /\ htlcHist.reason = "ON-CHAIN-PERSISTED"}
                                                latestHtlcHist == CHOOSE h \in htlcHists : \A oH \in htlcHists : h.index >= oH.index
                                            IN 
                                             IF \/ \E htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) :
                                                    /\ htlcHist.hash = htlcData.hash
                                                    /\ htlcHist.reason = "ON-CHAIN-PERSISTED"
                                                    /\ ~(htlcHist.state \in {"SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE", "PUNISHED"})
                                             THEN 
                                                     latestHtlcHist.state
                                             ELSE
                                                IF (IF isOnChainPersisted THEN latestHtlcHist.fulfilled ELSE htlcData.fulfilled)
                                                THEN
                                                    "FULFILLED"
                                                ELSE
                                                    "OFF-TIMEDOUT"
                               ELSE IF  /\ @ \in {"PERSISTED", "PUNISHED"}
                                        /\ htlcData.fulfilled
                                        /\ ~HTLCMutuallyOffChainPersisted(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages)
                                    THEN "PERSISTED"
                               ELSE IF /\ @ = "COMMITTED"
                                       /\ htlcData.hash \in PreimageInventory
                                       /\ htlcData.hash \in Vars.OtherKnownPreimages
                                       /\ "reason" \in DOMAIN htlcData => htlcData.reason # "ON-CHAIN-PERSISTED"
                                       /\ ~\E htlc \in OutgoingHTLCsFulfilledDuringClosing(DetailVars, Vars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, LedgerTx, MyPCState, OtherPCState) : htlc.hash = htlcData.hash
                                    THEN
                                        "FULFILLED"
                               ELSE IF /\ @ \in {"SENT-REMOVE", "PUNISHED"} \/ htlcData.punished
                                       /\ HTLCMutuallyOffChainPersisted(htlcData, MyName, OtherName, DetailVars, OtherDetailVars, OtherVars, HTLCHistory, OtherHTLCHistory, Messages)
                                    THEN "PERSISTED"
                               ELSE IF @ = "PUNISHED"
                                    THEN (CHOOSE htlcHist \in (HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs) : htlcHist.hash = htlcData.hash /\ htlcHist.reason = "FINALLY-PUNISHED").state
                               ELSE IF  /\ @ = "NEW"
                                        /\ IsClosingStateAfterCommit(MyPCState, OtherPCState, Vars, OtherVars, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx)
                                        /\  \/ ~\E htlc \in OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs :
                                                    /\ htlc.hash = htlcData.hash
                                            \/ Vars.HaveCheated \/ OtherVars.HaveCheated
                                         THEN "ABORTED"
                               ELSE @,
                     !.fulfilled = IF \/
                                          /\ \E htlcHist \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs :
                                                /\ htlcHist.hash = htlcData.hash
                                                /\ htlcHist.reason \in {"ON-CHAIN-PERSISTED"}
                                                /\ htlcHist.fulfilled = FALSE
                                                /\ ~\E pmt \in Payments : pmt.id = htlcHist.id
                                                /\ ~\E tx \in LedgerTx : \E input \in tx.inputs :
                                                    /\ "preimage" \in DOMAIN input.witness
                                                    /\ input.witness.preimage = htlcHist.hash
                                          /\ ~HTLCMutuallyOnChainFulfilled(htlcData, DetailVars, OtherDetailVars, HTLCHistory, OtherHTLCHistory, LedgerTx, MyPCState, OtherPCState, Vars, OtherVars)
                                          /\ ~HTLCWasOffChainThenOnChainFulfilled(htlcData, HTLCHistory, OtherHTLCHistory, MyName, Messages)
                                          /\ ~HTLCWasOnChainFulfilledBeforeOnChainCommit(htlcData, Vars, HTLCHistory, OtherHTLCHistory)
                                   THEN FALSE
                                   ELSE @,
                    !.punished = IF ~IsClosedState(MyPCState, OtherPCState) THEN FALSE ELSE @
             ]
                               
ReadyRefinementMappingForHTLCData(htlcData, OtherVars) ==
    [htlcData EXCEPT !.state =  IF @ \in {"SENT-COMMIT", "PENDING-COMMIT", "RECV-COMMIT"}
                                    THEN "NEW"
                                    ELSE IF @ = "COMMITTED" /\ \E htlc \in OtherVars.IncomingHTLCs \cup OtherVars.OutgoingHTLCs :
                                                                    /\ htlc.hash = htlcData.hash
                                                                    /\ htlc.state \in {"SENT-COMMIT", "PENDING-COMMIT", "RECV-COMMIT"}
                                    THEN "NEW"
                                    ELSE IF @ \in {"SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}
                                        THEN    IF htlcData.fulfilled
                                                THEN "FULFILLED"
                                                ELSE "OFF-TIMEDOUT"
                                        ELSE @
                               ]
                                        
RefinementMappingForHTLCs(HTLCs, MyName, OtherName, PreimageInventory, Payments, Vars, DetailVars, OtherDetailVars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, Messages, LedgerTx, ChannelAliceDetailVars, AliceInventory, BobInventory, UserA, UserB, AllSignatures) ==
    {RefinementMappingForHTLCData(htlcData, MyName, OtherName, PreimageInventory, Payments, Vars, DetailVars, OtherDetailVars, OtherVars, MyPCState, OtherPCState, HTLCHistory, OtherHTLCHistory, Messages, LedgerTx, ChannelAliceDetailVars, AliceInventory, BobInventory, UserA, UserB, AllSignatures) : htlcData \in HTLCs}
ReadyRefinementMappingForHTLCs(HTLCs, OtherVars) ==
    {ReadyRefinementMappingForHTLCData(htlcData, OtherVars) : htlcData \in HTLCs}


AbstractedPendingBalanceHelper(ChannelPendingBalance, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, ChannelAliceState, ChannelBobState, LedgerTx, AlicePayments, BobPayments, AlicePreimageInventory, BobPreimageInventory, UserA, UserB, Messages) ==
    IF  \/ IsUpdatingState(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
        \/ IsClosingStateAfterCommit(ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx)
        \/ IsClosingStateAfterFulfill(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
        \/ IsPreClosingState(LedgerTx, ChannelAliceState, ChannelBobState, ChannelAliceVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory)
    THEN ChannelPendingBalance
         - SumAmounts({htlc \in (ChannelBobVars.OutgoingHTLCs \cup ChannelAliceVars.OutgoingHTLCs) : /\ htlc.state \notin {"FULFILLED", "TIMEDOUT"}
                                                                                              /\ \/ htlc \in ChannelAliceVars.OutgoingHTLCs /\ HTLCWasAddedDuringThisUpdate(htlc, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceVars, ChannelBobVars, ChannelAliceState, ChannelBobState, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, UserA, UserB, Messages, LedgerTx)
                                                                                                 \/ htlc \in ChannelBobVars.OutgoingHTLCs /\ HTLCWasAddedDuringThisUpdate(htlc, ChannelBobDetailVars, ChannelAliceDetailVars, ChannelBobVars, ChannelAliceVars, ChannelBobState, ChannelAliceState, ChannelBobHTLCHistory, ChannelAliceHTLCHistory, UserB, UserA, Messages, LedgerTx)
                                                                                                 \/ htlc \in ChannelAliceVars.OutgoingHTLCs /\ HTLCAddedAndPersistedDuringThisUpdate(htlc, ChannelAliceDetailVars, ChannelBobDetailVars, ChannelAliceVars, ChannelBobVars, ChannelAliceState, ChannelBobState, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, UserA, UserB, Messages, LedgerTx)
                                                                                                 \/ htlc \in ChannelBobVars.OutgoingHTLCs /\ HTLCAddedAndPersistedDuringThisUpdate(htlc, ChannelBobDetailVars, ChannelAliceDetailVars, ChannelBobVars, ChannelAliceVars, ChannelBobState, ChannelAliceState, ChannelBobHTLCHistory, ChannelAliceHTLCHistory, UserB, UserA, Messages, LedgerTx)
                                                                                              })
         + SumAmounts(IncomingHTLCsFulfilledDuringClosing(ChannelAliceDetailVars, ChannelAliceVars, ChannelBobDetailVars, ChannelBobVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, LedgerTx, AlicePayments, ChannelAliceState, ChannelBobState)) + SumAmounts(IncomingHTLCsFulfilledDuringClosing(ChannelBobDetailVars, ChannelBobVars, ChannelAliceDetailVars, ChannelAliceVars, ChannelBobHTLCHistory, ChannelAliceHTLCHistory, LedgerTx, BobPayments, ChannelAliceState, ChannelBobState))
         + SumAmounts(OutgoingHTLCsTimedoutDuringClosing(ChannelAliceDetailVars, ChannelAliceVars, ChannelBobDetailVars, ChannelBobVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory, ChannelAliceState, ChannelBobState, LedgerTx))
         + SumAmounts(OutgoingHTLCsTimedoutDuringClosing(ChannelBobDetailVars, ChannelBobVars, ChannelAliceDetailVars, ChannelAliceVars, ChannelBobHTLCHistory, ChannelAliceHTLCHistory, ChannelAliceState, ChannelBobState, LedgerTx))
         - SumAmounts(IncomingHTLCsTimedoutDuringClosing(ChannelAliceDetailVars, ChannelAliceVars, ChannelBobDetailVars, ChannelAliceHTLCHistory, ChannelBobHTLCHistory))
         - SumAmounts(IncomingHTLCsTimedoutDuringClosing(ChannelBobDetailVars, ChannelBobVars, ChannelAliceDetailVars, ChannelBobHTLCHistory, ChannelAliceHTLCHistory))
         + SumAmounts(HTLCsPunishedByMeDuringClosing(AlicePreimageInventory, ChannelAliceVars, ChannelAliceDetailVars, ChannelAliceHTLCHistory)) + SumAmounts(HTLCsPunishedByMeDuringClosing(BobPreimageInventory, ChannelBobVars, ChannelBobDetailVars, ChannelBobHTLCHistory))
         - SumAmounts(HTLCsPunishedByOtherDuringClosing(AlicePreimageInventory, ChannelAliceVars, ChannelAliceDetailVars, ChannelAliceHTLCHistory)) - SumAmounts(HTLCsPunishedByOtherDuringClosing(BobPreimageInventory, ChannelBobVars, ChannelBobDetailVars, ChannelBobHTLCHistory))
         + (IF ChannelAliceState = "closed" /\ (ChannelAliceDetailVars.HavePunished \/ ChannelAliceVars.HaveCheated) THEN ChannelAliceDetailVars.BalancesBeforeClose[2] ELSE 0)
         + (IF ChannelBobState = "closed" /\ (ChannelBobDetailVars.HavePunished \/ ChannelBobVars.HaveCheated) THEN ChannelBobDetailVars.BalancesBeforeClose[2] ELSE 0)
    ELSE IF IsReadyState(ChannelAliceState, ChannelBobState)
    THEN ChannelPendingBalance
        - SumAmounts({htlc \in ChannelAliceVars.OutgoingHTLCs : \/ htlc.state \in {"SENT-COMMIT", "PENDING-COMMIT"}
                                                                \/ htlc.state \in {"RECV-COMMIT", "COMMITTED"} /\ \E oHtlc \in ChannelBobVars.IncomingHTLCs : htlc.hash = oHtlc.hash /\ oHtlc.state \in {"SENT-COMMIT", "PENDING-COMMIT"}})
        - SumAmounts({htlc \in ChannelBobVars.OutgoingHTLCs :   \/ htlc.state \in {"SENT-COMMIT", "PENDING-COMMIT"}
                                                                \/ htlc.state \in {"RECV-COMMIT", "COMMITTED"} /\ \E oHtlc \in ChannelAliceVars.IncomingHTLCs : htlc.hash = oHtlc.hash /\ oHtlc.state \in {"SENT-COMMIT", "PENDING-COMMIT"}})
    ELSE ChannelPendingBalance


HTLCsPersistedBeforeClosing(HTLCHistory, OtherHTLCHistory) ==
    {htlc.hash : htlc \in {htlc \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
        \cup {htlc.hash : htlc \in {htlc \in OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
        \cup ({htlc.hash : htlc \in {htlc \in HTLCHistory.IncomingHTLCs \cup HTLCHistory.OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}}
                \cap {htlc.hash : htlc \in {htlc \in OtherHTLCHistory.IncomingHTLCs \cup OtherHTLCHistory.OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}})

RECURSIVE AbstractedMessagesHelper(_)
AbstractedMessagesHelper(messages) ==
    IF Len(messages) = 0
    THEN <<>>
    ELSE
        LET firstMessage == Head(messages)
        IN  IF firstMessage.type \in {"OpenChannel", "AcceptChannel", "FundingCreated", "FundingSigned", "ChannelReady", "CommitmentSigned", "RevokeAndAck", "InitiateShutdown"} \* message types sent by PaymentChannelUser
            THEN AbstractedMessagesHelper(Tail(messages))
            ELSE <<firstMessage>> \o AbstractedMessagesHelper(Tail(messages))


=============================================================================