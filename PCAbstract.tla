---------------------------- MODULE PCAbstract ----------------------------

EXTENDS Integers, FiniteSets, TLC, Sequences, SumAmounts

VARIABLES
    ChannelUserState,
    ChannelUserBalance,
    ChannelUserVars,
    UserPreimageInventory,
    UserLatePreimages,
    UserHonest,
    UserExtBalance,
    ChannelPendingBalance,
    UserPayments,
    UserChannelBalance,
    LedgerTime,
    UnchangedVars
    
vars == <<ChannelUserState, ChannelUserBalance, ChannelUserVars, UserPreimageInventory, UserLatePreimages, UserHonest, UserExtBalance, ChannelPendingBalance, UserPayments, UserChannelBalance, LedgerTime>>

CONSTANTS
    MAX_TIME,
    TO_SELF_DELAY,
    SingleSignature,
    AllSignatures,
    SingleSigHashLock,
    AllSigHashLock,
    NameForUserID,
    NullUser

HTLCsByStates(states, HTLCSet) == {htlc \in HTLCSet : htlc.state \in states}

\* G is "a grace-period G blocks after HTLC timeout before giving up on an unresponsive peer and dropping to chain" (BOLT 02)
G == 3

TimeBound(ChannelID, UserAID, UserBID, aliceHonest, bobHonest) ==
    LET timelimits == UNION
        { 
        IF aliceHonest \/ bobHonest
        THEN    LET HTLCs == {}
                             \cup
                             (IF aliceHonest THEN
                             { htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs :
                                    /\  \/ htlc.state = "FULFILLED"
                                        \/  /\ htlc.state = "COMMITTED" \/ (htlc.state = "NEW" /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs)
                                            /\ htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID]
                                    /\ htlc.hash \notin UserPreimageInventory[UserBID]
                                    /\ htlc.hash \notin ChannelUserVars[ChannelID][UserAID].FulfilledAfterTimeoutHTLCs
                                    /\ ChannelUserVars[ChannelID][UserAID].Cheater # NameForUserID[UserBID] \* if the other user has cheated, we don't need this HTLC because we punish anyway
                             }
                             \cup
                             { htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs :
                                    /\ htlc.state = "PERSISTED"
                                    /\ ChannelUserVars[ChannelID][UserAID].Cheater # NameForUserID[UserBID] \* if the other user has cheated, we don't need this HTLC because we punish anyway
                                    /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                                    /\ \E oHtlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs :
                                        /\ oHtlc.hash = htlc.hash
                                        /\ ~oHtlc.fulfilled
                             }
                             ELSE {})
                             \cup
                             (IF bobHonest THEN
                             { htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs :
                                    /\  \/ htlc.state = "FULFILLED"
                                        \/  /\ htlc.state = "COMMITTED" \/ (htlc.state = "NEW" /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs)
                                            /\ htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID]
                                    /\ htlc.hash \notin UserPreimageInventory[UserAID]
                                    /\ htlc.hash \notin ChannelUserVars[ChannelID][UserBID].FulfilledAfterTimeoutHTLCs
                                    /\ ChannelUserVars[ChannelID][UserAID].Cheater # NameForUserID[UserAID]
                             }
                             \cup
                             { htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs :
                                    /\ htlc.state = "PERSISTED"
                                    /\ ChannelUserVars[ChannelID][UserAID].Cheater # NameForUserID[UserAID]
                                    /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                                    /\ \E oHtlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs :
                                        /\ oHtlc.hash = htlc.hash
                                        /\ ~oHtlc.fulfilled
                             }
                             ELSE {})
                IN { htlc.absTimelock + G - 1 : htlc \in HTLCs}
        ELSE {MAX_TIME},
        
        IF (ChannelUserState[ChannelID][UserAID] = "init" /\ ChannelUserState[ChannelID][UserBID] = "init") \/ (ChannelUserState[ChannelID][UserAID] = "rev-keys-exchanged" /\ ChannelUserState[ChannelID][UserBID] = "rev-keys-exchanged")
                 \/ (ChannelUserState[ChannelID][UserAID] = "closing-time-set" /\ ChannelUserState[ChannelID][UserBID] = "closing-time-set")
                \/ (ChannelUserState[ChannelID][UserAID] = "closing" /\ ChannelUserState[ChannelID][UserBID] = "closing")
        THEN {MAX_TIME - TO_SELF_DELAY}
        ELSE {MAX_TIME}
        }
    IN CHOOSE min \in timelimits : (\A time \in timelimits : min <= time)
    
TimelockRegions(ChannelID, UserAID, UserBID) == 
    LET timepoints ==
        (LET HTLCs == ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs
        IN UNION { {htlc.absTimelock, htlc.absTimelock + G + 1} : htlc \in HTLCs})
        \cup
        {MAX_TIME}
    IN timepoints

ValidMapping(f, htlc, ledgerTime, HTLCData, aliceHTLCs, bobHTLCs, aliceVars, bobVars, aliceHasCheated, bobHasCheated, aliceIsNegligent, bobIsNegligent, ChannelID, UserAID, UserBID) ==
    /\ htlc.state = "FULFILLED" =>
            \/ f[htlc] \in {"PERSISTED", "PUNISHED"}
            \/  /\ f[htlc] = "TIMEDOUT"
                /\  \/ htlc.hash \in aliceVars.FulfilledAfterTimeoutHTLCs \cup bobVars.FulfilledAfterTimeoutHTLCs
                    \/ htlc \in aliceVars.IncomingHTLCs /\ aliceIsNegligent 
                    \/ htlc \in bobVars.IncomingHTLCs /\ bobIsNegligent 
    /\ htlc.state \in {"COMMITTED", "OFF-TIMEDOUT"} => f[htlc] \in {"TIMEDOUT", "PERSISTED", "PUNISHED"}
    /\ f[htlc] = "TIMEDOUT" => htlc.absTimelock <= ledgerTime
    /\ htlc.state \in {"PERSISTED", "ABORTED"} => f[htlc] = htlc.state
    /\ \A otherHtlc \in HTLCData : (htlc.hash = otherHtlc.hash => f[htlc] = f[otherHtlc])
    /\ \/ /\ htlc \in aliceHTLCs => \E otherHtlc \in bobHTLCs : htlc.hash = otherHtlc.hash
          /\ htlc \in bobHTLCs => \E otherHtlc \in aliceHTLCs : htlc.hash = otherHtlc.hash
       \/ f[htlc] = "ABORTED"
    
    /\ htlc.state = "COMMITTED" => f[htlc] # "PERSISTED"
    
    /\ (htlc \in aliceHTLCs /\ ~\E oHtlc \in bobHTLCs : oHtlc.hash = htlc.hash) => f[htlc] = "ABORTED"
    /\ (htlc \in bobHTLCs /\ ~\E oHtlc \in aliceHTLCs : oHtlc.hash = htlc.hash) => f[htlc] = "ABORTED"
    
    /\ htlc.state = "NEW" /\ f[htlc] = "PUNISHED" => htlc.hash \in aliceVars.OnChainHTLCs
    
    /\ htlc.state = "TIMEDOUT" => f[htlc] # "ABORTED"
    /\ htlc.state = "TIMEDOUT" => f[htlc] # "PERSISTED"
    /\ f[htlc] = "TIMEDOUT" =>  
                /\ (htlc \in aliceVars.IncomingHTLCs /\ htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID]) => aliceHasCheated \/ aliceIsNegligent
                /\ (htlc \in bobVars.IncomingHTLCs /\ htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID]) => bobHasCheated \/ bobIsNegligent
    /\ f[htlc] = "PERSISTED" /\ htlc.state \notin {"PERSISTED", "FULFILLED"} \ {"FULFILLED"}
        =>
            \/ htlc.absTimelock + G - 1 >= ledgerTime 
            \/  /\ htlc \in aliceVars.OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID] \/ aliceHasCheated \/ aliceIsNegligent
                /\ htlc \in bobVars.OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID] \/ bobHasCheated \/ bobIsNegligent

HTLCToClosedStateMappings(aliceHasCheated, bobHasCheated, ledgerTime, aliceVars, bobVars, aliceIsNegligent, bobIsNegligent, ChannelID, UserAID, UserBID) ==
    LET HTLCData == aliceVars.IncomingHTLCs \cup bobVars.IncomingHTLCs \cup aliceVars.OutgoingHTLCs \cup bobVars.OutgoingHTLCs
        aliceHTLCs == aliceVars.IncomingHTLCs \cup aliceVars.OutgoingHTLCs
        bobHTLCs == bobVars.IncomingHTLCs \cup bobVars.OutgoingHTLCs
        possibleNewStates == IF aliceHasCheated \/ bobHasCheated THEN {"PUNISHED"} ELSE {"ABORTED", "PERSISTED", "TIMEDOUT"}
    IN  
    {f \in [HTLCData -> possibleNewStates] :
        \/ aliceHasCheated
        \/ bobHasCheated
        \/ \A htlc \in HTLCData :
            ValidMapping(f, htlc, ledgerTime, HTLCData, aliceHTLCs, bobHTLCs, aliceVars, bobVars, aliceHasCheated, bobHasCheated, aliceIsNegligent, bobIsNegligent, ChannelID, UserAID, UserBID)            
    }

AllHTLCs(ChannelID, UserAID, UserBID) == ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs

\* UserA is funder of channel
OpenPaymentChannel(ChannelID, UserAID, UserBID) ==
    /\ ChannelUserState[ChannelID][UserAID] = "init"
    /\ ChannelUserState[ChannelID][UserBID] = "init"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserAID] = "rev-keys-exchanged",
                                                    ![ChannelID][UserBID] = "rev-keys-exchanged"]
    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserAID] = UserExtBalance[UserAID],
                                                        ![ChannelID][UserBID] = 0]
    /\ UserExtBalance[UserAID] > 0 \/ UserExtBalance[UserBID] > 0
    /\ UserExtBalance' = [UserExtBalance EXCEPT ![UserAID] = 0]
    /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserAID] = @ + UserExtBalance[UserAID]]
    /\ UNCHANGED <<ChannelUserVars, UserPreimageInventory, ChannelPendingBalance, UserHonest, UserLatePreimages, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
AddableHTLCsDuringUpdate(ledgerTime, ChannelID, UserAID, UserBID) ==
    {htlcData \in HTLCsByStates({"NEW"}, AllHTLCs(ChannelID, UserAID, UserBID)) : \/ ledgerTime < htlcData.absTimelock
                                                     \/  /\ htlcData \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs
                                                         /\ ~UserHonest[UserAID]
                                                     \/  /\ htlcData \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs
                                                         /\ ~UserHonest[UserBID]
    }
    
RemovableHTLCsDuringUpdate(ledgerTime, ChannelID, UserAID, UserBID) ==
    {htlcData \in HTLCsByStates({"OFF-TIMEDOUT"}, AllHTLCs(ChannelID, UserAID, UserBID)) :
        /\ ledgerTime >= htlcData.absTimelock
        /\ \A htlc \in AllHTLCs(ChannelID, UserAID, UserBID) :
            HTLCsAreEqual(htlcData, htlc) => ~htlc.fulfilled \/ htlc.hash \notin ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
    }
    
    
UpdatePaymentChannelP(ledgerTime, ChannelID, UserAID, UserBID) ==
    /\ ChannelUserState[ChannelID][UserAID] \in {"rev-keys-exchanged", "closing-time-set"}
    /\ ChannelUserState[ChannelID][UserBID] \in {"rev-keys-exchanged", "closing-time-set"}
    /\  \/ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserAID] = "rev-keys-exchanged",
                                                        ![ChannelID][UserBID] = "rev-keys-exchanged"]
        \/ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserAID] = "closing",
                                                        ![ChannelID][UserBID] = "closing"] 
        \/ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserAID] = "closing-time-set",
                                                        ![ChannelID][UserBID] = "closing-time-set"]
    /\ ChannelUserState[ChannelID][UserAID] = "closing-time-set" => ChannelUserState[ChannelID][UserAID]' \in {"closing-time-set", "closing"}
    /\ LET addableHTLCs == AddableHTLCsDuringUpdate(ledgerTime, ChannelID, UserAID, UserBID)
           persistableHTLCs == {htlcData \in HTLCsByStates({"FULFILLED"}, AllHTLCs(ChannelID, UserAID, UserBID)) :
                                    /\ (\E htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : htlc.hash = htlcData.hash)
                                            => ~UserHonest[UserAID] \/ htlcData.hash \notin UserLatePreimages[UserAID]
                                    /\ (\E htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs : htlc.hash = htlcData.hash)
                                            => ~UserHonest[UserBID] \/ htlcData.hash \notin UserLatePreimages[UserBID]
                                }
           removableHTLCs == RemovableHTLCsDuringUpdate(ledgerTime, ChannelID, UserAID, UserBID)
           abortableHTLCs == IF ChannelUserState[ChannelID][UserAID]' = "closing" THEN HTLCsByStates({"NEW"}, {htlc \in AllHTLCs(ChannelID, UserAID, UserBID) : htlc.hash \notin ChannelUserVars[ChannelID][UserAID].OnChainHTLCs}) ELSE {}
       IN \E updatedHTLCs \in SUBSET(addableHTLCs \cup persistableHTLCs \cup removableHTLCs) :
            /\ Cardinality(updatedHTLCs) > 0
            /\ \A htlcData \in updatedHTLCs:
                /\ htlcData \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cap updatedHTLCs : HTLCsAreEqual(htlcData, htlc)
                /\ htlcData \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs =>
                    \/ \E htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : HTLCsAreEqual(htlcData, htlc) /\ htlc.fulfilled
                    \/ \E htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cap updatedHTLCs : HTLCsAreEqual(htlcData, htlc)
                /\ htlcData \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cap updatedHTLCs : HTLCsAreEqual(htlcData, htlc)
                /\ htlcData \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs =>
                    \/ \E htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : HTLCsAreEqual(htlcData, htlc) /\ htlc.fulfilled
                    \/ \E htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cap updatedHTLCs : HTLCsAreEqual(htlcData, htlc)
            /\ \E HTLCsToOnChainAbort \in SUBSET (abortableHTLCs \ updatedHTLCs) :
                /\ ChannelUserVars[ChannelID][UserAID].Cheater = NullUser => HTLCsToOnChainAbort = abortableHTLCs
                /\ LET HTLCsToAdd == updatedHTLCs \cap addableHTLCs
                       HTLCsToPersist == updatedHTLCs \cap persistableHTLCs
                       HTLCsToRemove == updatedHTLCs \cap removableHTLCs
                       HTLCsStillNew == (HTLCsByStates({"NEW"}, AllHTLCs(ChannelID, UserAID, UserBID)) \ HTLCsToAdd) \ HTLCsToOnChainAbort
                       HTLCsUnchanged == AllHTLCs(ChannelID, UserAID, UserBID) \ (updatedHTLCs \cup HTLCsToOnChainAbort)
                       newBalanceAlice == ChannelUserBalance[ChannelID][UserAID]
                                            - SumAmounts(HTLCsToAdd \cap ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs)
                                            + SumAmounts(HTLCsToRemove \cap ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs)
                       newBalanceBob == ChannelUserBalance[ChannelID][UserBID]
                                            - SumAmounts(HTLCsToAdd \cap ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs)
                                            + SumAmounts(HTLCsToRemove \cap ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs)
                       fulfilledHTLCBalanceAlice == SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \ HTLCsToPersist : htlc.state = "FULFILLED"})
                       fulfilledHTLCBalanceBob == SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \ HTLCsToPersist : htlc.state = "FULFILLED"})
                       channelBeingClosed == ChannelUserState[ChannelID][UserAID] = "rev-keys-exchanged" /\ ChannelUserState[ChannelID][UserAID]' # "rev-keys-exchanged"
                       cheater == ChannelUserVars[ChannelID][UserAID].Cheater
                   IN 
                    /\ ChannelUserState[ChannelID][UserAID]' = "closing-time-set" /\ ChannelUserVars[ChannelID][UserAID].Cheater = NullUser => \A htlc \in HTLCsToAdd : htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                    /\ \A addHTLC \in HTLCsToAdd :
                        \A persistHTLC \in HTLCsToPersist :
                            addHTLC.hash # persistHTLC.hash
                    /\ newBalanceAlice >= fulfilledHTLCBalanceAlice
                    /\ newBalanceBob >= fulfilledHTLCBalanceBob
                    /\ ChannelUserState[ChannelID][UserAID]' = "closing" => \A htlc \in HTLCsStillNew : htlc.absTimelock > ledgerTime
                    /\ \E onChainHTLCs \in IF channelBeingClosed THEN SUBSET {htlc.hash : htlc \in AllHTLCs(ChannelID, UserAID, UserBID)} ELSE {ChannelUserVars[ChannelID][UserAID].OnChainHTLCs} :
                        /\ channelBeingClosed /\ cheater = NullUser =>
                            /\ \A htlc \in HTLCsByStates({"COMMITTED"}, AllHTLCs(ChannelID, UserAID, UserBID) \ (HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort)) \cup HTLCsToAdd : htlc.hash \in onChainHTLCs
                            /\ \A htlc \in HTLCsByStates({"PERSISTED", "ABORTED", "TIMEDOUT"}, AllHTLCs(ChannelID, UserAID, UserBID)) \cup HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort : htlc.hash \notin onChainHTLCs
                        /\ channelBeingClosed /\ cheater # NullUser =>
                            /\  \/ \E htlc \in HTLCsByStates({"COMMITTED"}, AllHTLCs(ChannelID, UserAID, UserBID) \ (HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort)) \cup HTLCsToAdd : htlc.hash \notin onChainHTLCs
                                \/ \E htlc \in HTLCsByStates({"NEW"}, AllHTLCs(ChannelID, UserAID, UserBID) \ HTLCsToAdd) : htlc.hash \notin onChainHTLCs
                                \/ Cardinality(HTLCsByStates({"FULFILLED", "OFF-TIMEDOUT", "PERSISTED", "ABORTED", "TIMEDOUT"}, AllHTLCs(ChannelID, UserAID, UserBID)) \cup HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort) > 0
                        /\ channelBeingClosed => \A hash \in onChainHTLCs :
                            /\ \E htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : htlc.hash = hash
                            /\ \E htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : htlc.hash = hash
                            /\ \A htlc \in AllHTLCs(ChannelID, UserAID, UserBID) : htlc.hash = hash /\ htlc.state = "NEW" =>
                                \/ htlc.absTimelock + G > LedgerTime
                                \/ htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs /\ (ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID] \/ ~UserHonest[UserAID] \/ ~UserHonest[UserBID]) 
                                \/ htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs /\ (ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID] \/ ~UserHonest[UserAID] \/ ~UserHonest[UserBID])
                                \/ htlc.hash \in UserLatePreimages[UserAID] \cup UserLatePreimages[UserBID]
                        /\ ChannelUserVars' = [ChannelUserVars EXCEPT
                                                 ![ChannelID][UserAID].OutgoingHTLCs = (@ \ (HTLCsToAdd \cup HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort))
                                                                        \cup {[htlcData EXCEPT !.state = "COMMITTED"] : htlcData \in (HTLCsToAdd \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "PERSISTED"] : htlcData \in (HTLCsToPersist \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "TIMEDOUT"] : htlcData \in (HTLCsToRemove \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "ABORTED"] : htlcData \in (HTLCsToOnChainAbort \cap @)},
                                                 ![ChannelID][UserAID].IncomingHTLCs = (@ \ (HTLCsToAdd \cup HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort))
                                                                        \cup {[htlcData EXCEPT !.state = "COMMITTED"] : htlcData \in (HTLCsToAdd \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "PERSISTED"] : htlcData \in (HTLCsToPersist \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "TIMEDOUT"] : htlcData \in (HTLCsToRemove \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "ABORTED"] : htlcData \in (HTLCsToOnChainAbort \cap @)},
                                                 ![ChannelID][UserAID].OnChainHTLCs = onChainHTLCs,
                                                 ![ChannelID][UserBID].OutgoingHTLCs = (@ \ (HTLCsToAdd \cup HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort))
                                                                        \cup {[htlcData EXCEPT !.state = "COMMITTED"] : htlcData \in (HTLCsToAdd \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "PERSISTED"] : htlcData \in (HTLCsToPersist \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "TIMEDOUT"] : htlcData \in (HTLCsToRemove \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "ABORTED"] : htlcData \in (HTLCsToOnChainAbort \cap @)},
                                                 ![ChannelID][UserBID].IncomingHTLCs = (@ \ (HTLCsToAdd \cup HTLCsToPersist \cup HTLCsToRemove \cup HTLCsToOnChainAbort))
                                                                        \cup {[htlcData EXCEPT !.state = "COMMITTED"] : htlcData \in (HTLCsToAdd \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "PERSISTED"] : htlcData \in (HTLCsToPersist \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "TIMEDOUT"] : htlcData \in (HTLCsToRemove \cap @)}
                                                                        \cup {[htlcData EXCEPT !.state = "ABORTED"] : htlcData \in (HTLCsToOnChainAbort \cap @)},
                                                 ![ChannelID][UserBID].OnChainHTLCs = onChainHTLCs
                                                 ]
                        /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserAID] = newBalanceAlice,
                                                                           ![ChannelID][UserBID] = newBalanceBob]
                        /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @
                                                + SumAmounts(HTLCsToAdd \cap (ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs))
                                                - SumAmounts(HTLCsToRemove \cap (ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs))
                                                ]
                        /\ channelBeingClosed =>
                            /\ ChannelUserBalance[ChannelID][UserAID]
                                - SumAmounts(HTLCsByStates({"FULFILLED"}, {htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : htlc.hash \in onChainHTLCs}))
                                    >= SumAmounts(HTLCsByStates({"NEW"}, {htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : htlc.hash \in onChainHTLCs}))
                            /\ ChannelUserBalance[ChannelID][UserBID]
                                - SumAmounts(HTLCsByStates({"FULFILLED"}, {htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : htlc.hash \in onChainHTLCs}))
                                    >= SumAmounts(HTLCsByStates({"NEW"}, {htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs : htlc.hash \in onChainHTLCs}))
                    /\  \/ ChannelUserVars[ChannelID][UserAID]'.Cheater = NullUser
                        \/ ChannelUserState[ChannelID][UserAID]' # "closing"
                        \/  /\ ChannelUserVars[ChannelID][UserAID]'.Cheater = NameForUserID[UserAID]
                                            => ChannelUserBalance[ChannelID][UserAID]'
                                                    - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID]'.IncomingHTLCs : htlc.state \in {"FULFILLED"}})
                                                    - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID]'.OutgoingHTLCs : htlc.state \in {"NEW"}})
                                                >= 0
                            /\ ChannelUserVars[ChannelID][UserAID]'.Cheater = NameForUserID[UserBID]
                                            => ChannelUserBalance[ChannelID][UserBID]'
                                                    - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID]'.IncomingHTLCs : htlc.state \in {"FULFILLED"}})
                                                    - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID]'.OutgoingHTLCs : htlc.state \in {"NEW"}})
                                                >= 0
    /\ UNCHANGED <<UserPreimageInventory, UserExtBalance, UserHonest, UserLatePreimages, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
    
UpdatePaymentChannel(ChannelID, UserAID, UserBID) ==
    UpdatePaymentChannelP(LedgerTime, ChannelID, UserAID, UserBID)
    
SetOnChainHTLCsAndCheater(ChannelID, UserAID, UserBID) ==
    /\ ChannelUserState[ChannelID][UserAID] = "rev-keys-exchanged"
    /\ ChannelUserState[ChannelID][UserBID] = "rev-keys-exchanged"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserAID] = "closing-time-set",
                                                    ![ChannelID][UserBID] = "closing-time-set"]
    /\ ChannelUserVars[ChannelID][UserAID].Cheater = NullUser
    /\ LET allHTLCs == ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs
       IN \E cheater \in {NullUser, NameForUserID[UserAID], NameForUserID[UserBID]} :
        /\ cheater = NameForUserID[UserAID] =>
            /\ ~UserHonest[UserAID]
            /\ Cardinality(ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs) > 0
            /\ Cardinality(ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserAID].IncomingHTLCs) > 0
        /\ cheater = NameForUserID[UserBID] =>
            /\ ~UserHonest[UserBID]
            /\ Cardinality(ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserAID].IncomingHTLCs) > 0
            /\ Cardinality(ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs) > 0
        /\ \E onChainHTLCs \in SUBSET {htlc.hash : htlc \in allHTLCs} :
            /\ cheater = NullUser =>
                /\ \A htlc \in HTLCsByStates({"COMMITTED"}, allHTLCs) : htlc.hash \in onChainHTLCs
                /\ \A htlc \in HTLCsByStates({"PERSISTED", "ABORTED", "TIMEDOUT"}, allHTLCs) : htlc.hash \notin onChainHTLCs
            /\ cheater # NullUser =>
                /\  \/ \E htlc \in HTLCsByStates({"COMMITTED"}, allHTLCs) : htlc.hash \notin onChainHTLCs
                    \/ \E htlc \in HTLCsByStates({"NEW"}, allHTLCs) : htlc.hash \notin onChainHTLCs
                    \/ Cardinality(HTLCsByStates({"FULFILLED", "OFF-TIMEDOUT", "PERSISTED", "ABORTED", "TIMEDOUT"}, allHTLCs)) > 0
            /\ \A hash \in onChainHTLCs :
                /\ \E htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : htlc.hash = hash
                /\ \E htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : htlc.hash = hash
            /\ \A hash \in onChainHTLCs :
                \A htlc \in allHTLCs : htlc.hash = hash /\ htlc.state = "NEW" =>
                    \/ htlc.absTimelock + G > LedgerTime
                    \/ htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs /\ (ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID] \/ ~UserHonest[UserAID] \/ ~UserHonest[UserBID])
                    \/ htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs /\ (ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID] \/ ~UserHonest[UserAID] \/ ~UserHonest[UserBID])
                    \/ htlc.hash \in UserLatePreimages[UserAID] \cup UserLatePreimages[UserBID]
            /\ ChannelUserVars' = [ChannelUserVars EXCEPT
                                              ![ChannelID][UserAID].OnChainHTLCs = onChainHTLCs,
                                              ![ChannelID][UserAID].Cheater = cheater,
                                              ![ChannelID][UserAID].HTLCsPersistedBeforeClosing = {htlc.hash : htlc \in {htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : htlc.state \in {"PERSISTED", "TIMEDOUT"}}},
                                          ![ChannelID][UserBID].OnChainHTLCs = onChainHTLCs,
                                          ![ChannelID][UserBID].Cheater = cheater,
                                          ![ChannelID][UserBID].HTLCsPersistedBeforeClosing = {htlc.hash : htlc \in {htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : htlc.state \in {"PERSISTED", "TIMEDOUT"}}}
                            ]
            /\ ChannelUserBalance[ChannelID][UserAID]
                    >= SumAmounts(HTLCsByStates({"FULFILLED"}, {htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : htlc.hash \in onChainHTLCs}))
                        + SumAmounts(HTLCsByStates({"NEW"}, {htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : htlc.hash \in onChainHTLCs}))
                        + SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : /\ htlc.state = "FULFILLED"
                                                                         /\ ~ValidMapping((htlc :> "PERSISTED"), htlc, LedgerTime, {htlc}, {htlc}, {htlc}, ChannelUserVars[ChannelID][UserAID]', ChannelUserVars[ChannelID][UserBID]', cheater = NameForUserID[UserAID], cheater = NameForUserID[UserBID], ~UserHonest[UserAID], ~UserHonest[UserBID], ChannelID, UserAID, UserBID)
                                                         })
            /\ ChannelUserBalance[ChannelID][UserBID]
                    >= SumAmounts(HTLCsByStates({"FULFILLED"}, {htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : htlc.hash \in onChainHTLCs}))
                        + SumAmounts(HTLCsByStates({"NEW"}, {htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs : htlc.hash \in onChainHTLCs}))
                        + SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : /\ htlc.state = "FULFILLED"
                                                                       /\ ~ValidMapping((htlc :> "PERSISTED"), htlc, LedgerTime, {htlc}, {htlc}, {htlc}, ChannelUserVars[ChannelID][UserAID]', ChannelUserVars[ChannelID][UserBID]', cheater = NameForUserID[UserAID], cheater = NameForUserID[UserBID], ~UserHonest[UserAID], ~UserHonest[UserBID], ChannelID, UserAID, UserBID)
                                                         })
    /\ UNCHANGED <<UserHonest, ChannelUserBalance, UserExtBalance, UserPreimageInventory, ChannelPendingBalance, UserLatePreimages, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
HTLCToOnChainCommittedStateMappings(newHTLCs, onChainCommittedHTLCs, ChannelID, UserAID, UserBID) ==
    LET aliceHTLCs == ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs
        bobHTLCs == ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs
        possibleNewStates == {"NEW", "ABORTED", "COMMITTED"}
    IN
    {f \in [newHTLCs -> {"NEW", "ABORTED", "COMMITTED"}] :
        /\ \A htlc \in newHTLCs : 
            /\ IF htlc \in onChainCommittedHTLCs
                THEN f[htlc] = "COMMITTED"
                ELSE IF ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                THEN f[htlc] \in {"NEW", "ABORTED"}
                ELSE TRUE
            /\ f[htlc] = "COMMITTED" => htlc \in onChainCommittedHTLCs
            /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs => f[htlc] # "ABORTED"
            /\ (htlc \in aliceHTLCs /\ ~\E bobHtlc \in bobHTLCs : bobHtlc.hash = htlc.hash) => f[htlc] = "ABORTED"
            /\ (htlc \in bobHTLCs /\ ~\E aliceHtlc \in aliceHTLCs : aliceHtlc.hash = htlc.hash) => f[htlc] = "ABORTED"
    }
    

FulfillIncomingHTLCsOnChain(ChannelID, UserAID, UserBID) ==
    /\ ChannelUserState[ChannelID][UserAID] \in {"closing-time-set", "closing"}
    /\ ChannelUserState[ChannelID][UserBID] \in {"closing-time-set", "closing"}
    /\ UNCHANGED <<ChannelUserState>>
    /\ LET incomingHTLCs == ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs
           fulfillableHTLCs == {htlc \in HTLCsByStates({"COMMITTED", "FULFILLED", "OFF-TIMEDOUT"}, incomingHTLCs) :
                                    /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                                    /\
                                        \/ htlc.absTimelock + G > LedgerTime
                                        \/  /\ htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs => htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID] \/ ~UserHonest[UserAID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                                            /\ htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs => htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID] \/ ~UserHonest[UserBID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                                }
                                \cup
                                {
                                    htlc \in HTLCsByStates({"NEW"}, incomingHTLCs) :
                                        /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                                        /\  \/ htlc.absTimelock + G > LedgerTime
                                            \/  /\ htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs => htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID] \/ ~UserHonest[UserAID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                                                /\ htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs => htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID] \/ ~UserHonest[UserBID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                                }
       IN 
            /\ \E fulfilledHTLCs \in SUBSET fulfillableHTLCs :
                /\ Cardinality(fulfilledHTLCs) > 0
                /\ LET  
                        newPreimagesForAlice == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : \E oHTLC \in fulfilledHTLCs : iHTLC.hash = oHTLC.hash}}
                        newPreimagesForBob == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : \E oHTLC \in fulfilledHTLCs : iHTLC.hash = oHTLC.hash}}
                        newlyCommittedFulfilledHTLCBalanceAlice == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : ~htlc.fulfilled /\ htlc.state # "NEW"})
                        newlyCommittedFulfilledHTLCBalanceBob == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : ~htlc.fulfilled /\ htlc.state # "NEW"})
                        newlyUncommittedFulfilledHTLCBalanceAlice == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : htlc.state = "NEW"})
                        newlyUncommittedFulfilledHTLCBalanceBob == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : htlc.state = "NEW"})
                        fulfilledHTLCBalanceAlice == SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : htlc.state = "FULFILLED"} \cup (fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserAID].IncomingHTLCs))
                        fulfilledHTLCBalanceBob == SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : htlc.state = "FULFILLED"} \cup (fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserBID].IncomingHTLCs))
                   IN
                    /\ newPreimagesForAlice \subseteq UserPreimageInventory[UserBID]
                    /\ newPreimagesForBob \subseteq UserPreimageInventory[UserAID]
                    /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserAID].IncomingHTLCs = (@ \ fulfilledHTLCs)
                                                                            \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (fulfilledHTLCs \cap @)},
                                                      ![ChannelID][UserAID].OtherKnownPreimages = @ \cup newPreimagesForBob,
                                                      ![ChannelID][UserBID].IncomingHTLCs = (@ \ fulfilledHTLCs)
                                                                            \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (fulfilledHTLCs \cap @)},
                                                      ![ChannelID][UserBID].OtherKnownPreimages = @ \cup newPreimagesForAlice
                                    ]
                    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserAID] = @ + newlyCommittedFulfilledHTLCBalanceAlice + newlyUncommittedFulfilledHTLCBalanceAlice,
                                                                        ![ChannelID][UserBID] = @ + newlyCommittedFulfilledHTLCBalanceBob + newlyUncommittedFulfilledHTLCBalanceBob]
                    /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - newlyCommittedFulfilledHTLCBalanceAlice - newlyCommittedFulfilledHTLCBalanceBob
                                                        - newlyUncommittedFulfilledHTLCBalanceAlice - newlyUncommittedFulfilledHTLCBalanceBob]
                    /\ ChannelUserBalance[ChannelID][UserAID]' >= 0
                    /\ ChannelUserBalance[ChannelID][UserBID]' >= 0
                    /\ ChannelUserBalance[ChannelID][UserAID]' >= SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID]'.IncomingHTLCs : /\ htlc.state = "FULFILLED"
                                                                                        /\ ~ValidMapping((htlc :> "PERSISTED"), htlc, LedgerTime, {htlc}, {htlc}, {htlc}, ChannelUserVars[ChannelID][UserAID]', ChannelUserVars[ChannelID][UserBID]', ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID], ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID], ~UserHonest[UserAID], ~UserHonest[UserBID], ChannelID, UserAID, UserBID)
                                                                      })
                                        + SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID]'.OutgoingHTLCs : /\ ~htlc.fulfilled
                                                                                          /\ htlc.state \notin {"COMMITTED", "OFF-TIMEDOUT"}
                                                                                          /\ \E fulfilledHTLC \in fulfilledHTLCs : HTLCsAreEqual(fulfilledHTLC, htlc)
                                                                      })
                    /\ ChannelUserBalance[ChannelID][UserBID]' >= SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID]'.IncomingHTLCs : /\ htlc.state = "FULFILLED"
                                                                                    /\ ~ValidMapping((htlc :> "PERSISTED"), htlc, LedgerTime, {htlc}, {htlc}, {htlc}, ChannelUserVars[ChannelID][UserAID]', ChannelUserVars[ChannelID][UserBID]', ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID], ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID], ~UserHonest[UserAID], ~UserHonest[UserBID], ChannelID, UserAID, UserBID)
                                                                      })
                                        + SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID]'.OutgoingHTLCs : /\ ~htlc.fulfilled
                                                                                        /\ htlc.state \notin {"COMMITTED", "OFF-TIMEDOUT"}
                                                                                        /\ \E fulfilledHTLC \in fulfilledHTLCs : HTLCsAreEqual(fulfilledHTLC, htlc)
                                                                      })
                    /\ LET processedPaymentsAlice == {payment \in UserPayments[UserAID] : payment.state = "NEW" /\ \E htlc \in fulfilledHTLCs : htlc.id = payment.id}
                           receivedPaymentsAlice == {payment \in processedPaymentsAlice : payment.receiver = UserAID}
                           processedPaymentsBob == {payment \in UserPayments[UserBID] : payment.state = "NEW" /\ \E htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : htlc.id = payment.id}
                           receivedPaymentsBob == {payment \in processedPaymentsBob : payment.receiver = UserBID}
                       IN   /\ UserPayments' = [UserPayments EXCEPT ![UserAID] = (@ \ receivedPaymentsAlice) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in receivedPaymentsAlice},
                                                                    ![UserBID] = (@ \ receivedPaymentsBob) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in receivedPaymentsBob}]
                            /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserAID] = @ + SumAmounts(receivedPaymentsAlice),
                                                                                ![UserBID] = @ + SumAmounts(receivedPaymentsBob)]
                    /\ ~UNCHANGED <<UserPayments, ChannelUserVars>> \* this would be the combined FulfillHTLCsOnChain
    /\ UNCHANGED <<UserHonest, UserExtBalance, UserPreimageInventory, UserLatePreimages>>
    /\ UNCHANGED UnchangedVars

NoteFulfilledHTLCsOnChain(ChannelID, UserAID, UserBID) ==
    /\ ChannelUserState[ChannelID][UserAID] \in {"closing-time-set", "closing"}
    /\ ChannelUserState[ChannelID][UserBID] \in {"closing-time-set", "closing"}
    /\ UNCHANGED <<ChannelUserState>>
    /\ LET allHTLCs == ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs
            \* HTLC may not be fulfilled on-chain after timelock + G because after on-chain fulfillment, the HTLC cannot be timedout anymore
           fulfillableHTLCs == {htlc \in HTLCsByStates({"COMMITTED", "FULFILLED", "OFF-TIMEDOUT"}, allHTLCs) :
                                        \/ htlc.absTimelock + G > LedgerTime
                                        \/  /\ htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID] \/ ~UserHonest[UserAID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                                            /\ htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID] \/ ~UserHonest[UserBID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                                }
                                \cup
                                {
                                    htlc \in HTLCsByStates({"NEW"}, allHTLCs) :
                                        /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                                }
       IN 
            /\ \E fulfilledHTLCs \in SUBSET fulfillableHTLCs :
                /\ Cardinality(fulfilledHTLCs) > 0
                /\ \A htlc \in fulfilledHTLCs :
                        \/ \E incomingHtlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : HTLCsAreEqual(htlc, incomingHtlc) /\ incomingHtlc.fulfilled
                /\ LET  newPreimagesForAlice == {htlc.hash : htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cap fulfilledHTLCs}
                        newPreimagesForBob == {htlc.hash : htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cap fulfilledHTLCs}
                        newlyCommittedFulfilledHTLCBalanceAlice == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs : ~htlc.fulfilled /\ htlc.state # "NEW"})
                        newlyCommittedFulfilledHTLCBalanceBob == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : ~htlc.fulfilled /\ htlc.state # "NEW"})
                        newlyUncommittedFulfilledHTLCBalanceAlice == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs : htlc.state = "NEW"})
                        newlyUncommittedFulfilledHTLCBalanceBob == SumAmounts({htlc \in fulfilledHTLCs \cap ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : htlc.state = "NEW"})
                   IN
                    /\ newPreimagesForAlice \subseteq UserPreimageInventory[UserBID]
                    /\ newPreimagesForBob \subseteq UserPreimageInventory[UserAID]
                    /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserAID] = @ \cup newPreimagesForAlice,
                                                                              ![UserBID] = @ \cup newPreimagesForBob]
                    /\ UserLatePreimages' = [UserLatePreimages EXCEPT ![UserAID] = @ \cup ({htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cap fulfilledHTLCs : iHTLC.absTimelock + G < LedgerTime}} \ UserPreimageInventory[UserAID]),
                                                                      ![UserBID] = @ \cup ({htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cap fulfilledHTLCs : iHTLC.absTimelock + G < LedgerTime}} \ UserPreimageInventory[UserBID])]
                    /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserAID].OutgoingHTLCs = (@ \ fulfilledHTLCs)
                                                                            \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (fulfilledHTLCs \cap @)},
                                                      ![ChannelID][UserAID].OtherKnownPreimages = @ \cup newPreimagesForAlice,
                                                      ![ChannelID][UserBID].OutgoingHTLCs = (@ \ fulfilledHTLCs)
                                                                            \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (fulfilledHTLCs \cap @)},
                                                      ![ChannelID][UserBID].OtherKnownPreimages = @ \cup newPreimagesForBob
                                    ]
                    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserAID] = @ - newlyUncommittedFulfilledHTLCBalanceBob,
                                                                        ![ChannelID][UserBID] = @ - newlyUncommittedFulfilledHTLCBalanceAlice]
                    /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @
                                                        + newlyUncommittedFulfilledHTLCBalanceAlice + newlyUncommittedFulfilledHTLCBalanceBob]
                    /\ ChannelUserBalance[ChannelID][UserAID]' >= 0
                    /\ ChannelUserBalance[ChannelID][UserBID]' >= 0
                    /\ LET processedPaymentsAlice == {payment \in UserPayments[UserAID] : payment.state = "NEW" /\ \E htlc \in fulfilledHTLCs : htlc.id = payment.id}
                           sentPaymentsAlice == {payment \in processedPaymentsAlice : payment.sender = UserAID}
                           processedPaymentsBob == {payment \in UserPayments[UserBID] : payment.state = "NEW" /\ \E htlc \in fulfilledHTLCs : htlc.id = payment.id}
                           sentPaymentsBob == {payment \in processedPaymentsBob : payment.sender = UserBID}
                       IN   /\ UserPayments' = [UserPayments EXCEPT ![UserAID] = (@ \ sentPaymentsAlice) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in sentPaymentsAlice},
                                                                    ![UserBID] = (@ \ sentPaymentsBob) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in sentPaymentsBob}]
                            /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserAID] = @ - SumAmounts(sentPaymentsAlice),
                                                                                ![UserBID] = @ - SumAmounts(sentPaymentsBob)]
    /\ UNCHANGED <<UserHonest, UserExtBalance>>
    /\ UNCHANGED UnchangedVars
    
CommitHTLCsOnChain(ChannelID, UserAID, UserBID) ==
    /\ ChannelUserState[ChannelID][UserAID] = "closing-time-set"
    /\ ChannelUserState[ChannelID][UserBID] = "closing-time-set"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserAID] = "closing",
                                                    ![ChannelID][UserBID] = "closing"]
    /\ LET allHTLCs == ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs
           newHTLCs == HTLCsByStates({"NEW"}, allHTLCs)
           possibleNewCommHTLCs == SUBSET newHTLCs
           updatedHTLCs == newHTLCs
           persistableHTLCs == {htlc \in HTLCsByStates({"NEW", "COMMITTED", "FULFILLED", "OFF-TIMEDOUT"}, allHTLCs) :
                                    \/ LedgerTime <= htlc.absTimelock + G - 1
                                    \/  /\ htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID] \/ ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID] \/ ~UserHonest[UserAID]
                                        /\ htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID] \/ ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID] \/ ~UserHonest[UserBID]
                                }
           possiblePersistedHTLCs == SUBSET persistableHTLCs
       IN 
            /\ \E newlyOnChainCommittedHTLCs \in possibleNewCommHTLCs:
               \E persistedHTLCs \in possiblePersistedHTLCs :
                LET fulfilledHTLCBalanceAlice == SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \ persistedHTLCs : htlc.state = "FULFILLED" /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs})
                    fulfilledHTLCBalanceBob == SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \ persistedHTLCs : htlc.state = "FULFILLED" /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs})
                    newHTLCsBeingPersisted == {htlc \in persistedHTLCs : htlc.state = "NEW"}
                IN
                    /\ persistedHTLCs \cap newlyOnChainCommittedHTLCs = {}
                    /\ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser =>
                        /\ newlyOnChainCommittedHTLCs = {}
                    /\ \A htlc \in newlyOnChainCommittedHTLCs \cup newHTLCsBeingPersisted : htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                    /\ \A htlc \in newlyOnChainCommittedHTLCs \cup newHTLCsBeingPersisted :
                        \/ htlc.absTimelock + G > LedgerTime
                        \/ htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs /\ (ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID] \/ ~UserHonest[UserAID] \/ ~UserHonest[UserBID])
                        \/ htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs /\ (ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID] \/ ~UserHonest[UserAID] \/ ~UserHonest[UserBID])
                        \/ htlc.hash \in UserLatePreimages[UserAID] \cup UserLatePreimages[UserBID]
                        \/ htlc.hash \notin UserPreimageInventory[UserAID] \cup UserPreimageInventory[UserBID]
                    /\ \A htlc \in persistedHTLCs :
                        /\ htlc.hash \notin UserPreimageInventory[UserAID] \/ htlc.hash \notin UserPreimageInventory[UserBID] => htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
                    /\ \A htlcData \in persistedHTLCs:
                        /\ htlcData \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cap persistedHTLCs : HTLCsAreEqual(htlcData, htlc) 
                        /\ htlcData \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cap persistedHTLCs : HTLCsAreEqual(htlcData, htlc)
                        /\ htlcData \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cap persistedHTLCs : HTLCsAreEqual(htlcData, htlc) 
                        /\ htlcData \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cap persistedHTLCs : HTLCsAreEqual(htlcData, htlc)
                    /\ \E cheater \in {ChannelUserVars[ChannelID][UserAID].Cheater} :
                        /\ \E htlcToClosedState \in HTLCToOnChainCommittedStateMappings(newHTLCs, newlyOnChainCommittedHTLCs, ChannelID, UserAID, UserBID) :
                            LET 
                                onChainCommittedHTLCs == newlyOnChainCommittedHTLCs
                                committedBalanceAlice == SumAmounts(onChainCommittedHTLCs \cap ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs)
                                committedBalanceBob == SumAmounts(onChainCommittedHTLCs \cap ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs)
                                newPreimagesForAlice == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : \E oHTLC \in persistedHTLCs : iHTLC.hash = oHTLC.hash}}
                                newPreimagesForBob == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : \E oHTLC \in persistedHTLCs : iHTLC.hash = oHTLC.hash}}
                                aliceReceivedAlreadyPending == SumAmounts(persistedHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserAID].IncomingHTLCs))
                                bobReceivedAlreadyPending == SumAmounts(persistedHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserBID].IncomingHTLCs))
                                aliceReceivedNotPending == SumAmounts(persistedHTLCs \cap HTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserAID].IncomingHTLCs))
                                bobReceivedNotPending == SumAmounts(persistedHTLCs \cap HTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserBID].IncomingHTLCs))
                                aliceSentAlreadyPending == SumAmounts({htlc \in persistedHTLCs \cap HTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs) : \E oHtlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : HTLCsAreEqual(htlc, oHtlc) /\ oHtlc.fulfilled})
                                bobSentAlreadyPending == SumAmounts({htlc \in persistedHTLCs \cap HTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs) : \E oHtlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : HTLCsAreEqual(htlc, oHtlc) /\ oHtlc.fulfilled})
                                persistedHTLCsHashes == {htlc.hash : htlc \in persistedHTLCs}
                                updatedWithoutPersistedHTLCs == updatedHTLCs \ persistedHTLCs
                            IN
                                    /\ newPreimagesForAlice \subseteq UserPreimageInventory[UserBID]
                                    /\ newPreimagesForBob \subseteq UserPreimageInventory[UserAID]
                                    /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserAID] = @ \cup newPreimagesForAlice,
                                                                                              ![UserBID] = @ \cup newPreimagesForBob]
                                    /\ UserLatePreimages' = [UserLatePreimages EXCEPT ![UserAID] = @ \cup ({htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : iHTLC.absTimelock + G < LedgerTime /\ \E oHTLC \in persistedHTLCs : iHTLC.hash = oHTLC.hash}} \ UserPreimageInventory[UserAID]), 
                                                                                      ![UserBID] = @ \cup ({htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : iHTLC.absTimelock + G < LedgerTime /\ \E oHTLC \in persistedHTLCs : iHTLC.hash = oHTLC.hash}} \ UserPreimageInventory[UserBID])]
                                    /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserAID].IncomingHTLCs = {htlc \in (@ \ updatedHTLCs) : htlc.hash \notin persistedHTLCsHashes}
                                                                                            \cup {[htlc EXCEPT !.state = htlcToClosedState[htlc]] : htlc \in (updatedWithoutPersistedHTLCs \cap @)}
                                                                                            \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in persistedHTLCsHashes}},
                                                                      ![ChannelID][UserAID].OutgoingHTLCs = {htlc \in (@ \ updatedHTLCs) : htlc.hash \notin persistedHTLCsHashes}
                                                                                            \cup {[htlc EXCEPT !.state = htlcToClosedState[htlc]] : htlc \in (updatedWithoutPersistedHTLCs \cap @)}
                                                                                            \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in persistedHTLCsHashes}},
                                                                      ![ChannelID][UserAID].OtherKnownPreimages = @ \cup newPreimagesForBob \cup newPreimagesForAlice,
                                                                      ![ChannelID][UserAID].Cheater = cheater,
                                                                    ![ChannelID][UserBID].IncomingHTLCs = {htlc \in (@ \ updatedHTLCs) : htlc.hash \notin persistedHTLCsHashes}
                                                                                            \cup {[htlc EXCEPT !.state = htlcToClosedState[htlc]] : htlc \in (updatedWithoutPersistedHTLCs \cap @)}
                                                                                            \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in persistedHTLCsHashes}},
                                                                  ![ChannelID][UserBID].OutgoingHTLCs = {htlc \in (@ \ updatedHTLCs) : htlc.hash \notin persistedHTLCsHashes}
                                                                                            \cup {[htlc EXCEPT !.state = htlcToClosedState[htlc]] : htlc \in (updatedWithoutPersistedHTLCs \cap @)}
                                                                                            \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in persistedHTLCsHashes}},
                                                                  ![ChannelID][UserBID].OtherKnownPreimages = @ \cup newPreimagesForBob \cup newPreimagesForAlice,
                                                                  ![ChannelID][UserBID].Cheater = cheater
                                                    ]
                                    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserAID] = @ - committedBalanceAlice + aliceReceivedAlreadyPending + aliceReceivedNotPending - bobReceivedNotPending - aliceSentAlreadyPending,
                                                                                        ![ChannelID][UserBID] = @ - committedBalanceBob + bobReceivedAlreadyPending + bobReceivedNotPending - aliceReceivedNotPending - bobSentAlreadyPending]
                                    /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ + committedBalanceAlice + committedBalanceBob - aliceReceivedAlreadyPending - bobReceivedAlreadyPending + aliceSentAlreadyPending + bobSentAlreadyPending]
                                    /\ ChannelUserBalance[ChannelID][UserAID]' >= 0
                                    /\ ChannelUserBalance[ChannelID][UserBID]' >= 0
                                    /\ ChannelPendingBalance[ChannelID]' >= 0
                                    /\ ChannelUserBalance[ChannelID][UserAID]' >= fulfilledHTLCBalanceAlice
                                    /\ ChannelUserBalance[ChannelID][UserBID]' >= fulfilledHTLCBalanceBob
                                    /\ (\E htlc \in ChannelUserVars[ChannelID][UserAID]'.IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID]'.OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID]'.IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID]'.OutgoingHTLCs : htlc.state = "NEW")
                                            => cheater # NullUser
                                    /\  \/ ChannelUserVars[ChannelID][UserAID]'.Cheater = NullUser
                                        \/  /\ ChannelUserVars[ChannelID][UserAID]'.Cheater = NameForUserID[UserAID]
                                                => ChannelUserBalance[ChannelID][UserAID]'
                                                        - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID]'.IncomingHTLCs : htlc.state \in {"FULFILLED"}})
                                                        - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID]'.OutgoingHTLCs : htlc.state \in {"NEW"} })
                                                    >= 0
                                            /\ ChannelUserVars[ChannelID][UserAID]'.Cheater = NameForUserID[UserBID]
                                                => ChannelUserBalance[ChannelID][UserBID]'
                                                        - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID]'.IncomingHTLCs : htlc.state \in {"FULFILLED"}})
                                                        - SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID]'.OutgoingHTLCs : htlc.state \in {"NEW"}})
                                                    >= 0
                                    /\ ChannelUserBalance[ChannelID][UserAID]' >= SumAmounts({htlc \in ChannelUserVars[ChannelID][UserAID]'.IncomingHTLCs : /\ htlc.state = "FULFILLED"
                                                                                                        /\ ~ValidMapping((htlc :> "PERSISTED"), htlc, LedgerTime, {htlc}, {htlc}, {htlc}, ChannelUserVars[ChannelID][UserAID]', ChannelUserVars[ChannelID][UserBID]', ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID], ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID], ~UserHonest[UserAID], ~UserHonest[UserBID], ChannelID, UserAID, UserBID)
                                                                                      })
                                    /\ ChannelUserBalance[ChannelID][UserBID]' >= SumAmounts({htlc \in ChannelUserVars[ChannelID][UserBID]'.IncomingHTLCs : /\ htlc.state = "FULFILLED"
                                                                                                    /\ ~ValidMapping((htlc :> "PERSISTED"), htlc, LedgerTime, {htlc}, {htlc}, {htlc}, ChannelUserVars[ChannelID][UserAID]', ChannelUserVars[ChannelID][UserBID]', ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserAID], ChannelUserVars[ChannelID][UserAID].Cheater = NameForUserID[UserBID], ~UserHonest[UserAID], ~UserHonest[UserBID], ChannelID, UserAID, UserBID)
                                                                                      })
                                    /\ LET processedPaymentsAlice == {payment \in UserPayments[UserAID] : payment.state = "NEW" /\ \E htlc \in persistedHTLCs : htlc.id = payment.id}
                                           receivedPaymentsAlice == {payment \in processedPaymentsAlice : payment.receiver = UserAID}
                                           sentPaymentsAlice == {payment \in processedPaymentsAlice : payment.sender = UserAID}
                                           processedPaymentsBob == {payment \in UserPayments[UserBID] : payment.state = "NEW" /\ \E htlc \in persistedHTLCs : htlc.id = payment.id}
                                           receivedPaymentsBob == {payment \in processedPaymentsBob : payment.receiver = UserBID}
                                           sentPaymentsBob == {payment \in processedPaymentsBob : payment.sender = UserBID}
                                       IN   /\ UserPayments' = [UserPayments EXCEPT ![UserAID] = (@ \ processedPaymentsAlice) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPaymentsAlice},
                                                                                    ![UserBID] = (@ \ processedPaymentsBob) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPaymentsBob}]
                                            /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserAID] = @ + SumAmounts(receivedPaymentsAlice) - SumAmounts(sentPaymentsAlice),
                                                                                                ![UserBID] = @ + SumAmounts(receivedPaymentsBob) - SumAmounts(sentPaymentsBob)]
    /\ UNCHANGED <<UserExtBalance, UserHonest>>
    /\ UNCHANGED UnchangedVars

HTLCsToPossiblyFulfillOnChain(ledgerTime, ChannelID, UserAID, UserBID) ==
    {htlc \in HTLCsByStates({"COMMITTED", "FULFILLED", "OFF-TIMEDOUT"}, AllHTLCs(ChannelID, UserAID, UserBID)) :
        /\ htlc.hash \in ChannelUserVars[ChannelID][UserAID].OnChainHTLCs
        /\
            \/ ledgerTime <= htlc.absTimelock + G - 1
            \/  /\ htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserAID] \ UserLatePreimages[UserAID] \/ ~UserHonest[UserAID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
                /\ htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs => htlc.hash \in UserPreimageInventory[UserBID] \ UserLatePreimages[UserBID] \/ ~UserHonest[UserBID] \/ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
    }
    
    
FulfillHTLCsOnChainP(ledgerTime, ChannelID, UserAID, UserBID) ==
    /\ ChannelUserState[ChannelID][UserAID] \in {"closing-time-set", "closing"}
    /\ ChannelUserState[ChannelID][UserBID] \in {"closing-time-set", "closing"}
    /\ UNCHANGED <<ChannelUserState>>
    /\ \E HTLCsToFulfill \in SUBSET HTLCsToPossiblyFulfillOnChain(ledgerTime, ChannelID, UserAID, UserBID) :
            /\ Cardinality(HTLCsToFulfill) > 0
            /\ \A htlcData \in HTLCsToFulfill:
                /\ htlcData \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs \cap HTLCsToFulfill : HTLCsAreEqual(htlcData, htlc)
                /\ htlcData \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cap HTLCsToFulfill : HTLCsAreEqual(htlcData, htlc)
                /\ htlcData \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cap HTLCsToFulfill : HTLCsAreEqual(htlcData, htlc)
                /\ htlcData \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs => \E htlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cap HTLCsToFulfill : HTLCsAreEqual(htlcData, htlc)
            /\ \A htlcData \in HTLCsToFulfill :
                /\ htlcData.state = "FULFILLED" => \E htlc \in HTLCsToFulfill : HTLCsAreEqual(htlcData, htlc) /\ htlc.state # "FULFILLED"
            /\ LET newPreimagesForAlice == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : \E oHTLC \in HTLCsToFulfill : iHTLC.hash = oHTLC.hash}}
                   newPreimagesForBob == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : \E oHTLC \in HTLCsToFulfill : iHTLC.hash = oHTLC.hash}}
                   newlyFulfilledHTLCBalanceAlice == SumAmounts({htlc \in HTLCsToFulfill \cap ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : ~htlc.fulfilled})
                   newlyFulfilledHTLCBalanceBob == SumAmounts({htlc \in HTLCsToFulfill \cap ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : ~htlc.fulfilled})
                   HTLCsToFulfillHashes == {htlc.hash : htlc \in HTLCsToFulfill}
               IN 
                /\ newPreimagesForAlice \subseteq UserPreimageInventory[UserBID]
                /\ newPreimagesForBob \subseteq UserPreimageInventory[UserAID]
                /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserAID] = @ \cup newPreimagesForAlice,
                                                                          ![UserBID] = @ \cup newPreimagesForBob]
                /\ UserLatePreimages' = [UserLatePreimages EXCEPT ![UserAID] = @ \cup ({htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : iHTLC.absTimelock + G < LedgerTime /\ \E oHTLC \in HTLCsToFulfill : iHTLC.hash = oHTLC.hash}} \ UserPreimageInventory[UserAID]),
                                                                  ![UserBID] = @ \cup ({htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : iHTLC.absTimelock + G < LedgerTime /\ \E oHTLC \in HTLCsToFulfill : iHTLC.hash = oHTLC.hash}} \ UserPreimageInventory[UserBID])]
                /\ ChannelUserVars' = [ChannelUserVars EXCEPT
                                             ![ChannelID][UserAID].OutgoingHTLCs = {htlc \in @ : htlc.hash \notin HTLCsToFulfillHashes}
                                                                    \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in HTLCsToFulfillHashes}},
                                             ![ChannelID][UserAID].IncomingHTLCs = {htlc \in @ : htlc.hash \notin HTLCsToFulfillHashes}
                                                                    \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in HTLCsToFulfillHashes}},
                                             ![ChannelID][UserAID].OtherKnownPreimages = @ \cup newPreimagesForBob \cup newPreimagesForAlice,
                                             ![ChannelID][UserBID].OutgoingHTLCs = {htlc \in @ : htlc.hash \notin HTLCsToFulfillHashes}
                                                                    \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in HTLCsToFulfillHashes}},
                                             ![ChannelID][UserBID].IncomingHTLCs = {htlc \in @ : htlc.hash \notin HTLCsToFulfillHashes}
                                                                    \cup {[htlcData EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlcData \in {htlc \in @ : htlc.hash \in HTLCsToFulfillHashes}},
                                             ![ChannelID][UserBID].OtherKnownPreimages = @ \cup newPreimagesForBob \cup newPreimagesForAlice
                                             ]
                /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserAID] = @ + newlyFulfilledHTLCBalanceAlice,
                                                                    ![ChannelID][UserBID] = @ + newlyFulfilledHTLCBalanceBob]
                /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - newlyFulfilledHTLCBalanceAlice - newlyFulfilledHTLCBalanceBob]
                /\ LET processedPaymentsAlice == {payment \in UserPayments[UserAID] : payment.state = "NEW" /\ \E htlc \in HTLCsToFulfill : htlc.id = payment.id}
                       receivedPaymentsAlice == {payment \in processedPaymentsAlice : payment.receiver = UserAID}
                       sentPaymentsAlice == {payment \in processedPaymentsAlice : payment.sender = UserAID}
                       processedPaymentsBob == {payment \in UserPayments[UserBID] : payment.state = "NEW" /\ \E htlc \in HTLCsToFulfill : htlc.id = payment.id}
                       receivedPaymentsBob == {payment \in processedPaymentsBob : payment.receiver = UserBID}
                       sentPaymentsBob == {payment \in processedPaymentsBob : payment.sender = UserBID}
                   IN   /\ UserPayments' = [UserPayments EXCEPT ![UserAID] = (@ \ processedPaymentsAlice) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPaymentsAlice},
                                                                ![UserBID] = (@ \ processedPaymentsBob) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPaymentsBob}]
                        /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserAID] = @ + SumAmounts(receivedPaymentsAlice) - SumAmounts(sentPaymentsAlice),
                                                                            ![UserBID] = @ + SumAmounts(receivedPaymentsBob) - SumAmounts(sentPaymentsBob)]
    /\ UNCHANGED <<UserHonest, UserExtBalance>>
    /\ UNCHANGED UnchangedVars

FulfillHTLCsOnChain(ChannelID, UserAID, UserBID) ==
    FulfillHTLCsOnChainP(LedgerTime, ChannelID, UserAID, UserBID)

ClosePaymentChannelWithTime(ledgerTime, ChannelID, UserAID, UserBID) ==
    /\  \/  /\ ChannelUserState[ChannelID][UserAID] = "closing"
            /\ ChannelUserState[ChannelID][UserBID] = "closing"
        \/  /\ ChannelUserVars[ChannelID][UserAID].Cheater # NullUser
            /\ ChannelUserState[ChannelID][UserAID] = "closing-time-set"
            /\ ChannelUserState[ChannelID][UserBID] = "closing-time-set"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserAID] = "closed",
                                                    ![ChannelID][UserBID] = "closed"]
    /\ LET allHTLCs == ChannelUserVars[ChannelID][UserAID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserBID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs
           cheater == ChannelUserVars[ChannelID][UserAID].Cheater
           aliceHasCheated == cheater = NameForUserID[UserAID]
           bobHasCheated == cheater = NameForUserID[UserBID]
       IN
           /\ \E htlcToClosedState \in HTLCToClosedStateMappings(aliceHasCheated, bobHasCheated, ledgerTime, ChannelUserVars[ChannelID][UserAID], ChannelUserVars[ChannelID][UserBID], ~UserHonest[UserAID], ~UserHonest[UserBID], ChannelID, UserAID, UserBID) :
            LET onChainFulfilledHTLCs == {htlc \in allHTLCs : htlc.state \notin {"FULFILLED", "PERSISTED"} /\ htlcToClosedState[htlc] = "PERSISTED"}
                onChainTimedoutHTLCs == {htlc \in allHTLCs : htlc.state \in {"COMMITTED", "FULFILLED", "OFF-TIMEDOUT"} /\ htlcToClosedState[htlc] = "TIMEDOUT"}
                onChainPunishedHTLCs == {htlc \in allHTLCs : htlcToClosedState[htlc] = "PUNISHED"}
                \* HTLCs that have been started to be committed and are fulfilled on-chain
                aliceReceivedNotPending == SumAmounts(onChainFulfilledHTLCs \cap HTLCsByStates({"NEW", "TIMEDOUT"}, ChannelUserVars[ChannelID][UserAID].IncomingHTLCs))
                                               + SumAmounts(onChainTimedoutHTLCs \cap HTLCsByStates({"FULFILLED"}, ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs))
                aliceReceivedAlreadyPending == SumAmounts(onChainFulfilledHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserAID].IncomingHTLCs))
                                               + SumAmounts(onChainTimedoutHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs))
                                               + (IF ~aliceHasCheated THEN SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserAID].IncomingHTLCs)) ELSE 0)
                                               + (IF ~aliceHasCheated THEN SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserBID].IncomingHTLCs)) ELSE 0)
                aliceWasPunishedWith == IF aliceHasCheated
                                        THEN SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"NEW", "TIMEDOUT"}, ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs))
                                             + SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"FULFILLED"}, ChannelUserVars[ChannelID][UserAID].IncomingHTLCs))
                                        ELSE 0
                bobReceivedNotPending == SumAmounts(onChainFulfilledHTLCs \cap HTLCsByStates({"NEW", "TIMEDOUT"}, ChannelUserVars[ChannelID][UserBID].IncomingHTLCs))
                                               + SumAmounts(onChainTimedoutHTLCs \cap HTLCsByStates({"FULFILLED"}, ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs))
                bobReceivedAlreadyPending == SumAmounts(onChainFulfilledHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserBID].IncomingHTLCs))
                                               + SumAmounts(onChainTimedoutHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs))
                                             + (IF ~bobHasCheated THEN SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserBID].IncomingHTLCs)) ELSE 0)
                                             + (IF ~bobHasCheated THEN SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"COMMITTED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserAID].IncomingHTLCs)) ELSE 0)
                bobWasPunishedWith == IF bobHasCheated
                                      THEN SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"NEW", "TIMEDOUT"}, ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs))
                                           + SumAmounts(onChainPunishedHTLCs \cap HTLCsByStates({"FULFILLED"}, ChannelUserVars[ChannelID][UserBID].IncomingHTLCs))
                                      ELSE 0
                fulfilledHTLCs == onChainFulfilledHTLCs \cup HTLCsByStates({"FULFILLED"}, allHTLCs)
            IN
                /\ \E potentialOnChainFulfilledHTLCs \in SUBSET {htlc \in allHTLCs : htlc.state \in {"NEW", "COMMITTED", "OFF-TIMEDOUT"} \ {"NEW"} /\ htlcToClosedState[htlc] = "PUNISHED"} :
                    LET newPreimagesForAlice == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : \E oHTLC \in (onChainFulfilledHTLCs \cup potentialOnChainFulfilledHTLCs) : iHTLC.hash = oHTLC.hash}}
                        newPreimagesForBob == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : \E oHTLC \in (onChainFulfilledHTLCs \cup potentialOnChainFulfilledHTLCs) : iHTLC.hash = oHTLC.hash}}
                    IN
                    /\ \A htlc \in potentialOnChainFulfilledHTLCs : \E oHtlc \in allHTLCs : htlc.hash # oHtlc.hash \* another HTLC must exist so that htlc can be committed in an old ctx
                    /\ \A htlc \in potentialOnChainFulfilledHTLCs :
                        \A oHtlc \in allHTLCs :
                            htlc.hash = oHtlc.hash => oHtlc \in potentialOnChainFulfilledHTLCs 
                    /\ newPreimagesForAlice \subseteq UserPreimageInventory[UserBID]
                    /\ newPreimagesForBob \subseteq UserPreimageInventory[UserAID]
                    /\ ChannelUserVars' = [ChannelUserVars EXCEPT
                              ![ChannelID][UserAID].IncomingHTLCs = {[htlc EXCEPT !.state = htlcToClosedState[htlc], !.fulfilled = @ \/ (htlcToClosedState[htlc] = "PERSISTED" \/ htlc \in potentialOnChainFulfilledHTLCs)] : htlc \in @},
                              ![ChannelID][UserAID].OutgoingHTLCs = {[htlc EXCEPT !.state = htlcToClosedState[htlc], !.fulfilled = @ \/ (htlcToClosedState[htlc] = "PERSISTED" \/ htlc \in potentialOnChainFulfilledHTLCs)] : htlc \in @},
                              ![ChannelID][UserAID].OtherKnownPreimages = @ \cup newPreimagesForBob \cup newPreimagesForAlice,
                              ![ChannelID][UserAID].Cheater = cheater,
                              ![ChannelID][UserAID].HaveCheated = aliceHasCheated,
                              ![ChannelID][UserAID].Debug = {htlc.hash : htlc \in {htlc \in allHTLCs : htlc.state = "PERSISTED"} },
                              ![ChannelID][UserBID].IncomingHTLCs = {[htlc EXCEPT !.state = htlcToClosedState[htlc], !.fulfilled = @ \/ (htlcToClosedState[htlc] = "PERSISTED" \/ htlc \in potentialOnChainFulfilledHTLCs)] : htlc \in @},
                              ![ChannelID][UserBID].OutgoingHTLCs = {[htlc EXCEPT !.state = htlcToClosedState[htlc], !.fulfilled = @ \/ (htlcToClosedState[htlc] = "PERSISTED" \/ htlc \in potentialOnChainFulfilledHTLCs)] : htlc \in @},
                              ![ChannelID][UserBID].OtherKnownPreimages = @ \cup newPreimagesForAlice \cup newPreimagesForBob,
                              ![ChannelID][UserBID].Cheater = cheater,
                              ![ChannelID][UserBID].HaveCheated = bobHasCheated,
                              ![ChannelID][UserBID].Debug = {htlc.hash : htlc \in {htlc \in allHTLCs : htlc.state = "PERSISTED"} }]
                    /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserAID] = @ \cup newPreimagesForAlice,
                                                                              ![UserBID] = @ \cup newPreimagesForBob]
                    /\ LET newLatePreimagesA == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : iHTLC.absTimelock + G < LedgerTime /\ \E oHTLC \in (onChainFulfilledHTLCs \cup potentialOnChainFulfilledHTLCs) : iHTLC.hash = oHTLC.hash}}
                           newLatePreimagesB == {htlc.hash : htlc \in {iHTLC \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : iHTLC.absTimelock + G < LedgerTime /\ \E oHTLC \in (onChainFulfilledHTLCs \cup potentialOnChainFulfilledHTLCs) : iHTLC.hash = oHTLC.hash}}
                       IN UserLatePreimages' = [UserLatePreimages EXCEPT ![UserAID] = @ \cup newLatePreimagesA,
                                                                         ![UserBID] = @ \cup newLatePreimagesB]
                    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserAID] =
                                       IF aliceHasCheated
                                       THEN 0
                                       ELSE IF bobHasCheated
                                       THEN @ + ChannelUserBalance[ChannelID][UserBID] + ChannelPendingBalance[ChannelID]
                                       ELSE @ + aliceReceivedNotPending + aliceReceivedAlreadyPending - bobReceivedNotPending,
                                ![ChannelID][UserBID] =
                                     IF bobHasCheated
                                     THEN 0
                                     ELSE IF aliceHasCheated
                                     THEN ChannelUserBalance[ChannelID][UserAID] + @ + ChannelPendingBalance[ChannelID]
                                     ELSE @ + bobReceivedNotPending + bobReceivedAlreadyPending - aliceReceivedNotPending]
                    /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - aliceReceivedAlreadyPending - bobReceivedAlreadyPending]
                    /\ ChannelUserBalance[ChannelID][UserAID]' >= 0
                    /\ ChannelUserBalance[ChannelID][UserBID]' >= 0
                    /\ ChannelPendingBalance[ChannelID]' >= 0
                    /\ Cardinality(onChainPunishedHTLCs) > 0 /\ cheater = NullUser => PrintT("Error! Cardinality(onChainPunishedHTLCs) > 0 but no cheater")
                    /\ LET persistedHTLCsAlice == {aHtlc \in ChannelUserVars[ChannelID][UserAID].IncomingHTLCs : aHtlc.fulfilled = FALSE /\ \E oHtlc \in ChannelUserVars[ChannelID][UserAID]'.IncomingHTLCs :
                                                /\ aHtlc.hash = oHtlc.hash
                                                /\ oHtlc.fulfilled = TRUE} \cup
                                             {aHtlc \in ChannelUserVars[ChannelID][UserAID].OutgoingHTLCs : aHtlc.fulfilled = FALSE /\ \E oHtlc \in ChannelUserVars[ChannelID][UserAID]'.OutgoingHTLCs :
                                                /\ aHtlc.hash = oHtlc.hash
                                                /\ oHtlc.fulfilled = TRUE}
                           processedPaymentsAlice == {payment \in UserPayments[UserAID] : payment.state = "NEW" /\ \E htlc \in persistedHTLCsAlice : htlc.id = payment.id}
                           receivedPaymentsAlice == {payment \in processedPaymentsAlice : payment.receiver = UserAID}
                           sentPaymentsAlice == {payment \in processedPaymentsAlice : payment.sender = UserAID}
                           persistedHTLCsBob == {aHtlc \in ChannelUserVars[ChannelID][UserBID].IncomingHTLCs : aHtlc.fulfilled = FALSE /\ \E oHtlc \in ChannelUserVars[ChannelID][UserBID]'.IncomingHTLCs :
                                                /\ aHtlc.hash = oHtlc.hash
                                                /\ oHtlc.fulfilled = TRUE} \cup
                                             {aHtlc \in ChannelUserVars[ChannelID][UserBID].OutgoingHTLCs : aHtlc.fulfilled = FALSE /\ \E oHtlc \in ChannelUserVars[ChannelID][UserBID]'.OutgoingHTLCs :
                                                /\ aHtlc.hash = oHtlc.hash
                                                /\ oHtlc.fulfilled = TRUE}
                           processedPaymentsBob == {payment \in UserPayments[UserBID] : payment.state = "NEW" /\ \E htlc \in persistedHTLCsBob : htlc.id = payment.id}
                           receivedPaymentsBob == {payment \in processedPaymentsBob : payment.receiver = UserBID}
                           sentPaymentsBob == {payment \in processedPaymentsBob : payment.sender = UserBID}
                       IN   /\ UserPayments' = [UserPayments EXCEPT ![UserAID] = (@ \ processedPaymentsAlice) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPaymentsAlice},
                                                                    ![UserBID] = (@ \ processedPaymentsBob) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPaymentsBob}]
                            /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserAID] = @ + SumAmounts(receivedPaymentsAlice) - SumAmounts(sentPaymentsAlice),
                                                                                ![UserBID] = @ + SumAmounts(receivedPaymentsBob) - SumAmounts(sentPaymentsBob)]
    /\ UNCHANGED <<UserHonest, UserExtBalance>>
    /\ UNCHANGED UnchangedVars

ClosePaymentChannel(ChannelID, UserAID, UserBID) ==
    ClosePaymentChannelWithTime(LedgerTime, ChannelID, UserAID, UserBID)
    
Balances(ChannelID, UserAID, UserBID) ==
    [Alice |-> ChannelUserBalance[ChannelID][UserAID], Bob |-> ChannelUserBalance[ChannelID][UserBID], Pending |-> ChannelPendingBalance[ChannelID]]

UoCSet(users) == {users[1], users[2]}
Init(ChannelIDs, UserIDs, UsersOfChannel) ==
    /\ LedgerTime = 1
    /\ UserPreimageInventory = [u \in UserIDs |-> {}]
    /\ ChannelUserVars = [c \in ChannelIDs |-> [u \in UoCSet(UsersOfChannel[c]) |-> [
        MyKey |-> NameForUserID[u],
        FundingInputTxId |-> c,
        HaveCheated |-> FALSE,
        OtherKnownPreimages |-> {},
        IncomingHTLCs |-> {},
        OutgoingHTLCs |-> {},
        FulfilledAfterTimeoutHTLCs |-> {},
        HTLCsPersistedBeforeClosing |-> {},
        Debug |-> {},
        ClosingTime |-> -1,
        OnChainHTLCs |-> {},
        Cheater |-> NullUser ]]]
    /\ ChannelUserState = [c \in ChannelIDs |-> [u \in UoCSet(UsersOfChannel[c]) |-> "init"]]
    /\ ChannelUserBalance = [c \in ChannelIDs |-> [u \in UoCSet(UsersOfChannel[c]) |-> 0]]
    /\ ChannelPendingBalance = [c \in ChannelIDs |-> 0]
    
Next(ChannelID, UserAID, UserBID) ==
    \/ OpenPaymentChannel(ChannelID, UserAID, UserBID)
    \/ UpdatePaymentChannel(ChannelID, UserAID, UserBID)
    \/ SetOnChainHTLCsAndCheater(ChannelID, UserAID, UserBID)
    \/ FulfillIncomingHTLCsOnChain(ChannelID, UserAID, UserBID)
    \/ NoteFulfilledHTLCsOnChain(ChannelID, UserAID, UserBID)
    \/ CommitHTLCsOnChain(ChannelID, UserAID, UserBID)
    \/ FulfillHTLCsOnChain(ChannelID, UserAID, UserBID)
    \/ ClosePaymentChannel(ChannelID, UserAID, UserBID)
    

=============================================================================
