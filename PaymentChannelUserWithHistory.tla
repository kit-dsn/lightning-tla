------------------- MODULE PaymentChannelUserWithHistory -------------------

EXTENDS PaymentChannelUser, Integers

VARIABLES
    HTLCHistory,
    IsAfterOnChainCommit,
    IsAfterClosingTimeSet,
    ChannelPersistedHTLCsBeforeClose,
    AbstractedCUState, \*AbstractedChannelUserState,
    AbstractedCUVars \*AbstractedChannelUserVars

HTLCHistoryEntryForHTLC(htlc, latestCommitmentTXId, reason, ChannelID, UserID) ==
    [amount |-> htlc.amount,
     hash |-> htlc.hash,
     id |-> htlc.id,
     absTimelock |-> htlc.absTimelock,
     state |-> htlc.state,
     reason |-> reason,
     fulfilled |-> htlc.fulfilled,
     timedout |-> htlc.timedout,
     punished |-> htlc.punished,
     latestCommitmentTXId |-> latestCommitmentTXId,
     afterClosingTimeSet |-> IsAfterClosingTimeSet[ChannelID][UserID],
     afterOnChainCommit |-> IsAfterOnChainCommit[ChannelID][UserID],
     afterHavePunished |-> ChannelUserDetailVars[ChannelID][UserID].HavePunished \/ \E tx \in LedgerTx : TransactionCanBeRevokedWithExtraKeys(tx, LedgerTx, FALSE, { msg.data.rSecretKey : msg \in {msg \in SeqToSet(ChannelMessages[ChannelID]) : msg.recipient = NameForUserID[UserID]}}, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID] ),
     index |-> Cardinality(HTLCHistory[ChannelID][UserID].IncomingHTLCs) + Cardinality(HTLCHistory[ChannelID][UserID].OutgoingHTLCs)
     ]

HTLCsByStates2(states, HTLCSet) == {htlc \in HTLCSet : htlc.state \in states}
HTLCsByReason(reasons, HTLCSet) == {htlc \in HTLCSet : htlc.reason \in reasons}

GetPersistedHTLCs(abstractedAliceVars) ==
    {htlc.hash : htlc \in { htlc \in abstractedAliceVars.IncomingHTLCs \cup abstractedAliceVars.OutgoingHTLCs : htlc.state = "PERSISTED" }}

SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID) ==
    ChannelPersistedHTLCsBeforeClose' = 
        [ChannelPersistedHTLCsBeforeClose EXCEPT ![ChannelID] =
            IF AbstractedCUState[ChannelID][UserID] = "closed"
            THEN @
            ELSE IF AbstractedCUState[ChannelID][UserID]' = "closed"
            THEN GetPersistedHTLCs(AbstractedCUVars[ChannelID][UserID]) \cup GetPersistedHTLCs(AbstractedCUVars[ChannelID][OtherUserID])
            ELSE {}]

(* =============================================================================================
    all actions must follow the following form: ActionH == Action /\ HTLCHistory' = expression 
   ============================================================================================= *)

SendOpenChannelH(ChannelID, UserID, OtherUserID) ==
    /\ SendOpenChannel(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
                                       
SendAcceptChannelH(ChannelID, UserID, OtherUserID) ==
    /\ SendAcceptChannel(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
                                       
CreateFundingTransactionH(ChannelID, UserID, OtherUserID) ==
    /\ CreateFundingTransaction(ChannelID, UserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
                 
SendSignedFirstCommitTransactionH(ChannelID, UserID, OtherUserID) ==
    /\ SendSignedFirstCommitTransaction(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
                                                  
ReplyWithFirstCommitTransactionH(ChannelID, UserID, OtherUserID) ==
    /\ ReplyWithFirstCommitTransaction(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)

ReceiveCommitTransactionH(ChannelID, UserID, OtherUserID) ==
    /\ ReceiveCommitTransaction(ChannelID, UserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
PublishFundingTransactionH(ChannelID, UserID, OtherUserID) ==
    /\ PublishFundingTransaction(ChannelID, UserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
          
NoteThatFundingTransactionPublishedH(ChannelID, UserID, OtherUserID) ==
    /\ NoteThatFundingTransactionPublished(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
SendNewRevocationKeyH(ChannelID, UserID, OtherUserID) ==
    /\ SendNewRevocationKey(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
ReceiveNewRevocationKeyH(ChannelID, UserID, OtherUserID) ==
    /\ ReceiveNewRevocationKey(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)

SendSignedCommitmentH(ChannelID, UserID, OtherUserID) ==
    /\ SendSignedCommitment(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
ReceiveSignedCommitmentH(ChannelID, UserID, OtherUserID) ==
    /\ ReceiveSignedCommitment(ChannelID, UserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
RevokeAndAckH(ChannelID, UserID, OtherUserID) ==
    /\ RevokeAndAck(ChannelID, UserID, OtherUserID)
    /\ LET nowCommittedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           nowCommittedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           nowPersistedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           nowPersistedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           nowTimedoutOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
           nowTimedoutIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
       IN /\ HTLCHistory' = [HTLCHistory EXCEPT ![ChannelID][UserID].OutgoingHTLCs = @
                                                                      \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-PERSISTED", ChannelID, UserID) : htlc \in nowPersistedOutgoingHTLCs}
                                                                      \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-TIMEDOUT", ChannelID, UserID) : htlc \in nowTimedoutOutgoingHTLCs}
                                                                      \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "COMMITTED", ChannelID, UserID) : htlc \in nowCommittedOutgoingHTLCs},
                                                ![ChannelID][UserID].IncomingHTLCs = @
                                                                      \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-PERSISTED", ChannelID, UserID) : htlc \in nowPersistedIncomingHTLCs}
                                                                      \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-TIMEDOUT", ChannelID, UserID) : htlc \in nowTimedoutIncomingHTLCs}
                                                                      \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "COMMITTED", ChannelID, UserID) : htlc \in nowCommittedIncomingHTLCs} ]
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)

    
ReceiveRevocationKeyH(ChannelID, UserID, OtherUserID) ==
    /\ ReceiveRevocationKey(ChannelID, UserID, OtherUserID)
    /\ LET nowCommittedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           nowCommittedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           nowPersistedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           nowPersistedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           nowTimedoutOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
           nowTimedoutIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
           justOnChainPersistedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : \E htlcHist \in HTLCHistory[ChannelID][UserID].OutgoingHTLCs :
                                                            htlc.hash = htlcHist.hash /\ htlcHist.reason = "ON-CHAIN-PERSISTED" /\ htlcHist.state = "SENT-REMOVE" 
                                                    }
           offChainAfterOnChainCommittedHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs : \E htlcHist \in HTLCHistory[ChannelID][UserID].IncomingHTLCs :
                                                            /\ LedgerTime < htlc.absTimelock
                                                            /\ htlc.hash = htlcHist.hash
                                                            /\ htlcHist.reason = "ON-CHAIN-COMMITTED" /\ htlcHist.state = "SENT-COMMIT"
                                                    }
           updatedHTLCs == ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs
       IN /\ HTLCHistory' = [HTLCHistory EXCEPT ![ChannelID][UserID].OutgoingHTLCs = @
                                                                  \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-PERSISTED", ChannelID, UserID) : htlc \in nowPersistedOutgoingHTLCs \cup justOnChainPersistedOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-TIMEDOUT", ChannelID, UserID) : htlc \in nowTimedoutOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "COMMITTED", ChannelID, UserID) : htlc \in nowCommittedOutgoingHTLCs},
                                                ![ChannelID][UserID].IncomingHTLCs = @
                                                                  \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-PERSISTED", ChannelID, UserID) : htlc \in nowPersistedIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "OFF-CHAIN-TIMEDOUT", ChannelID, UserID) : htlc \in nowTimedoutIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlc, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, "COMMITTED", ChannelID, UserID) : htlc \in nowCommittedIncomingHTLCs \cup offChainAfterOnChainCommittedHTLCs} ]
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)

CloseChannelH(ChannelID, UserID, OtherUserID) ==
    /\ CloseChannel(ChannelID, UserID)
    /\ LET committedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           committedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           abortedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "ABORTED"}
           abortedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "ABORTED"}
           persistedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           persistedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           timedoutOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
           timedoutIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
       IN /\ HTLCHistory' = [HTLCHistory EXCEPT ![ChannelID][UserID].StateBeforeClosing = ChannelUserState[ChannelID][UserID],
                                                ![ChannelID][UserID].IncomingHTLCs = @
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-COMMITTED", ChannelID, UserID) : htlcData \in committedIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-PERSISTED", ChannelID, UserID) : htlcData \in persistedIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-TIMEDOUT", ChannelID, UserID) : htlcData \in timedoutIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-ABORTED", ChannelID, UserID) : htlcData \in abortedIncomingHTLCs},
                                                ![ChannelID][UserID].OutgoingHTLCs = @
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-COMMITTED", ChannelID, UserID) : htlcData \in committedOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-PERSISTED", ChannelID, UserID) : htlcData \in persistedOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-TIMEDOUT", ChannelID, UserID) : htlcData \in timedoutOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-ABORTED", ChannelID, UserID) : htlcData \in abortedOutgoingHTLCs}]
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)

    
WillPunishLaterH(ChannelID, UserID, OtherUserID) ==
    /\ WillPunishLater(ChannelID, UserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
    
IgnoreMessageDuringClosingH(ChannelID, UserID, OtherUserID) ==
    /\ IgnoreMessageDuringClosing(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)

ClosingActionsH(ChannelID, UserID, OtherUserID) ==
    /\ ClosingActions(ChannelID, UserID, OtherUserID)
    /\ LET committedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           committedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "COMMITTED"}
           abortedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "ABORTED"}
           abortedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "ABORTED"}
           persistedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           persistedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PERSISTED"}
           htlcsForWhichPreimageReceived == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserID].IncomingHTLCs : \/ htlc.hash \in UserPreimageInventory[UserID]' \ UserPreimageInventory[UserID] }
           timedoutOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
           timedoutIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "TIMEDOUT"}
           punishedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \ ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.OutgoingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PUNISHED"}
           punishedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \ ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : \E aHTLC \in ChannelUserVars[ChannelID][UserID]'.IncomingHTLCs : aHTLC.hash = htlc.hash /\ aHTLC.state = "PUNISHED"}
       IN /\ HTLCHistory' = [HTLCHistory EXCEPT ![ChannelID][UserID].IncomingHTLCs = @
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-COMMITTED", ChannelID, UserID) : htlcData \in committedIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-PERSISTED", ChannelID, UserID) : htlcData \in persistedIncomingHTLCs \cup (htlcsForWhichPreimageReceived \cap ChannelUserVars[ChannelID][UserID].IncomingHTLCs)}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-TIMEDOUT", ChannelID, UserID) : htlcData \in timedoutIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-ABORTED", ChannelID, UserID) : htlcData \in abortedIncomingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "FINALLY-PUNISHED", ChannelID, UserID) : htlcData \in punishedIncomingHTLCs},
                                                ![ChannelID][UserID].OutgoingHTLCs = @
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-COMMITTED", ChannelID, UserID) : htlcData \in committedOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-PERSISTED", ChannelID, UserID) : htlcData \in persistedOutgoingHTLCs \cup (htlcsForWhichPreimageReceived \cap ChannelUserVars[ChannelID][UserID].OutgoingHTLCs)}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-TIMEDOUT", ChannelID, UserID) : htlcData \in timedoutOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "ON-CHAIN-ABORTED", ChannelID, UserID) : htlcData \in abortedOutgoingHTLCs}
                                                                  \cup {HTLCHistoryEntryForHTLC(htlcData, ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, "FINALLY-PUNISHED", ChannelID, UserID) : htlcData \in punishedOutgoingHTLCs},
                                                ![ChannelID][UserID].StateBeforeClosing = IF @ = "" /\ ChannelUserState[ChannelID][UserID]' = "closing" THEN ChannelUserState[ChannelID][UserID] ELSE @,
                                                ![ChannelID][UserID].OtherWasHonestBeforeCheat = IF ~ChannelUserVars[ChannelID][UserID].HaveCheated /\ ChannelUserVars[ChannelID][UserID]'.HaveCheated THEN UserHonest[OtherUserID] ELSE @]
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
InitiateShutdownH(ChannelID, UserID, OtherUserID) ==
    /\ InitiateShutdown(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
ReceiveInitiateShutdownH(ChannelID, UserID, OtherUserID) ==
    /\ ReceiveInitiateShutdown(ChannelID, UserID)
    /\ UNCHANGED <<HTLCHistory>>
    /\ SetChannelPersistedHTLCsBeforeClose(ChannelID, UserID, OtherUserID)
    
NextH(ChannelID, UserID, OtherUserID) ==
    \/ SendOpenChannelH(ChannelID, UserID, OtherUserID)
    \/ SendAcceptChannelH(ChannelID, UserID, OtherUserID)
    \/ CreateFundingTransactionH(ChannelID, UserID, OtherUserID)
    \/ SendSignedFirstCommitTransactionH(ChannelID, UserID, OtherUserID)
    \/ ReplyWithFirstCommitTransactionH(ChannelID, UserID, OtherUserID)
    \/ ReceiveCommitTransactionH(ChannelID, UserID, OtherUserID)
    \/ PublishFundingTransactionH(ChannelID, UserID, OtherUserID)
    \/ NoteThatFundingTransactionPublishedH(ChannelID, UserID, OtherUserID)
    \/ SendNewRevocationKeyH(ChannelID, UserID, OtherUserID)
    \/ ReceiveNewRevocationKeyH(ChannelID, UserID, OtherUserID)
    \/ SendSignedCommitmentH(ChannelID, UserID, OtherUserID)
    \/ ReceiveSignedCommitmentH(ChannelID, UserID, OtherUserID)
    \/ RevokeAndAckH(ChannelID, UserID, OtherUserID)
    \/ ReceiveRevocationKeyH(ChannelID, UserID, OtherUserID)
    \/ CloseChannelH(ChannelID, UserID, OtherUserID)
    \/ ClosingActionsH(ChannelID, UserID, OtherUserID)
    \/ IgnoreMessageDuringClosingH(ChannelID, UserID, OtherUserID)
    \/ WillPunishLaterH(ChannelID, UserID, OtherUserID)
    \/ InitiateShutdownH(ChannelID, UserID, OtherUserID)
    \/ ReceiveInitiateShutdownH(ChannelID, UserID, OtherUserID)
    
NextHFair(ChannelID, UserID, OtherUserID) ==
    \/ SendOpenChannelH(ChannelID, UserID, OtherUserID)
    \/ SendAcceptChannelH(ChannelID, UserID, OtherUserID)
    \/ CreateFundingTransactionH(ChannelID, UserID, OtherUserID)
    \/ SendSignedFirstCommitTransactionH(ChannelID, UserID, OtherUserID)
    \/ ReplyWithFirstCommitTransactionH(ChannelID, UserID, OtherUserID)
    \/ ReceiveCommitTransactionH(ChannelID, UserID, OtherUserID)
    \/ PublishFundingTransactionH(ChannelID, UserID, OtherUserID)
    \/ NoteThatFundingTransactionPublishedH(ChannelID, UserID, OtherUserID)
    \/ UserHonest[UserID] /\ SendNewRevocationKeyH(ChannelID, UserID, OtherUserID)
    \/ ReceiveNewRevocationKeyH(ChannelID, UserID, OtherUserID)
    \/ UserHonest[UserID] /\ SendSignedCommitmentH(ChannelID, UserID, OtherUserID)
    \/ ReceiveSignedCommitmentH(ChannelID, UserID, OtherUserID)
    \/ UserHonest[UserID] /\ RevokeAndAckH(ChannelID, UserID, OtherUserID)
    \/ ReceiveRevocationKeyH(ChannelID, UserID, OtherUserID)
    \/ UserHonest[UserID] /\ CloseChannelH(ChannelID, UserID, OtherUserID)
    \/ ClosingActionsH(ChannelID, UserID, OtherUserID)
    \/ IgnoreMessageDuringClosingH(ChannelID, UserID, OtherUserID)
    \/ WillPunishLaterH(ChannelID, UserID, OtherUserID)
    \/ InitiateShutdownH(ChannelID, UserID, OtherUserID)
    \/ ReceiveInitiateShutdownH(ChannelID, UserID, OtherUserID)
    
=============================================================================
\* Modification History
\* Last modified Mon Mar 31 21:17:15 CEST 2025 by matthias
\* Created Fri Dec 02 13:37:10 CET 2022 by matthias
