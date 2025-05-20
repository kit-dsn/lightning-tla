------------------------ MODULE SpecificationIItoIII ------------------------

EXTENDS SpecificationII

VARIABLES
    ChannelPersistedHTLCsBeforeClose,
    ChannelUserHTLCHistory
    
varsIItoIII == <<vars, ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory>>

GetClosingTime(ChannelID, UserID) ==
    IF  /\ ChannelUserDetailVars[ChannelID][UserID].fundingTxId > 0
        /\ \E ctx \in LedgerTx : \E input \in ctx.inputs : input.parentId = ChannelUserDetailVars[ChannelID][UserID].fundingTxId
    THEN (CHOOSE ctx \in LedgerTx : \E input \in ctx.inputs : input.parentId = ChannelUserDetailVars[ChannelID][UserID].fundingTxId).publishedAt
    ELSE -1
    
GetCheater(ChannelID, UserID, OtherUserID) ==
    IF ChannelUserVars[ChannelID][UserID].HaveCheated
    THEN NameForUserID[UserID]
    ELSE IF ChannelUserVars[ChannelID][OtherUserID].HaveCheated
    THEN NameForUserID[OtherUserID]
    ELSE NullUser

AbstractedChannelUserState(ChannelID, UserID, OtherUserID) ==
    IF IsOpeningState(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
    THEN "init"
    ELSE IF \/ IsOpenState(ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID])
            \/ IsUpdatingState(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
            \/ IsPreClosingState(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
    THEN IF GetClosingTime(ChannelID, UserID) > -1
         THEN "closing-time-set"
         ELSE "rev-keys-exchanged"
    ELSE IF IsClosingStateAfterCommit(ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], LedgerTx) \/ IsClosingStateAfterFulfill(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
    THEN "closing"
    ELSE ChannelUserState[ChannelID][UserID]
AbstractedChannelUserVars(ChannelID, UserID, OtherUserID) ==
    IF IsUpdatingState(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID]) \/ IsClosingStateAfterCommit(ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], LedgerTx) \/ IsClosingStateAfterFulfill(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID]) \/ IsPreClosingState(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
    THEN [ChannelUserVars[ChannelID][UserID] EXCEPT !.IncomingHTLCs = RefinementMappingForHTLCs(@, NameForUserID[UserID], NameForUserID[OtherUserID], UserPreimageInventory[UserID], UserPayments[UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], ChannelMessages[ChannelID], LedgerTx, ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID], ChannelUserInventory[ChannelID][OtherUserID], NameForUserID[UserID], NameForUserID[OtherUserID], AllSignatures),
                           !.OutgoingHTLCs = RefinementMappingForHTLCs(@, NameForUserID[UserID], NameForUserID[OtherUserID], UserPreimageInventory[UserID], UserPayments[UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], ChannelMessages[ChannelID], LedgerTx, ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID], ChannelUserInventory[ChannelID][OtherUserID], NameForUserID[UserID], NameForUserID[OtherUserID], AllSignatures),
                           !.OtherKnownPreimages = (@ \ {htlc.hash : htlc \in IncomingHTLCsFulfilledDuringClosing(ChannelUserDetailVars[ChannelID][UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], LedgerTx, UserPayments[UserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID])
                                                                        \cup {htlc \in OutgoingHTLCsFulfilledDuringClosing(ChannelUserDetailVars[ChannelID][UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID]) :
                                                                                        ~\E oHtlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \cup ChannelUserHTLCHistory[ChannelID][UserID].OutgoingHTLCs :
                                                                                            /\ htlc.hash = oHtlc.hash
                                                                                            /\ oHtlc.state \in {"FULFILLED", "RECV-REMOVE", "PENDING-REMOVE", "SENT-REMOVE"}
                                                                                            /\ oHtlc.fulfilled}})
                                                    \cup OffChainThenOnChainFulfilledHTLCs(ChannelUserHTLCHistory[ChannelID][OtherUserID], NameForUserID[UserID], ChannelMessages[ChannelID])
                                                    \cup {htlc.hash : htlc \in OnChainFullfilledHTLCsBeforeCommit(ChannelUserVars[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID]) \cup OnChainFullfilledHTLCsBeforeCommit(ChannelUserVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID])},
                           !.HaveCheated = FALSE,
                           !.OnChainHTLCs = IF GetClosingTime(ChannelID, UserID) < 0
                                            THEN {}
                                            ELSE LET closingTx == CHOOSE ctx \in LedgerTx : \E input \in ctx.inputs : input.parentId = ChannelUserDetailVars[ChannelID][UserID].fundingTxId
                                                 IN Ledger!HashesInCommitTransaction(closingTx),
                           !.Cheater = GetCheater(ChannelID, UserID, OtherUserID),
                           !.Debug = ChannelPersistedHTLCsBeforeClose[ChannelID],
                           !.HTLCsPersistedBeforeClosing = IF GetClosingTime(ChannelID, UserID) < 0
                                                           THEN {}
                                                           ELSE {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][UserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][UserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
                                                                    \cup {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][OtherUserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][OtherUserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
                                                                    \cup ({htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][UserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][UserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}}
                                                                            \cap {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][OtherUserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][OtherUserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}})
                        ] 
    ELSE IF IsReadyState(ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID])
    THEN [ChannelUserVars[ChannelID][UserID] EXCEPT !.IncomingHTLCs = ReadyRefinementMappingForHTLCs(@, ChannelUserVars[ChannelID][OtherUserID]),
                           !.OutgoingHTLCs = ReadyRefinementMappingForHTLCs(@, ChannelUserVars[ChannelID][OtherUserID]),
                           !.OnChainHTLCs = IF GetClosingTime(ChannelID, UserID) < 0
                                            THEN {}
                                            ELSE LET closingTx == CHOOSE ctx \in LedgerTx : \E input \in ctx.inputs : input.parentId = ChannelUserDetailVars[ChannelID][UserID].fundingTxId
                                                 IN Ledger!HashesInCommitTransaction(closingTx),
                           !.Cheater = GetCheater(ChannelID, UserID, OtherUserID),
                           !.Debug = ChannelPersistedHTLCsBeforeClose[ChannelID],
                           !.HTLCsPersistedBeforeClosing = IF GetClosingTime(ChannelID, UserID) < 0
                                                           THEN {}
                                                           ELSE {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][UserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][UserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
                                                                    \cup {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][OtherUserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][OtherUserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
                                                                    \cup ({htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][UserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][UserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}}
                                                                            \cap {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][OtherUserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][OtherUserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}})
         ]
    ELSE [ChannelUserVars[ChannelID][UserID] EXCEPT
                           !.OnChainHTLCs = IF GetClosingTime(ChannelID, UserID) < 0
                                            THEN {}
                                            ELSE LET closingTx == CHOOSE ctx \in LedgerTx : \E input \in ctx.inputs : input.parentId = ChannelUserDetailVars[ChannelID][UserID].fundingTxId
                                                 IN Ledger!HashesInCommitTransaction(closingTx),
                           !.Cheater = GetCheater(ChannelID, UserID, OtherUserID),
                           !.Debug = ChannelPersistedHTLCsBeforeClose[ChannelID],
                           !.HTLCsPersistedBeforeClosing = IF GetClosingTime(ChannelID, UserID) < 0
                                                           THEN {}
                                                           ELSE {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][UserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][UserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
                                                                    \cup {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][OtherUserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][OtherUserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-PERSISTED"} /\ ~htlc.afterClosingTimeSet}}
                                                                    \cup ({htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][UserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][UserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}}
                                                                            \cap {htlc.hash : htlc \in {htlc \in ChannelUserHTLCHistory[ChannelID][OtherUserID].IncomingHTLCs \cup ChannelUserHTLCHistory[ChannelID][OtherUserID].OutgoingHTLCs : htlc.reason \in {"OFF-CHAIN-TIMEDOUT"} /\ ~htlc.afterClosingTimeSet}})
                ]
AbstractedChannelUserBalance(ChannelID, UserID, OtherUserID) ==
    IF  /\ LedgerTime = 100
        /\  \/ ChannelUserState[ChannelID][UserID] \in {"closing", "closed"}
            \/ ChannelUserState[ChannelID][OtherUserID] \in {"closing", "closed"}
        /\ UserHonest[UserID]
    THEN ChannelUserBalance[ChannelID][UserID]
    ELSE
    IF  \/ IsUpdatingState(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
        \/ IsClosingStateAfterCommit(ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], LedgerTx)
        \/ IsClosingStateAfterFulfill(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
        \/ IsPreClosingState(LedgerTx, ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID])
    THEN ChannelUserBalance[ChannelID][UserID]
         + Ledger!SumAmounts({htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs :
                                             /\ htlc.state \notin {"FULFILLED", "TIMEDOUT"}
                                             /\ HTLCWasAddedDuringThisUpdate(htlc, ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], NameForUserID[UserID], NameForUserID[OtherUserID], ChannelMessages[ChannelID], LedgerTx)
                                             /\ ~/\ HTLCAddedAndPersistedDuringThisUpdate(htlc, ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], NameForUserID[UserID], NameForUserID[OtherUserID], ChannelMessages[ChannelID], LedgerTx)
                                                                 })
         + Ledger!SumAmounts({htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : /\ HTLCAddedAndPersistedDuringThisUpdate(htlc, ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], NameForUserID[UserID], NameForUserID[OtherUserID], ChannelMessages[ChannelID], LedgerTx)})
         - Ledger!SumAmounts(IncomingHTLCsFulfilledDuringClosing(ChannelUserDetailVars[ChannelID][UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], LedgerTx, UserPayments[UserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID]))
         - Ledger!SumAmounts(OutgoingHTLCsTimedoutDuringClosing(ChannelUserDetailVars[ChannelID][UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID], ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID], LedgerTx))
         + Ledger!SumAmounts(IncomingHTLCsTimedoutDuringClosing(ChannelUserDetailVars[ChannelID][UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID], ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID]))
         - Ledger!SumAmounts(HTLCsPunishedByMeDuringClosing(UserPreimageInventory[UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][UserID]))
         + Ledger!SumAmounts(HTLCsPunishedByOtherDuringClosing(UserPreimageInventory[UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][UserID]))
         + (IF ChannelUserState[ChannelID][UserID] = "closed" /\ (ChannelUserDetailVars[ChannelID][UserID].HavePunished \/ ChannelUserVars[ChannelID][UserID].HaveCheated) THEN ChannelUserDetailVars[ChannelID][UserID].BalancesBeforeClose[1] - ChannelUserBalance[ChannelID][UserID] ELSE 0)
    ELSE IF IsReadyState(ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID])
    THEN ChannelUserBalance[ChannelID][UserID]
        + Ledger!SumAmounts({htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : \/ htlc.state \in {"SENT-COMMIT", "PENDING-COMMIT"}
                                                                                         \/ htlc.state \in {"RECV-COMMIT", "COMMITTED"} /\ \E oHtlc \in ChannelUserVars[ChannelID][OtherUserID].IncomingHTLCs : htlc.hash = oHtlc.hash /\ oHtlc.state \in {"SENT-COMMIT", "PENDING-COMMIT"}})
    ELSE ChannelUserBalance[ChannelID][UserID]
AbstractedChannelPendingBalance(ChannelID, UserID, OtherUserID) ==
    AbstractedPendingBalanceHelper(ChannelPendingBalance[ChannelID],
                            ChannelUserVars[ChannelID][UserID], ChannelUserVars[ChannelID][OtherUserID],
                            ChannelUserDetailVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][OtherUserID],
                            ChannelUserHTLCHistory[ChannelID][UserID], ChannelUserHTLCHistory[ChannelID][OtherUserID],
                            ChannelUserState[ChannelID][UserID], ChannelUserState[ChannelID][OtherUserID],
                            LedgerTx,
                            UserPayments[UserID], UserPayments[OtherUserID],
                            UserPreimageInventory[UserID], UserPreimageInventory[OtherUserID],
                            NameForUserID[UserID], NameForUserID[OtherUserID],
                            ChannelMessages[ChannelID])
AbstractedChannelMessages(ChannelID) ==
    AbstractedMessagesHelper(ChannelMessages[ChannelID])

SpecificationIII == INSTANCE SpecificationIII WITH
    ChannelMessages <- [c \in ChannelIDs |-> AbstractedChannelMessages(c)],
    ChannelPendingBalance <- [c \in ChannelIDs |-> AbstractedChannelPendingBalance(c, UsersOfChannel[c][1], UsersOfChannel[c][2])],
    ChannelUserState <- [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> AbstractedChannelUserState(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)]],
    ChannelUserBalance <- [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> AbstractedChannelUserBalance(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)]],
    ChannelUserVars <-[c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> AbstractedChannelUserVars(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)]]

-----------------------------------------------------------------------------

PCUwH(CID) == INSTANCE PaymentChannelUserWithHistory WITH
            UnchangedVars <- <<Messages, LedgerTime, UserNewPayments, UserPaymentSecretForPreimage>>,
            AvailableTransactionIds <- [c \in ChannelIDs |-> (100*c+30)..(100*c+69)],
            HTLCHistory <- ChannelUserHTLCHistory,
            IsAfterOnChainCommit <- [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> 
                                        LET o == CHOOSE o \in UsersOfChannelSet(c) : o # u 
                                        IN IsClosingStateAfterCommit(ChannelUserState[c][u], ChannelUserState[c][o], ChannelUserVars[c][u], ChannelUserVars[c][o], ChannelUserDetailVars[c][u], ChannelUserDetailVars[c][o], ChannelUserHTLCHistory[c][u], ChannelUserHTLCHistory[c][o], LedgerTx)
                                    ]],
            IsAfterClosingTimeSet <- [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> GetClosingTime(c, u) > -1]],
            AbstractedCUState <-
                [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> 
                    LET o == CHOOSE o \in UsersOfChannelSet(c) : o # u 
                    IN AbstractedChannelUserState(c, u, o)
                ]],
            AbstractedCUVars <-
                [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> 
                    LET o == CHOOSE o \in UsersOfChannelSet(c) : o # u 
                    IN AbstractedChannelUserVars(c, u, o)
                ]]

-----------------------------------------------------------------------------


InitIItoIII ==
    /\ Init
    /\ ChannelUserHTLCHistory = [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> [
        IncomingHTLCs |-> {},
        OutgoingHTLCs |-> {},
        StateBeforeClosing |-> "",
        OtherWasHonestBeforeCheat |-> FALSE
       ] ]]
    /\ ChannelPersistedHTLCsBeforeClose = [c \in ChannelIDs |-> {}]

NextIItoIII ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeII /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory>>
    \/ \E c \in ActiveChannels : PCUwH(c)!NextH(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : PCUwH(c)!NextH(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory>>
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory>>
    \/ WithdrawBalancesAfterChannelClosedII(TRUE) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory>>
    
SpecIItoIII ==
    /\ InitIItoIII
    /\ [][NextIItoIII]_varsIItoIII
    /\ WF_vars(NextIIFair)


=============================================================================
