------------------------- MODULE PaymentChannelUser -------------------------

EXTENDS Integers, FiniteSets,
            TLC,
            SumAmounts,
            PCUHelper

CONSTANTS
    EmptyMessage,
    SingleSignature,
    AllSignatures,
    SingleSigHashLock,
    AllSigHashLock,
    IDs,
    Users,
    Keys,
    RevocationKeys,
    Hashes,
    AvailableTransactionIds,
    Time,
    Preimages,
    Amounts,
    MAX_TIME,
    NameForUserID,
    RevKeyBaseForChannelAndUserID,
    TO_SELF_DELAY,
    OptimizedTxAge,
    UsersOfChannel,
    UserInitialBalance,
    FORCE_LONG_SIMULATION,
    SIMULATION_MIN_LENGTH

VARIABLES
    LedgerTime,
    LedgerTx,
    
    UserChannelBalance,
    UserPayments,
    UserExtBalance,
    UserHonest,
    UserPreimageInventory,
    UserLatePreimages,
    
    ChannelMessages,
    ChannelUsedTransactionIds,
    ChannelPendingBalance,
    
    ChannelUserBalance,
    ChannelUserState,
    ChannelUserVars,
    ChannelUserDetailVars,
    ChannelUserInventory,
    
    TxAge,
    UnchangedVars
    
TIO == INSTANCE TransactionIdOracle WITH UsedTransactionIds <- ChannelUsedTransactionIds
            
Ledger == INSTANCE Ledger

\* G is "a grace-period G blocks after HTLC timeout before giving up on an unresponsive peer and dropping to chain" (BOLT 02)
G == 3

MyMessages(ChannelID, UserID) ==
    LET allMessages == {ChannelMessages[ChannelID][index] : index \in DOMAIN ChannelMessages[ChannelID]}
        myMessages == {m \in allMessages : m.recipient = NameForUserID[UserID]}
        indexOfMessage[m \in allMessages] == CHOOSE index \in DOMAIN ChannelMessages[ChannelID] : ChannelMessages[ChannelID][index] = m
    IN IF myMessages = {} THEN {} ELSE {CHOOSE m \in myMessages : \A otherM \in myMessages : indexOfMessage[otherM] >= indexOfMessage[m]}
RemoveMyFirstMessage(ChannelID, UserID) ==
    RemoveMyFirstMessageHelper(ChannelMessages[ChannelID], NameForUserID[UserID])

(*
Mapping of HTLC states from https://github.com/ElementsProject/lightning/blob/master/common/htlc_state.h to HTLC states used here:
    /* When we add a new htlc, it goes in this order. */    -> OutgoingHTLCs
    SENT_ADD_HTLC,              -> NEW
    SENT_ADD_COMMIT,            -> SENT-COMMIT
    RCVD_ADD_REVOCATION,        -> PENDING-COMMIT
    RCVD_ADD_ACK_COMMIT,        -> RECV-COMMIT
    SENT_ADD_ACK_REVOCATION,    -> COMMITTED

    /* When they remove an HTLC, it goes from SENT_ADD_ACK_REVOCATION: */    -> OutgoingHTLCs
    (RCVD_REMOVE_HTLC,)         -> FULFILLED / OFF-TIMEDOUT
    RCVD_REMOVE_COMMIT,         -> RECV-REMOVE
    SENT_REMOVE_REVOCATION,     -> PENDING-REMOVE
    SENT_REMOVE_ACK_COMMIT,     -> SENT-REMOVE
    RCVD_REMOVE_ACK_REVOCATION, -> PERSISTED / TIMEDOUT

    /* When they add a new htlc, it goes in this order. */  -> IncomingHTLCs
    RCVD_ADD_HTLC,              -> NEW
    RCVD_ADD_COMMIT,            -> RECV-COMMIT
    SENT_ADD_REVOCATION,        -> PENDING-COMMIT
    SENT_ADD_ACK_COMMIT,        -> SENT-COMMIT
    RCVD_ADD_ACK_REVOCATION,    -> COMMITTED

    /* When we remove an HTLC, it goes from RCVD_ADD_ACK_REVOCATION: */  -> IncomingHTLCs
    SENT_REMOVE_HTLC,           -> FULFILLED / OFF-TIMEDOUT
    SENT_REMOVE_COMMIT,         -> SENT-REMOVE
    RCVD_REMOVE_REVOCATION,     -> PENDING-REMOVE
    RCVD_REMOVE_ACK_COMMIT,     -> RECV-REMOVE
    SENT_REMOVE_ACK_REVOCATION, -> PERSISTED / TIMEDOUT
*)
  
TimeBounds(ChannelID, UserID) ==
    LET timelimits ==
        {
        LET FulfilledIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs :
                                                /\ \/ htlc.state \in {"COMMITTED", "FULFILLED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}
                                                   \/ htlc.state \in {"NEW", "SENT-COMMIT", "RECV-COMMIT", "PENDING-COMMIT"}
                                                /\ htlc.hash \in UserPreimageInventory[UserID]
                                      }
        IN IF UserHonest[UserID] /\ Cardinality(FulfilledIncomingHTLCs) >= 1
           THEN (CHOOSE htlc \in FulfilledIncomingHTLCs : (\A otherHTLC \in FulfilledIncomingHTLCs : otherHTLC.absTimelock >= htlc.absTimelock)).absTimelock - 1
           ELSE MAX_TIME,

        LET PendingCommittedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : 
                                                /\ htlc.state \in {"SENT-COMMIT", "PENDING-COMMIT", "RECV-COMMIT"}
                                                /\ \A tx \in LedgerTx :
                                                        TransactionSpendsFundingOutput(tx, ChannelUserDetailVars[ChannelID][UserID]) => htlc.hash \in Ledger!HashesInCommitTransaction(tx)
                                                /\ ~ChannelUserDetailVars[ChannelID][UserID].WillPunish
                                                }
        IN IF UserHonest[UserID] /\ Cardinality(PendingCommittedOutgoingHTLCs) >= 1
           THEN (CHOOSE htlc \in PendingCommittedOutgoingHTLCs :
                        (\A otherHTLC \in PendingCommittedOutgoingHTLCs :
                            otherHTLC.absTimelock >= htlc.absTimelock)
                 ).absTimelock + G - 1
           ELSE MAX_TIME,
           
        IF /\ UserHonest[UserID]
           /\ ~ChannelUserDetailVars[ChannelID][UserID].WillPunish
           /\ Cardinality(Ledger!LedgerTxIds \cap (ChannelUserDetailVars[ChannelID][UserID].OldOtherCommitTXIds \cup ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds \cup {ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id})) > 0
        THEN
        LET UnfulfilledOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlc.state \in {"PENDING-COMMIT", "COMMITTED"} /\ htlc.hash \notin UserPreimageInventory[UserID] }
        IN IF Cardinality(UnfulfilledOutgoingHTLCs) >= 1
           THEN (CHOOSE htlc \in UnfulfilledOutgoingHTLCs : (\A otherHTLC \in UnfulfilledOutgoingHTLCs : otherHTLC.absTimelock >= htlc.absTimelock)).absTimelock + G - 1
           ELSE MAX_TIME
        ELSE MAX_TIME,
        
        LET UnfulfilledOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs :
                                                                       /\ htlc.hash \notin UserPreimageInventory[UserID]
                                                                       /\ ~htlc.fulfilled
                                                                       /\ htlc.state \in {"COMMITTED", "OFF-TIMEDOUT", "RECV-REMOVE", "PENDING-REMOVE", "SENT-REMOVE"}
                                                                       /\ \A tx \in LedgerTx : TransactionSpendsFundingOutput(tx, ChannelUserDetailVars[ChannelID][UserID]) => htlc.hash \in Ledger!HashesInCommitTransaction(tx)
                                                                       /\ ~ChannelUserDetailVars[ChannelID][UserID].WillPunish
                                         }
        IN IF UserHonest[UserID] /\ Cardinality(UnfulfilledOutgoingHTLCs) >= 1
           THEN (CHOOSE htlc \in UnfulfilledOutgoingHTLCs : (\A otherHTLC \in UnfulfilledOutgoingHTLCs : otherHTLC.absTimelock >= htlc.absTimelock)).absTimelock + G - 1
           ELSE MAX_TIME,
           
        IF ChannelUserState[ChannelID][UserID] # "closed"
        THEN MAX_TIME - TO_SELF_DELAY
        ELSE MAX_TIME
        }
    IN IF ChannelUserState[ChannelID][UserID] # "closed"
        THEN timelimits
        ELSE {MAX_TIME}
        
TxTimeBounds(ChannelID, UserID) ==
    [ id \in {tx.id : tx \in LedgerTx} |->
        IF  /\ ~ChannelUserVars[ChannelID][UserID].HaveCheated
            /\ ChannelUserState[ChannelID][UserID] # "closed"
            /\ id \in ChannelUserDetailVars[ChannelID][UserID].OldOtherCommitTXIds \cup ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds \cup {ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id}
            /\ Cardinality(Ledger!OnChainOutputSpendableByUser({CHOOSE tx \in LedgerTx : tx.id = id}, ChannelUserInventory[ChannelID][UserID], UserPreimageInventory[UserID], MAX_TIME, TO_SELF_DELAY)) > 0
        THEN TO_SELF_DELAY - 1
        ELSE MAX_TIME
    ]
    
TimelockRegions(ChannelID, UserID) ==
    LET timepoints ==
        (LET HTLCs == {htlc \in (ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs) : htlc.state \in {"NEW", "RECV-COMMIT", "PENDING-COMMIT", "SENT-COMMIT", "COMMITTED"} }
        IN { htlc.absTimelock : htlc \in HTLCs})
        \cup
        (LET HTLCs == {htlc \in (ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs) : htlc.state \in {"NEW", "RECV-COMMIT", "PENDING-COMMIT", "SENT-COMMIT", "COMMITTED", "FULFILLED", "OFF-TIMEDOUT", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"} }
        IN { htlc.absTimelock + G + 1: htlc \in HTLCs})
        \cup
        UNION UNION { { { condition.absTimelock : condition \in output.conditions} : output \in tx.outputs} : tx \in LedgerTx}
        \cup
        UNION UNION { { { condition.absTimelock : condition \in output.conditions} : output \in tx.outputs} : tx \in ChannelUserInventory[ChannelID][UserID].transactions}
    IN timepoints

SendMessageM(messages, message, messagesVar, channelID, myName, otherState) ==
    /\ messagesVar' = [messagesVar EXCEPT ![channelID] = Append(messages, [message EXCEPT !.sender = myName])]
    /\ otherState # "closed"

SendOpenChannel(ChannelID, UserID, OtherUserID) ==
    /\ UserID = UsersOfChannel[ChannelID][1]
    /\ ChannelUserState[ChannelID][UserID] = "init"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-sent-open-channel"]
    /\ UserExtBalance[UserID] > 0
    /\ SendMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                       !.type = "OpenChannel",
                                       !.data.key = ChannelUserVars[ChannelID][UserID].MyKey,
                                       !.data.capacity = UserExtBalance[UserID],
                                       !.data.rKey = ChannelUserDetailVars[ChannelID][UserID].MyRKey], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
    /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].Capacity = UserExtBalance[UserID]]
    /\ UNCHANGED <<ChannelUserVars, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars

SendAcceptChannel(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "init"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-sent-accept-channel"]
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "OpenChannel"
        /\ message.data.capacity > 0
        /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].OtherKey = message.data.key,
                                            ![ChannelID][UserID].OtherRKey = message.data.rKey,
                                            ![ChannelID][UserID].Capacity = message.data.capacity]
        /\ SendMessageM(RemoveMyFirstMessage(ChannelID, UserID), [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                           !.type = "AcceptChannel",
                                           !.data.key = ChannelUserVars[ChannelID][UserID].MyKey,
                                           !.data.rKey = ChannelUserDetailVars[ChannelID][UserID].MyRKey], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
    /\ UNCHANGED <<ChannelUserInventory, UserPreimageInventory, UserLatePreimages, ChannelUserVars, ChannelUserBalance, UserExtBalance, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars

CreateFundingTransaction(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "open-sent-open-channel"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-funding-created"]
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "AcceptChannel"
        /\ LET fundingTxId == TIO!GetNewTransactionId(ChannelID)
           IN /\ TIO!MarkAsUsed(fundingTxId, ChannelID)
              /\ LET fundingTransaction == 
                     [id |-> fundingTxId,
                      inputs |-> {[parentId |-> ChannelUserVars[ChannelID][UserID].FundingInputTxId,
                                   outputId |-> 1,
                                   witness |-> [signatures |-> {ChannelUserVars[ChannelID][UserID].MyKey}],
                                   relTimelock |-> 0]},
                      outputs |-> {[parentId |-> fundingTxId,
                                    outputId |-> 1,
                                    amount |-> UserExtBalance[UserID],
                                    conditions |-> {Ledger!AllSignaturesCondition({ChannelUserVars[ChannelID][UserID].MyKey, message.data.key})}
                                  ]},
                      absTimelock |-> 0
                     ]
                 IN /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].transactions = @ \cup {fundingTransaction}]
                    /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].OtherKey = message.data.key,
                                                        ![ChannelID][UserID].OtherRKey = message.data.rKey,
                                                        ![ChannelID][UserID].fundingTxId = fundingTransaction.id]
                    /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstMessage(ChannelID, UserID)]
    /\ UNCHANGED <<ChannelUserVars, UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, LedgerTx, TxAge, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
                 
SendSignedFirstCommitTransaction(ChannelID, UserID, OtherUserID) ==
   /\ ChannelUserState[ChannelID][UserID] = "open-funding-created"
   /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-sent-commit-funder"]
   /\ LET commitTxId == TIO!GetNewTransactionId(ChannelID)
      IN /\ TIO!MarkAsUsed(commitTxId, ChannelID)
         /\ LET firstCommit ==
                         [id |-> commitTxId,
                          inputs |-> {[parentId |-> ChannelUserDetailVars[ChannelID][UserID].fundingTxId,
                                       outputId |-> 1,
                                       witness |-> [signatures |-> {ChannelUserVars[ChannelID][UserID].MyKey}],
                                       relTimelock |-> 0]},
                           outputs |-> {[parentId |-> commitTxId,
                                        outputId |-> 1,
                                        amount |-> UserExtBalance[UserID],
                                        conditions |-> {Ledger!SingleSignatureCondition(ChannelUserVars[ChannelID][UserID].MyKey)} ],
                                       [parentId |-> commitTxId,
                                        outputId |-> 2,
                                        amount |-> ChannelUserDetailVars[ChannelID][UserID].Capacity - UserExtBalance[UserID],
                                        conditions |-> {[Ledger!SingleSignatureCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey) EXCEPT !.relTimelock = TO_SELF_DELAY],
                                                        Ledger!AllSignaturesCondition({ChannelUserVars[ChannelID][UserID].MyKey, ChannelUserDetailVars[ChannelID][UserID].OtherRKey})}
                                      ]},
                           absTimelock |-> 0
                         ]
            IN /\ SendMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                                  !.type = "FundingCreated",
                                                  !.data.transaction = firstCommit,
                                                  !.data.fundingTxId = ChannelUserDetailVars[ChannelID][UserID].fundingTxId], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
               /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].CurrentOtherCommitTX = firstCommit]
    /\ UNCHANGED <<ChannelUserVars, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, LedgerTx, TxAge, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
                                                  
ReplyWithFirstCommitTransaction(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "open-sent-accept-channel"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-sent-commit"]
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "FundingCreated"
        /\  \* validity checks to defend against messages with arbitrary content
            /\ message.data.transaction.inputs = 
                             {[parentId |-> message.data.fundingTxId,
                               outputId |-> 1,
                               witness |-> [signatures |-> {ChannelUserDetailVars[ChannelID][UserID].OtherKey}],
                               relTimelock |-> 0]}
            /\ message.data.transaction.outputs = 
                               {[parentId |-> message.data.transaction.id,
                                outputId |-> 1,
                                amount |-> ChannelUserDetailVars[ChannelID][UserID].Capacity,
                                conditions |-> {Ledger!SingleSignatureCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey)} ],
                               [parentId |-> message.data.transaction.id,
                                outputId |-> 2,
                                amount |-> 0,
                                conditions |-> {[Ledger!SingleSignatureCondition(ChannelUserVars[ChannelID][UserID].MyKey) EXCEPT !.relTimelock = TO_SELF_DELAY],
                                                Ledger!AllSignaturesCondition({ChannelUserDetailVars[ChannelID][UserID].OtherKey, ChannelUserDetailVars[ChannelID][UserID].MyRKey})}
                              ]}
            /\ message.data.transaction.absTimelock = 0
        /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].transactions = @ \cup {message.data.transaction}]
        /\ LET commitTxId == TIO!GetNewTransactionId(ChannelID)
           IN /\ TIO!MarkAsUsed(commitTxId, ChannelID)
              /\ LET firstCommit == [id |-> commitTxId,
                               inputs |-> {[parentId |-> message.data.fundingTxId,
                                            outputId |-> 1,
                                            witness |-> [signatures |-> {ChannelUserVars[ChannelID][UserID].MyKey}],
                                            relTimelock |-> 0]},
                               outputs |-> {[parentId |-> commitTxId,
                                             outputId |-> 1,
                                             amount |-> 0,
                                             conditions |-> {Ledger!SingleSignatureCondition(ChannelUserVars[ChannelID][UserID].MyKey)}
                                            ],
                                            [parentId |-> commitTxId,
                                             outputId |-> 2,
                                             amount |-> ChannelUserDetailVars[ChannelID][UserID].Capacity - 0,
                                             conditions |-> {
                                                [Ledger!SingleSignatureCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey) EXCEPT !.relTimelock = TO_SELF_DELAY],
                                                Ledger!AllSignaturesCondition({ChannelUserVars[ChannelID][UserID].MyKey, ChannelUserDetailVars[ChannelID][UserID].OtherRKey})
                                             }
                                            ]
                                           },
                               absTimelock |-> 0
                              ]
                 IN /\ SendMessageM(RemoveMyFirstMessage(ChannelID, UserID), [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                                       !.type = "FundingSigned",
                                                       !.data.transaction = firstCommit], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
                    /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].CurrentOtherCommitTX = firstCommit,
                                                        ![ChannelID][UserID].fundingTxId = message.data.fundingTxId,
                                                        ![ChannelID][UserID].LatestCommitTransactionId = message.data.transaction.id,
                                                        ![ChannelID][UserID].CommitmentTxIds = @ \cup {message.data.transaction.id}]
    /\ UNCHANGED <<ChannelUserVars, UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars

ReceiveCommitTransaction(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "open-sent-commit-funder"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-recv-commit"]
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "FundingSigned"
        /\  \* validity checks to defend against messages with arbitrary content
            /\ message.data.transaction.inputs = 
                             {[parentId |-> ChannelUserDetailVars[ChannelID][UserID].fundingTxId,
                               outputId |-> 1,
                               witness |-> [signatures |-> {ChannelUserDetailVars[ChannelID][UserID].OtherKey}],
                               relTimelock |-> 0]}
            /\ message.data.transaction.outputs = 
                               {[parentId |-> message.data.transaction.id,
                                outputId |-> 1,
                                amount |-> 0,
                                conditions |-> {Ledger!SingleSignatureCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey)} ],
                               [parentId |-> message.data.transaction.id,
                                outputId |-> 2,
                                amount |-> ChannelUserDetailVars[ChannelID][UserID].Capacity,
                                conditions |-> {[Ledger!SingleSignatureCondition(ChannelUserVars[ChannelID][UserID].MyKey) EXCEPT !.relTimelock = TO_SELF_DELAY],
                                                Ledger!AllSignaturesCondition({ChannelUserDetailVars[ChannelID][UserID].OtherKey, ChannelUserDetailVars[ChannelID][UserID].MyRKey})}
                              ]}
            /\ message.data.transaction.absTimelock = 0
        /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].transactions = @ \cup {message.data.transaction}]
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstMessage(ChannelID, UserID)]
        /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].LatestCommitTransactionId = message.data.transaction.id,
                                            ![ChannelID][UserID].CommitmentTxIds = @ \cup {message.data.transaction.id}]
    /\ UNCHANGED <<ChannelUserVars, UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
PublishFundingTransaction(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "open-recv-commit"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-funding-pub"]
    /\ \E tx \in ChannelUserInventory[ChannelID][UserID].transactions : tx.id = ChannelUserDetailVars[ChannelID][UserID].fundingTxId
    /\ LET fundingTx == Ledger!SignTransaction(CHOOSE tx \in ChannelUserInventory[ChannelID][UserID].transactions : tx.id = ChannelUserDetailVars[ChannelID][UserID].fundingTxId, ChannelUserVars[ChannelID][UserID].MyKey)
       IN /\ Ledger!PublishTx(fundingTx)
          /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].transactions = @ \ {fundingTx}]
    /\ UserExtBalance[UserID] > 0
    /\ UserExtBalance' = [UserExtBalance EXCEPT ![UserID] = 0]
    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = UserExtBalance[UserID]]
    /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + UserExtBalance[UserID]]
    /\ UNCHANGED <<ChannelMessages, ChannelUserVars, ChannelUserDetailVars, UserPreimageInventory, UserLatePreimages, ChannelUsedTransactionIds, ChannelPendingBalance, UserHonest, UserPayments>>
    /\ UNCHANGED UnchangedVars
          
NoteThatFundingTransactionPublished(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "open-sent-commit"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-funding-pub"]
    (***********************************************************************
    This verifies that the funding transaction has been published on the blockchain.
    See CVE-2019-12998 / CVE-2019-12999 / CVE-2019-13000 and
    https://lists.linuxfoundation.org/pipermail/lightning-dev/2019-September/002174.html
     ***********************************************************************)
    /\ \E tx \in LedgerTx :
        /\ tx.id = ChannelUserDetailVars[ChannelID][UserID].fundingTxId
        \* Verify that the funding transaction uses the correct capacity:
        /\ \E output \in tx.outputs :
            /\ \E condition \in output.conditions :
                condition.data.keys = {ChannelUserVars[ChannelID][UserID].MyKey, ChannelUserDetailVars[ChannelID][UserID].OtherKey}
            /\ output.amount = ChannelUserDetailVars[ChannelID][UserID].Capacity
    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = 0]
    /\ UNCHANGED <<UserExtBalance, ChannelMessages, ChannelUserVars, ChannelUserDetailVars, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
SendNewRevocationKey(ChannelID, UserID, OtherUserID) ==
    /\ \/ ChannelUserState[ChannelID][UserID] = "open-funding-pub" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-new-key-sent"]
       \/ ChannelUserState[ChannelID][UserID] = "open-new-key-received" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "rev-keys-exchanged"]
    /\ LET newRevocationKey == [ChannelUserDetailVars[ChannelID][UserID].MyRKey EXCEPT !.Index = @ + 1]
       IN /\ SendMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                             !.type = "ChannelReady",
                                             !.data.rKey = newRevocationKey], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
          /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].MyNewRKey = newRevocationKey
                                              ]
          /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].keys = @ \cup {newRevocationKey}]
    /\ UNCHANGED <<ChannelUserBalance, UserExtBalance, ChannelUserVars, UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
ReceiveNewRevocationKey(ChannelID, UserID, OtherUserID) ==
    /\ \/ ChannelUserState[ChannelID][UserID] = "open-funding-pub" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "open-new-key-received"]
       \/ ChannelUserState[ChannelID][UserID] = "open-new-key-sent" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "rev-keys-exchanged"]
       \/ ChannelUserState[ChannelID][UserID] = "closing" /\ UNCHANGED ChannelUserState
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "ChannelReady"
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstMessage(ChannelID, UserID)]
        /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].OtherNewRKey = message.data.rKey
                                            ]
    /\ UNCHANGED <<ChannelUserVars, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, ChannelUserInventory, LedgerTx, TxAge, ChannelUsedTransactionIds, UserPreimageInventory, UserLatePreimages, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
CreateHTLCTransactions(commitmentTransaction, newHTLCs, oldHTLCs, ChannelID, UserID) ==
    LET HTLCs == (newHTLCs \cup HTLCsByStates({"COMMITTED", "FULFILLED"}, ChannelUserVars[ChannelID][UserID]) \cup OutHTLCsByStates({"PENDING-COMMIT", "RECV-COMMIT", "PENDING-REMOVE", "RECV-REMOVE"}, ChannelUserVars[ChannelID][UserID])) \ oldHTLCs
        NewTransactionIds == TIO!GetNewTransactionIds(Cardinality(HTLCs), {commitmentTransaction.id}, ChannelID)
        IdForHTLC == CHOOSE bijection \in Bijection(HTLCs, NewTransactionIds) :
            (\A h1 \in HTLCs : (\A h2 \in HTLCs : (h1.hash < h2.hash => bijection[h1] < bijection[h2])))
    IN
       { LET htlcTransactionId == IdForHTLC[htlc]
          IN  [id |-> htlcTransactionId,
           inputs |-> {[parentId |-> commitmentTransaction.id,
                        outputId |-> (CHOOSE output \in commitmentTransaction.outputs :
                                            (\E condition \in output.conditions :
                                                    /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                                                    /\ condition.data.hash = htlc.hash )
                                      ).outputId,
                        witness |-> [signatures |-> {ChannelUserVars[ChannelID][UserID].MyKey}],
                        relTimelock |-> 0]},
           outputs |-> {[parentId |-> htlcTransactionId,
                         outputId |-> 1,
                         amount |-> htlc.amount,
                         conditions |-> {
                            [Ledger!SingleSignatureCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey) EXCEPT !.relTimelock = TO_SELF_DELAY], 
                            Ledger!AllSignaturesCondition({ChannelUserVars[ChannelID][UserID].MyKey, ChannelUserDetailVars[ChannelID][UserID].OtherNewRKey})
                         }
                        ]
                       },
          \* the locktime is bound to the HTLC transaction (see https://github.com/lightning/bolts/blob/master/03-transactions.md#htlc-timeout-and-htlc-success-transactions)
           absTimelock |-> IF \E outgoingHtlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlc.hash = outgoingHtlc.hash \* if HTLC is in outgoingHTLCs, then this is the success transaction
                           THEN 0
                           ELSE htlc.absTimelock
          ]
        : htlc \in HTLCs}
    
SendSignedCommitment(ChannelID, UserID, OtherUserID) ==
    /\  \/ ChannelUserState[ChannelID][UserID] = "rev-keys-exchanged" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "update-commitment-signed"]
        \/ ChannelUserState[ChannelID][UserID] = "update-commitment-received" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "update-commitment-signed-received"]
    /\ ChannelUserDetailVars[ChannelID][UserID].ShutdownInitiated = FALSE
    /\ LET addableHTLCs == {htlcData \in OutHTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserID]) : LedgerTime < htlcData.absTimelock} \cup IncHTLCsByStates({"SENT-COMMIT", "PENDING-COMMIT"}, ChannelUserVars[ChannelID][UserID])
           removableHTLCs == (IncHTLCsByStates({"FULFILLED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserID]) \cup OutHTLCsByStates({"PENDING-REMOVE"}, ChannelUserVars[ChannelID][UserID]))
           updatedHTLCs == addableHTLCs \cup removableHTLCs
           Vars == ChannelUserVars[ChannelID][UserID]
           DetailVars == ChannelUserDetailVars[ChannelID][UserID]
       IN
          /\ Cardinality(updatedHTLCs) > 0
          /\ LET HTLCsToAdd == addableHTLCs
                 HTLCsToRemove == removableHTLCs
                 FulfilledHTLCsToRemove == {htlc \in removableHTLCs : htlc.state \in {"PENDING-REMOVE", "FULFILLED"} /\ htlc.fulfilled}
                 TimedoutHTLCsToRemove == {htlc \in removableHTLCs : htlc.state \in {"PENDING-REMOVE", "OFF-TIMEDOUT"} /\ ~htlc.fulfilled}
                 commitTxId == TIO!GetNewTransactionId(ChannelID)
                 htlcAmountForMe == Ledger!SumAmounts(FulfilledHTLCsToRemove \cap Vars.IncomingHTLCs)
                                        - Ledger!SumAmounts(HTLCsToAdd \cap Vars.OutgoingHTLCs)
                                        + Ledger!SumAmounts(TimedoutHTLCsToRemove \cap Vars.OutgoingHTLCs)
                 htlcAmountForOther == Ledger!SumAmounts(FulfilledHTLCsToRemove \cap Vars.OutgoingHTLCs)
                                        - Ledger!SumAmounts(HTLCsToAdd \cap Vars.IncomingHTLCs)
                                        + Ledger!SumAmounts(TimedoutHTLCsToRemove \cap Vars.IncomingHTLCs)
                 outputToMe == CHOOSE output \in DetailVars.CurrentOtherCommitTX.outputs : output.outputId = 1
                 outputToOther == CHOOSE output \in DetailVars.CurrentOtherCommitTX.outputs : output.outputId = 2
                 htlcOutputsToRemove == { output \in DetailVars.CurrentOtherCommitTX.outputs : (\E condition \in output.conditions : condition.type \in {SingleSigHashLock, AllSigHashLock} /\ (\E htlc \in HTLCsToRemove : condition.data.hash = htlc.hash)) } 
             IN 
                /\ outputToMe.amount + htlcAmountForMe >= 0
                /\ outputToOther.amount + htlcAmountForOther >= 0
                /\ LET existingHTLCOutputs == {htlc \in (Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs) : (\E output \in DetailVars.CurrentOtherCommitTX.outputs : (\E condition \in output.conditions : (condition.type \in {SingleSigHashLock, AllSigHashLock} /\ condition.data.hash = htlc.hash)))}
                       allNewHTLCsInOutputs == HTLCsToAdd \cup (existingHTLCOutputs \ HTLCsToRemove)
                       newHTLCOutputIds == CHOOSE set \in SUBSET(IDs \ {1,2}) : Cardinality(set) = Cardinality(allNewHTLCsInOutputs)
                       IdForHTLCOutput == CHOOSE bijection \in Bijection(allNewHTLCsInOutputs, newHTLCOutputIds) : 
                            (\A h1 \in allNewHTLCsInOutputs : (\A h2 \in allNewHTLCsInOutputs : (h1.hash < h2.hash => bijection[h1] < bijection[h2])))
                       newCommit ==
                            [DetailVars.CurrentOtherCommitTX
                             EXCEPT !.id = commitTxId,
                                    !.outputs = {[output EXCEPT !.parentId = commitTxId,
                                                                !.outputId = IdForHTLCOutput[CHOOSE htlc \in allNewHTLCsInOutputs : (\E condition \in output.conditions : (condition.type \in {SingleSigHashLock, AllSigHashLock} /\ condition.data.hash = htlc.hash))],
                                                                !.conditions = UpdateRKeyInConditions(@, DetailVars.OtherRKey, DetailVars.OtherNewRKey)] : output \in (@ \ (htlcOutputsToRemove \cup {outputToMe, outputToOther}))}
                                                \cup {[outputToMe EXCEPT !.parentId = commitTxId,
                                                                         !.amount = @ + htlcAmountForMe,
                                                                         !.conditions = UpdateRKeyInConditions(@, DetailVars.OtherRKey, DetailVars.OtherNewRKey) ]}
                                                \cup {[outputToOther EXCEPT !.parentId = commitTxId,
                                                                            !.amount = @ + htlcAmountForOther,
                                                                            !.conditions = UpdateRKeyInConditions(@, DetailVars.OtherRKey, DetailVars.OtherNewRKey) ]}
                                                \cup {[ parentId |-> commitTxId,
                                                        outputId |-> IdForHTLCOutput[htlcData],
                                                        amount |-> htlcData.amount,
                                                        conditions |-> {
                                                            (IF htlcData \in Vars.OutgoingHTLCs
                                                                THEN Ledger!AllSigHashLockCondition({Vars.MyKey, DetailVars.OtherKey}, htlcData.hash) \* spent by HTLC success transaction
                                                                ELSE Ledger!SingleSigHashLockCondition(Vars.MyKey, htlcData.hash)),
                                                            (IF htlcData \in Vars.OutgoingHTLCs
                                                                THEN [Ledger!SingleSignatureCondition(Vars.MyKey) EXCEPT !.absTimelock = htlcData.absTimelock]
                                                                ELSE [Ledger!AllSignaturesCondition({Vars.MyKey, DetailVars.OtherKey}) EXCEPT !.absTimelock = 0]), \* spent by HTLC timeout transaction
                                                            Ledger!AllSignaturesCondition({Vars.MyKey, DetailVars.OtherNewRKey})
                                                        }
                                                     ] : htlcData \in HTLCsToAdd}
                            ]
                       HTLCTransactions == CreateHTLCTransactions(newCommit, HTLCsToAdd, HTLCsToRemove, ChannelID, UserID)
                   IN 
                      /\ TIO!MarkMultipleAsUsed({commitTxId} \cup {tx.id : tx \in HTLCTransactions}, ChannelID)
                      /\ SendMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                                         !.type = "CommitmentSigned",
                                                         !.data.transaction = newCommit,
                                                         !.data.htlcTransactions = HTLCTransactions], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
                      /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OutgoingHTLCs = (@ \ (HTLCsToAdd \cup HTLCsToRemove))
                                                                    \cup {[htlcData EXCEPT !.state = "SENT-COMMIT"] : htlcData \in (HTLCsToAdd \cap @)}
                                                                    \cup {[htlc EXCEPT !.state = "SENT-REMOVE"] : htlc \in (HTLCsToRemove \cap @)},
                                              ![ChannelID][UserID].IncomingHTLCs = (@ \ (HTLCsToAdd \cup HTLCsToRemove))
                                                                    \cup {[htlcData EXCEPT !.state = "SENT-COMMIT"] : htlcData \in (HTLCsToAdd \cap @)}
                                                                    \cup {[htlc EXCEPT !.state = "SENT-REMOVE"] : htlc \in (HTLCsToRemove \cap @)}
                                              ]
                      /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].CurrentOtherCommitTX = newCommit,
                                                          ![ChannelID][UserID].OtherOldRKey = DetailVars.OtherRKey,
                                                          ![ChannelID][UserID].OtherRKey = DetailVars.OtherNewRKey,
                                                          ![ChannelID][UserID].CurrentOtherHTLCTransactionIds = {tx.id : tx \in HTLCTransactions},
                                                          ![ChannelID][UserID].PendingOldOtherCommitTxIds = @ \cup {DetailVars.CurrentOtherCommitTX.id} \cup DetailVars.CurrentOtherHTLCTransactionIds]
                      /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ + Ledger!SumAmounts(OutHTLCsByStates({"NEW"}, Vars) \cap HTLCsToAdd)]
                      /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ - Ledger!SumAmounts(OutHTLCsByStates({"NEW"}, Vars) \cap HTLCsToAdd)]
    /\ UNCHANGED <<UserExtBalance, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
ExpectedOutputs(id, ChannelID, UserID) ==
    LET    allHTLCsInOutputs == {htlc \in IncHTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserID]) : htlc.absTimelock > LedgerTime}
                                    \cup IncHTLCsByStates({"SENT-COMMIT", "PENDING-COMMIT", "COMMITTED", "OFF-TIMEDOUT", "FULFILLED", "SENT-REMOVE"}, ChannelUserVars[ChannelID][UserID])
                                    \cup OutHTLCsByStates({"PENDING-COMMIT", "RECV-COMMIT", "COMMITTED"}, ChannelUserVars[ChannelID][UserID])
           newHTLCOutputIds == CHOOSE set \in SUBSET(IDs \ {1,2}) : Cardinality(set) = Cardinality(allHTLCsInOutputs)
           IdForHTLCOutput == CHOOSE bijection \in Bijection(allHTLCsInOutputs, newHTLCOutputIds) : 
                (\A h1 \in allHTLCsInOutputs : (\A h2 \in allHTLCsInOutputs : (h1.hash < h2.hash => bijection[h1] < bijection[h2])))
           outputs == {[parentId |-> id,
                        outputId |-> 1,
                        amount |-> ChannelUserDetailVars[ChannelID][UserID].Capacity - ChannelUserBalance[ChannelID][UserID] - Ledger!SumAmounts(allHTLCsInOutputs) - Ledger!SumAmounts({htlc \in OutHTLCsByStates({"SENT-COMMIT", "OFF-TIMEDOUT", "PENDING-REMOVE", "SENT-REMOVE"}, ChannelUserVars[ChannelID][UserID]) : ~htlc.fulfilled}) + Ledger!SumAmounts({htlc \in IncHTLCsByStates({"FULFILLED", "SENT-REMOVE"}, ChannelUserVars[ChannelID][UserID]) : htlc.fulfilled}),
                        conditions |-> {Ledger!SingleSignatureCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey)} ],
                       [parentId |-> id,
                        outputId |-> 2,
                        amount |-> ChannelUserBalance[ChannelID][UserID] + Ledger!SumAmounts({htlc \in OutHTLCsByStates({"SENT-COMMIT", "OFF-TIMEDOUT", "PENDING-REMOVE", "SENT-REMOVE"}, ChannelUserVars[ChannelID][UserID]) : ~htlc.fulfilled}) - Ledger!SumAmounts({htlc \in IncHTLCsByStates({"FULFILLED", "SENT-REMOVE"}, ChannelUserVars[ChannelID][UserID]) : htlc.fulfilled}),
                        conditions |-> {[Ledger!SingleSignatureCondition(ChannelUserVars[ChannelID][UserID].MyKey) EXCEPT !.relTimelock = TO_SELF_DELAY],
                                        Ledger!AllSignaturesCondition({ChannelUserDetailVars[ChannelID][UserID].OtherKey, ChannelUserDetailVars[ChannelID][UserID].MyNewRKey})} ]
                        } \cup
                        {[parentId |-> id,
                        outputId |-> IdForHTLCOutput[htlc],
                        amount |-> htlc.amount,
                        conditions |-> {(IF htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs
                                        THEN Ledger!AllSigHashLockCondition({ChannelUserDetailVars[ChannelID][UserID].OtherKey, ChannelUserVars[ChannelID][UserID].MyKey}, htlc.hash) \* spent by HTLC success transaction
                                        ELSE Ledger!SingleSigHashLockCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey, htlc.hash)),
                                    (IF htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs
                                        THEN [Ledger!SingleSignatureCondition(ChannelUserDetailVars[ChannelID][UserID].OtherKey) EXCEPT !.absTimelock = htlc.absTimelock]
                                        ELSE [Ledger!AllSignaturesCondition({ChannelUserDetailVars[ChannelID][UserID].OtherKey, ChannelUserVars[ChannelID][UserID].MyKey}) EXCEPT !.absTimelock = 0]), \* spent by HTLC timeout transaction
                                    Ledger!AllSignaturesCondition({ChannelUserDetailVars[ChannelID][UserID].OtherKey, ChannelUserDetailVars[ChannelID][UserID].MyNewRKey})
                                    }
                            ] : htlc \in allHTLCsInOutputs}
    IN outputs

IsExpectedHTLCTransaction(htlcTransaction, commitmentTx, Vars, DetailVars) ==
    /\ LET allHTLCsInOutputs == {htlc \in IncHTLCsByStates({"NEW"}, Vars) : htlc.absTimelock > LedgerTime}
                                    \cup IncHTLCsByStates({"SENT-COMMIT", "PENDING-COMMIT", "COMMITTED", "OFF-TIMEDOUT", "FULFILLED", "SENT-REMOVE"}, Vars)
                                    \cup OutHTLCsByStates({"PENDING-COMMIT", "COMMITTED"}, Vars)
       IN \E htlc \in allHTLCsInOutputs :
        /\ htlcTransaction.inputs = {[parentId |-> commitmentTx.id,
                        outputId |-> (CHOOSE output \in commitmentTx.outputs :
                                            (\E condition \in output.conditions :
                                                    /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                                                    /\ condition.data.hash = htlc.hash )
                                      ).outputId,
                        witness |-> [signatures |-> {DetailVars.OtherKey}],
                        relTimelock |-> 0]}
        /\ htlcTransaction.outputs = {[parentId |-> htlcTransaction.id,
                         outputId |-> 1,
                         amount |-> htlc.amount,
                         conditions |-> {
                            [Ledger!SingleSignatureCondition(Vars.MyKey) EXCEPT !.relTimelock = TO_SELF_DELAY], 
                            Ledger!AllSignaturesCondition({DetailVars.OtherKey, DetailVars.MyNewRKey})
                         }
                        ]
                       }
        /\ htlcTransaction.absTimelock = IF \E incomingHtlc \in Vars.IncomingHTLCs : htlc.hash = incomingHtlc.hash \* if HTLC is in incomingHTLCs, then this is the success transaction
                           THEN 0
                           ELSE htlc.absTimelock
    
ReceiveSignedCommitment(ChannelID, UserID) == 
    /\  \/ ChannelUserState[ChannelID][UserID] = "rev-keys-exchanged" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "update-commitment-received"]
        \/ ChannelUserState[ChannelID][UserID] = "update-commitment-signed" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "update-commitment-signed-received"]
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.type = "CommitmentSigned"
        /\ message.recipient = NameForUserID[UserID]
        /\ \* validity check for transactions received
            /\ message.data.transaction.inputs = (CHOOSE tx \in ChannelUserInventory[ChannelID][UserID].transactions : tx.id = ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId).inputs
            /\ message.data.transaction.outputs = ExpectedOutputs(message.data.transaction.id, ChannelID, UserID) \* outputs
            /\ message.data.transaction.absTimelock = 0
            /\ IF \A htlcTx \in message.data.htlcTransactions : IsExpectedHTLCTransaction(htlcTx, message.data.transaction, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID])
               THEN TRUE
               ELSE /\ Print("Received transaction is invalid", FALSE)
        /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].transactions = @ \cup {message.data.transaction} \cup message.data.htlcTransactions]
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstMessage(ChannelID, UserID)]
        /\ LET lastCommitmentTx == CHOOSE tx \in ChannelUserInventory[ChannelID][UserID].transactions : tx.id = ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId
               newlyCommittedHTLCs == {htlc \in IncHTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserID]) \cup OutHTLCsByStates({"PENDING-COMMIT"}, ChannelUserVars[ChannelID][UserID]) :
                                                    /\ htlc.hash \in Ledger!HashesInCommitTransaction(message.data.transaction)
                                                    /\ htlc.hash \notin Ledger!HashesInCommitTransaction(lastCommitmentTx)
                                        }
               newlyRemovedHTLCs == {htlc \in OutHTLCsByStates({"FULFILLED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserID]) \cup IncHTLCsByStates({"PENDING-REMOVE"}, ChannelUserVars[ChannelID][UserID]) :
                                                    /\ htlc.hash \notin Ledger!HashesInCommitTransaction(message.data.transaction)
                                                    /\ htlc.hash \in Ledger!HashesInCommitTransaction(lastCommitmentTx)}
           IN
              /\ \A htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cap newlyCommittedHTLCs : htlc.absTimelock > LedgerTime \* do not accept commitment transactions that we do not want to commit to
              /\ ChannelUserVars' = [ChannelUserVars EXCEPT
                                     ![ChannelID][UserID].OutgoingHTLCs = (@ \ (newlyCommittedHTLCs \cup newlyRemovedHTLCs))
                                                       \cup {[htlc EXCEPT !.state = "RECV-COMMIT"] : htlc \in (newlyCommittedHTLCs \cap @)}
                                                       \cup {[htlc EXCEPT !.state = "RECV-REMOVE"] : htlc \in (newlyRemovedHTLCs \cap @)},
                                     ![ChannelID][UserID].IncomingHTLCs = (@ \ (newlyCommittedHTLCs \cup newlyRemovedHTLCs))
                                                       \cup {[htlc EXCEPT !.state = "RECV-COMMIT"] : htlc \in (newlyCommittedHTLCs \cap @)}
                                                       \cup {[htlc EXCEPT !.state = "RECV-REMOVE"] : htlc \in (newlyRemovedHTLCs \cap @)}
                                     ]
              /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].PendingNewCommitTransactionId = message.data.transaction.id,
                                                  ![ChannelID][UserID].CommitmentTxIds = @ \cup {message.data.transaction.id}]
    /\ UNCHANGED <<LedgerTx, TxAge, ChannelUsedTransactionIds, UserPreimageInventory, UserLatePreimages, UserHonest, UserExtBalance, ChannelPendingBalance, ChannelUserBalance, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
RevokeAndAck(ChannelID, UserID, OtherUserID) ==
    /\ \/ ChannelUserState[ChannelID][UserID] = "update-commitment-received" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "rev-keys-exchanged"]
       \/ ChannelUserState[ChannelID][UserID] = "update-commitment-signed-received" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "update-commitment-signed"]
    /\ LET lastCommitmentTx == CHOOSE tx \in ChannelUserInventory[ChannelID][UserID].transactions : tx.id = ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId
           nowCommittedHTLCs == HTLCsByStates({"RECV-COMMIT"}, ChannelUserVars[ChannelID][UserID])
           nowPersistedHTLCs == HTLCsByStates({"RECV-REMOVE"}, ChannelUserVars[ChannelID][UserID])
           newRevocationKey == [ChannelUserDetailVars[ChannelID][UserID].MyNewRKey EXCEPT !.Index = @ + 1]
       IN /\ SendMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                       !.type = "RevokeAndAck",
                                       !.data.rSecretKey = ChannelUserDetailVars[ChannelID][UserID].MyRKey,
                                       !.data.rKey = newRevocationKey], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
          /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OutgoingHTLCs = (@ \ (nowCommittedHTLCs \cup nowPersistedHTLCs))
                                                    \cup {[htlc EXCEPT !.state = "COMMITTED"] : htlc \in (nowCommittedHTLCs \cap @)}
                                                    \cup {[htlc EXCEPT !.state = "PENDING-REMOVE"] : htlc \in (nowPersistedHTLCs \cap @)},
                                  ![ChannelID][UserID].IncomingHTLCs = (@ \ (nowCommittedHTLCs \cup nowPersistedHTLCs))
                                                   \cup {[htlc EXCEPT !.state = "PENDING-COMMIT"] : htlc \in (nowCommittedHTLCs \cap @)}
                                                   \cup {[htlc EXCEPT !.state = IF htlc.fulfilled THEN "PERSISTED" ELSE "TIMEDOUT"] : htlc \in (nowPersistedHTLCs \cap @)}
                                                        ]
          /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].MyRKey = ChannelUserDetailVars[ChannelID][UserID].MyNewRKey,
                                              ![ChannelID][UserID].MyNewRKey = newRevocationKey,
                                              ![ChannelID][UserID].LatestCommitTransactionId = ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId
                                              ]
          /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].keys = @ \cup {newRevocationKey}]
    /\ UNCHANGED <<UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
ReceiveRevocationKey(ChannelID, UserID, OtherUserID) ==
    /\ \/ ChannelUserState[ChannelID][UserID] = "update-commitment-signed" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "rev-keys-exchanged"]
       \/ ChannelUserState[ChannelID][UserID] = "update-commitment-signed-received" /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "update-commitment-received"]
       \/ ChannelUserState[ChannelID][UserID] = "closing" /\ UNCHANGED ChannelUserState
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "RevokeAndAck"
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstMessage(ChannelID, UserID)]
        /\ message.data.rSecretKey = ChannelUserDetailVars[ChannelID][UserID].OtherOldRKey    \* validity check
        /\ ChannelUserInventory' = [ChannelUserInventory EXCEPT ![ChannelID][UserID].keys = @ \cup {message.data.rSecretKey}]
        /\ LET sentCommitHTLCs == IF ChannelUserDetailVars[ChannelID][UserID].HavePunished \/ ChannelUserVars[ChannelID][UserID].HaveCheated THEN {} ELSE HTLCsByStates({"SENT-COMMIT"}, ChannelUserVars[ChannelID][UserID])
               nowCommittedHTLCs == {htlc \in sentCommitHTLCs : htlc.absTimelock > LedgerTime \/ htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs }
               nowTimedoutHTLCs == sentCommitHTLCs \ nowCommittedHTLCs
               nowPersistedHTLCs == HTLCsByStates({"SENT-REMOVE"}, ChannelUserVars[ChannelID][UserID]) \cup {htlc \in HTLCsByStates({"TIMEDOUT"}, ChannelUserVars[ChannelID][UserID]) : htlc.hash \in ChannelUserDetailVars[ChannelID][UserID].MightBePersistedTimedoutHTLCs}
               nowTimedoutPersistedHTLCs == {htlc \in nowPersistedHTLCs : ~htlc.fulfilled}               
               haveAlreadyPunishedUsingTimeout ==    /\ ~ChannelUserDetailVars[ChannelID][UserID].HavePunished
                                                    /\ ~ChannelUserVars[ChannelID][UserID].HaveCheated
                                                    /\ ChannelUserState[ChannelID][UserID] = "closing"
                                                    /\ \E ctx \in LedgerTx :
                                                        /\ TransactionSpendsFundingOutput(ctx, ChannelUserDetailVars[ChannelID][UserID])
                                                        /\ \E output \in ctx.outputs :
                                                            \E condition \in output.conditions :
                                                                /\ condition.type = AllSignatures
                                                                /\ \E key \in condition.data.keys : key \in RevocationKeys
                                                                /\ \A key \in condition.data.keys : key \in ChannelUserInventory[ChannelID][UserID]'.keys
                                                        /\ \A output \in ctx.outputs :
                                                            \/ \E spendingTx \in LedgerTx :
                                                                /\ \E input \in spendingTx.inputs : input.parentId = ctx.id /\ input.outputId = output.outputId
                                                                \* if the spendingTx is a second-level HTLC transaction then it must be already spent
                                                                /\ (/\ Cardinality(spendingTx.outputs) = 1
                                                                    /\ \E spendingOutput \in spendingTx.outputs :
                                                                        \E condition \in spendingOutput.conditions :
                                                                            /\ condition.type = AllSignatures
                                                                            /\ ChannelUserVars[ChannelID][UserID].MyKey \in condition.data.keys
                                                                            /\ \E key \in condition.data.keys : key \in RevocationKeys)
                                                                            => \E sspendingTx \in LedgerTx :
                                                                                /\ \E input \in sspendingTx.inputs : input.parentId = spendingTx.id
                                                            \/ output.amount = 0
                                                            \/  /\ Cardinality(output.conditions) = 1
                                                                /\ \A condition \in output.conditions : condition.data.keys = {ChannelUserVars[ChannelID][UserID].MyKey}
               punishedHTLCsBeingPersistedLost == Ledger!SumAmounts({htlc \in nowPersistedHTLCs : ~htlc.punished /\ htlc.hash \in ChannelUserDetailVars[ChannelID][UserID].MightBePersistedTimedoutHTLCs})
               timedoutHTLCBalance == Ledger!SumAmounts(ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \cap nowTimedoutPersistedHTLCs)
           IN /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OutgoingHTLCs = (@ \ (nowCommittedHTLCs \cup nowPersistedHTLCs))
                                                             \cup {[htlc EXCEPT !.state = "PENDING-COMMIT"] : htlc \in (nowCommittedHTLCs \cap @)}
                                                             \cup {[htlc EXCEPT !.state = IF htlc.fulfilled THEN "PERSISTED" ELSE "TIMEDOUT"] : htlc \in (nowPersistedHTLCs \cap @)},
                                           ![ChannelID][UserID].IncomingHTLCs = (@ \ (nowCommittedHTLCs \cup nowPersistedHTLCs))
                                                            \cup {[htlc EXCEPT !.state = "COMMITTED"] : htlc \in (nowCommittedHTLCs \cap @)}
                                                            \cup {[htlc EXCEPT !.state = "PENDING-REMOVE"] : htlc \in (nowPersistedHTLCs \cap @)}
                                                            ]
              /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].OldOtherCommitTXIds = @ \cup ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds,
                                                  ![ChannelID][UserID].PendingOldOtherCommitTxIds = {},
                                                  ![ChannelID][UserID].OtherNewRKey = message.data.rKey,
                                                  ![ChannelID][UserID].OtherCommittedButTimedout = @ \cup {htlc.hash : htlc \in nowTimedoutHTLCs \cap ChannelUserVars[ChannelID][UserID].IncomingHTLCs},
                                                  ![ChannelID][UserID].HavePunished = @ \/ haveAlreadyPunishedUsingTimeout
                                    ]
              /\    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ - punishedHTLCsBeingPersistedLost + timedoutHTLCBalance]
                    /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ + punishedHTLCsBeingPersistedLost - timedoutHTLCBalance]
    /\ UNCHANGED <<UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, ChannelUsedTransactionIds, UserHonest, UserExtBalance, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
TransactionWasRevoked(tx, ledger, Vars, DetailVars) ==
    /\ \E output \in tx.outputs :
        /\ \E spendingTx \in ledger :
            \E input \in spendingTx.inputs :
                /\ input.parentId = tx.id
                /\ input.outputId = output.outputId
                /\ \/ \E revKey \in (input.witness.signatures \ {Vars.MyKey, DetailVars.OtherKey}) :
                        revKey.Base \in {DetailVars.MyRKey.Base, DetailVars.OtherRKey.Base}
                   \* or a depending HTLC transaction might have been revoked
                   \/ \E spendingOutput \in spendingTx.outputs :
                        \E spendingHTLCTx \in ledger :
                            \E htlcInput \in spendingHTLCTx.inputs :
                                /\ htlcInput.parentId = spendingTx.id
                                /\ htlcInput.outputId = spendingOutput.outputId
                                /\ \/ \E revKey \in (htlcInput.witness.signatures \ {Vars.MyKey, DetailVars.OtherKey}) :
                                        revKey.Base \in {DetailVars.MyRKey.Base, DetailVars.OtherRKey.Base}

TransactionCanBeRevokedWithExtraKeys(tx, ledger, couldTheoretically, extraKeys, Vars, DetailVars, Inventory) ==
    \E output \in tx.outputs :
        \/  /\  \/ ~ \E spendingTx \in ledger :
                    /\ \E input \in spendingTx.inputs :
                        /\ input.parentId = tx.id
                        /\ input.outputId = output.outputId
            /\ output.amount > 0 \/ couldTheoretically
            /\ \E condition \in output.conditions :
                /\ \E key \in condition.data.keys :
                    /\ ~key \in {Vars.MyKey, DetailVars.OtherKey}
                    /\ key \in RevocationKeys
                    /\ \/ /\ key.Base = DetailVars.MyRKey.Base
                          /\ key.Index < DetailVars.MyRKey.Index
                       \/ /\ key.Base = DetailVars.OtherRKey.Base
                          /\ key \in Inventory.keys \cup extraKeys
                /\ condition.type = AllSignatures /\ Cardinality(condition.data.keys) = 2 =>
                        \/ Vars.MyKey \in condition.data.keys
                        \/ DetailVars.OtherKey \in condition.data.keys
        \/  /\ \E spendingTx \in ledger :
                /\ \E input \in spendingTx.inputs :
                    /\ input.parentId = tx.id
                    /\ input.outputId = output.outputId
                    /\ \E spendingOutput \in spendingTx.outputs :
                        /\ ~ \E spendingHTLCTx \in ledger :
                            \E htlcInput \in spendingHTLCTx.inputs :
                                /\ htlcInput.parentId = spendingTx.id
                                /\ htlcInput.outputId = spendingOutput.outputId
                        /\ spendingOutput.amount > 0 \/ couldTheoretically
                        /\ \E condition \in spendingOutput.conditions :
                            \E key \in condition.data.keys :
                                /\ ~key \in Keys
                                /\ \/ /\ key.Base = DetailVars.MyRKey.Base
                                      /\ key.Index < DetailVars.MyRKey.Index
                                   \/ /\ key.Base = DetailVars.OtherRKey.Base
                                      /\ key \in Inventory.keys \cup extraKeys
TransactionCanBeRevoked(tx, ledger, couldTheoretically, Vars, DetailVars, Inventory) ==
    TransactionCanBeRevokedWithExtraKeys(tx, ledger, couldTheoretically, {}, Vars, DetailVars, Inventory)
                    
PublishingPartyHasSpentTheirOutput(tx) ==
    /\ \E spendingTx \in LedgerTx :
        /\ Cardinality(spendingTx.outputs) = 1
        /\ Cardinality((CHOOSE output \in spendingTx.outputs : TRUE).conditions) = 1
        /\ \E input \in spendingTx.inputs :
            /\ input.parentId = tx.id
            /\ \E output \in tx.outputs :
                /\ input.outputId = output.outputId
                /\ Cardinality(output.conditions) = 2
                /\ \E condition \in output.conditions :
                    /\ condition.type = AllSignatures
                    /\ \E key \in condition.data.keys : \* revocation key was not used by spending input
                        /\ key \in RevocationKeys
                        /\ key \notin input.witness.signatures

OutgoingPersistedHTLCWasSpentUsingTimeoutOrRevocationCondition(commitTx, newTxs, Vars) ==    
    \E htlc \in HTLCsByStates({"PERSISTED"}, Vars) \cap Vars.OutgoingHTLCs :
        /\ htlc.hash \in Ledger!HashesInCommitTransaction(commitTx)
        /\ \E spendingTx \in LedgerTx \cup newTxs :
            \E input \in spendingTx.inputs :
                /\ input.parentId = commitTx.id
                /\ \E output \in commitTx.outputs :
                    /\ input.outputId = output.outputId
                    /\ \E condition \in output.conditions :
                        /\ condition.type = AllSigHashLock
                        /\ htlc.hash = condition.data.hash
                /\ "preimage" \notin DOMAIN input.witness

UnpunishableTxByOtherPartyWasPublished(Balance, Vars, DetailVars, Inventory) ==
    /\ Cardinality(DetailVars.OldOtherCommitTXIds \cap Ledger!LedgerTxIds) > 0
    /\ \E oldCommitmentTx \in LedgerTx :
        /\ oldCommitmentTx.id \in DetailVars.OldOtherCommitTXIds
        /\ \E output \in oldCommitmentTx.outputs :
            /\ output.amount >= Balance
            /\ \A condition \in output.conditions :
                /\ condition.type = SingleSignature
                /\ condition.data.keys = {Vars.MyKey}
    \* assert that there is no revocable commitment tx in ledger
    /\ ~\E oldCommitmentTx \in LedgerTx :
        /\ oldCommitmentTx.id \in DetailVars.OldOtherCommitTXIds
        /\ \E output \in oldCommitmentTx.outputs :
            /\ output.amount > 0
            /\ \E condition \in output.conditions :
                /\ condition.type = AllSignatures
                /\ \E key \in condition.data.keys : key \in RevocationKeys
                /\ condition.data.keys \in SUBSET Inventory.keys
                
AndNoteCommittedAndUncommittedAndPersistedHTLCs(tx, action, ChannelID, UserID) ==
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "closing"]
    /\ TransactionSpendsFundingOutput(tx, ChannelUserDetailVars[ChannelID][UserID])
    /\ LET nowCommittedHTLCs == {htlc \in HTLCsByStates({"SENT-COMMIT", "RECV-COMMIT", "PENDING-COMMIT"}, ChannelUserVars[ChannelID][UserID]) : htlc.hash \in Ledger!HashesInCommitTransaction(tx)}
           abortAndPersistHTLCs ==  \/ PublishingPartyHasSpentTheirOutput(tx)
                                    \/ ~TransactionWasRevoked(tx, LedgerTx, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID]) /\ ~TransactionCanBeRevoked(tx, LedgerTx, TRUE, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID])
           abortedHTLCs == ((IncHTLCsByStates({"NEW", "RECV-COMMIT", "PENDING-COMMIT"}, ChannelUserVars[ChannelID][UserID]) \cup OutHTLCsByStates({"NEW", "SENT-COMMIT", "PENDING-COMMIT"}, ChannelUserVars[ChannelID][UserID])) \ nowCommittedHTLCs)
                                \cup IF abortAndPersistHTLCs
                                     THEN {htlc \in HTLCsByStates({"NEW", "SENT-COMMIT", "RECV-COMMIT", "PENDING-COMMIT"}, ChannelUserVars[ChannelID][UserID]) \ nowCommittedHTLCs : htlc.hash \notin ChannelUserDetailVars[ChannelID][UserID].OtherCommittedButTimedout}
                                     ELSE {}
           persistedHTLCs == IF abortAndPersistHTLCs
                             THEN {htlc \in HTLCsByStates({"FULFILLED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}, ChannelUserVars[ChannelID][UserID]) : htlc.fulfilled = TRUE /\ htlc.hash \notin Ledger!HashesInCommitTransaction(tx)}
                             ELSE {}
           timedoutHTLCs == IF abortAndPersistHTLCs
                             THEN {htlc \in HTLCsByStates({"OFF-TIMEDOUT", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}, ChannelUserVars[ChannelID][UserID]) : htlc.fulfilled = FALSE /\ htlc.hash \notin Ledger!HashesInCommitTransaction(tx)}
                             ELSE {}
           uncommittedOutgoingHTLCs == (abortedHTLCs \cup timedoutHTLCs) \cap ChannelUserVars[ChannelID][UserID].OutgoingHTLCs
           uncommittedOutgoingHTLCAmounts == Ledger!SumAmounts({htlc \in uncommittedOutgoingHTLCs : htlc.state # "NEW"})
       IN   /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ + uncommittedOutgoingHTLCAmounts]
            /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - uncommittedOutgoingHTLCAmounts]
            /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].IncomingHTLCs = (@ \ (nowCommittedHTLCs \cup abortedHTLCs \cup persistedHTLCs \cup timedoutHTLCs))
                                                            \cup {[htlc EXCEPT !.state = "COMMITTED"] : htlc \in nowCommittedHTLCs \cap @}
                                                            \cup {[htlc EXCEPT !.state = "ABORTED"] : htlc \in abortedHTLCs \cap @}
                                                            \cup {[htlc EXCEPT !.state = "PERSISTED"] : htlc \in persistedHTLCs \cap @}
                                                            \cup {[htlc EXCEPT !.state = "TIMEDOUT"] : htlc \in timedoutHTLCs \cap @}
                                                            ,
                                    ![ChannelID][UserID].OutgoingHTLCs = (@ \ (nowCommittedHTLCs \cup abortedHTLCs \cup persistedHTLCs \cup timedoutHTLCs))
                                                            \cup {[htlc EXCEPT !.state = "COMMITTED"] : htlc \in nowCommittedHTLCs \cap @}
                                                            \cup {[htlc EXCEPT !.state = "ABORTED"] : htlc \in abortedHTLCs \cap @}
                                                            \cup {[htlc EXCEPT !.state = "PERSISTED"] : htlc \in persistedHTLCs \cap @}
                                                            \cup {[htlc EXCEPT !.state = "TIMEDOUT"] : htlc \in timedoutHTLCs \cap @}
                        ]
            /\ ChannelUserDetailVars' = IF abortAndPersistHTLCs
                             THEN [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].MightBePunishedCommittedHTLCs = @ \cup {htlc.hash : htlc \in abortedHTLCs \ HTLCsByStates({"NEW"}, ChannelUserVars[ChannelID][UserID])},
                                                     ![ChannelID][UserID].Debug = Append(@, action)
                                    ]
                             ELSE [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].Debug = Append(@, action)]
    
CloseChannel(ChannelID, UserID) ==
    /\ FORCE_LONG_SIMULATION => TLCGet("level") > SIMULATION_MIN_LENGTH
    /\ ChannelUserState[ChannelID][UserID] # "closed" /\ ChannelUserState[ChannelID][UserID] # "closing"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "closing"]
    /\ Cardinality(ChannelUserInventory[ChannelID][UserID].transactions) > 0
    /\ \E tx \in ChannelUserInventory[ChannelID][UserID].transactions :
        /\ tx.id \in {ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId}
                                    \* IncomingHTLCs: do not commit to an incoming HTLC after it has timeouted, better abort the HTLC instead 
        /\ (\E htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserID].IncomingHTLCs : htlc.state = "RECV-COMMIT" /\ LedgerTime >= htlc.absTimelock)
                => tx.id = ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId
        /\ LET signedTx == Ledger!SignTransaction(tx, ChannelUserVars[ChannelID][UserID].MyKey)
           IN Ledger!PublishTx(signedTx)
        /\ AndNoteCommittedAndUncommittedAndPersistedHTLCs(tx, "CloseChannel", ChannelID, UserID)
    /\ UNCHANGED <<ChannelUserInventory, UserExtBalance, ChannelMessages, UserPreimageInventory, UserLatePreimages, ChannelUsedTransactionIds, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars

NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] # "closed" /\ ChannelUserState[ChannelID][UserID] # "closing"
    /\  \/  /\ "id" \in DOMAIN ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX
            /\ ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id \in Ledger!LedgerTxIds
        \/ \E tx \in LedgerTx :
            /\ tx.id \in ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds
            /\ ~\E output \in tx.outputs : \E condition \in output.conditions : \E key \in condition.data.keys :
                /\ key \in RevocationKeys
                /\ key \in ChannelUserInventory[ChannelID][UserID].keys
                
NoteThatOtherPartyClosedHonestly(ChannelID, UserID) ==
    /\ NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "closing"]
    /\ LET closingTx == CHOOSE tx \in LedgerTx : tx.id \in ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds \/ ("id" \in DOMAIN ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX /\ tx.id = ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id)
       IN /\ AndNoteCommittedAndUncommittedAndPersistedHTLCs(closingTx, "NoteThatOtherPartyClosedHonestly", ChannelID, UserID)
    /\ UNCHANGED <<ChannelMessages, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, ChannelUsedTransactionIds, UserHonest, UserExtBalance, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars

MyPossibleTxInputs(parentSet, ChannelID, UserID) ==
    UNION {
        UNION {
            LET parentAge == IF parent.id \in DOMAIN TxAge THEN TxAge[parent.id] ELSE 0
                relTimelocks == {condition.relTimelock : condition \in output.conditions}
                relTimelock1 == MaxOfSet({timelock \in relTimelocks : timelock <= parentAge})
            IN
                [parentId: {parent.id},
                 outputId: {output.outputId},
                 relTimelock: {relTimelock1},
                 witness: IF \E witness \in MyReducedWitnesses(UNION {condition.data.keys : condition \in output.conditions}, ChannelUserInventory[ChannelID][UserID], UserPreimageInventory[UserID]) : Ledger!WitnessMatchesConditions(witness, relTimelock1, output.conditions, LedgerTime)
                          THEN {CHOOSE witness \in MyReducedWitnesses(UNION {condition.data.keys : condition \in output.conditions}, ChannelUserInventory[ChannelID][UserID], UserPreimageInventory[UserID]) : Ledger!WitnessMatchesConditions(witness, relTimelock1, output.conditions, LedgerTime)}
                          ELSE {}
                 ]
            : output \in {output \in parent.outputs : output.amount >= 0 /\ (~\E input \in Ledger!LedgerInputs(LedgerTx) : input.parentId = parent.id /\ input.outputId = output.outputId) } } : parent \in parentSet}
MyPossibleTxOutputs(parentId1, amount1, ChannelID, UserID) == [parentId: {parentId1}, outputId: {1}, amount: {amount1}, conditions: {{[type |-> SingleSignature, data |-> [keys |-> {ChannelUserVars[ChannelID][UserID].MyKey}], absTimelock |-> 0, relTimelock |-> 0]}}]
MyPossibleNewTransactions(txInputs, parentSet, txId, ChannelID, UserID) == 
    IF txInputs = {} 
        THEN {}
        ELSE [id: {txId},
              inputs: {txInputs},
              outputs: Subset1(MyPossibleTxOutputs(txId, Ledger!AmountSpentByInputs(txInputs, LedgerTx), ChannelID, UserID)),
              absTimelock: {MaxOfSet(UNION UNION {{{timelock \in {condition.absTimelock : condition \in output.conditions} : timelock <= LedgerTime} : output \in parent.outputs} : parent \in parentSet})}
              ]
MyPossibleNewTransactionsWithoutOwnParents(parentSet, ChannelID, UserID) ==
    { tx \in MyPossibleNewTransactions(MyPossibleTxInputs(parentSet, ChannelID, UserID), parentSet, TIO!GetNewTransactionId(ChannelID), ChannelID, UserID) :
        LET parents == Ledger!ConfirmedParentTx(tx, LedgerTx)
        IN \E parent \in parents :
             \E output \in parent.outputs :
                 \E condition \in output.conditions :
                    /\ \E input \in tx.inputs : input.outputId = output.outputId /\ input.parentId = parent.id
                    /\  \/ condition.type # SingleSignature
                        \/ condition.data.keys # {ChannelUserVars[ChannelID][UserID].MyKey}
                        \/ condition.absTimelock > 0
                        \/ condition.relTimelock > 0
    }
SetsWithOneHTLCInput(inputs) ==
    {set \in SUBSET(inputs) :
        /\ \A input \in inputs :
            "preimage" \notin DOMAIN input.witness => input \in set
        /\ (\E input \in inputs : "preimage" \in DOMAIN input.witness)
            => (\E input \in set : "preimage" \in DOMAIN input.witness)
    }
MyPossibleNewTransactionsMultiple(txInputs, parentSet, txId, ChannelID, UserID) == 
    IF txInputs = {} 
        THEN {}
        ELSE {[id |-> txId,
              inputs |-> inputs,
              outputs |-> MyPossibleTxOutputs(txId, Ledger!AmountSpentByInputs(inputs, LedgerTx), ChannelID, UserID),
              absTimelock |-> MaxOfSet(UNION UNION {{{timelock \in {condition.absTimelock : condition \in output.conditions} : timelock <= LedgerTime} : output \in parent.outputs} : parent \in parentSet})
              ]: inputs \in SetsWithOneHTLCInput(txInputs)}
MyPossibleNewTransactionsWithoutOwnParentMultiple(parentSet, ChannelID, UserID) ==
    { tx \in MyPossibleNewTransactionsMultiple(MyPossibleTxInputs(parentSet, ChannelID, UserID), parentSet, TIO!GetNewTransactionId(ChannelID), ChannelID, UserID) :
        LET parents == Ledger!ConfirmedParentTx(tx, LedgerTx)
        IN \E parent \in parents :
             \E output \in parent.outputs :
                 \E condition \in output.conditions :
                    /\ \E input \in tx.inputs : input.outputId = output.outputId /\ input.parentId = parent.id
                    /\  \/ condition.type # SingleSignature
                        \/ condition.data.keys # {ChannelUserVars[ChannelID][UserID].MyKey}
                        \/ condition.absTimelock > 0
                        \/ condition.relTimelock > 0
    }


\* Redeem an HTLC in the honest case    
RedeemHTLCAfterClose(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "closing"
    /\ Cardinality(HTLCsByStates({"COMMITTED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE", "FULFILLED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserID])) >= 1
    /\ \E commitmentTx \in LedgerTx :
            \* Fulfill HTLCs in published commitment transaction that we know the preimage for
            \/  /\ commitmentTx.id \in (ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds \cup {ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id} \cup ChannelUserDetailVars[ChannelID][UserID].CommitmentTxIds \cup ChannelUserDetailVars[ChannelID][UserID].CurrentOtherHTLCTransactionIds)
                /\ \E tx \in MyPossibleNewTransactionsWithoutOwnParentMultiple({commitmentTx}, ChannelID, UserID) :
                    /\ TIO!MarkAsUsed(tx.id, ChannelID)
                    /\ Ledger!PublishTx(tx)
                    /\ LET fulfilledHTLCs == {htlc \in (ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs) :
                                                \E output \in commitmentTx.outputs :
                                                    \E input \in tx.inputs :
                                                        /\ input.parentId = commitmentTx.id
                                                        /\ input.outputId = output.outputId
                                                        /\ \E condition \in output.conditions :
                                                            /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                                                            /\ htlc.hash = condition.data.hash
                                                            /\ "preimage" \in DOMAIN input.witness
                                                            /\ condition.data.hash = input.witness.preimage
                                                }
                           timedoutHTLCs == {htlc \in (ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs) :
                                                \E output \in commitmentTx.outputs :
                                                    \E input \in tx.inputs :
                                                        /\ input.parentId = commitmentTx.id
                                                        /\ input.outputId = output.outputId
                                                        /\ \E condition \in output.conditions :
                                                            /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                                                            /\ htlc.hash = condition.data.hash
                                                            /\ ~ "preimage" \in DOMAIN input.witness
                                                }
                       IN 
                          /\ Cardinality(fulfilledHTLCs) > 0 \/ Cardinality(timedoutHTLCs) > 0
                          /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].IncomingHTLCs = (@ \ (fulfilledHTLCs \cup timedoutHTLCs))
                                                                    \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (fulfilledHTLCs \cap @)}
                                                                    \cup {[htlc EXCEPT !.state = IF htlc \in fulfilledHTLCs THEN "PERSISTED" ELSE "TIMEDOUT"] : htlc \in (timedoutHTLCs \cap @)},
                                                  ![ChannelID][UserID].OutgoingHTLCs = (@ \ (fulfilledHTLCs \cup timedoutHTLCs))
                                                                    \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (fulfilledHTLCs \cap @)}
                                                                    \cup {[htlc EXCEPT !.state = IF htlc \in fulfilledHTLCs THEN "PERSISTED" ELSE "TIMEDOUT"] : htlc \in (timedoutHTLCs \cap @)},
                                                  ![ChannelID][UserID].OtherKnownPreimages = @ \cup {htlc.hash : htlc \in fulfilledHTLCs}
                                     ]
                          /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].MightBePersistedTimedoutHTLCs = @ \cup {htlc.hash : htlc \in {htlc \in timedoutHTLCs \cap ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlc.state = "SENT-REMOVE"}},
                                                              ![ChannelID][UserID].OnChainPersistedHTLCs = @ \cup {htlc.hash : htlc \in {htlc \in fulfilledHTLCs : htlc.state \notin {"PERSISTED"}}},
                                                              ![ChannelID][UserID].Debug = Append(@, "RedeemHTLCAfterClose1")]
                          /\ Cardinality(ChannelUserDetailVars'[ChannelID][UserID].OnChainPersistedHTLCs) > 0 =>
                                ~\E htlc \in ChannelUserVars'[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars'[ChannelID][UserID].OutgoingHTLCs :
                                    /\ htlc.state \in {"PENDING-COMMIT"}
                          \* Newly received amount is the sum of amounts of HTLCs that have not yet been fulfilled
                          /\ LET receivedAmount == Ledger!SumAmounts({htlc \in (fulfilledHTLCs \cup timedoutHTLCs): htlc.fulfilled = FALSE }) 
                                                        + Ledger!SumAmounts({htlc \in timedoutHTLCs: htlc.fulfilled = TRUE })
                             IN /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ + receivedAmount]
                                /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - receivedAmount]
                                /\ LET processedPayments == {payment \in UserPayments[UserID] : payment.state = "NEW" /\ \E htlc \in fulfilledHTLCs : htlc.id = payment.id}
                                       receivedPayments == {payment \in processedPayments : payment.receiver = UserID}
                                       sentPayments == {payment \in processedPayments : payment.sender = UserID} 
                                   IN   /\ UserPayments' = [UserPayments EXCEPT ![UserID] = (@ \ processedPayments) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPayments}]
                                        /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + SumAmounts(receivedPayments) - SumAmounts(sentPayments)]
            \* Publish HTLC success or timeout transaction to redeem HTLC in published commitment transaction
            \/  /\ commitmentTx.id \in (ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds \cup {ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id} \cup ChannelUserDetailVars[ChannelID][UserID].CommitmentTxIds \cup ChannelUserDetailVars[ChannelID][UserID].CurrentOtherHTLCTransactionIds)
                /\ UNCHANGED <<ChannelUsedTransactionIds>>
                /\ \E tx \in ChannelUserInventory[ChannelID][UserID].transactions :
                    /\ LET signedTransaction == Ledger!SignTransaction(tx, ChannelUserVars[ChannelID][UserID].MyKey)
                       IN  \E htlc \in HTLCsByStates({"COMMITTED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE", "FULFILLED", "OFF-TIMEDOUT"}, ChannelUserVars[ChannelID][UserID]) :
                              \E output \in commitmentTx.outputs :
                                /\ \E condition \in output.conditions : condition.type \in {SingleSigHashLock, AllSigHashLock} /\ condition.data.hash = htlc.hash
                                /\ \E input \in signedTransaction.inputs :
                                    /\ input.parentId = commitmentTx.id
                                    /\ input.outputId = output.outputId
                                    /\ LET isSuccessTransaction == \E condition \in output.conditions : condition.type = AllSigHashLock
                                           \* validTransaction adds the corresponding preimage to an existing HTLC success transaction 
                                           validTransaction == IF isSuccessTransaction
                                                               THEN [signedTransaction EXCEPT !.inputs = {[inp EXCEPT !.witness = [signatures |-> inp.witness.signatures, preimage |-> htlc.hash]] : inp \in @}]
                                                               ELSE signedTransaction
                                       IN   
                                            /\ Ledger!PublishTx(validTransaction)
                                            /\ isSuccessTransaction => htlc.hash \in UserPreimageInventory[UserID]
                                            /\  
                                                IF ChannelUserVars[ChannelID][UserID].HaveCheated /\ ~isSuccessTransaction /\ htlc.state \in {"FULFILLED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"} /\ htlc.fulfilled
                                                THEN UNCHANGED ChannelUserVars
                                                ELSE ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].IncomingHTLCs = IF htlc \in @ THEN (@ \ {htlc}) \cup {[htlc EXCEPT !.state = IF isSuccessTransaction THEN "PERSISTED" ELSE "TIMEDOUT", !.fulfilled = @ \/ isSuccessTransaction]} ELSE @,
                                                                          ![ChannelID][UserID].OutgoingHTLCs = IF htlc \in @ THEN (@ \ {htlc}) \cup {[htlc EXCEPT !.state = IF isSuccessTransaction THEN "PERSISTED" ELSE "TIMEDOUT", !.fulfilled = @ \/ isSuccessTransaction]} ELSE @, 
                                                                          ![ChannelID][UserID].OtherKnownPreimages = @ \cup IF isSuccessTransaction THEN {htlc.hash} ELSE {}
                                                             ]
                                            /\ IF ChannelUserVars[ChannelID][UserID].HaveCheated /\ ~isSuccessTransaction /\ htlc.state \in {"FULFILLED", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}
                                               THEN ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].Debug = Append(@, "RedeemHTLCAfterClose2")]
                                               ELSE ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].MightBePersistedTimedoutHTLCs = @ \cup IF ~isSuccessTransaction /\ htlc.state = "SENT-REMOVE" /\ htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs THEN {htlc.hash} ELSE {},
                                                                                     ![ChannelID][UserID].OnChainPersistedHTLCs = @ \cup IF isSuccessTransaction /\ htlc.state # "PERSISTED" THEN {htlc.hash} ELSE {},
                                                                                     ![ChannelID][UserID].Debug = Append(@, "RedeemHTLCAfterClose2")]
                                            /\ Cardinality(ChannelUserDetailVars'[ChannelID][UserID].OnChainPersistedHTLCs) > 0 =>
                                                 ~\E pendingHTLC \in ChannelUserVars'[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars'[ChannelID][UserID].OutgoingHTLCs :
                                                    /\ pendingHTLC.state \in {"PENDING-COMMIT"}
                                            \* Change balance only if HTLC has not already been fulfilled or is not new
                                            /\ LET receivedAmount == (IF ((isSuccessTransaction /\ htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs) \/ ~isSuccessTransaction) /\ htlc.fulfilled = FALSE THEN htlc.amount ELSE 0)
                                                                        + (IF ~isSuccessTransaction /\ htlc.fulfilled = TRUE /\ ~ChannelUserVars[ChannelID][UserID].HaveCheated THEN htlc.amount ELSE 0)
                                               IN
                                                    /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ + receivedAmount]
                                                    /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - receivedAmount]
                                                    /\ LET processedPayments == {payment \in UserPayments[UserID] : payment.state = "NEW" /\ isSuccessTransaction /\ htlc.id = payment.id}
                                                           receivedPayments == {payment \in processedPayments : payment.receiver = UserID}
                                                           sentPayments == {payment \in processedPayments : payment.sender = UserID}
                                                       IN   /\ UserPayments' = [UserPayments EXCEPT ![UserID] = (@ \ processedPayments) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPayments}]
                                                            /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + SumAmounts(receivedPayments) - SumAmounts(sentPayments)]
    /\ UNCHANGED <<ChannelUserState, ChannelMessages, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, UserHonest, UserExtBalance>>
    /\ UNCHANGED UnchangedVars
    
Punish(ChannelID, UserID) ==
    /\ Cardinality(LedgerTx) > 2
    /\ Cardinality((ChannelUserDetailVars[ChannelID][UserID].OldOtherCommitTXIds \cup ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds) \cap Ledger!LedgerTxIds) > 0
    /\ LET cheatingTx == {parent \in LedgerTx: parent.id \in (ChannelUserDetailVars[ChannelID][UserID].OldOtherCommitTXIds \cup ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds)}
           possiblePunishmentTransactions == UNION {MyPossibleNewTransactions(MyPossibleTxInputs({cheatingTxs}, ChannelID, UserID), {cheatingTxs}, TIO!GetNewTransactionId(ChannelID), ChannelID, UserID) : cheatingTxs \in cheatingTx}
       IN
        /\ Cardinality(possiblePunishmentTransactions) > 0
        /\ \E tx \in possiblePunishmentTransactions :
            /\ TIO!MarkAsUsed(tx.id, ChannelID)
            /\ Ledger!PublishTx(tx)
            /\ LET spentOutputs == {output \in Ledger!LedgerOutputs(LedgerTx) : \E input \in tx.inputs : output.parentId = input.parentId /\ output.outputId = input.outputId }
               IN 
                /\ \E output \in spentOutputs :
                        \E condition \in output.conditions :
                            condition # [ type |-> SingleSignature,
                                          data |-> [keys |-> {ChannelUserVars[ChannelID][UserID].MyKey}],
                                          absTimelock |-> 0,
                                          relTimelock |-> 0 ]
                /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].HavePunished = \E parentTx \in cheatingTx : \/ TransactionWasRevoked(parentTx, LedgerTx \cup {tx}, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID])
                                                                                                                                           \/ TransactionCanBeRevoked(parentTx, LedgerTx \cup {tx}, TRUE, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID]) /\ ~TransactionCanBeRevoked(parentTx, LedgerTx \cup {tx}, FALSE, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID])
                                                                                                                                           \/ OutgoingPersistedHTLCWasSpentUsingTimeoutOrRevocationCondition(parentTx, {tx}, ChannelUserVars[ChannelID][UserID]),
                                                    ![ChannelID][UserID].Debug = Append(@, "Punish")
                                                    ]
                /\ LET punishedTx == CHOOSE punishedTx \in cheatingTx : \E input \in tx.inputs : input.parentId = punishedTx.id
                   IN ~\E input \in punishedTx.inputs :
                        /\ "preimage" \in DOMAIN input.witness
                        /\ input.witness.preimage \notin UserPreimageInventory[UserID]
    /\ IF ChannelUserState[ChannelID][UserID] = "closed"
       THEN UNCHANGED ChannelUserState
       ELSE ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "closing"]
    /\ UNCHANGED <<ChannelMessages, ChannelUserVars, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
WillPunishLater(ChannelID, UserID) ==
    /\ ~ChannelUserVars[ChannelID][UserID].HaveCheated
    /\ ChannelUserState[ChannelID][UserID] \notin {"closed", "closing"}
    /\ ~ChannelUserDetailVars[ChannelID][UserID].WillPunish
    /\ LET relTimelock == TO_SELF_DELAY
           otherOldTxInLedger == {oldTx \in LedgerTx : oldTx.id \in ChannelUserDetailVars[ChannelID][UserID].OldOtherCommitTXIds /\ Cardinality(Ledger!OnChainOutputSpendableByUser({oldTx}, ChannelUserInventory[ChannelID][UserID], UserPreimageInventory[UserID], MAX_TIME, relTimelock)) > 0}
       IN /\ Cardinality(otherOldTxInLedger) > 0
          /\ ~UnpunishableTxByOtherPartyWasPublished(ChannelUserBalance[ChannelID][UserID], ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID])
          /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].WillPunish = TRUE]
    /\ UNCHANGED <<ChannelUserState, ChannelMessages, ChannelUserVars, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, UserHonest, LedgerTx, TxAge, ChannelUsedTransactionIds, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
NoteThatHTLCTimedOutOnChain(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "closing"
    /\ \E htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs :
        /\ htlc.state \in {"COMMITTED", "PENDING-REMOVE", "SENT-REMOVE", "RECV-REMOVE", "OFF-TIMEDOUT", "FULFILLED"}
        /\ htlc.state = "PERSISTED" => ChannelUserVars[ChannelID][UserID].HaveCheated /\ htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs
        /\ \E output \in Ledger!LedgerOutputs(LedgerTx) :
            /\ \E condition \in output.conditions :
                /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                /\ htlc.hash = condition.data.hash
            /\ \E child \in LedgerTx :
                /\ \E input \in child.inputs :
                    /\ input.parentId = output.parentId
                    /\ input.outputId = output.outputId
                    /\ ~"preimage" \in DOMAIN input.witness
                /\ \A input \in child.inputs :
                    /\ \A key \in input.witness.signatures : key \in {ChannelUserDetailVars[ChannelID][UserID].OtherKey, ChannelUserVars[ChannelID][UserID].MyKey} \* i.e., no revocation key used
            /\ \E tx \in LedgerTx :
                /\ output \in tx.outputs
                /\ TransactionSpendsFundingOutput(tx, ChannelUserDetailVars[ChannelID][UserID])
        /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].IncomingHTLCs = (@ \ {htlc}) \cup IF htlc \in @ THEN {[htlc EXCEPT !.state = "TIMEDOUT"]} ELSE {},
                                ![ChannelID][UserID].OutgoingHTLCs = (@ \ {htlc}) \cup IF htlc \in @ THEN {[htlc EXCEPT !.state = "TIMEDOUT"]} ELSE {}]
        /\ LET  addedBalance == IF htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs THEN htlc.amount ELSE 0
                removedBalance == IF htlc.fulfilled = TRUE /\ htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs THEN htlc.amount ELSE 0
           IN   /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ + addedBalance - removedBalance]
                /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - addedBalance + removedBalance]
        /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].MightBePersistedTimedoutHTLCs = IF (htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs /\ htlc.state = "SENT-REMOVE") THEN @ \cup {htlc.hash} ELSE @,
                                            ![ChannelID][UserID].Debug = Append(@, "NoteThatHTLCTimedOutOnChain")
                            ]
    /\ UNCHANGED <<ChannelUserState, LedgerTx, TxAge, ChannelUsedTransactionIds, UserExtBalance, ChannelMessages, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
NoteAbortedHTLCsEnabled(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "closing"
    /\ ChannelUserVars[ChannelID][UserID].HaveCheated = TRUE
    /\ \E tx \in LedgerTx :
        /\ tx.id \in {invTx.id : invTx \in ChannelUserInventory[ChannelID][UserID].transactions}
    /\ LET abortedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlc.state \in {"NEW"} }
           abortedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs : htlc.state \in {"NEW"} }
       IN 
          /\ Cardinality(abortedOutgoingHTLCs) + Cardinality(abortedIncomingHTLCs) > 0
    
NoteAbortedHTLCs(ChannelID, UserID) ==
    /\ NoteAbortedHTLCsEnabled(ChannelID, UserID)
    /\ LET abortedOutgoingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlc.state \in {"NEW"} }
           abortedIncomingHTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs : htlc.state \in {"NEW"} }
       IN 
          /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OutgoingHTLCs = (@ \ abortedOutgoingHTLCs)
                                                    \cup {[htlc EXCEPT !.state = "ABORTED"] : htlc \in abortedOutgoingHTLCs},
                                  ![ChannelID][UserID].IncomingHTLCs = (@ \ abortedIncomingHTLCs)
                                                    \cup {[htlc EXCEPT !.state = "ABORTED"] : htlc \in abortedIncomingHTLCs}
                                  ]
    /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].Debug = Append(@, "NoteAbortedHTLCs")]
    /\ UNCHANGED <<ChannelUserState, LedgerTx, TxAge, ChannelMessages, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, ChannelUsedTransactionIds, UserHonest, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
ChannelTxIds(ChannelID, UserID) ==
    {invTx.id : invTx \in ChannelUserInventory[ChannelID][UserID].transactions}
        \cup {ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id}
        \cup ChannelUserDetailVars[ChannelID][UserID].CurrentOtherHTLCTransactionIds
        \cup ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds \cup ChannelUserDetailVars[ChannelID][UserID].OldOtherCommitTXIds
        \cup {ChannelUserDetailVars[ChannelID][UserID].fundingTxId}
    
NoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID) ==
    /\ \E htlcSet \in SUBSET(ChannelUserVars[ChannelID][UserID].OutgoingHTLCs \cup ChannelUserVars[ChannelID][UserID].IncomingHTLCs) :
        /\ Cardinality(htlcSet) > 0
        /\ \A htlc \in htlcSet :
            /\ htlc.state \notin {"PERSISTED", "PUNISHED"}
            /\ \E output \in Ledger!LedgerOutputs(LedgerTx) :
                /\ \E condition \in output.conditions :
                    /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                    /\ htlc.hash = condition.data.hash
                /\ output.parentId \in ChannelTxIds(ChannelID, UserID)
                /\ \E child \in LedgerTx :
                    /\ \E input \in child.inputs :
                        /\ input.parentId = output.parentId
                        /\ input.outputId = output.outputId
                        /\ "preimage" \in DOMAIN input.witness
                        /\ input.witness.preimage = htlc.hash
        /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OutgoingHTLCs = (@ \ htlcSet) \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (htlcSet \cap @)},
                                ![ChannelID][UserID].IncomingHTLCs = (@ \ htlcSet) \cup {[htlc EXCEPT !.state = "PERSISTED", !.fulfilled = TRUE] : htlc \in (htlcSet \cap @)},
                                ![ChannelID][UserID].OtherKnownPreimages = @ \cup {htlc.hash : htlc \in htlcSet}]
        /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserID] = @ \cup {htlc.hash : htlc \in htlcSet}]
        /\ UserLatePreimages' = [UserLatePreimages EXCEPT ![UserID] = @ \cup {htlc.hash: htlc \in {htlc \in htlcSet :
                                                                /\ htlc.absTimelock + G < LedgerTime
                                                                /\ htlc.hash \notin UserPreimageInventory[UserID]
                                                            }}]
        /\ LET fulfilledAbortedOutgoingHTLCAmounts == Ledger!SumAmounts({htlc \in (htlcSet \cap ChannelUserVars[ChannelID][UserID].OutgoingHTLCs) : htlc.state = "ABORTED"})
           IN /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ - fulfilledAbortedOutgoingHTLCAmounts]
              /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ + fulfilledAbortedOutgoingHTLCAmounts]
        /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].OnChainPersistedHTLCs = @ \cup {htlc.hash : htlc \in htlcSet},
                                            ![ChannelID][UserID].Debug = Append(@, "NoteThatHTLCFulfilledOnChainByOtherUser")
                            ]
        /\ \A onChainHTLCId \in ChannelUserDetailVars'[ChannelID][UserID].OnChainPersistedHTLCs :
            ~\E htlc \in ChannelUserVars'[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars'[ChannelID][UserID].OutgoingHTLCs :
                /\ htlc.id = onChainHTLCId
                /\ htlc.state \in {"PENDING-COMMIT"}
        /\ LET processedPayments == {payment \in UserPayments[UserID] : payment.state = "NEW" /\ \E htlc \in htlcSet : htlc.id = payment.id}
               receivedPayments == {payment \in processedPayments : payment.receiver = UserID}
               sentPayments == {payment \in processedPayments : payment.sender = UserID}
           IN   /\ UserPayments' = [UserPayments EXCEPT ![UserID] = (@ \ processedPayments) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPayments}]
                /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + SumAmounts(receivedPayments) - SumAmounts(sentPayments)]
    /\ UNCHANGED <<ChannelUserState, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelMessages, ChannelUserInventory, UserHonest, UserExtBalance>>
    /\ UNCHANGED UnchangedVars
    
NoteThatHTLCFulfilledOnChainInOtherChannel(ChannelID, UserID) ==
    /\ \E htlcSet \in SUBSET(ChannelUserVars[ChannelID][UserID].IncomingHTLCs) :
        /\ Cardinality(htlcSet) > 0
        /\ \A htlc \in htlcSet :
            /\ htlc.hash \notin UserPreimageInventory[UserID]
            /\ \E output \in Ledger!LedgerOutputs(LedgerTx) :
                /\ \E condition \in output.conditions :
                    /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                    /\ htlc.hash = condition.data.hash
                \* these are the commitment tx ids of ALL channels that we are in:
                /\ LET myChannels == {c \in DOMAIN ChannelUserDetailVars : UserID \in DOMAIN ChannelUserDetailVars[c]}
                   IN output.parentId \notin UNION { ChannelTxIds(c, UserID) : c \in myChannels}
                /\ \E child \in LedgerTx :
                    /\ \E input \in child.inputs :
                        /\ input.parentId = output.parentId
                        /\ input.outputId = output.outputId
                        /\ "preimage" \in DOMAIN input.witness
                        /\ input.witness.preimage = htlc.hash
        /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserID] = @ \cup {htlc.hash : htlc \in htlcSet}]
        /\ UserLatePreimages' = [UserLatePreimages EXCEPT ![UserID] = @ \cup {htlc.hash: htlc \in {htlc \in htlcSet :
                                                                /\ htlc.absTimelock + G < LedgerTime
                                                                /\ htlc.hash \notin UserPreimageInventory[UserID]
                                                            }}]
    /\ UNCHANGED <<ChannelUserDetailVars, ChannelUserVars, ChannelUserBalance, ChannelPendingBalance, ChannelUserState, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelMessages, ChannelUserInventory, UserHonest, UserExtBalance, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
IgnoreMessageDuringClosing(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "closing"
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.type = "CommitmentSigned"
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstMessage(ChannelID, UserID)]
        /\ ~ ENABLED ReceiveRevocationKey(ChannelID, UserID, OtherUserID)
    /\ UNCHANGED <<ChannelUserState, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelUserVars, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, ChannelUserDetailVars, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
ShouldNoteIncomingUnfulfillableHTLCsAsTimedout(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "closing"
    /\ \E htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs :
        /\ htlc.state \in {"COMMITTED", "OFF-TIMEDOUT", "SENT-REMOVE", "PENDING-REMOVE", "RECV-REMOVE"}
        /\ htlc.hash \notin UserPreimageInventory[UserID]
        /\ LedgerTime > htlc.absTimelock + G 
        /\ \E tx \in LedgerTx :
            /\ TransactionSpendsFundingOutput(tx, ChannelUserDetailVars[ChannelID][UserID])
            /\ \E output \in tx.outputs : \E condition \in output.conditions :
                /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                /\ condition.data.hash = htlc.hash
    
NoteThatChannelClosedAndAllHTLCsRedeemed(ChannelID, UserID) ==
    /\ ChannelUserState[ChannelID][UserID] = "closing"
    /\ ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "closed"]
    /\ Cardinality(MyMessages(ChannelID, UserID)) = 0
    /\ ChannelUserVars[ChannelID][UserID].HaveCheated \/ ChannelUserDetailVars[ChannelID][UserID].HavePunished \/ \A htlcData \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs : htlcData.state \in {"ABORTED", "TIMEDOUT", "PERSISTED"}
    /\ ChannelUserVars[ChannelID][UserID].HaveCheated \/ ChannelUserDetailVars[ChannelID][UserID].HavePunished \/ \A htlcData \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlcData.state \in {"ABORTED", "TIMEDOUT", "PERSISTED"}
    /\ \A tx \in LedgerTx : ~TransactionCanBeRevoked(tx, LedgerTx, FALSE, ChannelUserVars[ChannelID][UserID], ChannelUserDetailVars[ChannelID][UserID], ChannelUserInventory[ChannelID][UserID])
    /\ IF ChannelUserVars[ChannelID][UserID].HaveCheated \/ ChannelUserDetailVars[ChannelID][UserID].HavePunished
       THEN ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].IncomingHTLCs = {[htlc EXCEPT !.state = "PUNISHED"] : htlc \in @},
                               ![ChannelID][UserID].OutgoingHTLCs = {[htlc EXCEPT !.state = "PUNISHED"] : htlc \in @}
                           ]
       ELSE UNCHANGED ChannelUserVars
    /\ IF ChannelUserDetailVars[ChannelID][UserID].HavePunished
       THEN /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = ChannelUserDetailVars[ChannelID][UserID].Capacity]
            /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = 0]
            /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].BalancesBeforeClose = <<ChannelUserBalance[ChannelID][UserID], ChannelPendingBalance[ChannelID]>>] 
       ELSE IF ChannelUserVars[ChannelID][UserID].HaveCheated
       THEN /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = 0]
            /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = 0]
            /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].BalancesBeforeClose = <<ChannelUserBalance[ChannelID][UserID], ChannelPendingBalance[ChannelID]>>] 
       ELSE
        /\ UNCHANGED <<ChannelUserBalance, ChannelPendingBalance>>
        /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].Debug = Append(@, "NoteThatChannelClosedAndAllHTLCsRedeemed")]
    /\ UNCHANGED <<ChannelMessages, LedgerTx, TxAge, ChannelUsedTransactionIds, UserExtBalance, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
Cheat(ChannelID, UserID) ==
    /\ FORCE_LONG_SIMULATION => TLCGet("level") > SIMULATION_MIN_LENGTH
    /\ UserHonest[UserID] = FALSE 
    /\  \/ \E tx \in ChannelUserInventory[ChannelID][UserID].transactions :
            /\ tx.id # ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId \* This case would be closing
            /\ tx.id # ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId
            /\ tx.id # ChannelUserDetailVars[ChannelID][UserID].fundingTxId
            /\ \E input \in tx.inputs : input.parentId = ChannelUserDetailVars[ChannelID][UserID].fundingTxId
            /\ LET signedTx == Ledger!SignTransaction(tx, ChannelUserVars[ChannelID][UserID].MyKey)
               IN Ledger!PublishTx(signedTx)
            /\ ChannelUserState[ChannelID][UserID] # "closed" => ChannelUserState' = [ChannelUserState EXCEPT ![ChannelID][UserID] = "closing"]
            /\ ChannelUserState[ChannelID][UserID] = "closed" => UNCHANGED ChannelUserState
            /\ UNCHANGED <<ChannelUsedTransactionIds>>
        \/ 
           /\ LET myOtherChannels == {c \in DOMAIN ChannelUserState : c # ChannelID /\ UserID \in DOMAIN ChannelUserState[c]}
                  txIdsInMyOtherChannels == UNION { ChannelTxIds(c, UserID) : c \in myOtherChannels } 
                  ledgerTxWithoutTxOfOtherOwnChannels == {ltx \in LedgerTx : ltx.id \notin txIdsInMyOtherChannels}
                  possibleParents == ledgerTxWithoutTxOfOtherOwnChannels
              IN \E tx \in UNION {MyPossibleNewTransactionsWithoutOwnParents({ledgerTx}, ChannelID, UserID) : ledgerTx \in possibleParents} :
                    /\ TIO!MarkAsUsed(tx.id, ChannelID)
                    /\ Ledger!PublishTx(tx)
                    /\ UNCHANGED <<ChannelUserState>>
    /\ IF ChannelUserState[ChannelID][UserID] # "closed"
       THEN LET haveCheated == /\ LedgerTx' # LedgerTx
                               /\ LET tx == CHOOSE tx \in LedgerTx' \ LedgerTx : TRUE
                                      commitmentTxIds == {ChannelUserDetailVars[ChannelID][UserID].LatestCommitTransactionId, ChannelUserDetailVars[ChannelID][UserID].PendingNewCommitTransactionId, ChannelUserDetailVars[ChannelID][UserID].CurrentOtherCommitTX.id} \cup ChannelUserDetailVars[ChannelID][UserID].PendingOldOtherCommitTxIds \cup ChannelUserDetailVars[ChannelID][UserID].OldOtherCommitTXIds \cup {invTx.id : invTx \in ChannelUserInventory[ChannelID][UserID].transactions}
                                  IN 
                                     \A ctx \in LedgerTx :
                                        ctx.id \in commitmentTxIds
                                        => ~  ( /\ \E input \in tx.inputs : input.parentId = ctx.id
                                                /\ \A output \in ctx.outputs :
                                                    \/ (\E input \in tx.inputs : input.parentId = ctx.id /\ input.outputId = output.outputId)
                                                        => \E condition \in output.conditions :
                                                            /\ condition.type = SingleSignature
                                                            /\ condition.data.keys = {ChannelUserVars[ChannelID][UserID].MyKey}
                                                    \/ output.amount = 0
                                            )
            IN  /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].HaveCheated = @ \/ haveCheated]
       ELSE /\ LedgerTx' # LedgerTx
            /\ UNCHANGED <<UserHonest, ChannelUserVars>>
    /\  LET tx == CHOOSE tx \in LedgerTx' \ LedgerTx : TRUE
            revMsg == CHOOSE msg \in SeqToSet(ChannelMessages[ChannelID]) : msg.type = "RevokeAndAck" /\ msg.sender = NameForUserID[UserID]
            revocationPendingForCheatingTx ==
                /\ \E msg \in SeqToSet(ChannelMessages[ChannelID]) : msg.type = "RevokeAndAck" /\ msg.sender = NameForUserID[UserID]
                /\ \E output \in tx.outputs : \E condition \in output.conditions : revMsg.data.rSecretKey \in condition.data.keys
        IN ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].Debug = Append(@, "Cheat"),
                                            ![ChannelID][UserID].CheatTxPendingRevocation =
                                                    IF revocationPendingForCheatingTx
                                                    THEN tx.id :> revMsg.data.rSecretKey
                                                    ELSE <<>>]
    /\ UNCHANGED <<ChannelMessages, UserHonest, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
ClosingActions(ChannelID, UserID, OtherUserID) ==
    IF ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    THEN NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    ELSE IF NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    THEN NoteThatOtherPartyClosedHonestly(ChannelID, UserID)
    ELSE
      \E beActive \in {TRUE, UserHonest[UserID]} :
        IF (beActive \/ ShouldNoteIncomingUnfulfillableHTLCsAsTimedout(ChannelID, OtherUserID)) /\ ENABLED RedeemHTLCAfterClose(ChannelID, UserID)    \* can be taken by dishonest user but must not
        THEN RedeemHTLCAfterClose(ChannelID, UserID)
        ELSE IF NoteAbortedHTLCsEnabled(ChannelID, UserID)
        THEN NoteAbortedHTLCs(ChannelID, UserID)
        ELSE IF beActive /\ ENABLED Punish(ChannelID, UserID)    \* can be taken by dishonest user but must not
        THEN Punish(ChannelID, UserID)
        ELSE IF ENABLED NoteThatHTLCFulfilledOnChainInOtherChannel(ChannelID, UserID)
        THEN NoteThatHTLCFulfilledOnChainInOtherChannel(ChannelID, UserID)
        ELSE IF ENABLED NoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID)
        THEN NoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID)
        ELSE    \/ beActive /\ Cheat(ChannelID, UserID)
                \/ NoteThatChannelClosedAndAllHTLCsRedeemed(ChannelID, UserID)
            
CLOSENoteThatHTLCTimedOutOnChain(ChannelID, UserID) ==
    NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
CLOSENoteThatOtherPartyClosedHonestly(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ NoteThatOtherPartyClosedHonestly(ChannelID, UserID)
CLOSERedeemHTLCAfterClose(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ ~NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ RedeemHTLCAfterClose(ChannelID, UserID)
CLOSENoteAbortedHTLCs(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ ~NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ ~ENABLED RedeemHTLCAfterClose(ChannelID, UserID)
    /\ NoteAbortedHTLCs(ChannelID, UserID)
CLOSEPunish(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ ~NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ ~ENABLED RedeemHTLCAfterClose(ChannelID, UserID)
    /\ ~NoteAbortedHTLCsEnabled(ChannelID, UserID)
    /\ Punish(ChannelID, UserID)
CLOSENoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ ~NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ ~ENABLED RedeemHTLCAfterClose(ChannelID, UserID)
    /\ ~NoteAbortedHTLCsEnabled(ChannelID, UserID)
    /\ ~ENABLED Punish(ChannelID, UserID)
    /\ NoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID)
CLOSENoteThatHTLCFulfilledOnChainInOtherChannel(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ ~NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ ~ENABLED RedeemHTLCAfterClose(ChannelID, UserID)
    /\ ~NoteAbortedHTLCsEnabled(ChannelID, UserID)
    /\ ~ENABLED Punish(ChannelID, UserID)
    /\ NoteThatHTLCFulfilledOnChainInOtherChannel(ChannelID, UserID)
CLOSECheat(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ ~NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ ~ENABLED RedeemHTLCAfterClose(ChannelID, UserID)
    /\ ~NoteAbortedHTLCsEnabled(ChannelID, UserID)
    /\ ~ENABLED Punish(ChannelID, UserID)
    /\ ~ENABLED NoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID)
    /\ Cheat(ChannelID, UserID)
CLOSENoteThatChannelClosedAndAllHTLCsRedeemed(ChannelID, UserID) ==
    /\ ~ENABLED NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    /\ ~NoteThatOtherPartyClosedHonestlyEnabled(ChannelID, UserID)
    /\ ~ENABLED RedeemHTLCAfterClose(ChannelID, UserID)
    /\ ~NoteAbortedHTLCsEnabled(ChannelID, UserID)
    /\ ~ENABLED Punish(ChannelID, UserID)
    /\ ~ENABLED NoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID)
    /\ NoteThatChannelClosedAndAllHTLCsRedeemed(ChannelID, UserID)
            
            
InitiateShutdown(ChannelID, UserID, OtherUserID) ==
    /\ FALSE
    /\ ChannelUserState[ChannelID][UserID] \in {"rev-keys-exchanged"}
    /\ ChannelUserDetailVars[ChannelID][UserID].ShutdownInitiated = FALSE
    /\ SendMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                       !.type = "InitiateShutdown"], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
    /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].ShutdownInitiated = TRUE ]
    /\ UNCHANGED <<ChannelUserState, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelUserVars, ChannelUserBalance, UserExtBalance, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars
    
ReceiveInitiateShutdown(ChannelID, UserID) ==
    /\ FALSE
    /\ \E message \in MyMessages(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "InitiateShutdown"
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstMessage(ChannelID, UserID)]
    /\ ChannelUserDetailVars' = [ChannelUserDetailVars EXCEPT ![ChannelID][UserID].ShutdownInitiated = TRUE ]
    /\ UNCHANGED <<ChannelUserState, ChannelUserInventory, UserPreimageInventory, UserLatePreimages, LedgerTx, TxAge, ChannelUsedTransactionIds, ChannelUserVars, ChannelUserBalance, ChannelPendingBalance, UserHonest, UserChannelBalance, UserPayments>>
    /\ UNCHANGED UnchangedVars

InitialLedgerTx(ChannelID, FundingUserID, InitialBalance) ==
    [id |-> ChannelID,
    inputs |-> {
        [parentId |-> ChannelID,
         outputId |-> 1,
         witness |-> [signatures |-> {NameForUserID[FundingUserID]}],
         relTimelock |-> 0]},
    outputs |-> {
       [parentId |-> ChannelID,
        outputId |-> 1,
        amount |-> InitialBalance,
        conditions |-> {
            [type |-> SingleSignature,
             data |-> [keys |-> {NameForUserID[FundingUserID]}],
             absTimelock |-> 0,
             relTimelock |-> 0]} ]},
    absTimelock |-> 0,
    publishedAt |-> 0]
    
UoCSet(users) == {users[1], users[2]}
Init(ChannelIDs, UserIDs) ==
    /\ LedgerTx = {InitialLedgerTx(c,UsersOfChannel[c][1],UserInitialBalance[UsersOfChannel[c][1]]) : c \in ChannelIDs}
    /\ LedgerTime = 1
    /\ TxAge = [id \in {tx.id : tx \in LedgerTx} |-> TO_SELF_DELAY]
    /\ ChannelUsedTransactionIds = [c \in ChannelIDs |-> {}]
    /\ ChannelUserInventory = [c \in ChannelIDs |-> [u \in UoCSet(UsersOfChannel[c]) |-> [
        keys |-> {NameForUserID[u]},
        transactions |-> {}]]]
    /\ UserPreimageInventory = [u \in UserIDs |-> {}]
    /\ UserLatePreimages = [u \in UserIDs |-> {}]
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
        Cheater |-> "None" ]]]
    /\ ChannelUserDetailVars = [c \in ChannelIDs |-> [u \in UoCSet(UsersOfChannel[c]) |-> [
        MyRKey |-> [Base |-> RevKeyBaseForChannelAndUserID[c][u], Index |-> 1],
        MyNewRKey |-> [Base |-> RevKeyBaseForChannelAndUserID[c][u], Index |-> 1], 
        OtherKey |-> 0,
        Capacity |-> 0,
        OtherRKey |-> [Base |-> 0, Index |-> 0],
        OtherOldRKey |-> [null |-> 0],
        OtherNewRKey |-> [null |-> 0, Index |-> 0],
        fundingTxId |-> 0,
        CurrentOtherCommitTX |-> [null |-> 0, id |-> 0],
        PendingOldOtherCommitTxIds |-> {},
        OldOtherCommitTXIds |-> {},
        LatestCommitTransactionId |-> 0,
        PendingNewCommitTransactionId |-> 0,
        CommitmentTxIds |-> {},
        CurrentOtherHTLCTransactionIds |-> {},
        HavePunished |-> FALSE,
        WillPunish |-> FALSE, 
        MightBePunishedCommittedHTLCs |-> {},
        MightBePersistedPunishedHTLCs |-> {},
        MightBePersistedTimedoutHTLCs |-> {}, 
        AbortedMustBePunishedHTLCs |-> {},
        OnChainPersistedHTLCs |-> {},
        ShutdownInitiated |-> FALSE,
        OtherCommittedButTimedout |-> {},
        BalancesBeforeClose |-> <<>>,
        CheatTxPendingRevocation |-> <<>>,
        Debug |-> <<>>
       ]]]
    /\ ChannelUserState = [c \in ChannelIDs |-> [u \in UoCSet(UsersOfChannel[c]) |-> "init"]]
    /\ ChannelUserBalance = [c \in ChannelIDs |-> [u \in UoCSet(UsersOfChannel[c]) |-> 0]]
    /\ ChannelPendingBalance = [c \in ChannelIDs |-> 0]
    /\ ChannelMessages = [c \in ChannelIDs |-> <<>>]
    /\ UserChannelBalance = [u \in UserIDs |-> 0]

Next(ChannelID, UserID, OtherUserID) ==
    \/ SendOpenChannel(ChannelID, UserID, OtherUserID)
    \/ SendAcceptChannel(ChannelID, UserID, OtherUserID)
    \/ CreateFundingTransaction(ChannelID, UserID)
    \/ SendSignedFirstCommitTransaction(ChannelID, UserID, OtherUserID)
    \/ ReplyWithFirstCommitTransaction(ChannelID, UserID, OtherUserID)
    \/ ReceiveCommitTransaction(ChannelID, UserID)
    \/ PublishFundingTransaction(ChannelID, UserID)
    \/ NoteThatFundingTransactionPublished(ChannelID, UserID, OtherUserID)
    \/ SendNewRevocationKey(ChannelID, UserID, OtherUserID)
    \/ ReceiveNewRevocationKey(ChannelID, UserID, OtherUserID)
    \/ SendSignedCommitment(ChannelID, UserID, OtherUserID)
    \/ ReceiveSignedCommitment(ChannelID, UserID)
    \/ RevokeAndAck(ChannelID, UserID, OtherUserID)
    \/ ReceiveRevocationKey(ChannelID, UserID, OtherUserID)
    \/ CloseChannel(ChannelID, UserID)
    \/ ClosingActions(ChannelID, UserID, OtherUserID)
    \/ WillPunishLater(ChannelID, UserID)
    \/ InitiateShutdown(ChannelID, UserID, OtherUserID)
    \/ ReceiveInitiateShutdown(ChannelID, UserID)
    \/ IgnoreMessageDuringClosing(ChannelID, UserID, OtherUserID)

NextFair(ChannelID, UserID, OtherUserID) ==
    \/ SendOpenChannel(ChannelID, UserID, OtherUserID)
    \/ SendAcceptChannel(ChannelID, UserID, OtherUserID)
    \/ CreateFundingTransaction(ChannelID, UserID)
    \/ SendSignedFirstCommitTransaction(ChannelID, UserID, OtherUserID)
    \/ ReplyWithFirstCommitTransaction(ChannelID, UserID, OtherUserID)
    \/ ReceiveCommitTransaction(ChannelID, UserID)
    \/ PublishFundingTransaction(ChannelID, UserID)
    \/ NoteThatFundingTransactionPublished(ChannelID, UserID, OtherUserID)
    \/ ReceiveNewRevocationKey(ChannelID, UserID, OtherUserID)
    \/ ReceiveSignedCommitment(ChannelID, UserID)
    \/ ReceiveRevocationKey(ChannelID, UserID, OtherUserID)
    \/ NoteThatOtherPartyClosedHonestly(ChannelID, UserID)
    \/ NoteAbortedHTLCs(ChannelID, UserID)
    \/ NoteThatHTLCFulfilledOnChainByOtherUser(ChannelID, UserID)
    \/ NoteThatHTLCFulfilledOnChainInOtherChannel(ChannelID, UserID)
    \/ NoteThatHTLCTimedOutOnChain(ChannelID, UserID)
    \/ InitiateShutdown(ChannelID, UserID, OtherUserID)
    \/ ReceiveInitiateShutdown(ChannelID, UserID)
    \/ IgnoreMessageDuringClosing(ChannelID, UserID, OtherUserID)
    \/ NoteThatChannelClosedAndAllHTLCsRedeemed(ChannelID, UserID)
    \/  /\  \/ UserHonest[UserID]   \* being active after channel opening is required only for honest users
            \/ ChannelUserState[ChannelID][OtherUserID] = "closed" \* or if the other user has already terminated (for cleanup, simplifies abstraction by letting both users end in state 'closed')
        /\  \/ Punish(ChannelID, UserID)
            \/ WillPunishLater(ChannelID, UserID)
            \/ RedeemHTLCAfterClose(ChannelID, UserID)
            \/ CloseChannel(ChannelID, UserID)
            \/ SendSignedCommitment(ChannelID, UserID, OtherUserID)
            \/ RevokeAndAck(ChannelID, UserID, OtherUserID)
            \/ SendNewRevocationKey(ChannelID, UserID, OtherUserID)
            \/ Cheat(ChannelID, UserID)
    \/  /\ ShouldNoteIncomingUnfulfillableHTLCsAsTimedout(ChannelID, OtherUserID)
        /\ RedeemHTLCAfterClose(ChannelID, UserID)
            

=============================================================================
