------------------------ MODULE SpecificationIItoIIa ------------------------

EXTENDS SpecificationII, MockHelper

VARIABLES
    ChannelMappedLedgerTime,
    ChannelMappedLedgerTimeHistory
    
varsIItoIIa == <<vars, ChannelMappedLedgerTime, ChannelMappedLedgerTimeHistory>>

PredecessorsOfTx(tx) ==
    CHOOSE predecessors \in SUBSET LedgerTx :
        /\ \A pred \in predecessors :
            \A input \in pred.inputs :
                \E prePred \in predecessors :
                    input.parentId = prePred.id
        /\ \A input \in tx.inputs :
            \E pred \in predecessors :
                input.parentId = pred.id

TranslateTimeOfTxs(ChannelID, Txs) ==
    {[tx EXCEPT !.absTimelock = IF @ \in DOMAIN ChannelMappedLedgerTimeHistory[ChannelID] THEN ChannelMappedLedgerTimeHistory[ChannelID][@] ELSE @ ] : tx \in Txs}
ChannelLedgerTx(ChannelID) ==
    {tx \in LedgerTx : tx.id = ChannelID \/ ChannelID \in {pred.id : pred \in PredecessorsOfTx(tx)}}

SpecificationIIa(CID) == INSTANCE SpecificationIIa WITH
        ActiveChannels <- {CID},
        Messages <- {msg \in Messages : msg.sender \in {NameForUserID[uid] : uid \in UsersOfChannelSet(CID)} \/ msg.recipient \in {NameForUserID[uid] : uid \in UsersOfChannelSet(CID)}},
        LedgerTx <- TranslateTimeOfTxs(CID, ChannelLedgerTx(CID)),
        LedgerTime <- ChannelMappedLedgerTime[CID],
        TxAge <- [id \in {tx.id : tx \in ChannelLedgerTx(CID)} |-> TxAge[id]],
        UserPreimageInventory <- [u \in UsersOfChannelSet(CID) |-> UserPreimageInventory[u] \cap RelevantPreimages(ChannelUserVars[CID][u], UserPaymentSecretForPreimage[u])],
        UserLatePreimages <- [u \in UsersOfChannelSet(CID) |-> UserLatePreimages[u] \cap RelevantPreimages(ChannelUserVars[CID][u], UserPaymentSecretForPreimage[u])],
        UserPaymentSecretForPreimage <- [u \in UsersOfChannelSet(CID) |-> UserPaymentSecretForPreimage[u]],
        UserChannelBalance <- [u \in UsersOfChannelSet(CID) |-> UserChannelBalance[u]],
        UserPayments <- [u \in UsersOfChannelSet(CID) |-> UserPayments[u]],
        UserNewPayments <- [u \in UsersOfChannelSet(CID) |-> MockedNewPayments(IF u = UsersOfChannel[CID][1] THEN NameForUserID[UsersOfChannel[CID][2]] ELSE NameForUserID[UsersOfChannel[CID][1]],
                                                                        UserNewPayments[u],
                                                                        ChannelUserVars[CID][u].IncomingHTLCs,
                                                                        NameForUserID[u])],
        UserHonest <- [u \in UsersOfChannelSet(CID) |-> UserHonest[u]],
        UserExtBalance <- [u \in UsersOfChannelSet(CID) |-> UserExtBalance[u]],
        UserRequestedInvoices <- [u \in UsersOfChannelSet(CID) |-> MockedRequestedInvoices(UserInitialBalance[u],
                                            {IF UserIsFunderOfChannel(c, u) THEN ChannelUserState[c][u] ELSE "" : c \in ChannelIDs \ {CID}} \ {""},
                                            UNION {UserInitialPayments[o] : o \in {o \in UserIDs : o # u}},
                                            UNION {UserNewPayments[o] : o \in {o \in UserIDs : o \notin UsersOfChannelSet(CID)}},
                                            NameForUserID[u],
                                            NameForUserID[CHOOSE o \in UsersOfChannelSet(CID) : o # u],
                                            AllInitialPayments, UserNewPayments, NameForUserID)],
        ChannelMessages <- [ c\in {CID} |-> ChannelMessages[c]],
        ChannelUsedTransactionIds <- [c\in {CID} |-> ChannelUsedTransactionIds[c]],
        ChannelPendingBalance <- [c\in {CID} |-> ChannelPendingBalance[c]],
        ChannelUserBalance <- [c\in {CID} |-> ChannelUserBalance[c]],
        ChannelUserState <- [c\in {CID} |-> ChannelUserState[c]],
        ChannelUserVars <- [c\in {CID} |-> ChannelUserVars[c]],
        ChannelUserDetailVars <- [c\in {CID} |-> ChannelUserDetailVars[c]],
        ChannelUserInventory <- [c\in {CID} |-> ChannelUserInventory[c]],
        STRICT_WITHDRAW <- FALSE
        
        
AdvanceLedgerTimeIItoIIa ==
    /\ AdvanceLedgerTimeII
    /\ ChannelMappedLedgerTime' = 
            [c \in ChannelIDs |->
                MaxOfSet({ChannelMappedLedgerTime[c]} \cup {time \in SpecificationIIa(c)!relETPIIa : time <= LedgerTime'})
            ]
    /\ ChannelMappedLedgerTimeHistory' = [c \in ChannelIDs |->
                            [x \in DOMAIN ChannelMappedLedgerTimeHistory[c] \cup {LedgerTime'} |->
                                        IF x \in DOMAIN ChannelMappedLedgerTimeHistory[c]
                                        THEN ChannelMappedLedgerTimeHistory[c][x]
                                        ELSE ChannelMappedLedgerTime[c]'] 
                                            ]

WithdrawBalancesAfterChannelClosedIItoIIa ==
    /\ WithdrawBalancesAfterChannelClosedII(TRUE)
    /\ ChannelMappedLedgerTime' = [c \in ChannelIDs |-> 100]
    /\ ChannelMappedLedgerTimeHistory' = [c \in ChannelIDs |->
                            [x \in DOMAIN ChannelMappedLedgerTimeHistory[c] \cup {LedgerTime'} |->
                                        IF x \in DOMAIN ChannelMappedLedgerTimeHistory[c]
                                        THEN ChannelMappedLedgerTimeHistory[c][x]
                                        ELSE ChannelMappedLedgerTime[c]'] 
                                            ]
    

InitIItoIIa ==
    /\ Init
    /\ ChannelMappedLedgerTime = [c \in ChannelIDs |-> 1]
    /\ ChannelMappedLedgerTimeHistory = [c \in ChannelIDs |-> [x \in -1..1 |-> x]]

NextIItoIIa ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIItoIIa
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED <<ChannelMappedLedgerTime, ChannelMappedLedgerTimeHistory>>
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED <<ChannelMappedLedgerTime, ChannelMappedLedgerTimeHistory>>
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED <<ChannelMappedLedgerTime, ChannelMappedLedgerTimeHistory>>
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED <<ChannelMappedLedgerTime, ChannelMappedLedgerTimeHistory>>
    \/ WithdrawBalancesAfterChannelClosedIItoIIa
    
SpecIItoIIa ==
    /\ InitIItoIIa
    /\ [][NextIItoIIa]_varsIItoIIa
    /\ WF_vars(NextIIFair)

=============================================================================
