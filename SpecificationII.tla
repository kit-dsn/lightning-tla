-------------------------- MODULE SpecificationII --------------------------

EXTENDS SpecificationI

SpecIINCTPs == 
        UNION UNION UNION {{{PCU!TimelockRegions(c, u),
                             HU!TimelockRegions(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)} :
                                        u \in UsersOfChannelSet(c)} : c \in ChannelIDs}
                                        
relETP == SpecIINCTPs \cup {t + 1 : t \in TimeBounds}

LedgerTimeInstanceII == INSTANCE LedgerTime WITH
    Time <- LedgerTime,
    TimeBounds <- TimeBounds,
    NextChangingTimePoints <- relETP
LedgerTimeInstanceNegligentII(ChannelID, UserID) == INSTANCE LedgerTime WITH
    Time <- LedgerTime,
    TimeBounds <- NegligentTimeBounds(ChannelID, UserID),
    NextChangingTimePoints <- relETP

AdvanceLedgerTimeII ==
    /\ FORCE_LONG_SIMULATION => TLCGet("level") > SIMULATION_MIN_LENGTH
    /\ LedgerTime < MAX_TIME
    /\  \/ LedgerTimeInstanceII!AdvanceLedgerTime
        \/ UNCHANGED LedgerTime
    /\  \/  /\  LET unspendableTx == {tx \in LedgerTx : tx.id \in DOMAIN TxAge => TxAge[tx.id] < TO_SELF_DELAY}
                IN \E makeSpendableTx \in SUBSET unspendableTx :
                  /\ makeSpendableTx # {}
                  /\ TxAge' = [id \in {tx.id : tx \in LedgerTx} |->
                                                IF \E tx \in makeSpendableTx : tx.id = id
                                                THEN TO_SELF_DELAY
                                                ELSE TxAge[id]
                           ]
            /\ \A c \in ActiveChannels : \A u \in UsersOfChannelSet(c) : CheckTxTimeBounds(TxAge', PCU!TxTimeBounds(c,u))
            /\ \A c \in ActiveChannels : \A u \in UsersOfChannelSet(c) : CheckCheatingTxPendingRevocation(ChannelUserDetailVars[c][u].CheatTxPendingRevocation, c)
        \/  /\ UNCHANGED TxAge
            /\ LedgerTime' > LedgerTime
    /\ UNCHANGED <<Messages, UserHonest, LedgerTx, UserNewPayments, UserExtBalance, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelMessages, ChannelUsedTransactionIds, ChannelPendingBalance, ChannelUserBalance, ChannelUserState, ChannelUserVars, ChannelUserDetailVars, ChannelUserInventory, UserChannelBalance, UserPayments>>

WithdrawBalancesAfterChannelClosedII(withExternal) ==
    /\ WithdrawBalancesAfterChannelClosed(withExternal)
    /\ TxAge' = [id \in {tx.id : tx \in LedgerTx} |-> TO_SELF_DELAY ]
    /\ UNCHANGED LedgerTx
   
NextII ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeII
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedII(TRUE)
NextIIFair ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeII
    \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedII(TRUE)

SpecII ==
    /\ Init
    /\ [][NextII]_vars
    /\ WF_vars(NextIIFair)

=============================================================================
