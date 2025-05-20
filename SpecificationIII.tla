-------------------------- MODULE SpecificationIII --------------------------

EXTENDS BaseSpec

VARIABLES
    ChannelUserState,
    ChannelUserBalance,
    ChannelUserVars,
    
    UserPreimageInventory,
    UserLatePreimages,
    UserPaymentSecretForPreimage,
    UserNewPayments,
    
    ChannelPendingBalance,
    ChannelMessages,
    
    Messages

CONSTANTS
    SingleSigHashLock,
    AllSigHashLock
    
vars ==                  <<ChannelUserState, ChannelUserBalance, ChannelUserVars, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, UserHonest, UserExtBalance, UserNewPayments, ChannelPendingBalance, ChannelMessages, Messages, LedgerTime, UserPayments, UserChannelBalance>>
varsWithoutLedgerTime == <<ChannelUserState, ChannelUserBalance, ChannelUserVars, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage,             UserExtBalance, UserNewPayments, ChannelPendingBalance, ChannelMessages, Messages,             UserPayments, UserChannelBalance>>
varsWithoutBalances ==   <<ChannelUserState,                     ChannelUserVars, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage,                             UserNewPayments, ChannelPendingBalance, ChannelMessages, Messages,             UserPayments>>

InitialPayments ==
    UNION {UserInitialPayments[u] : u \in UserIDs}

Ledger == INSTANCE SumAmounts
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

AbstractChannel == INSTANCE PCAbstract WITH
    UnchangedVars <- <<ChannelMessages, LedgerTime, Messages, UserNewPayments, UserPaymentSecretForPreimage>>
    
HU == INSTANCE HTLCUser WITH
    UnchangedVars <- <<ChannelUserState, LedgerTime, UserExtBalance, UserHonest>>
    
AllVarsSet ==
    UNION {{ChannelUserVars[c][u] : u \in UsersOfChannelSet(c)} : c \in ChannelIDs}

TimeBounds ==
    {AbstractChannel!TimeBound(c, UsersOfChannel[c][1], UsersOfChannel[c][2],
                            UserHonest[UsersOfChannel[c][1]], UserHonest[UsersOfChannel[c][2]]) : c \in ActiveChannels}
                            
LedgerTimeInstanceIII == INSTANCE LedgerTime WITH
    Time <- LedgerTime,
    TimeBounds <- TimeBounds,
    NextChangingTimePoints <- 1..MAX_TIME

AdvanceLedgerTimeIII ==
    /\  \/  /\ LedgerTimeInstanceIII!Next
            /\ UNCHANGED <<UserHonest>>
    /\ UNCHANGED varsWithoutLedgerTime
    
MaxOfSet(set) ==
    IF set = {}
    THEN 0
    ELSE CHOOSE x \in set : (\A y \in set : y <= x)
    
PendingBalanceRange(maxPendingBalance) ==
    (-maxPendingBalance)..maxPendingBalance
    
Abs(int) == IF int < 0 THEN -int ELSE int
    
WithdrawBalancesAfterChannelClosed ==
    /\ LedgerTime < 100
    /\ LedgerTime' = 100
    /\ \A c \in ActiveChannels :
        \/ \A u \in UsersOfChannelSet(c) : ChannelUserState[c][u] \in {"closed", "init"} \/ ~UserHonest[u]
    /\ \A c \in ActiveChannels : \A msg \in SeqToSet(ChannelMessages[c]) : msg.type # "HTLCPreimage"
    /\ LET closedChannels == {c \in ActiveChannels : \E u \in UsersOfChannelSet(c) : ChannelUserState[c][u] \in {"closed", "closing-time-set", "closing"}}
       IN
        /\ \E punishBalances \in [closedChannels -> ({0} \cup UNION UNION {{{ChannelUserBalance[c][u], -ChannelUserBalance[c][u]}  : u \in UsersOfChannelSet(c)} : c \in closedChannels})] :
            /\ \A c \in closedChannels : punishBalances[c] \in
                                        IF  \/ ChannelUserVars[c][UsersOfChannel[c][1]].HaveCheated /\ ~UserHonest[UsersOfChannel[c][2]]
                                            \/ ChannelUserVars[c][UsersOfChannel[c][2]].HaveCheated /\ ~UserHonest[UsersOfChannel[c][1]]
                                        THEN {0, -ChannelUserBalance[c][UsersOfChannel[c][1]], ChannelUserBalance[c][UsersOfChannel[c][1]],
                                                 -ChannelUserBalance[c][UsersOfChannel[c][2]], ChannelUserBalance[c][UsersOfChannel[c][2]]}
                                        ELSE IF ChannelUserVars[c][UsersOfChannel[c][1]].HaveCheated
                                        THEN {0, -ChannelUserBalance[c][UsersOfChannel[c][1]]}
                                        ELSE IF ChannelUserVars[c][UsersOfChannel[c][2]].HaveCheated
                                        THEN {0, ChannelUserBalance[c][UsersOfChannel[c][2]]}
                                        ELSE {0}
            /\ UserExtBalance' = [u \in DOMAIN UserExtBalance |->
                                            IF UserHonest[u]
                                            THEN
                                                UserExtBalance[u] + Ledger!SumAmounts({[c |-> c, amount |-> ChannelUserBalance[c][u]] : c \in {c \in closedChannels : u \in UsersOfChannelSet(c)}})
                                                    + Ledger!SumAmounts({[c |-> c, amount |-> punishBalances[c]] : c \in {c \in closedChannels : u \in DOMAIN ChannelUserVars[c] /\ u = UsersOfChannel[c][1]}}) 
                                                    + Ledger!SumAmounts({[c |-> c, amount |-> -punishBalances[c]] : c \in {c \in closedChannels : u \in DOMAIN ChannelUserVars[c] /\ u = UsersOfChannel[c][2]}})
                                            ELSE UserExtBalance[u]
                                        ]
            /\ \A u \in DOMAIN UserExtBalance : UserExtBalance'[u] >= UserExtBalance[u]
        /\ ChannelUserBalance' = [c \in DOMAIN ChannelUserBalance |->
                                                       IF c \in closedChannels
                                                       THEN [u \in UsersOfChannelSet(c) |-> IF UserHonest[u] THEN 0 ELSE ChannelUserBalance[c][u] ]
                                                       ELSE ChannelUserBalance[c] ]
        /\ UserChannelBalance' = [u \in DOMAIN UserChannelBalance |-> IF UserHonest[u] THEN 0 ELSE UserChannelBalance[u] ]
    /\ LedgerTime' = 100
    /\ UNCHANGED UserHonest
    /\ UNCHANGED varsWithoutBalances
    
NextIII ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIII
    \/ \E c \in ActiveChannels : AbstractChannel!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosed
    
NextIIIFair ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIII
    \/ \E c \in ActiveChannels : (UserHonest[UsersOfChannel[c][1]] \/ UserHonest[UsersOfChannel[c][2]]) /\ AbstractChannel!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) 
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosed
    
Init ==
    /\ AbstractChannel!Init(ChannelIDs, UserIDs, UsersOfChannel)
    /\ HU!Init(ChannelIDs, UserIDs)
    /\ InitBase(UserIDs)
    
    
SpecIII ==
    /\ Init
    /\ [][NextIII]_vars
    /\ WF_vars(NextIIIFair)


=============================================================================
