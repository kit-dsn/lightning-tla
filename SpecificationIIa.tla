-------------------------- MODULE SpecificationIIa --------------------------

(***************************************************************************)
(* This specification restricts specification II to only a single active   *)
(* channel.  The actions of other channels that can have an effect on the  *)
(* specified channel are mocked by the module MultiHopMock.                *)
(***************************************************************************)

EXTENDS SpecificationII

ASSUME Cardinality(ActiveChannels) = 1
ActiveUsers == UNION {{UsersOfChannel[c][1], UsersOfChannel[c][2]} : c \in ActiveChannels}

VARIABLES
    UserRequestedInvoices
    
CONSTANT
    STRICT_WITHDRAW
    
varsIIa == <<vars, UserRequestedInvoices>>

(***************************************************************************)
(* Mock for the actions of other channels that can have an effect on this  *)
(* channel.                                                                *)
(***************************************************************************)
MHM == INSTANCE MultiHopMock WITH
    UnchangedVars <- <<ChannelMessages, ChannelPendingBalance, ChannelUsedTransactionIds, ChannelUserBalance, ChannelUserDetailVars, ChannelUserInventory, ChannelUserState, LedgerTime, LedgerTx, TxAge>>

(***************************************************************************)
(* Points in time to which time adances.                                   *)
(***************************************************************************)
SpecIIaNCTPs == 
        UNION UNION UNION {{{PCU!TimelockRegions(c, u),
                             HU!TimelockRegions(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u),
                             MHM!TimelockRegions(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)} :
                                        u \in UsersOfChannelSet(c)} : c \in ActiveChannels}

relETPIIa == SpecIIaNCTPs \cup {t + 1 : t \in TimeBounds}

LedgerTimeInstanceIIa == INSTANCE LedgerTime WITH
    Time <- LedgerTime,
    TimeBounds <- TimeBounds,
    NextChangingTimePoints <- relETPIIa
    
AdvanceLedgerTimeIIa ==
    /\ FORCE_LONG_SIMULATION => TLCGet("level") > SIMULATION_MIN_LENGTH
    /\ LedgerTime < MAX_TIME
    /\ LedgerTimeInstanceIIa!AdvanceLedgerTime
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
    /\ UNCHANGED <<UserHonest, Messages, LedgerTx, UserNewPayments, UserExtBalance, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelMessages, ChannelUsedTransactionIds, ChannelPendingBalance, ChannelUserBalance, ChannelUserState, ChannelUserVars, ChannelUserDetailVars, ChannelUserInventory, UserChannelBalance, UserPayments>>

WithdrawBalancesAfterChannelClosedIIa ==
    /\ WithdrawBalancesAfterChannelClosedII(FALSE)
    /\ STRICT_WITHDRAW =>
        UserExtBalance' = [u \in DOMAIN UserExtBalance |-> UserExtBalance[u]
                                                            + IF UserHonest[u]
                                                              THEN UserOnChainBalance(LedgerTx, LedgerTime', LedgerTime' - LedgerTime, u)
                                                                + SumAmounts({i \in UserRequestedInvoices[u] : "type" \in DOMAIN i /\ i.type = "BalanceInOtherChannel"})
                                                              ELSE 0
                            ]
    /\ UserExtBalance' \in [DOMAIN UserExtBalance -> Int]
    /\ \A u \in DOMAIN UserExtBalance :
        UserExtBalance'[u] >= UserExtBalance[u]
                                    + IF UserHonest[u]
                                      THEN UserOnChainBalance(LedgerTx, LedgerTime', LedgerTime' - LedgerTime, u)
                                      ELSE 0

NextIIa ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIIa /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : MHM!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : MHM!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedIIa /\ UNCHANGED UserRequestedInvoices
NextIIaFair ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIIa
    \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedII(TRUE)

InitIIa ==
    /\ LET a == 1
       IN
        /\ PCU!Init(ActiveChannels, ActiveUsers)
        /\ HU!Init(ActiveChannels, ActiveUsers)
        /\ InitBase(ActiveUsers)
        /\ UserRequestedInvoices = [u \in ActiveUsers |-> {}]

SpecIIa ==
    /\ InitIIa
    /\ [][NextIIa]_varsIIa
    /\ WF_vars(NextIIaFair)

=============================================================================
