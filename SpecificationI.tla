--------------------------- MODULE SpecificationI ---------------------------

(***************************************************************************)
(* This is the main specification and the most detailed specification of   *)
(* Lightning in this repository.                                           *)
(***************************************************************************)

EXTENDS AbstractionHelpers, HTLCUserHelper, BaseSpec

VARIABLES
    (***********************************************************************)
    (* Global variables                                                    *)
    (***********************************************************************)
    Messages,
    LedgerTx,
    TxAge,
    
    (***********************************************************************)
    (* User variables (one entry for each user)                            *)
    (***********************************************************************)
    UserNewPayments,
    UserPreimageInventory,
    UserLatePreimages,
    UserPaymentSecretForPreimage,
    
    (***********************************************************************)
    (* Channel variables (one entry for each user)                         *)
    (***********************************************************************)
    ChannelMessages,
    ChannelUsedTransactionIds,
    ChannelPendingBalance,
    
    (***********************************************************************)
    (* Variables per channel and user (one entry for each channel and      *)
    (* user)                                                               *)
    (***********************************************************************)
    ChannelUserBalance,
    ChannelUserState,
    ChannelUserVars,
    ChannelUserDetailVars,
    ChannelUserInventory
    
vars ==                <<LedgerTime, Messages, LedgerTx, UserNewPayments, UserExtBalance, UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelMessages, ChannelUsedTransactionIds, ChannelPendingBalance, ChannelUserBalance, ChannelUserState, ChannelUserVars, ChannelUserDetailVars, ChannelUserInventory, UserChannelBalance, UserPayments, TxAge>>
varsWithoutBalances == <<            Messages,           UserNewPayments,                 UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelMessages, ChannelUsedTransactionIds, ChannelPendingBalance,                     ChannelUserState, ChannelUserVars, ChannelUserDetailVars, ChannelUserInventory,                     UserPayments>>

(***************************************************************************)
(* Collection of helper functions for working with the ledger              *)
(***************************************************************************)
Ledger == INSTANCE Ledger

(***************************************************************************)
(* User actions for channel lifecycle (open, update, close, cheat, punish, *)
(* ...)                                                                    *)
(***************************************************************************)
PCU == INSTANCE PaymentChannelUser WITH
            UnchangedVars <- <<Messages, LedgerTime, UserNewPayments, UserPaymentSecretForPreimage>>,
            AvailableTransactionIds <- [c \in ChannelIDs |-> (100*c+30)..(100*c+69)]
(***************************************************************************)
(* User actions for HTLC-based payments (invoice/add/fulfill/timeout)      *)
(***************************************************************************)
HU == INSTANCE HTLCUser WITH
            UnchangedVars <- <<TxAge, ChannelUsedTransactionIds, ChannelUserDetailVars, ChannelUserInventory, ChannelUserState, LedgerTime, LedgerTx, UserExtBalance, UserHonest>>

(***************************************************************************)
(* Sum of amounts currently spendable on-chain by a user, given their      *)
(* inventory and preimages.                                                *)
(***************************************************************************)
UserOnChainBalance(ledger, time, relTimelock, UserID) ==
    LET CombinedUserInventory == [keys |-> UNION {ChannelUserInventory[c][UserID].keys : c \in {c \in ActiveChannels : UserID \in DOMAIN ChannelUserInventory[c]}}]
    IN Ledger!SumAmounts({outputWithParent.output : outputWithParent \in Ledger!OnChainOutputSpendableByUser(ledger, CombinedUserInventory, UserPreimageInventory[UserID], time, relTimelock)})

(***************************************************************************)
(* Next points in time at which one of the users wants to take a step at   *)
(* the latest.                                                             *)
(***************************************************************************)
TimeBounds ==
    UNION UNION { {PCU!TimeBounds(c, u) : u \in UsersOfChannelSet(c)} : c \in ActiveChannels} \cup {MAX_TIME}
(***************************************************************************)
(* Next points in time at which one of the users wants to take a step at   *)
(* the latest ignoring a negligent user.                                   *)
(***************************************************************************)
NegligentTimeBounds(ChannelID, UserID) ==
    UNION UNION { {IF u # UserID \/ c # ChannelID THEN PCU!TimeBounds(c, u) ELSE {MAX_TIME} : u \in UsersOfChannelSet(c)} : c \in ActiveChannels} \cup {MAX_TIME}
                    \cup IF \E c \in ActiveChannels : UserID \in UsersOfChannelSet(c) /\ ChannelUserState[c][UserID] # "closed" THEN {MAX_TIME - 5} ELSE {}

(***************************************************************************)
(* Instances for advancing time                                               *)
(***************************************************************************)
LedgerTimeInstance == INSTANCE LedgerTime WITH
    Time <- LedgerTime,
    TimeBounds <- TimeBounds,
    NextChangingTimePoints <- 1..MAX_TIME
LedgerTimeInstanceNegligent(ChannelID, UserID) == INSTANCE LedgerTime WITH
    Time <- LedgerTime,
    TimeBounds <- NegligentTimeBounds(ChannelID, UserID),
    NextChangingTimePoints <- 1..MAX_TIME

(***************************************************************************)
(* Check that time is allowed to advance respecting the given time bounds. *)
(***************************************************************************)
CheckTxTimeBounds(txAge, timeBounds) ==
    /\ \A txid \in DOMAIN txAge :
        /\ txAge[txid] <= timeBounds[txid]
CheckCheatingTxPendingRevocation(CheatTxPendingRevocation, channelID) ==
    CheatTxPendingRevocation # <<>> =>
        LET cheatingTxId == CHOOSE txid \in DOMAIN CheatTxPendingRevocation : TRUE
            childTxs == {tx \in LedgerTx : \E input \in tx.inputs : input.parentId = cheatingTxId}
            childTxWithRevKey == {tx \in childTxs :
                                    \E output \in tx.outputs :
                                        \E condition \in output.conditions :
                                            CheatTxPendingRevocation[cheatingTxId] \in condition.data.keys
                                  }
        IN 
            \/  /\ TxAge'[cheatingTxId] < TO_SELF_DELAY
                /\ \A txid \in {tx.id : tx \in childTxWithRevKey} :
                    TxAge'[txid] < TO_SELF_DELAY
            \/ ~\E msg \in SeqToSet(ChannelMessages[channelID]) : msg.data.rSecretKey = CheatTxPendingRevocation[cheatingTxId]

(***************************************************************************)
(* Advance time                                                            *)
(***************************************************************************)
AdvanceLedgerTimeI ==
    /\ FORCE_LONG_SIMULATION => TLCGet("level") > SIMULATION_MIN_LENGTH
    /\ LedgerTimeInstance!AdvanceLedgerTime
    /\ TxAge' = [id \in {tx.id : tx \in LedgerTx} |-> LedgerTime' - (CHOOSE tx \in LedgerTx : tx.id = id).publishedAt]
    /\ \A c \in ActiveChannels : \A u \in UsersOfChannelSet(c) : CheckTxTimeBounds(TxAge', PCU!TxTimeBounds(c,u))
    /\ \A c \in ActiveChannels : \A u \in UsersOfChannelSet(c) : CheckCheatingTxPendingRevocation(ChannelUserDetailVars[c][u].CheatTxPendingRevocation, c)
    /\ UNCHANGED <<UserHonest, Messages, LedgerTx, UserNewPayments, UserExtBalance, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelMessages, ChannelUsedTransactionIds, ChannelPendingBalance, ChannelUserBalance, ChannelUserState, ChannelUserVars, ChannelUserDetailVars, ChannelUserInventory, UserChannelBalance, UserPayments>>
    
(***************************************************************************)
(* Move remaining balances on-chain after channels have been closed        *)
(* (helper).                                                               *)
(***************************************************************************)
WithdrawBalancesAfterChannelClosed(withExternal) ==
    /\ LedgerTime < 100
    /\ \A c \in ActiveChannels :
        \/  /\ \A u \in UsersOfChannelSet(c) : ChannelUserState[c][u] \in {"closed", "init", "open-sent-accept-channel", "open-sent-commit-funder", "open-sent-commit", "open-recv-commit"}
            /\ (\E u \in UsersOfChannelSet(c) : ChannelUserState[c][u] \in {"closed"})
                => \/ \A u \in UsersOfChannelSet(c) : ChannelUserState[c][u] \in {"closed"}
        \/ \A u \in UsersOfChannelSet(c) : ~UserHonest[u]
        /\ \A u \in UsersOfChannelSet(c) :
                ChannelUserState[c][u] \in {"open-funding-pub", "open-new-key-sent", "closing", "closed"}
                    => \A o \in UsersOfChannelSet(c) : u = o \/ ChannelUserState[c][o] \in {"closed"} \/ ~UserHonest[o]
    /\ \A c \in ActiveChannels : \A msg \in SeqToSet(ChannelMessages[c]) : msg.type # "HTLCPreimage"
    /\ LedgerTime' = 100
    /\ withExternal => UserExtBalance' = [u \in DOMAIN UserExtBalance |-> UserExtBalance[u] + 
                                                IF UserHonest[u]
                                                THEN UserOnChainBalance(LedgerTx, LedgerTime', LedgerTime' - LedgerTime, u)
                                                ELSE 0
                                                ]
    /\ ChannelUserBalance' = [c \in DOMAIN ChannelUserBalance |->
                                                   IF \E u \in UsersOfChannelSet(c) : ChannelUserState[c][u] \in {"closed", "closing"}
                                                   THEN [u \in UsersOfChannelSet(c) |-> IF UserHonest[u] THEN 0 ELSE ChannelUserBalance[c][u] ]
                                                   ELSE ChannelUserBalance[c] ]
    /\ UserChannelBalance' = [u \in DOMAIN UserChannelBalance |-> IF UserHonest[u] THEN 0 ELSE UserChannelBalance[u] ]
    /\ UNCHANGED varsWithoutBalances
    
(***************************************************************************)
(* Move remaining balances on-chain after channels have been closed        *)
(***************************************************************************)
WithdrawBalancesAfterChannelClosedI ==
    /\ WithdrawBalancesAfterChannelClosed(TRUE)
    /\ TxAge' = [id \in {tx.id : tx \in LedgerTx} |-> LedgerTime' - (CHOOSE tx \in LedgerTx : tx.id = id).publishedAt]
    /\ UNCHANGED LedgerTx

(***************************************************************************)
(* Initialize channel/payment modules and base state.               *)
(***************************************************************************)
Init ==
    /\ PCU!Init(ChannelIDs, UserIDs)
    /\ HU!Init(ChannelIDs, UserIDs)
    /\ InitBase(UserIDs)
    

(***************************************************************************)
(* One step—advance time, a payment channel / HTLC action, or              *)
(* withdraw-after-close.                                                   *)
(***************************************************************************)
NextI ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeI
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedI
NextIFair ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeI
    \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedI

SpecI ==
    /\ Init
    /\ [][NextI]_vars
    /\ WF_vars(NextIFair)
    
=============================================================================
