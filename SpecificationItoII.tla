------------------------- MODULE SpecificationItoII -------------------------

EXTENDS SpecificationI

VARIABLES
    MappedLedgerTime,
    MappedTxAge
    
varsItoII == <<vars, MappedLedgerTime, MappedTxAge>>

TransactionContainsRelativeTimelock(id) ==
    LET tx == CHOOSE tx \in LedgerTx : tx.id = id
    IN  \E output \in tx.outputs :
            \E condition \in output.conditions :
                condition.relTimelock > 0
                
TxAgeMapping(id) ==
    IF id \in DOMAIN MappedTxAge
    THEN MappedTxAge[id]
    ELSE IF ~OptimizedTxAge \/ TransactionContainsRelativeTimelock(id)
         THEN 0
         ELSE TO_SELF_DELAY

SpecificationII == INSTANCE SpecificationII WITH
                LedgerTime <- MappedLedgerTime,
                TxAge <- [id \in {tx.id : tx \in LedgerTx} |-> TxAgeMapping(id)]

AdvanceLedgerTimeItoII ==
    /\ AdvanceLedgerTimeI
    /\ MappedLedgerTime' = MaxOfSet({MappedLedgerTime} \cup {time \in SpecificationII!relETP : time <= LedgerTime'})
    /\ MappedTxAge' = [id \in {tx.id : tx \in LedgerTx} |->
                                           IF \/ id \in DOMAIN MappedTxAge /\ MappedTxAge[id] = TO_SELF_DELAY
                                              \/ TxAge'[id] >= TO_SELF_DELAY
                                           THEN TO_SELF_DELAY
                                           ELSE IF id \in DOMAIN MappedTxAge
                                                THEN MappedTxAge[id]
                                                ELSE IF TransactionContainsRelativeTimelock(id) THEN 0 ELSE TO_SELF_DELAY]

WithdrawBalancesAfterChannelClosedIoII ==
    /\ WithdrawBalancesAfterChannelClosedI
    /\ MappedLedgerTime' = 100
    /\ MappedTxAge' = [id \in {tx.id : tx \in LedgerTx} |-> TO_SELF_DELAY ]

InitItoII ==
    /\ Init
    /\ MappedLedgerTime = 1
    /\ MappedTxAge = [id \in {tx.id : tx \in LedgerTx} |-> TO_SELF_DELAY]

NextItoII ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeItoII
    \/  /\ UNCHANGED <<MappedLedgerTime, MappedTxAge>>
        /\  \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
            \/ \E c \in ActiveChannels : PCU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
            \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
            \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedIoII
NextItoIIFair ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeItoII
    \/  /\ UNCHANGED <<MappedLedgerTime, MappedTxAge>>
        /\  \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
            \/ \E c \in ActiveChannels : PCU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
            \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
            \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedIoII
    
SpecItoII ==
    /\ InitItoII
    /\ [][NextItoII]_varsItoII
    /\ WF_varsItoII(NextItoIIFair)

THEOREM SpecItoII => SpecificationII!SpecII

=============================================================================
