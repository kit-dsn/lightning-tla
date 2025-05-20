------------------------ MODULE SpecificationIIItoIV ------------------------

EXTENDS SpecificationIII

VARIABLES
    MappedLedgerTime,
    MappedLedgerTimeHistory
    
varsIIItoIV == <<vars, MappedLedgerTime, MappedLedgerTimeHistory>>

SpecificationIV == INSTANCE SpecificationIV WITH LedgerTime <- MappedLedgerTime

AdvanceLedgerTimeIIItoIV ==
    /\ AdvanceLedgerTimeIII
    /\ MappedLedgerTime' = MaxOfSet({MappedLedgerTime} \cup {time \in SpecificationIV!SpecIVNCTPs : time <= LedgerTime'})
    /\ MappedLedgerTimeHistory' = MappedLedgerTimeHistory @@ LedgerTime' :> MappedLedgerTime'
    
WithdrawBalancesAfterChannelClosedIIItoIV ==
    /\ WithdrawBalancesAfterChannelClosed
    /\ MappedLedgerTime' = 100
    /\ MappedLedgerTimeHistory' = [x \in DOMAIN MappedLedgerTimeHistory \cup {LedgerTime'} |->
                                        IF x \in DOMAIN MappedLedgerTimeHistory
                                        THEN MappedLedgerTimeHistory[x]
                                        ELSE MappedLedgerTime']

InitIIItoIV ==
    /\ Init
    /\ MappedLedgerTime = 1
    /\ MappedLedgerTimeHistory = [x \in -1..1 |-> x]

NextIIItoIV ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIIItoIV
    \/  /\ UNCHANGED <<MappedLedgerTime, MappedLedgerTimeHistory>>
        /\  \/ \E c \in ActiveChannels : AbstractChannel!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
            \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
            \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosedIIItoIV

SpecIIItoIV ==
    /\ InitIIItoIV
    /\ [][NextIIItoIV]_varsIIItoIV
    /\ WF_vars(NextIIIFair)

=============================================================================
