------------------------- MODULE SpecificationIIIa -------------------------

EXTENDS SpecificationIII, FiniteSets

ASSUME Cardinality(ActiveChannels) = 1
ActiveUsers == UNION {{UsersOfChannel[c][1], UsersOfChannel[c][2]} : c \in ActiveChannels}

VARIABLES
    UserRequestedInvoices
    
varsIIIa == <<vars, UserRequestedInvoices>>

MHM == INSTANCE MultiHopMock WITH
    UnchangedVars <- <<ChannelMessages, ChannelPendingBalance, ChannelUserBalance, ChannelUserState, LedgerTime, UserPayments>>

NextIIIa ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIII /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : AbstractChannel!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : MHM!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : MHM!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosed /\ UNCHANGED UserRequestedInvoices
NextIIIaFair ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIII
    \/ \E c \in ActiveChannels : (UserHonest[UsersOfChannel[c][1]] \/ UserHonest[UsersOfChannel[c][2]]) /\ AbstractChannel!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) 
    \/ WithdrawBalancesAfterChannelClosed

InitIIIa ==
    /\ AbstractChannel!Init(ActiveChannels, ActiveUsers, UsersOfChannel)
    /\ HU!Init(ActiveChannels, ActiveUsers)
    /\ InitBase(ActiveUsers)
    /\ UserRequestedInvoices = [u \in ActiveUsers |-> {}]

SpecIIIa ==
    /\ InitIIIa
    /\ [][NextIIIa]_varsIIIa
    /\ WF_vars(NextIIIaFair)

=============================================================================
