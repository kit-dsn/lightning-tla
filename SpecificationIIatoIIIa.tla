----------------------- MODULE SpecificationIIatoIIIa -----------------------

EXTENDS SpecificationIIa, SpecificationIItoIII

varsIIatoIIIa == <<varsIItoIII, UserRequestedInvoices>>

NextIIatoIIIa ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIIa /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory, UserRequestedInvoices>>
    \/ \E c \in ActiveChannels : PCUwH(c)!NextH(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : PCUwH(c)!NextH(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED UserRequestedInvoices
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory, UserRequestedInvoices>>
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory, UserRequestedInvoices>>
    \/ \E c \in ActiveChannels : MHM!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory>>
    \/ \E c \in ActiveChannels : MHM!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1]) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory>>
    \/ WithdrawBalancesAfterChannelClosedII(TRUE) /\ UNCHANGED <<ChannelPersistedHTLCsBeforeClose, ChannelUserHTLCHistory, UserRequestedInvoices>>

InitIIatoIIIa ==
    /\ InitIIa
    /\ ChannelUserHTLCHistory = [c \in ChannelIDs |-> [u \in UsersOfChannelSet(c) |-> [
        IncomingHTLCs |-> {},
        OutgoingHTLCs |-> {},
        StateBeforeClosing |-> "",
        OtherWasHonestBeforeCheat |-> FALSE
       ] ]]
    /\ ChannelPersistedHTLCsBeforeClose = [c \in ChannelIDs |-> {}]
    
SpecIIatoIIIa ==
    /\ InitIIatoIIIa
    /\ [][NextIIatoIIIa]_varsIIatoIIIa
    /\ WF_vars(NextIIaFair)

SpecificationIIIa == INSTANCE SpecificationIIIa WITH
    ChannelMessages <- [c \in ActiveChannels |-> AbstractedChannelMessages(c)],
    ChannelPendingBalance <- [c \in ActiveChannels |-> AbstractedChannelPendingBalance(c, UsersOfChannel[c][1], UsersOfChannel[c][2])],
    ChannelUserState <- [c \in ActiveChannels |-> [u \in UsersOfChannelSet(c) |-> AbstractedChannelUserState(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)]],
    ChannelUserBalance <- [c \in ActiveChannels |-> [u \in UsersOfChannelSet(c) |-> AbstractedChannelUserBalance(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)]],
    ChannelUserVars <-[c \in ActiveChannels |-> [u \in UsersOfChannelSet(c) |-> AbstractedChannelUserVars(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u)]]

=============================================================================
