--------------------------- MODULE SpecificationV ---------------------------

VARIABLES BlockchainBalances, ChannelBalances,
    Payments, Honest
CONSTANTS UserIds, InitialPayments, Numbers
    
IdealUser(user) == INSTANCE IdealUser WITH
    UserId <- user,
    ChannelBalance <- ChannelBalances[user],
    BlockchainBalance <- BlockchainBalances[user],
    Payments <- Payments[user],
    Honest <- Honest[user]
    
IdealPayments == INSTANCE IdealPayments
    
Spec ==
    /\ \A user \in UserIds : IdealUser(user)!Spec
    /\ IdealPayments!Spec

=============================================================================
