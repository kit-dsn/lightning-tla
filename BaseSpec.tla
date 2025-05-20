------------------------------ MODULE BaseSpec ------------------------------

EXTENDS Integers, Sequences, TLC

VARIABLES
    UserPayments,
    UserExtBalance,
    UserChannelBalance,
    UserHonest,
    LedgerTime

CONSTANT
    NullUser,
    NameForUserID,
    RevKeyForUserID,
    SingleSignature,
    AllSignatures,
    MAX_TIME,
    UserInitialPayments,
    UserInitialBalance,
    ActiveChannels,
    OptimizedTxAge
    
Users == {NameForUserID[i] : i \in DOMAIN NameForUserID} \cup {NullUser}
RevocationKeys == [Base: {RevKeyForUserID[i] : i \in DOMAIN RevKeyForUserID}, Index: 0..100]
Keys == Users \cup RevocationKeys
Hashes == 0..900
Preimages == 0..900
Time == 0..100
IDs == 1..900
Amounts == 0..20
NUM_USERS == Len(NameForUserID)
NUM_CHANNELS == NUM_USERS - 1
TO_SELF_DELAY == 5 \* could be defined externally (we define it here so that we don't have to update all models when we modify it)

SIMULATION_MIN_LENGTH == 127
FORCE_LONG_SIMULATION == FALSE

EmptyMessage ==
    [recipient |-> NullUser,
        type |-> "",
        data |-> [key |-> NullUser, rKey |-> NullUser, rSecretKey |-> NullUser, capacity |-> 0,
            transaction |-> 0, htlcTransactions |-> {}, fundingTxId |-> 0,
            htlcData |-> [null |-> 0], hash |-> 0, preimage |-> 0, paymentSecret |-> 0, id |-> 0],
        module |-> "",
        timestamp |-> 0,
        sender |-> NullUser]
        
RECURSIVE UtoIHelper(_, _) 
UtoIHelper(username, id) ==
    IF id = 0
    THEN Print("Error! Unknown username", username)
    ELSE IF username = NameForUserID[id]
    THEN id
    ELSE UtoIHelper(username, id - 1)
UsernameToId(username) ==
    UtoIHelper(username, NUM_USERS)
UserIDs == DOMAIN NameForUserID
ChannelIDs == 1..NUM_CHANNELS
RevKeyBaseForChannelAndUserID == [c \in ChannelIDs |-> RevKeyForUserID]

UsersOfChannel == [c \in ChannelIDs |-> <<c, c+1>>] \* first user is funder
UserIsFunderOfChannel(c, u) == u = UsersOfChannel[c][1]
UsersOfChannelSet(c) == {UsersOfChannel[c][1], UsersOfChannel[c][2]}

AllInitialPayments == UNION {UserInitialPayments[u] : u \in UserIDs}

InitialExternalPayments ==
    {[  amount |-> payment.amount,
        sender |-> UsernameToId(payment.path[1]),
        receiver |-> UsernameToId(payment.path[Len(payment.path)]),
        state |-> "NEW",
        id |-> payment.id
        ] : payment \in AllInitialPayments }

InitBase(userIDs) ==
    /\ UserPayments = [u \in userIDs |-> {pmt \in InitialExternalPayments : pmt.sender = u \/ pmt.receiver = u}]
    /\ UserExtBalance = [u \in userIDs |-> UserInitialBalance[u]]
    /\ UserChannelBalance = [u \in userIDs |-> 0]
    /\ UserHonest \in [userIDs -> {TRUE, FALSE}]
    /\ LedgerTime = 1
    
    
IdealPayments == INSTANCE IdealPayments WITH
    Payments <- UserPayments,
    Numbers <- 0..40,
    UserIds <- UserIDs
    
IdealUser(UID) == INSTANCE IdealUser WITH
    UserId <- UID,
    InitialPayments <- InitialExternalPayments,
    ChannelBalance <- UserChannelBalance[UID],
    BlockchainBalance <- UserExtBalance[UID],
    Payments <- UserPayments[UID],
    Honest <- UserHonest[UID],
    Numbers <- 0..40,
    UserIds <- UserIDs

=============================================================================
