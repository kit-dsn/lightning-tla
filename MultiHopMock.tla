---------------------------- MODULE MultiHopMock ----------------------------

(***************************************************************************)
(* Module that mocks the whole environment of one channel for one          *)
(* particular user and channel.  Required for the specifications of a      *)
(* single channel (IIa and IIIa).                                          *)
(***************************************************************************)

EXTENDS Sequences, Naturals, TLC, FiniteSets, HTLCUserHelper

VARIABLES
    UserRequestedInvoices,
    UnchangedVars,
    
    LedgerTime,
    Messages,
    
    UserPayments,
    UserNewPayments,
    UserChannelBalance,
    UserExtBalance,
    UserHonest,
    UserPreimageInventory,
    UserLatePreimages,
    UserPaymentSecretForPreimage,
    
    ChannelUserState,
    ChannelUserVars
    
CONSTANTS
    Preimages,
    Amounts,
    IDs,
    NameForUserID,
    AllInitialPayments,
    UserInitialPayments,
    EmptyMessage,
    MAX_TIME,
    FORCE_LONG_SIMULATION,
    SIMULATION_MIN_LENGTH

SeqToSet(seq) ==
  { seq[i] : i \in DOMAIN seq }

SendMessage(messages, message) ==
    /\ Messages' = messages \cup {message}
    
OtherNames(UserID, OtherUserID) ==
    {NameForUserID[o] : o \in {o \in DOMAIN NameForUserID : o # UserID /\ o # OtherUserID}}
    
TimelockRegions(ChannelID, UserID, OtherUserID) ==
    LET timepoints ==
        { htlc.absTimelock : htlc \in {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs : htlc.hash \notin UserPreimageInventory[UserID] } }
        \cup 
        UNION {
            (TimestampsInDataForNextHop(CalculateDataForNextHops(Tail(payment.path), 0, 0, payment.absTimelock - G - 1), {NameForUserID[UserID]}))
                    : payment \in {pmt \in AllInitialPayments :
                                        /\ pmt.path[1] \in OtherNames(UserID, OtherUserID)
                                        /\ ~\E htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlc.id = pmt.id
                                   }
        }
    IN timepoints

Init(UserIDs) ==
    /\ UserRequestedInvoices = [u \in UserIDs |-> {}]

RequestInvoice(ChannelID, UserID, OtherUserID) ==
    /\ \E payment \in AllInitialPayments \ UserRequestedInvoices[UserID] :
        /\ payment.path[Len(payment.path)] = NameForUserID[UserID]
        /\  \/ payment.path[1] \in OtherNames(UserID, OtherUserID)
        /\ SendMessage(Messages, [EmptyMessage EXCEPT
                                                    !.recipient = NameForUserID[UserID],
                                                    !.sender = payment.path[1],
                                                    !.type = "RequestInvoice",
                                                    !.data.id = payment.id])
        /\ UserRequestedInvoices' = [UserRequestedInvoices EXCEPT ![UserID] = @ \cup {payment}]
    /\ UNCHANGED <<UserPayments, UserChannelBalance, UserExtBalance, UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, UserNewPayments, ChannelUserVars, UnchangedVars>>

GenerateAndSendPaymentHash(ChannelID, UserID, OtherUserID) ==
    /\ \E message \in Messages :
        /\ message.recipient \in OtherNames(UserID, OtherUserID)
        /\ message.sender = NameForUserID[UserID]
        /\ message.type = "RequestInvoice"
        /\ LET preimage == message.data.id + 150
               paymentSecret == message.data.id + 250
           IN   /\ LET hash == preimage
                   IN /\ SendMessage(Messages \ {message}, [EmptyMessage EXCEPT
                                                        !.recipient = message.sender, \* MyName
                                                        !.sender = message.recipient,
                                                        !.type = "Invoice",
                                                        !.data.hash = hash,
                                                        !.data.paymentSecret = paymentSecret])
    /\ UNCHANGED <<UserPayments, UserChannelBalance, UserExtBalance, UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, UserNewPayments, ChannelUserVars, UserRequestedInvoices, UnchangedVars>>

ReceiveInvoice(ChannelID, UserID, OtherUserID) ==
    /\ \E message \in Messages :
        /\ message.recipient \in OtherNames(UserID, OtherUserID)
        /\ message.type = "Invoice"
        /\ Messages' = Messages \ {message}
    /\ UNCHANGED <<UserPayments, UserChannelBalance, UserExtBalance, UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, UserNewPayments, ChannelUserVars, UserRequestedInvoices, UnchangedVars>>

IgnoreMessageDuringClosing(ChannelID, UserID, OtherUserID) ==
    /\ FORCE_LONG_SIMULATION => TLCGet("level") > SIMULATION_MIN_LENGTH
    /\ \E message \in Messages :
        /\ message.recipient \in OtherNames(UserID, OtherUserID)
        /\ message.type = "RequestInvoice"
        /\ Messages' = Messages \ {message}
    /\ UNCHANGED <<UserPayments, UserChannelBalance, UserExtBalance, UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, UserNewPayments, ChannelUserVars, UserRequestedInvoices, UnchangedVars>>

AddOutgoingHTLCToOtherChannel(ChannelID, UserID, OtherUserID) ==
    /\ \E payment \in UserNewPayments[UserID] :
        /\ payment.nextHop \in OtherNames(UserID, OtherUserID)
        /\ UserNewPayments' = [UserNewPayments EXCEPT ![UserID] = @ \ {payment}]
    /\ UNCHANGED <<UserPayments, UserChannelBalance, UserExtBalance, UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, Messages, ChannelUserVars, UserRequestedInvoices, UnchangedVars>>

AddNewForwardedPayment(ChannelID, UserID, OtherUserID) ==
    /\ \E payment \in AllInitialPayments :
        /\ Len(payment.path) > 2
        /\ \E i \in 2..(Len(payment.path)-1) :
            /\ payment.path[i] = NameForUserID[UserID]
            /\ payment.path[i-1] \in OtherNames(UserID, OtherUserID)
            /\ \E receiverId \in DOMAIN NameForUserID :
               LET receiver == payment.path[Len(payment.path)]
               IN
                /\ NameForUserID[receiverId] = payment.path[Len(payment.path)]
                /\  LET preimage == payment.id + 150
                        paymentSecret == payment.id + 250
                    IN
                            /\ receiver = NameForUserID[OtherUserID] => preimage \in UserPreimageInventory[receiverId]
                            /\ ~\E otherPayment \in UserNewPayments[UserID] :
                                    /\ otherPayment.amount = payment.amount
                                    /\ "sender" \in DOMAIN otherPayment
                                    /\ otherPayment.sender = payment.path[i-1]
                                    /\ otherPayment.nextHop = payment.path[i]
                            /\ ~\E htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : htlc.hash = preimage
                            /\ ~\E otherPayment \in UserNewPayments[UserID] : otherPayment.hash = preimage 
                            /\ UserNewPayments' = [UserNewPayments EXCEPT ![UserID] = @ \cup {
                                                                [amount |-> payment.amount,
                                                                   hash |-> preimage,
                                                            absTimelock |-> payment.absTimelock - (G + 1) * (i-1),
                                                                 sender |-> payment.path[i-1], 
                                                       invoiceRequested |-> TRUE,
                                                                nextHop |-> payment.path[i+1],
                                                         dataForNextHop |-> CalculateDataForNextHops([n \in 1..(Len(payment.path)-i) |-> payment.path[n+i]], paymentSecret, payment.amount, payment.absTimelock - G - 1 - G - 1),
                                                                     id |-> payment.id ]}]
    /\ UNCHANGED <<UserPayments, UserChannelBalance, UserExtBalance, UserHonest, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelUserVars, Messages, UserRequestedInvoices, UnchangedVars>>

ReceivePreimageForIncomingHTLC(ChannelID, UserID) ==
    /\ \E htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs :
        /\ htlc.state \in {"NEW", "ABORTED", "COMMITTED", "PUNISHED", "OFF-TIMEDOUT", "SENT-REMOVE", "RECV-REMOVE", "PENDING-REMOVE", "TIMEDOUT"}
        /\ htlc.hash \notin UserPreimageInventory[UserID]
        /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserID] = @ \cup {htlc.hash}]
        /\ ~\E payment \in UserNewPayments[UserID] : payment.hash = htlc.hash \* we cannot receive a preimage unless we have already forwarded the HTLC
        /\  \/  /\ htlc.absTimelock > LedgerTime
                /\ UNCHANGED UserLatePreimages
            \/  UserLatePreimages' = [UserLatePreimages EXCEPT ![UserID] = @ \cup {htlc.hash}]
    /\ UNCHANGED <<UserPayments, UserChannelBalance, UserExtBalance, UserHonest, UserNewPayments, UserPaymentSecretForPreimage, ChannelUserVars, Messages, UserRequestedInvoices, UnchangedVars>>
        
UserOpensPaymentChannel(UserID) ==
    /\ ~\E inv \in UserRequestedInvoices[UserID] : "type" \in DOMAIN inv
    /\ UserExtBalance[UserID] > 0
    /\ UserExtBalance' = [UserExtBalance EXCEPT ![UserID] = 0]
    /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + UserExtBalance[UserID]]
    /\ UserRequestedInvoices' = [UserRequestedInvoices EXCEPT ![UserID] = @ \cup {[type |-> "BalanceInOtherChannel", amount |-> UserExtBalance[UserID]]}]
    /\ UNCHANGED <<UserPayments, UserHonest, UserNewPayments, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelUserVars, Messages, UnchangedVars>>

ProcessOtherPayment(ChannelID, UserID, OtherUserID) ==
    /\ \E pmt \in UserPayments[UserID] :
        \/
            /\ pmt.receiver = UserID
            /\ \A initPmt \in UserInitialPayments[pmt.sender] :
                initPmt.id = pmt.id =>
                    NameForUserID[OtherUserID] \notin SeqToSet(initPmt.path)
            /\ UserPayments' = [UserPayments EXCEPT ![UserID] = (@ \ {pmt}) \cup {[pmt EXCEPT !.state = "PROCESSED"]}]
            /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + pmt.amount]
        \/
            /\ pmt.sender = UserID
            /\ \A initPmt \in UserInitialPayments[UserID] :
                initPmt.id = pmt.id =>
                    NameForUserID[OtherUserID] \notin SeqToSet(initPmt.path)
            /\ UserPayments' = [UserPayments EXCEPT ![UserID] = (@ \ {pmt}) \cup {[pmt EXCEPT !.state = "PROCESSED"]}]
            /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ - pmt.amount]
    /\ UNCHANGED <<UserHonest, UserExtBalance, UserRequestedInvoices, UserNewPayments, UserPreimageInventory, UserLatePreimages, UserPaymentSecretForPreimage, ChannelUserVars, Messages, UnchangedVars>>
    

Next(ChannelID, UserID, OtherUserID) ==
    \/ RequestInvoice(ChannelID, UserID, OtherUserID)
    \/ GenerateAndSendPaymentHash(ChannelID, UserID, OtherUserID)
    \/ ReceiveInvoice(ChannelID, UserID, OtherUserID)
    \/ IgnoreMessageDuringClosing(ChannelID, UserID, OtherUserID)
    \/ AddOutgoingHTLCToOtherChannel(ChannelID, UserID, OtherUserID)
    \/ AddNewForwardedPayment(ChannelID, UserID, OtherUserID)
    \/ ReceivePreimageForIncomingHTLC(ChannelID, UserID)
    \/ UserOpensPaymentChannel(UserID)
    \/ ProcessOtherPayment(ChannelID, UserID, OtherUserID)


=============================================================================
