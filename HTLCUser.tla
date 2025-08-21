------------------------------ MODULE HTLCUser ------------------------------

(***************************************************************************)
(* This module specifies the actions for HTLC-based payments               *)
(* (invoice/add/fulfill/timeout).                                          *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC, HTLCUserHelper, SumAmounts

CONSTANTS EmptyMessage,
          IDs,
          Hashes,
          Time,
          Preimages,
          Amounts,
          MAX_TIME,
          NameForUserID,
          UserInitialPayments,
          FORCE_LONG_SIMULATION,
          SIMULATION_MIN_LENGTH

VARIABLES
    LedgerTime,
    Messages,
    UserChannelBalance,
    UserPayments,
    UserNewPayments,
    UserPreimageInventory,
    UserLatePreimages,
    UserPaymentSecretForPreimage,
    UserHonest,
    
    ChannelMessages,
    ChannelPendingBalance,
    
    ChannelUserBalance,
    ChannelUserState,
    ChannelUserVars,
    
    UnchangedVars

SeqToSet(seq) ==
  { seq[i] : i \in DOMAIN seq }

RECURSIVE MyFirstChannelMessageHelper(_, _)
MyFirstChannelMessageHelper(msgs, UserID) ==
    IF Len(msgs) = 0 THEN {} ELSE
    IF Head(msgs).recipient # NameForUserID[UserID] THEN MyFirstChannelMessageHelper(Tail(msgs), UserID) ELSE
    {Head(msgs)}
MyFirstChannelMessage(ChannelID, UserID) ==
    MyFirstChannelMessageHelper(ChannelMessages[ChannelID], UserID)
    
RECURSIVE RemoveMyFirstChannelMessageHelper(_, _)
RemoveMyFirstChannelMessageHelper(msgs, UserID) ==
    IF Head(msgs).recipient = NameForUserID[UserID] THEN Tail(msgs) ELSE
    <<Head(msgs)>> \o RemoveMyFirstChannelMessageHelper(Tail(msgs), UserID)
RemoveMyFirstChannelMessage(ChannelID, UserID) ==
    RemoveMyFirstChannelMessageHelper(ChannelMessages[ChannelID], UserID)
    
SendChannelMessageM(messages, message, messagesVar, channelID, myName, otherState) ==
    /\ messagesVar' = [messagesVar EXCEPT ![channelID] = Append(messages, [message EXCEPT !.sender = myName])]
    /\ otherState # "closed"

TimelockRegions(ChannelID, UserID, OtherUserID) ==
    LET timepoints ==
        UNION {
            (IF payment.nextHop = NameForUserID[OtherUserID] THEN {payment.absTimelock, payment.absTimelock + G + 1} ELSE {})
            \cup
            (IF payment.dataForNextHop # [None |-> 0]
             THEN TimestampsInDataForNextHop(payment.dataForNextHop, {NameForUserID[OtherUserID]})
             ELSE TimestampsInDataForNextHop(CalculateDataForNextHops(Tail(payment.path), 0, 0, payment.absTimelock - G - 1), {NameForUserID[OtherUserID]}))
                    : payment \in UserNewPayments[UserID]
        }
        \cup
        UNION {
            (IF message.type = "UpdateAddHTLC" /\ message.sender = NameForUserID[UserID]
             THEN TimestampsInDataForNextHop(message.data.htlcData.dataForNextHop, {NameForUserID[OtherUserID]})
             ELSE {})  : message \in SeqToSet(ChannelMessages[ChannelID])
        }
        \cup
        LET HTLCs == {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs : \/ htlc.state \in {"NEW", "SENT-COMMIT", "RECV-COMMIT", "PENDING-COMMIT", "COMMITTED"}
                                                                            \/ htlc.fulfilled = FALSE }
        IN UNION { {htlc.absTimelock, htlc.absTimelock + G + 1} : htlc \in HTLCs}
    IN timepoints
    
Init(ChannelIDs, UserIDs) ==
    /\ Messages = {}
    /\ ChannelMessages = [c \in ChannelIDs |-> <<>>]
    /\ \A u \in UserIDs :
        /\ \A pmt \in UserInitialPayments[u] : pmt.absTimelock \in Time
        /\ Cardinality({pmt.id : pmt \in UserInitialPayments[u]}) = Cardinality(UserInitialPayments[u])
    /\ UserNewPayments = [u \in UserIDs |-> 
                    {[ id |-> payment.id,
                        amount |-> payment.amount,
                        path |-> payment.path,
                        absTimelock |-> payment.absTimelock,
                        invoiceRequested |-> FALSE,
                        hash |-> -1,
                        paymentSecret |-> -1,
                        nextHop |-> Head(Tail(payment.path)),
                        dataForNextHop |-> [None |-> 0]] : payment \in UserInitialPayments[u]}
                ]
    /\ UserLatePreimages = [u \in UserIDs |-> {}]
    /\ UserPaymentSecretForPreimage = [u \in UserIDs |-> <<>>]

(***************************************************************************)
(* Requests an invoice from another user to whom a payment should be sent. *)
(***************************************************************************)
RequestInvoice(UserID) ==
    /\ Cardinality(UserNewPayments[UserID]) > 0
    /\ \E payment \in UserNewPayments[UserID] :
        /\ payment.invoiceRequested = FALSE
        /\ \A otherP \in {pmt \in UserNewPayments[UserID] : pmt.invoiceRequested = FALSE} : otherP.absTimelock >= payment.absTimelock
        /\ Messages' = Messages \cup {[EmptyMessage EXCEPT !.recipient = payment.path[Len(payment.path)],
                                                      !.sender = NameForUserID[UserID],
                                                      !.type = "RequestInvoice",
                                                      !.data.id = payment.id]}
        /\ UserNewPayments' = [UserNewPayments EXCEPT ![UserID] = (@ \ {payment})
                                \cup {[payment EXCEPT !.invoiceRequested = TRUE]}]
    /\ UNCHANGED <<ChannelMessages, UserPreimageInventory, UserPaymentSecretForPreimage, UserLatePreimages, ChannelUserVars, ChannelUserBalance, ChannelPendingBalance, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars  
    
(***************************************************************************)
(* Receive the request for an invoice and reply by generating and sending  *)
(* a payment hash.                                                         *)
(***************************************************************************)
GenerateAndSendPaymentHash(UserID) ==
    /\ \E message \in Messages :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "RequestInvoice"
        /\ LET preimage == message.data.id + 150
               paymentSecret == message.data.id + 250
           IN   /\ ~ preimage \in UserPreimageInventory[UserID] \* this check is not required, just an assertion as validity check for the specification 
                /\ LET hash == preimage
                   IN /\ Messages' = (Messages \ {message}) \cup {[EmptyMessage EXCEPT !.recipient = message.sender,
                                                         !.sender = NameForUserID[UserID],
                                                         !.type = "Invoice",
                                                         !.data.hash = hash,
                                                         !.data.paymentSecret = paymentSecret]}
                      /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserID] = @ \cup {preimage}]
                      /\ UserPaymentSecretForPreimage' = [UserPaymentSecretForPreimage EXCEPT ![UserID] = [x \in DOMAIN @ \cup {preimage} |-> IF x = preimage THEN paymentSecret ELSE @[x]]]
    /\ UNCHANGED <<ChannelMessages, UserLatePreimages, ChannelUserBalance, ChannelPendingBalance, UserNewPayments, ChannelUserVars, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars
   
(***************************************************************************)
(* Receive an invoice / payment hash for a payment for which an invoice    *)
(* was requested.                                                          *)
(***************************************************************************)
ReceivePaymentHash(UserID) ==
    /\ \E message \in Messages :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "Invoice"
        /\ \E payment \in UserNewPayments[UserID] :
            /\ "path" \in DOMAIN payment
            /\ message.sender = payment.path[Len(payment.path)] \* sender of message is receiver of payment
            /\ payment.invoiceRequested
            /\ UserNewPayments' = [UserNewPayments EXCEPT ![UserID] = (@ \ {payment}) \cup
                                    {[payment EXCEPT !.hash = message.data.hash,
                                                     !.paymentSecret = message.data.paymentSecret,
                                                     !.dataForNextHop = CalculateDataForNextHops(
                                                                                Tail(payment.path),
                                                                                message.data.paymentSecret,
                                                                                payment.amount,
                                                                                payment.absTimelock - G - 1
                                                                            )]}]
        /\ Messages' = Messages \ {message}
    /\ UNCHANGED <<ChannelMessages, UserLatePreimages, UserPaymentSecretForPreimage, UserPreimageInventory, ChannelUserBalance, ChannelPendingBalance, ChannelUserVars, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars
    
(***************************************************************************)
(* Add an outgoing HTLC for a payment that should be sent.  And send an    *)
(* UpdateAddHTLC message to the other user to add the HTLC.                *)
(***************************************************************************)
AddAndSendOutgoingHTLC(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] \in {"rev-keys-exchanged", "closing-time-set"}
    /\ Cardinality(UserNewPayments[UserID]) > 0
    /\ \E payment \in UserNewPayments[UserID] :
        /\ payment.hash > 0
        /\ LedgerTime < payment.absTimelock 
        /\ \A otherP \in UserNewPayments[UserID] : ((otherP.absTimelock > LedgerTime /\ NameForUserID[OtherUserID] = otherP.nextHop) => otherP.absTimelock >= payment.absTimelock)
        /\ LET 
           htlcData == [amount |-> payment.amount,
                        hash |-> payment.hash,
                        absTimelock |-> payment.absTimelock,
                        dataForNextHop |-> payment.dataForNextHop,
                        id |-> payment.id
                       ]
           IN
            /\ NameForUserID[OtherUserID] = payment.nextHop
            /\ LET  myOtherChannels == {c \in DOMAIN ChannelUserVars : UserID \in DOMAIN ChannelUserVars[c]}
                    myVarsInOtherChannels == {ChannelUserVars[c][UserID] : c \in myOtherChannels}
               IN \A otherVars \in myVarsInOtherChannels :
                    \A htlc \in otherVars.IncomingHTLCs :
                        (htlc.hash = payment.hash) => htlc.state = "COMMITTED"
            /\ \A htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs \cup ChannelUserVars[ChannelID][UserID].OutgoingHTLCs :
                htlc.hash # payment.hash
            /\ ChannelUserBalance[ChannelID][UserID] >= payment.amount
            /\ UserNewPayments' = [UserNewPayments EXCEPT ![UserID] = @ \ {payment}]
            /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OutgoingHTLCs = @ \cup {[amount |-> payment.amount,
                                                                hash |-> payment.hash,
                                                                absTimelock |-> payment.absTimelock,
                                                                state |-> "NEW",
                                                                fulfilled |-> FALSE,
                                                                punished |-> FALSE,
                                                                timedout |-> FALSE,
                                                                id |-> payment.id]}]
            /\ SendChannelMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT
                                                !.recipient = NameForUserID[OtherUserID],
                                                !.type = "UpdateAddHTLC",
                                                !.data.htlcData = htlcData], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
    /\ UNCHANGED <<Messages, UserLatePreimages, UserPaymentSecretForPreimage, ChannelUserBalance, ChannelPendingBalance, UserPreimageInventory, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars
    
(***************************************************************************)
(* Receive an UpdateAddHTLC message.  If we should forward the payment,    *)
(* add the payment to be forwarded to the set of new payments.             *)
(***************************************************************************)
ReceiveUpdateAddHTLC(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] # "closed"
    /\ \E message \in MyFirstChannelMessage(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.sender = NameForUserID[OtherUserID]
        /\ message.type = "UpdateAddHTLC"
        /\ LET state == IF ChannelUserState[ChannelID][UserID] \in {"closing", "closed"} THEN "ABORTED" ELSE "NEW"
               newHTLC == [amount |-> message.data.htlcData.amount, hash |-> message.data.htlcData.hash, absTimelock |-> message.data.htlcData.absTimelock, state |-> state, fulfilled |-> FALSE, punished |-> FALSE, timedout |-> FALSE, id |-> message.data.htlcData.id]
           IN ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].IncomingHTLCs = @ \cup {newHTLC}]
        /\ IF "paymentSecret" \in DOMAIN message.data.htlcData.dataForNextHop
           THEN \* we are the payment's receiver
                /\ UNCHANGED UserNewPayments
                /\ UserPaymentSecretForPreimage[UserID][message.data.htlcData.hash] = message.data.htlcData.dataForNextHop.paymentSecret
                /\ message.data.htlcData.amount = message.data.htlcData.dataForNextHop.amount
                /\ \E pmt \in UserPayments[UserID] :
                    /\ pmt.receiver = UserID
                    /\ pmt.id = message.data.htlcData.id
                    /\ pmt.amount = message.data.htlcData.amount
           ELSE \* we forward the payment
                /\ IF message.data.htlcData.dataForNextHop.absTimelock + G < message.data.htlcData.absTimelock 
                   THEN UserNewPayments' = [UserNewPayments EXCEPT ![UserID] = @ \cup {
                                                [amount |-> message.data.htlcData.amount,
                                                   hash |-> message.data.htlcData.hash,
                                            absTimelock |-> message.data.htlcData.dataForNextHop.absTimelock,
                                                 sender |-> NameForUserID[OtherUserID], 
                                       invoiceRequested |-> TRUE,
                                                nextHop |-> message.data.htlcData.dataForNextHop.nextHop,
                                         dataForNextHop |-> message.data.htlcData.dataForNextHop.dataForNextHop,
                                                     id |-> message.data.htlcData.id] }]
                   ELSE UNCHANGED UserNewPayments
                /\ message.data.htlcData.hash \notin UserPreimageInventory[UserID]
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstChannelMessage(ChannelID, UserID)]
    /\ UNCHANGED <<Messages, UserLatePreimages, UserPaymentSecretForPreimage, UserPreimageInventory, ChannelUserBalance, ChannelPendingBalance, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars
    
(***************************************************************************)
(* Fulfill an HTLC by sending the preimage.                                *)
(***************************************************************************)
SendHTLCPreimage(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] \in {"rev-keys-exchanged", "closing-time-set"}
    /\ \E htlc \in {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs : htlc.state = "COMMITTED"} :
        /\ htlc.hash \in (UserPreimageInventory[UserID] \ ChannelUserVars[ChannelID][UserID].OtherKnownPreimages)
        /\ LedgerTime < htlc.absTimelock \* we could still fulfill as long as LedgerTime < timelock + G, however, BOLT-02 says that we "SHOULD fail an HTLC which has timed out"
        /\ SendChannelMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                           !.type = "HTLCPreimage",
                                           !.data.preimage = htlc.hash], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
        /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OtherKnownPreimages = @ \cup {htlc.hash},
                                ![ChannelID][UserID].IncomingHTLCs = (@ \ {htlc}) \cup {[htlc EXCEPT !.state = "FULFILLED", !.fulfilled = TRUE]},
                                ![ChannelID][UserID].FulfilledAfterTimeoutHTLCs = @ \cup IF LedgerTime >= htlc.absTimelock THEN {htlc.hash} ELSE {}
                    ]
        /\ ChannelUserBalance' = [ChannelUserBalance EXCEPT ![ChannelID][UserID] = @ + htlc.amount]
        /\ ChannelPendingBalance' = [ChannelPendingBalance EXCEPT ![ChannelID] = @ - htlc.amount]
        /\ LET processedPayments == {payment \in UserPayments[UserID] : payment.state = "NEW" /\ htlc.id = payment.id}
               receivedPayments == {payment \in processedPayments : payment.receiver = UserID}
               sentPayments == {payment \in processedPayments : payment.sender = UserID}
           IN   /\ UserPayments' = [UserPayments EXCEPT ![UserID] = (@ \ processedPayments) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPayments}]
                /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + SumAmounts(receivedPayments) - SumAmounts(sentPayments)]
    /\ UNCHANGED <<Messages, UserLatePreimages, UserPaymentSecretForPreimage, UserPreimageInventory, UserNewPayments>>
    /\ UNCHANGED UnchangedVars
    
(***************************************************************************)
(* Receive the preimage of an HTLC.                                        *)
(***************************************************************************)
ReceiveHTLCPreimage(ChannelID, UserID, OtherUserID) ==
    /\ \E message \in MyFirstChannelMessage(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.sender = NameForUserID[OtherUserID]
        /\ message.type = "HTLCPreimage"
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstChannelMessage(ChannelID, UserID)]
        /\ UserPreimageInventory' = [UserPreimageInventory EXCEPT ![UserID] = @ \cup {message.data.preimage}]
        /\ IF /\ message.data.preimage \notin UserPreimageInventory[UserID]
              /\ \E htlc \in ChannelUserVars[ChannelID][UserID].OutgoingHTLCs :
                /\ htlc.hash = message.data.preimage
                /\ htlc.absTimelock + G < LedgerTime
           THEN UserLatePreimages' = [UserLatePreimages EXCEPT ![UserID] = @ \cup {message.data.preimage}]
           ELSE UNCHANGED UserLatePreimages
        /\ LET fulfilledHTLCs == {htlc \in (ChannelUserVars[ChannelID][UserID].OutgoingHTLCs) : htlc.hash = message.data.preimage}
           IN   /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OtherKnownPreimages = @ \cup {message.data.preimage},
                                   ![ChannelID][UserID].OutgoingHTLCs = (@ \ fulfilledHTLCs) \cup {[htlc EXCEPT !.state = IF @ = "COMMITTED" THEN "FULFILLED" ELSE @, !.fulfilled = TRUE] : htlc \in (fulfilledHTLCs \cap @)} ]
                /\ LET processedPayments == {payment \in UserPayments[UserID] : payment.state = "NEW" /\ \E htlc \in fulfilledHTLCs : htlc.id = payment.id}
                       receivedPayments == {payment \in processedPayments : payment.receiver = UserID}
                       sentPayments == {payment \in processedPayments : payment.sender = UserID}
                   IN   /\ UserPayments' = [UserPayments EXCEPT ![UserID] = (@ \ processedPayments) \cup {[payment EXCEPT !.state = "PROCESSED"] : payment \in processedPayments}]
                        /\ UserChannelBalance' = [UserChannelBalance EXCEPT ![UserID] = @ + SumAmounts(receivedPayments) - SumAmounts(sentPayments)]
    /\ UNCHANGED <<Messages, UserPaymentSecretForPreimage, ChannelUserBalance, ChannelPendingBalance, UserNewPayments>>
    /\ UNCHANGED UnchangedVars
    
(***************************************************************************)
(* Abort a committed HTLC if it cannot be fulfilled.                       *)
(***************************************************************************)
SendHTLCFail(ChannelID, UserID, OtherUserID) ==
    /\ ChannelUserState[ChannelID][UserID] \in {"rev-keys-exchanged", "closing-time-set"}
    /\ \E htlc \in {htlc \in ChannelUserVars[ChannelID][UserID].IncomingHTLCs : htlc.state = "COMMITTED"} :
        /\ htlc.hash \notin ChannelUserVars[ChannelID][UserID].OtherKnownPreimages
        /\ htlc.hash \notin UserPreimageInventory[UserID]
        /\ LedgerTime >= htlc.absTimelock
        /\ SendChannelMessageM(ChannelMessages[ChannelID], [EmptyMessage EXCEPT !.recipient = NameForUserID[OtherUserID],
                                           !.type = "FailHTLC",
                                           !.data.id = htlc.id], ChannelMessages, ChannelID, NameForUserID[UserID], ChannelUserState[ChannelID][OtherUserID])
        /\ ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].IncomingHTLCs = (@ \ {htlc}) \cup {[htlc EXCEPT !.state = "OFF-TIMEDOUT", !.timedout = TRUE]} ]
    /\ UNCHANGED <<Messages, UserLatePreimages, UserPaymentSecretForPreimage, UserPreimageInventory, ChannelUserBalance, ChannelPendingBalance, UserNewPayments, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars
    
(***************************************************************************)
(* Receive the other user's request to abort an HTLC.                      *)
(***************************************************************************)
ReceiveHTLCFail(ChannelID, UserID, OtherUserID) ==
    /\ \E message \in MyFirstChannelMessage(ChannelID, UserID) :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "FailHTLC"
        /\ ChannelMessages' = [ChannelMessages EXCEPT ![ChannelID] = RemoveMyFirstChannelMessage(ChannelID, UserID)]
        /\ LET failedHTLCs == {htlc \in (ChannelUserVars[ChannelID][UserID].OutgoingHTLCs) : htlc.id = message.data.id /\ htlc.absTimelock <= LedgerTime} 
           IN ChannelUserVars' = [ChannelUserVars EXCEPT ![ChannelID][UserID].OutgoingHTLCs = (@ \ failedHTLCs) \cup {[htlc EXCEPT !.state = IF @ = "COMMITTED" THEN "OFF-TIMEDOUT" ELSE @, !.timedout = TRUE] : htlc \in (failedHTLCs \cap @)} ]
    /\ UNCHANGED <<Messages, UserLatePreimages, UserPaymentSecretForPreimage, UserPreimageInventory, ChannelUserBalance, ChannelPendingBalance, UserNewPayments, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars
    
(***************************************************************************)
(* Ignore a request for an invoice.                                        *)
(*                                                                         *)
(* This is required for liveness.                                          *)
(***************************************************************************)
IgnoreInvoiceRequest(ChannelID, UserID, OtherUserID) ==
    /\ FORCE_LONG_SIMULATION => TLCGet("level") > SIMULATION_MIN_LENGTH
    /\ \E message \in Messages :
        /\ message.recipient = NameForUserID[UserID]
        /\ message.type = "RequestInvoice"
        /\ Messages' = Messages \ {message}
    /\ UNCHANGED <<ChannelMessages, UserLatePreimages, UserPaymentSecretForPreimage, ChannelUserVars, ChannelUserBalance, ChannelPendingBalance, UserPreimageInventory, UserNewPayments, UserPayments, UserChannelBalance>>
    /\ UNCHANGED UnchangedVars

Next(ChannelID, UserID, OtherUserID) ==
    \/ RequestInvoice(UserID)
    \/ GenerateAndSendPaymentHash(UserID)
    \/ ReceivePaymentHash(UserID)
    \/ AddAndSendOutgoingHTLC(ChannelID, UserID, OtherUserID)
    \/ ReceiveUpdateAddHTLC(ChannelID, UserID, OtherUserID)
    \/ SendHTLCPreimage(ChannelID, UserID, OtherUserID)
    \/ ReceiveHTLCPreimage(ChannelID, UserID, OtherUserID)
    \/ SendHTLCFail(ChannelID, UserID, OtherUserID)
    \/ ReceiveHTLCFail(ChannelID, UserID, OtherUserID)
    \/ IgnoreInvoiceRequest(ChannelID, UserID, OtherUserID)

(***************************************************************************)
(* Fairness requires all users to receive messages.  Honest users are      *)
(* required to send messages if the protocol expects them to send a        *)
(* message.                                                                *)
(***************************************************************************)
NextFair(ChannelID, UserID, OtherUserID) ==
    \/ UserHonest[UserID] /\ RequestInvoice(UserID)
    \/ UserHonest[UserID] /\ GenerateAndSendPaymentHash(UserID)
    \/ ReceivePaymentHash(UserID)
    \/ ReceiveUpdateAddHTLC(ChannelID, UserID, OtherUserID)
    \/ UserHonest[UserID] /\ SendHTLCPreimage(ChannelID, UserID, OtherUserID)
    \/ ReceiveHTLCPreimage(ChannelID, UserID, OtherUserID)
    \/ UserHonest[UserID] /\ SendHTLCFail(ChannelID, UserID, OtherUserID)
    \/ ReceiveHTLCFail(ChannelID, UserID, OtherUserID)
    \/ IgnoreInvoiceRequest(ChannelID, UserID, OtherUserID)
    
=============================================================================
