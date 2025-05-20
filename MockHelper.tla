----------------------------- MODULE MockHelper -----------------------------

EXTENDS Integers, Sequences

RECURSIVE RemoveMessagesInOtherChannelsHelper(_, _, _, _)
RemoveMessagesInOtherChannelsHelper(msgs, MyName, OtherName, PaymentReceivers) ==
    IF Len(msgs) = 0 THEN <<>> ELSE
    IF  \/  /\ Head(msgs).sender \in PaymentReceivers \/ Head(msgs).recipient \in PaymentReceivers
            /\ MyName \in {Head(msgs).sender, Head(msgs).recipient}
    THEN <<Head(msgs)>> \o RemoveMessagesInOtherChannelsHelper(Tail(msgs), MyName, OtherName, PaymentReceivers)
    ELSE RemoveMessagesInOtherChannelsHelper(Tail(msgs), MyName, OtherName, PaymentReceivers)
RemoveMessagesInOtherChannels(Messages, MyName, OtherName, OtherNames, NewPayments, OtherNewPayments) ==
    LET PaymentReceivers == {name \in OtherNames : \E payment \in NewPayments :
                                    /\ "path" \in DOMAIN payment
                                    /\ payment.path[2] = OtherName
                                    /\ payment.path[Len(payment.path)] = name
                            }
        PaymentSenders == {name \in OtherNames : \E payment \in OtherNewPayments :
                                    /\ "path" \in DOMAIN payment
                                    /\ payment.path[Len(payment.path) - 1] = OtherName
                                    /\ payment.path[Len(payment.path)] = MyName
                           }
    IN RemoveMessagesInOtherChannelsHelper(Messages, MyName, OtherName, PaymentReceivers \cup PaymentSenders)
    
RelevantPreimages(Vars, PaymentSecretForPreimage) ==
    (DOMAIN PaymentSecretForPreimage) \cup {htlc.hash : htlc \in Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs}
    
MockPaymentSecretForPreimage(PaymentSecretForPreimage, relevantPreimages) ==
    [x \in relevantPreimages |-> PaymentSecretForPreimage[x]]
        
MockedNewPayments(OtherUser, NewPayments, IncomingHTLCs, MyName) ==
    LET relevantPayments == {pmt \in NewPayments :  \/ pmt.nextHop = OtherUser
                                                    \/ \E htlc \in IncomingHTLCs : htlc.hash = pmt.hash
                                                    \/ "path" \in DOMAIN pmt /\ pmt.path[1] = MyName}
    IN  relevantPayments
    
MockedRequestedInvoices(initialBalance, myOtherChannelStates, OtherUsersInitialPayments, OtherUsersNewPayments, User, OtherUser, AllInitialPayments, UserNewPayments, NameForUserID) ==
    (IF /\ \E state \in myOtherChannelStates : state \notin {"init", "open-sent-open-channel", "open-funding-created", "open-sent-commit-funder", "open-recv-commit"}
        /\ initialBalance > 0
     THEN {[type |-> "BalanceInOtherChannel", amount |-> initialBalance]} \* should be one per channel
     ELSE {}
    ) \cup
        {payment : payment \in {payment \in OtherUsersInitialPayments : \E pmt \in OtherUsersNewPayments :
                /\ payment.id = pmt.id
                /\ payment.amount = pmt.amount
\*                /\ "path" \in DOMAIN pmt /\ payment.path = pmt.path
                /\ payment.path[Len(payment.path)] = User
                /\ pmt.invoiceRequested}
        }
        \cup
        { payment \in AllInitialPayments :
            /\ payment.path[1] # OtherUser
            /\ payment.path[Len(payment.path)] = User
            /\ ~\E uid \in DOMAIN UserNewPayments :
                /\ payment.path[1] = NameForUserID[uid]
                /\ \E pmt \in UserNewPayments[uid] : pmt.id = payment.id
        } 

(*
    A MultiHopMock mocks the whole enviornment of one channel for one particular user and channel.
*)

=============================================================================
\* Modification History
\* Last modified Thu Apr 10 21:41:27 CEST 2025 by matthias
\* Created Mon Apr 29 16:29:30 CEST 2024 by matthias
