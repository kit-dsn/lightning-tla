----------------------------- MODULE PCUHelper -----------------------------

EXTENDS Integers, FiniteSets,
            TLC,
            Sequences
 
SeqToSet(seq) ==
  { seq[i] : i \in DOMAIN seq }
    
RECURSIVE MyMessagesHelper(_, _)
MyMessagesHelper(msgs, myName) ==
    IF Len(msgs) = 0 THEN {} ELSE  
    IF Head(msgs).recipient # myName THEN MyMessagesHelper(Tail(msgs), myName) ELSE 
    {Head(msgs)}
    
RECURSIVE RemoveMyFirstMessageHelper(_, _)
RemoveMyFirstMessageHelper(msgs, myName) ==
    IF Head(msgs).recipient = myName THEN Tail(msgs) ELSE
    <<Head(msgs)>> \o RemoveMyFirstMessageHelper(Tail(msgs), myName)

    
SendMessage(messages, message, messagesVar, myName, otherState) ==
    /\ messagesVar' = Append(messages, [message EXCEPT !.sender = myName])
    /\ otherState # "closed"
                    
HTLCsByStates(states, vars) == {htlc \in (vars.IncomingHTLCs \cup vars.OutgoingHTLCs) : htlc.state \in states}
IncHTLCsByStates(states, vars) == {htlc \in vars.IncomingHTLCs : htlc.state \in states}
OutHTLCsByStates(states, vars) == {htlc \in vars.OutgoingHTLCs : htlc.state \in states}

TransactionSpendsFundingOutput(tx, detailVars) ==
    \E input \in tx.inputs :
        input.parentId = detailVars.fundingTxId

MaxNum(set) ==
    CHOOSE x \in set : \A y \in set : y <= x
    
UpdateRKeyInConditions(conditions, oldRKey, newRKey) ==
    {IF oldRKey \in condition.data.keys
     THEN [condition EXCEPT !.data.keys = (@ \ {oldRKey}) \cup {newRKey}]
     ELSE condition
     : condition \in conditions}
     
\* from https://github.com/tlaplus/Examples/blob/master/specifications/lamport_mutex/Functions.tla
Injection(S,T) == { M \in [S -> T] : \A a,b \in S : M[a] = M[b] => a = b }
Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }
Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)

Subset1(set) == {{x} : x \in set}
MyWitnesses(inventory, preimageInventory) == [signatures: SUBSET inventory.keys] \cup [signatures: SUBSET inventory.keys, preimage: preimageInventory]
\* Only select witnesses that might match the given conditions
MyReducedWitnesses(selection, inventory, preimageInventory) == [signatures: SUBSET (inventory.keys \cap selection)] \cup [signatures: SUBSET (inventory.keys \cap selection), preimage: preimageInventory]


=============================================================================
