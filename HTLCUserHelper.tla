--------------------------- MODULE HTLCUserHelper ---------------------------

EXTENDS Integers, Sequences

\* G is "a grace-period G blocks after HTLC timeout before giving up on an unresponsive peer and dropping to chain" (BOLT 02)
G == 3

RECURSIVE CalculateDataForNextHops(_, _, _, _)
CalculateDataForNextHops(path, paymentSecret, amount, timelock) ==
    IF Len(path) > 1
    THEN
        [   nextHop |-> Head(Tail(path)),
            absTimelock |-> timelock,
            dataForNextHop |-> CalculateDataForNextHops(Tail(path), paymentSecret, amount, timelock - G - 1)  
        ]
    ELSE
        [   paymentSecret |-> paymentSecret,
            amount |-> amount
        ]
    
RECURSIVE TimestampsInDataForNextHop(_, _)
TimestampsInDataForNextHop(dataForNextHop, OtherNames) ==
    IF "dataForNextHop" \in DOMAIN dataForNextHop
    THEN (IF dataForNextHop.nextHop \in OtherNames THEN {dataForNextHop.absTimelock, dataForNextHop.absTimelock + G + 1} ELSE {})
            \cup TimestampsInDataForNextHop(dataForNextHop.dataForNextHop, OtherNames)
    ELSE {}

=============================================================================
