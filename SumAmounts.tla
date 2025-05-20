----------------------------- MODULE SumAmounts -----------------------------

EXTENDS Naturals, Sequences, FiniteSets

\* From https://learntla.com/libraries/sets/
Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == Pick(S)
                              IN SetReduce(Op, S \ {s}, Op(s, value)) 
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)
\* End from https://learntla.com/libraries/sets/
SumAmounts(outputs) == LET _op(a, b) == a.amount + b
                       IN SetReduce(_op, outputs, 0)

SumSeq(seq) ==
    LET SumInt[ i \in 1..Len(seq) ] == IF i = 1 THEN seq[i] ELSE seq[i] + SumInt[i-1]
    IN IF seq = <<>> THEN 0 ELSE SumInt[Len(seq)]
SumSeqAmounts(seq) ==
    LET SumInt[ i \in 1..Len(seq) ] == IF i = 1 THEN seq[i].amount ELSE seq[i].amount + SumInt[i-1]
    IN IF seq = <<>> THEN 0 ELSE SumInt[Len(seq)]

MaxOfSet(set) == CHOOSE x \in set : \A y \in set : y <= x

HTLCsAreEqual(htlc1, htlc2) ==
    htlc1.hash = htlc2.hash /\ htlc1.amount = htlc2.amount /\ htlc1.absTimelock = htlc2.absTimelock

=============================================================================
