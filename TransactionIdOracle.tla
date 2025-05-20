------------------------ MODULE TransactionIdOracle ------------------------

EXTENDS Naturals, FiniteSets

VARIABLES UsedTransactionIds,
          AvailableTransactionIds
   
TypeOK == UsedTransactionIds \in SUBSET Nat

GetNewTransactionId(ChannelID) == CHOOSE id \in AvailableTransactionIds[ChannelID] : ~ id \in UsedTransactionIds[ChannelID]

GetNewTransactionIdWithout(disallow, ChannelID) == CHOOSE id \in AvailableTransactionIds[ChannelID] : ~ id \in (disallow \cup UsedTransactionIds[ChannelID])

GetNewTransactionIds(count, disallow, ChannelID) == CHOOSE set \in SUBSET(AvailableTransactionIds[ChannelID] \ (disallow \cup UsedTransactionIds[ChannelID])) : Cardinality(set) = count

MarkMultipleAsUsed(newTransactionIds, ChannelID) ==
    UsedTransactionIds' = [UsedTransactionIds EXCEPT ![ChannelID] = @ \cup newTransactionIds]
MarkAsUsed(newTransactionId, ChannelID) == MarkMultipleAsUsed({newTransactionId}, ChannelID)

=============================================================================
