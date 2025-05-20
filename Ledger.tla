------------------------------- MODULE Ledger -------------------------------

EXTENDS LedgerHelper, Naturals, FiniteSets, TLC

CONSTANTS Users,
          Amounts,
          IDs

VARIABLES LedgerTx,
          LedgerTime,
          TxAge
          
Subset2(set) == {subset \in SUBSET set : Cardinality(subset) <= 2}
Subset(set, n) == {subset \in SUBSET set : Cardinality(subset) <= n}


TransactionInputs == [
    parentId: IDs,
    outputId: IDs,
    witness: Witnesses,
    relTimelock: Time  \* relative timelock is implemented in Bitcoin as "sequence number" (BIP 68)
]
TransactionOutputs == [
    parentId: IDs,
    outputId: IDs,
    amount: Amounts,
    conditions: Subset(Conditions, 3)
]
Transactions == [
    id: IDs,
    absTimelock: Time,   \* absolute timelock is implemented in Bitcoin as "nLockTime"
    inputs: Subset(TransactionInputs, 6),
    outputs: Subset(TransactionOutputs, 6)
]
PublishedTransactions == [
    id: IDs,
    absTimelock: Time,   \* absolute timelock is implemented in Bitcoin as "nLockTime"
    inputs: Subset(TransactionInputs, 6),
    outputs: Subset(TransactionOutputs, 6),
    publishedAt: {0,1}
]

TypeOK == /\ LedgerTx \subseteq PublishedTransactions
          /\ \A tx \in LedgerTx : (\A output \in tx.outputs : output.parentId = tx.id)
          /\ LedgerTime \in Time

LedgerTxIds == {tx.id : tx \in LedgerTx}

LedgerInputs(ledger) == UNION {tx.inputs : tx \in ledger}
LedgerOutputs(ledger) == UNION {tx.outputs : tx \in ledger}
LedgerOutputsWithParent(ledger) ==
    UNION { { [output |-> output, parent |-> tx] : output \in tx.outputs} : tx \in ledger }

ConfirmedParentTx(tx, ledger) == { parent \in ledger :
                             (\E input \in tx.inputs : input.parentId = parent.id)}
OutputsSpentByInputs(inputs, ledger) ==
    { output \in LedgerOutputs(ledger) :
        (\E input \in inputs :
            input.outputId = output.outputId /\ output.parentId = input.parentId) }

UnspentLedgerOutputs(ledger) ==
    {output \in LedgerOutputs(ledger) :
        (~\E input \in LedgerInputs(ledger) :
            /\ input.parentId = output.parentId
            /\ input.outputId = output.outputId)}
UnspentLedgerOutputsWithParent(ledger) ==
    {outputWithParent \in LedgerOutputsWithParent(ledger) :
        (~\E input \in LedgerInputs(ledger) :
            /\ input.parentId = outputWithParent.output.parentId
            /\ input.outputId = outputWithParent.output.outputId)}

AmountSpentByInputs(inputs, ledger) ==
    SumAmounts(OutputsSpentByInputs(inputs, ledger))
    
TxValid(tx, ledger, txAge) ==
    /\ \A output \in tx.outputs : output.parentId = tx.id
    /\ \A parent \in ConfirmedParentTx(tx, ledger) :
        /\ \A txInput \in tx.inputs : txInput.parentId = parent.id =>
            \A parentOutput \in parent.outputs :
                parentOutput.outputId = txInput.outputId =>
                    /\ WitnessMatchesConditions(txInput.witness,
                                                txInput.relTimelock,
                                                parentOutput.conditions,
                                                tx.absTimelock)
                    /\ IF parent.id \in DOMAIN txAge
                       THEN txAge[parent.id] >= txInput.relTimelock   \* see BIP 68
                       ELSE 0 = txInput.relTimelock
        /\ \A parentOutput \in parent.outputs :
            \* There is at most one child that is not the parent itself
            Cardinality(
                {spendingTx \in ledger :
                    \E input \in spendingTx.inputs :
                        /\ input.parentId = parent.id
                        /\ input.outputId = parentOutput.outputId
                } \ {parent}
            ) <= 1
    /\ \A input \in tx.inputs :
        \* circular transactions are only accepted at time 0 (in initial state)
        /\ tx.publishedAt > 0 => input.parentId # tx.id 
        /\ \E parent \in ConfirmedParentTx(tx, ledger) :
            \E parentOutput \in parent.outputs :
                /\ parentOutput.outputId = input.outputId
                /\ parent.id = input.parentId \* all referenced parents exist
    \* the transaction's outputs do not spend more than the inputs:
    /\ SumAmounts(tx.outputs) <= AmountSpentByInputs(tx.inputs, ledger)
    /\ AmountSpentByInputs(tx.inputs, ledger) > 0
    
NLockTimeCheck(tx, ledgerTime) ==
    ledgerTime >= tx.absTimelock

PublishableTxForTx(tx) == PublishableTxForTxAndTime(tx, LedgerTime)
PublishableTxsForTxs(txs) == PublishableTxsForTxsAndTime(txs, LedgerTime)

PublishTx(tx) ==
    /\ tx.id \notin LedgerTxIds
    /\ LET publishedTx == PublishableTxForTx(tx)
       IN /\ LedgerTx' = LedgerTx \cup {publishedTx}
          /\ TxAge' = TxAge @@ tx.id :> IF ~OptimizedTxAge \/ TransactionContainsRelativeTimelock(tx)
                                        THEN 0
                                        ELSE TO_SELF_DELAY
          /\ TxValid(publishedTx, LedgerTx', TxAge)
          /\ NLockTimeCheck(publishedTx, LedgerTime)


PublishTxs(txs) ==
    /\ \A tx \in txs : tx.id \notin LedgerTxIds
    /\ LET publishedTxs == PublishableTxsForTxs(txs)
       IN /\ LedgerTx' = LedgerTx \cup publishedTxs
          /\ TxAge' = TxAge @@ [id \in {tx.id : tx \in txs} |->
                                        IF ~OptimizedTxAge \/ TransactionContainsRelativeTimelock(CHOOSE tx \in LedgerTx : tx.id = id)
                                        THEN 0
                                        ELSE TO_SELF_DELAY]
          /\ \A publishedTx \in publishedTxs : TxValid(publishedTx, LedgerTx', TxAge') /\ NLockTimeCheck(publishedTx, LedgerTime)

OnChainOutputSpendableByUser(ledger, inventory, preimageInventory, time, relTimelock) ==
    {outputWithParent \in UnspentLedgerOutputsWithParent(ledger) :
        \/  \E preimage \in preimageInventory :
                LET witness == [signatures |-> inventory.keys, preimage |-> preimage]
                IN WitnessMatchesConditions(witness,
                                            relTimelock,
                                            outputWithParent.output.conditions,
                                            time + relTimelock)
        \/  /\ Cardinality(preimageInventory) = 0
            /\ LET witness == [signatures |-> inventory.keys]
               IN WitnessMatchesConditions(witness,
                                           relTimelock,
                                           outputWithParent.output.conditions,
                                           time + relTimelock)
    }
     
=============================================================================
