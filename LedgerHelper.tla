---------------------------- MODULE LedgerHelper ----------------------------

EXTENDS Naturals, FiniteSets, TLC, SumAmounts

CONSTANTS
    SingleSignature,
    AllSignatures,
    SingleSigHashLock,
    AllSigHashLock,
    Hashes,
    Time,
    Preimages,
    Keys,
    OptimizedTxAge,
    TO_SELF_DELAY
    
ConditionData == [keys: SUBSET Keys] \cup [keys: SUBSET Keys, hash: Hashes]
Conditions == [type: {SingleSignature, AllSignatures, SingleSigHashLock, AllSigHashLock},
               data: ConditionData,
               absTimelock: Time, \* absolute timelock is implemented in Bitcoin as "OP_CHECKLOCKTIMEVERIFY" (BIP 65)
               relTimelock: Time] \* relative timelock is implemented in Bitcoin as "OP_CHECKSEQUENCEVERIFY" (BIP 112)
Signatures == SUBSET Keys
Witnesses == [signatures: Signatures] \cup [signatures: Signatures, preimage: Preimages]

SingleSignatureCondition(key) == [type |-> SingleSignature,
                                  data |-> [keys |-> {key}],
                                  absTimelock |-> 0,
                                  relTimelock |-> 0]
AllSignaturesCondition(keys) == [type |-> AllSignatures,
                                 data |-> [keys |-> keys],
                                 absTimelock |-> 0,
                                 relTimelock |-> 0]
SingleSigHashLockCondition(key, hash) == [type |-> SingleSigHashLock,
                                          data |-> [keys |-> {key},
                                                    hash |-> hash],
                                          absTimelock |-> 0,
                                          relTimelock |-> 0]
AllSigHashLockCondition(keys, hash) ==
    [type |-> AllSigHashLock,
     data |-> [keys |-> keys,
               hash |-> hash],
     absTimelock |-> 0,
     relTimelock |-> 0]
     
TransactionContainsRelativeTimelock(tx) ==
    \E output \in tx.outputs :
        \E condition \in output.conditions :
            condition.relTimelock > 0

PublishedAtForTx(tx, ledgerTime) ==
    1

PublishableTxForTxAndTime(tx, ledgerTime) ==
    [   id |-> tx.id,
        inputs |-> tx.inputs,
        outputs |-> tx.outputs,
        absTimelock |-> tx.absTimelock,
        publishedAt |-> PublishedAtForTx(tx, ledgerTime)
    ]
PublishableTxsForTxsAndTime(txs, ledgerTime) ==
    {PublishableTxForTxAndTime(tx, ledgerTime) : tx \in txs}

SignTransaction(transaction, key) ==
    LET signedInputs == {[input EXCEPT !.witness.signatures = @ \cup {key}] : input \in transaction.inputs}
    IN  [transaction EXCEPT !.inputs = signedInputs]
    
WitnessMatchesConditions(witness, inputRelTimelock, conditions, txAbsTimelock) ==
    /\ conditions \in SUBSET Conditions
    /\ witness \in Witnesses
    /\ \E condition \in conditions : \* one condition needs to be fulfilled by the signature
        /\ condition.type \in {SingleSignature, SingleSigHashLock} =>
            (\E key \in condition.data.keys : key \in witness.signatures)
        /\ condition.type \in {AllSignatures, AllSigHashLock} =>
            (\A key \in condition.data.keys : key \in witness.signatures)
        /\ condition.type \in {SingleSigHashLock, AllSigHashLock} =>
            /\ "preimage" \in DOMAIN witness
            /\ condition.data.hash = witness.preimage
        /\ condition.absTimelock > 0 => txAbsTimelock >= condition.absTimelock
        /\ condition.relTimelock > 0 => inputRelTimelock >= condition.relTimelock

HashesInCommitTransaction(tx) ==
    {condition.data.hash :
        condition \in { condition \in UNION {output.conditions : output \in tx.outputs} : condition.type \in {AllSigHashLock, SingleSigHashLock} }
    }
     
=============================================================================
