---- MODULE MC ----
EXTENDS SpecificationIIatoIIIa, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1744621671575102000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1744621671575103000 == 
<<
    {[id |-> 1, amount |-> 5, path |-> <<[name |-> "UserA"], [name |-> "UserB"]>>, absTimelock |-> 9, incomingCommitted |-> TRUE, invoiceRequested |-> FALSE],
[id |-> 3, amount |-> 3, path |-> <<[name |-> "UserA"], [name |-> "UserB"]>>, absTimelock |-> 9, incomingCommitted |-> TRUE, invoiceRequested |-> FALSE]},
    {},
    {},
    {},
    {}
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1744621671575104000 == 
25
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1744621671575105000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"]>>
----

\* CONSTANT definitions @modelParameterConstants:8NullUser
const_1744621671575106000 == 
[name |-> "None"]
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1744621671575107000 == 
<<"UserARev", "UserBRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1744621671575108000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1744621671575109000 == 
<<10, 0>>
----

\* CONSTANT definitions @modelParameterConstants:12STRICT_WITHDRAW
const_1744621671575110000 == 
TRUE
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1744621671576111000 ==
SpecificationIIIa!SpecIIIa
----
=============================================================================
\* Modification History
\* Created Mon Apr 14 11:07:51 CEST 2025 by matthias
