---- MODULE MC ----
EXTENDS SpecificationIIatoIIIa, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_174542016109612000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_174542016109613000 == 
<<
    {[id |-> 3, amount |-> 3, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16, incomingCommitted |-> TRUE, invoiceRequested |-> FALSE]},
    {},
    {},
    {},
    {}
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_174542016109614000 == 
25
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_174542016109615000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"]>>
----

\* CONSTANT definitions @modelParameterConstants:8NullUser
const_174542016109616000 == 
[name |-> "None"]
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_174542016109617000 == 
<<"UserARev", "UserBRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_174542016109618000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_174542016109619000 == 
<<10, 0>>
----

\* CONSTANT definitions @modelParameterConstants:12STRICT_WITHDRAW
const_174542016109620000 == 
TRUE
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174542016109721000 ==
SpecificationIIIa!SpecIIIa
----
=============================================================================
\* Modification History
\* Created Wed Apr 23 16:56:01 CEST 2025 by matthias
