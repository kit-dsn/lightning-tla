---- MODULE MC ----
EXTENDS SpecificationIIatoIIIa, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1744315620689635000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1744315620689636000 == 
<<
    {},
    {},
    {[id |-> 7, amount |-> 4, path |-> <<[name |-> "UserC"], [name |-> "UserA"], [name |-> "UserB"], [name |-> "UserD"]>>, absTimelock |-> 11]},
    {},
    {}
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1744315620689637000 == 
25
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1744315620689638000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"]>>
----

\* CONSTANT definitions @modelParameterConstants:8NullUser
const_1744315620689639000 == 
[name |-> "None"]
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1744315620689640000 == 
<<"UserARev", "UserBRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1744315620689641000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1744315620689642000 == 
<<10, 0>>
----

\* CONSTANT definitions @modelParameterConstants:12STRICT_WITHDRAW
const_1744315620689643000 == 
TRUE
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1744315620690644000 ==
SpecificationIIIa!SpecIIIa
----
=============================================================================
\* Modification History
\* Created Thu Apr 10 22:07:00 CEST 2025 by matthias
