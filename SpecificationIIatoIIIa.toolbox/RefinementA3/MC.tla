---- MODULE MC ----
EXTENDS SpecificationIIatoIIIa, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_174429783780667000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_174429783780668000 == 
<<
    {
        [id |-> 3, amount |-> 3, path |-> <<[name |-> "UserA"], [name |-> "UserB"]>>, absTimelock |-> 16]
    },
    {}
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_174429783780669000 == 
25
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_174429783780670000 == 
<<[name |-> "UserA"],
[name |-> "UserB"]>>
----

\* CONSTANT definitions @modelParameterConstants:8NullUser
const_174429783780671000 == 
[name |-> "None"]
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_174429783780672000 == 
<<"UserARev", "UserBRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_174429783780673000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_174429783780674000 == 
<<10, 0>>
----

\* CONSTANT definitions @modelParameterConstants:12STRICT_WITHDRAW
const_174429783780675000 == 
TRUE
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174429783780676000 ==
SpecificationIIIa!SpecIIIa
----
=============================================================================
\* Modification History
\* Created Thu Apr 10 17:10:37 CEST 2025 by matthias
