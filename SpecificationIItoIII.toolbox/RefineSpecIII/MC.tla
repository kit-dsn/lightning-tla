---- MODULE MC ----
EXTENDS SpecificationIItoIII, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738617749092705000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738617749093706000 == 
<<
    {
    	[id |-> 1, amount |-> 1, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"], [name |-> "UserD"], [name |-> "UserE"], [name |-> "UserF"]>>, absTimelock |-> 41]
    },
    {
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {
    },
    {
    	[id |-> 3, amount |-> 1, path |-> <<[name |-> "UserD"], [name |-> "UserC"]>>, absTimelock |-> 10]
    },
    {
    },
    {
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1738617749093707000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738617749093708000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:8NullUser
const_1738617749093709000 == 
[name |-> "None"]
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738617749093710000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738617749093711000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738617749093712000 == 
<<0, 10, 10, 0, 0, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738617749093713000 ==
SpecificationIII!SpecIII
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 22:22:29 CET 2025 by matthias
