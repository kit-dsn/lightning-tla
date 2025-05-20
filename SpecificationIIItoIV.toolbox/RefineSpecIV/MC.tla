---- MODULE MC ----
EXTENDS SpecificationIIItoIV, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738617623574673000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738617623574674000 == 
<<
    {
    	[id |-> 1, amount |-> 4, path |-> <<[name |-> "UserA"], [name |-> "UserB"]>>, absTimelock |-> 6]
    },
    {
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {
    	[id |-> 3, amount |-> 3, path |-> <<[name |-> "UserC"], [name |-> "UserD"], [name |-> "UserE"], [name |-> "UserF"]>>, absTimelock |-> 26]
    },
    {
    	[id |-> 4, amount |-> 3, path |-> <<[name |-> "UserD"], [name |-> "UserE"], [name |-> "UserF"]>>, absTimelock |-> 29]
    },
    {
    },
    {
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1738617623574675000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738617623574676000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738617623574677000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738617623574678000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738617623574679000 == 
<<0, 10, 10, 10, 0, 10>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738617623575680000 ==
SpecificationIV!SpecIV
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 22:20:23 CET 2025 by matthias
