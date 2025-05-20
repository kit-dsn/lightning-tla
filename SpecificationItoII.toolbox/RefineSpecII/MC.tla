---- MODULE MC ----
EXTENDS SpecificationItoII, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_174412440859068000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_174412440859069000 == 
<<
    {
    	[id |-> 1, amount |-> 5, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"], [name |-> "UserD"]>>, absTimelock |-> 36]
    },
    {
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {
    	[id |-> 3, amount |-> 2, path |-> <<[name |-> "UserC"], [name |-> "UserD"]>>, absTimelock |-> 26]
    },
    {
    },
    {
    },
    {
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_174412440859070000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_174412440859071000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_174412440859072000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_174412440859073000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_174412440859074000 == 
<<0, 10, 10, 0, 0, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174412440859175000 ==
SpecificationII!SpecII
----
=============================================================================
\* Modification History
\* Created Tue Apr 08 17:00:08 CEST 2025 by matthias
