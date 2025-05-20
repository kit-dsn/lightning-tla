---- MODULE MC ----
EXTENDS SpecificationIII, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738617517761644000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738617517761645000 == 
<<
    {
    	[id |-> 1, amount |-> 2, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"], [name |-> "UserD"]>>, absTimelock |-> 26]
    },
    {
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {
    },
    {
    	[id |-> 3, amount |-> 3, path |-> <<[name |-> "UserD"], [name |-> "UserC"], [name |-> "UserB"], [name |-> "UserA"]>>, absTimelock |-> 36]
    },
    {
    },
    {
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1738617517761646000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738617517761647000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738617517761648000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738617517761649000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738617517761650000 == 
<<10, 10, 10, 10, 10, 10>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738617517761651000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1738617517761652000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1738617517761653000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1738617517761654000 ==
IdealUser(3)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_1738617517761655000 ==
IdealUser(4)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:5
prop_1738617517761656000 ==
IdealUser(5)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:6
prop_1738617517761657000 ==
IdealUser(6)!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 22:18:37 CET 2025 by matthias
