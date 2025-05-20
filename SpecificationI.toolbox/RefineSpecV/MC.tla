---- MODULE MC ----
EXTENDS SpecificationI, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738616885722416000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738616885722417000 == 
<<
    {
    	[id |-> 1, amount |-> 5, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 10]
    },
    {
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {
    },
    {
    	[id |-> 4, amount |-> 4, path |-> <<[name |-> "UserD"], [name |-> "UserC"], [name |-> "UserB"], [name |-> "UserA"]>>, absTimelock |-> 20]
    },
    {
    },
    {
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1738616885722418000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738616885722419000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738616885722420000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738616885722421000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738616885722422000 == 
<<10, 10, 10, 20, 10, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738616885723423000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1738616885723424000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1738616885723425000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1738616885723426000 ==
IdealUser(3)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_1738616885723427000 ==
IdealUser(4)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:5
prop_1738616885723428000 ==
IdealUser(5)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:6
prop_1738616885723429000 ==
IdealUser(6)!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 22:08:05 CET 2025 by matthias
