---- MODULE MC ----
EXTENDS SpecificationIV, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738616704053363000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738616704053364000 == 
<<
    {[id |-> 1, amount |-> 3, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"], [name |-> "UserD"]>>, absTimelock |-> 40]},
    {
    },
    {
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
const_1738616704053365000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738616704053366000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738616704053367000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738616704053368000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738616704053369000 == 
<<10, 10, 10, 10, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738616704053370000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1738616704053371000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1738616704053372000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1738616704053373000 ==
IdealUser(3)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_1738616704053374000 ==
IdealUser(4)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:5
prop_1738616704053375000 ==
IdealUser(5)!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 22:05:04 CET 2025 by matthias
