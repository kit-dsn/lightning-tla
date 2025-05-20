---- MODULE MC ----
EXTENDS SpecificationII, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738617312015598000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738617312015599000 == 
<<
    {
    	[id |-> 1, amount |-> 2, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"], [name |-> "UserD"]>>, absTimelock |-> 26]
    },
    {
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {},
    {
    	[id |-> 3, amount |-> 2, path |-> <<[name |-> "UserD"], [name |-> "UserC"], [name |-> "UserB"], [name |-> "UserA"]>>, absTimelock |-> 29]
    },
    {},
    {
    	[id |-> 4, amount |-> 4, path |-> <<[name |-> "UserF"], [name |-> "UserE"], [name |-> "UserD"], [name |-> "UserC"], [name |-> "UserB"], [name |-> "UserA"]>>, absTimelock |-> 43]
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1738617312015600000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738617312015601000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738617312015602000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738617312015603000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738617312015604000 == 
<<10, 10, 10, 10, 20, 10>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738617312016605000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1738617312016606000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1738617312016607000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1738617312016608000 ==
IdealUser(3)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_1738617312016609000 ==
IdealUser(4)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:5
prop_1738617312016610000 ==
IdealUser(5)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:6
prop_1738617312016611000 ==
IdealUser(6)!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 22:15:12 CET 2025 by matthias
