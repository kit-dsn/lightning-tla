---- MODULE MC ----
EXTENDS SpecificationIV, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738618365926772000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738618365926773000 == 
<<
    {
    	[id |-> 1, amount |-> 4, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"], [name |-> "UserD"], [name |-> "UserE"], [name |-> "UserF"]>>, absTimelock |-> 42]
    },
    {
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {
    	[id |-> 3, amount |-> 3, path |-> <<[name |-> "UserC"], [name |-> "UserD"]>>, absTimelock |-> 17],
    	[id |-> 4, amount |-> 3, path |-> <<[name |-> "UserC"], [name |-> "UserE"]>>, absTimelock |-> 18]
    },
    {
    	[id |-> 5, amount |-> 2, path |-> <<[name |-> "UserD"], [name |-> "UserC"], [name |-> "UserB"]>>, absTimelock |-> 19]
    },
    {
    },
    {
    	[id |-> 6, amount |-> 10, path |-> <<[name |-> "UserF"], [name |-> "UserE"], [name |-> "UserD"], [name |-> "UserC"]>>, absTimelock |-> 32]
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_1738618365926774000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738618365926775000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738618365926776000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738618365926777000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738618365926778000 == 
<<10, 10, 10, 20, 30, 40>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738618365927779000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1738618365927780000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1738618365927781000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1738618365927782000 ==
IdealUser(3)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_1738618365927783000 ==
IdealUser(4)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:5
prop_1738618365927784000 ==
IdealUser(5)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:6
prop_1738618365927785000 ==
IdealUser(6)!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 22:32:45 CET 2025 by matthias
