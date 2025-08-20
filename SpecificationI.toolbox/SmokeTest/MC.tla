---- MODULE MC ----
EXTENDS SpecificationI, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_175569713012294000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_175569713012395000 == 
<<
    {
    },
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
const_175569713012396000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_175569713012397000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_175569713012398000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_175569713012399000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1755697130123100000 == 
<<0, 0, 0, 0, 0, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1755697130123101000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1755697130123102000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1755697130123103000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1755697130123104000 ==
IdealUser(3)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_1755697130123105000 ==
IdealUser(4)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:5
prop_1755697130123106000 ==
IdealUser(5)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:6
prop_1755697130123107000 ==
IdealUser(6)!Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 20 15:38:50 CEST 2025 by matthias
