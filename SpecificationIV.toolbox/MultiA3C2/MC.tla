---- MODULE MC ----
EXTENDS SpecificationIV, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738615435806197000 == 
{1, 2}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738615435806198000 == 
<<
    {
	    [id |-> 1, amount |-> 3, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 15]
    },
    {
    },
    {
    	[id |-> 4, amount |-> 2, path |-> <<[name |-> "UserC"], [name |-> "UserB"], [name |-> "UserA"]>>, absTimelock |-> 17]
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
const_1738615435806199000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738615435806200000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738615435806201000 == 
<<"UserARev", "UserBRev", "UserCRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738615435806202000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738615435806203000 == 
<<10, 10, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738615435806204000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1738615435806205000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1738615435806206000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1738615435806207000 ==
IdealUser(3)!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 21:43:55 CET 2025 by matthias
