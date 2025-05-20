---- MODULE MC ----
EXTENDS SpecificationIV, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_174481923198913000 == 
{1, 2}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_174481923198914000 == 
<<
    {
	    [id |-> 1, amount |-> 3, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 15]
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
const_174481923198915000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_174481923198916000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_174481923198917000 == 
<<"UserARev", "UserBRev", "UserCRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_174481923198918000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_174481923198919000 == 
<<10, 10, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174481923199020000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_174481923199021000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_174481923199022000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_174481923199023000 ==
IdealUser(3)!Spec
----
=============================================================================
\* Modification History
\* Created Wed Apr 16 18:00:31 CEST 2025 by matthias
