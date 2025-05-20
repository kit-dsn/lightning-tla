---- MODULE MC ----
EXTENDS SpecificationIV, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_1738615396706186000 == 
{1, 2}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_1738615396706187000 == 
<<
    {
	    [id |-> 1, amount |-> 3, path |-> <<[name |-> "UserA"], [name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 15],
        [id |-> 2, amount |-> 2, path |-> <<[name |-> "UserA"], [name |-> "UserB"]>>, absTimelock |-> 17]
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
const_1738615396706188000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_1738615396706189000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_1738615396706190000 == 
<<"UserARev", "UserBRev", "UserCRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_1738615396706191000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_1738615396706192000 == 
<<10, 10, 0>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1738615396706193000 ==
IdealPayments!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1738615396706194000 ==
IdealUser(1)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1738615396706195000 ==
IdealUser(2)!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1738615396706196000 ==
IdealUser(3)!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 03 21:43:16 CET 2025 by matthias
