---- MODULE MC ----
EXTENDS SpecificationIIatoIIIa, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_174409625980222000 == 
{2}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_174409625980323000 == 
<<
    {
    },
    {
        [id |-> 1, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 19],
        [id |-> 2, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16],
        [id |-> 3, amount |-> 4, path |-> <<[name |-> "UserB"], [name |-> "UserC"]>>, absTimelock |-> 16]
    },
    {
    	[id |-> 4, amount |-> 5, path |-> <<[name |-> "UserC"], [name |-> "UserB"]>>, absTimelock |-> 16]
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
const_174409625980324000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_174409625980325000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:8NullUser
const_174409625980326000 == 
[name |-> "None"]
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_174409625980327000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_174409625980328000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_174409625980329000 == 
<<0, 10, 0, 0, 0, 0>>
----

\* CONSTANT definitions @modelParameterConstants:12STRICT_WITHDRAW
const_174409625980330000 == 
TRUE
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174409625980331000 ==
SpecificationIIIa!SpecIIIa
----
=============================================================================
\* Modification History
\* Created Tue Apr 08 09:10:59 CEST 2025 by matthias
