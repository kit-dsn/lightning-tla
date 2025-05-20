---- MODULE MC ----
EXTENDS SpecificationIItoIIa, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_174435544950946000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_174435544950947000 == 
<<
    {
    },
    {
        [id |-> 1, amount |-> 6, path |-> <<[name |-> "UserB"], [name |-> "UserC"], [name |-> "UserD"], [name |-> "UserE"]>>, absTimelock |-> 36]
    },
    {
    },
    {
    	[id |-> 2, amount |-> 4, path |-> <<[name |-> "UserD"], [name |-> "UserC"], [name |-> "UserB"]>>, absTimelock |-> 40]
    },
    {
    },
    {
    }
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_174435544950948000 == 
50
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_174435544950949000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"],
[name |-> "UserF"]>>
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_174435544950950000 == 
<<"UserARev", "UserBRev", "UserCRev", "UserDRev", "UserERev", "UserFRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_174435544950951000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_174435544950952000 == 
<<0, 10, 10, 10, 20, 10>>
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174435544950953000 ==
SpecificationIIa(1)!SpecIIa
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_174435544950954000 ==
SpecificationIIa(2)!SpecIIa
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_174435544950955000 ==
SpecificationIIa(3)!SpecIIa
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_174435544950956000 ==
SpecificationIIa(4)!SpecIIa
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_174435544950957000 ==
SpecificationIIa(5)!SpecIIa
----
=============================================================================
\* Modification History
\* Created Fri Apr 11 09:10:49 CEST 2025 by matthias
