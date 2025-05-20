---- MODULE MC ----
EXTENDS SpecificationIIatoIIIa, TLC

\* CONSTANT definitions @modelParameterConstants:0ActiveChannels
const_174409986335834000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2UserInitialPayments
const_174409986335835000 == 
<<
    {[id |-> 3, amount |-> 5, path |-> <<[name |-> "UserA"], [name |-> "UserB"]>>, absTimelock |-> 9, incomingCommitted |-> TRUE, invoiceRequested |-> FALSE]},
    {[id |-> 4, amount |-> 3, path |-> <<[name |-> "UserB"], [name |-> "UserA"], [name |-> "UserC"]>>, absTimelock |-> 16, incomingCommitted |-> TRUE, invoiceRequested |-> FALSE]},
    {},
    {},
    {}
>>
----

\* CONSTANT definitions @modelParameterConstants:3MAX_TIME
const_174409986335836000 == 
25
----

\* CONSTANT definitions @modelParameterConstants:7NameForUserID
const_174409986335837000 == 
<<[name |-> "UserA"],
[name |-> "UserB"],
[name |-> "UserC"],
[name |-> "UserD"],
[name |-> "UserE"]>>
----

\* CONSTANT definitions @modelParameterConstants:8NullUser
const_174409986335838000 == 
[name |-> "None"]
----

\* CONSTANT definitions @modelParameterConstants:9RevKeyForUserID
const_174409986335839000 == 
<<"UserARev", "UserBRev">>
----

\* CONSTANT definitions @modelParameterConstants:10OptimizedTxAge
const_174409986335840000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:11UserInitialBalance
const_174409986335841000 == 
<<10, 0>>
----

\* CONSTANT definitions @modelParameterConstants:12STRICT_WITHDRAW
const_174409986335842000 == 
TRUE
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174409986335943000 ==
SpecificationIIIa!SpecIIIa
----
=============================================================================
\* Modification History
\* Created Tue Apr 08 10:11:03 CEST 2025 by matthias
