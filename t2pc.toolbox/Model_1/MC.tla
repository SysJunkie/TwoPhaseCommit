---- MODULE MC ----
EXTENDS t2pc, TLC

\* CONSTANT definitions @modelParameterConstants:0ENABLEBTM
const_151251950604188000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:1RMMAYFAIL
const_151251950604189000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:2TMMAYFAIL
const_151251950604190000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:3RM
const_151251950604191000 == 
{1,2,3,4}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_151251950604192000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_151251950604193000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_151251950604194000 ==
Consistent
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_151251950604195000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Tue Dec 05 19:18:26 EST 2017 by varunjai
