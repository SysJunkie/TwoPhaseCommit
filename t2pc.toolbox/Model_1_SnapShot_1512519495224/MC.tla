---- MODULE MC ----
EXTENDS t2pc, TLC

\* CONSTANT definitions @modelParameterConstants:0ENABLEBTM
const_151251949116072000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:1RMMAYFAIL
const_151251949116073000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:2TMMAYFAIL
const_151251949116074000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:3RM
const_151251949116075000 == 
{1,2,3,4}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_151251949116076000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_151251949116077000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_151251949116078000 ==
Consistent
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_151251949116079000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Tue Dec 05 19:18:11 EST 2017 by varunjai
