---- MODULE MC ----
EXTENDS Example1, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT definitions V
const_1643852442693483000 == 
{v1}
----

\* CONSTANT definitions @modelParameterConstants:0C
const_1643852442693484000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1N
const_1643852442693485000 == 
3
----

\* Constant expression definition @modelExpressionEval
const_expr_1643852442693486000 == 
RingNetworkPlusOneEdge
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1643852442693486000>>)
----

=============================================================================
\* Modification History
\* Created Wed Feb 02 17:40:42 PST 2022 by nano
