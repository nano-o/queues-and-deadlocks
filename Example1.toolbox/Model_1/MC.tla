---- MODULE MC ----
EXTENDS Example1, TLC

\* CONSTANT definitions @modelParameterConstants:0C
const_1643854324220514000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1N
const_1643854324220515000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_1643854324220516000 == 
RingNetworkPlusOneEdge
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1643854324220516000>>)
----

=============================================================================
\* Modification History
\* Created Wed Feb 02 18:12:04 PST 2022 by nano
