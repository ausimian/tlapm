---- MODULE box_closure_definition_test ----
(* A defined operator applied to formulas closed under [] is closed when   *)
(* its body is, with the arguments substituted, whether or not the        *)
(* definition is hidden.                                                   *)
EXTENDS Naturals, TLAPS

VARIABLES p, q

Id(P) == P
And2(A, B) == A /\ B
Id2(P) == Id(P)
NotNot(b) == ~~b
Q == []p

THEOREM Identity == ASSUME Id([]p) PROVE [](Id([]p))
<1> HIDE DEF Id
<1> QED BY PTL

THEOREM Conjunction == ASSUME And2([]p, []q) PROVE [](And2([]p, []q))
<1> HIDE DEF And2
<1> QED BY PTL

THEOREM Nested == ASSUME Id2([]p) PROVE [](Id2([]p))
<1> HIDE DEF Id2, Id
<1> QED BY PTL

THEOREM DoubleNegation == ASSUME NotNot([]p) PROVE [](NotNot([]p))
<1> HIDE DEF NotNot
<1> QED BY PTL

THEOREM NoArguments == ASSUME Q PROVE []Q
<1> HIDE DEF Q
<1> QED BY PTL
====
