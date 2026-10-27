---- MODULE substitutivity_fairness_unsound_test ----
(* False congruence steps, so none must prove. WF_y(A), SF_y(A),          *)
(* [][A]_y and <><<A>>_y depend on how y changes over time, so a LAMBDA   *)
(* over y that uses one of them is not Leibniz, and Ap(F, a) is not       *)
(* substitutive in a when F is such a LAMBDA.                             *)
EXTENDS Naturals, TLAPS

VARIABLE x

Ap(F(_), a) == F(a)

THEOREM WeakFairness ==
  ASSUME x = 1, Ap(LAMBDA y : WF_y(x' = 0), x)
  PROVE  Ap(LAMBDA y : WF_y(x' = 0), 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

THEOREM StrongFairness ==
  ASSUME x = 1, Ap(LAMBDA y : SF_y(x' = 0), x)
  PROVE  Ap(LAMBDA y : SF_y(x' = 0), 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

THEOREM AngleSubscript ==
  ASSUME x = 1, Ap(LAMBDA y : <><<x' = 0>>_y, x)
  PROVE  Ap(LAMBDA y : <><<x' = 0>>_y, 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

THEOREM SquareSubscript ==
  ASSUME x = 1, Ap(LAMBDA y : [][x' = 0]_y, x)
  PROVE  Ap(LAMBDA y : [][x' = 0]_y, 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS
====
stderr: status:failed
nostderr: status:proved
