---- MODULE box_closure_application_unsound_test ----
(* Every theorem here is false, so none must prove. A formula closed under *)
(* [] stays true once true, but an equality or a defined operator applied  *)
(* to such a formula need not keep its value: with p false initially and  *)
(* true afterwards, ([]p) = FALSE holds only at the start.                 *)
EXTENDS Naturals, TLAPS

VARIABLES p, q

Not(b) == ~b
NotWrap(b) == Not(b)
Impl(A, B) == A => B
Eq(A, B) == A = B

THEOREM BoxEq ==
  ASSUME ([]p) = FALSE
  PROVE  [](([]p) = FALSE)
BY PTL

THEOREM QuantEq ==
  ASSUME (\A i \in Nat: []p) = FALSE
  PROVE  []((\A i \in Nat: []p) = FALSE)
BY PTL

THEOREM BoxNot ==
  ASSUME Not([]p)
  PROVE  [](Not([]p))
<1> HIDE DEF Not
<1> QED BY PTL

THEOREM QuantNot ==
  ASSUME Not(\A i \in Nat: []p)
  PROVE  [](Not(\A i \in Nat: []p))
<1> HIDE DEF Not
<1> QED BY PTL

THEOREM WrappedNot ==
  ASSUME NotWrap([]p)
  PROVE  [](NotWrap([]p))
<1> HIDE DEF NotWrap, Not
<1> QED BY PTL

THEOREM DefinedImplication ==
  ASSUME Impl([]p, []q)
  PROVE  [](Impl([]p, []q))
<1> HIDE DEF Impl
<1> QED BY PTL

THEOREM DefinedEquality ==
  ASSUME Eq([]p, FALSE)
  PROVE  [](Eq([]p, FALSE))
<1> HIDE DEF Eq
<1> QED BY PTL
====
stderr: status:failed
nostderr: status:proved
