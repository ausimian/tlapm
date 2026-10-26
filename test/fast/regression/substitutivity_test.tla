---- MODULE substitutivity_test ----
(* Valid rewriting under x = 1 through hidden operators that are           *)
(* substitutive in the argument.                                            *)
EXTENDS Naturals, TLAPS

VARIABLE x

A(p, q) == p' = q
B(u, v) == A(u, v)

THEOREM SubstitutivePosition == ASSUME x = 1, B(0, x) PROVE B(0, 1)
<1> HIDE DEF A, B
<1> QED OBVIOUS

E(v) == v = 1
C(u) == E(u) /\ u \in Nat

THEOREM NestedSubstitutive == ASSUME x = 1, C(x) PROVE C(1)
<1> HIDE DEF C, E
<1> QED OBVIOUS
====
