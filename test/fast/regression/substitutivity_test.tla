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
====
