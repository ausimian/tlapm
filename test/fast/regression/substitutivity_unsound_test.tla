---- MODULE substitutivity_unsound_test ----
(* Every theorem here is false, so none must prove. Each relies on tlapm    *)
(* treating a hidden operator as substitutive in an argument where it is    *)
(* not, so that the backends rewrite the argument x to 1 under x = 1.       *)
EXTENDS Naturals, TLAPS

VARIABLE x

(* B passes its first parameter to the primed position of A. The            *)
(* substitutivity array is indexed from the last parameter.                 *)
A(p, q) == p' = q
B(u, v) == A(u, v)
LEMMA B11 == B(1, 1)
PROOF OMITTED

THEOREM ArgumentOrder == ASSUME x = 1 PROVE B(x, 1)
<1> HIDE DEF A, B
<1> QED BY B11
====
stderr: status:failed
nostderr: status:proved
