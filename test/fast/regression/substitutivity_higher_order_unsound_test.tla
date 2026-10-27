---- MODULE substitutivity_higher_order_unsound_test ----
(* False, so it must not prove. H takes an operator parameter, so its     *)
(* substitutivity array assumes a Leibniz argument for G; passed to Outer *)
(* as an operator argument, it gets LAMBDA y : [](x = y) instead, and     *)
(* Outer(H, a) is [](x = a), which is not substitutive in a. SANY rejects *)
(* passing H as an operator argument, but tlapm accepts the module.       *)
EXTENDS Naturals, TLAPS

VARIABLE x

H(G(_), a) == G(a)
Outer(K(_, _), a) == K(LAMBDA y : [](x = y), a)

LEMMA Refl == [](x = x)
<1>1. x = x  OBVIOUS
<1> QED BY <1>1, PTL

THEOREM NestedHigherOrder ==
  ASSUME x = 1
  PROVE  [](x = 1)
<1>1. Outer(H, x)  BY Refl DEF Outer, H
<1>2. Outer(H, 1)
  <2> HIDE DEF Outer, H
  <2> QED BY <1>1
<1> QED BY <1>2 DEF Outer, H
====
stderr: status:failed
