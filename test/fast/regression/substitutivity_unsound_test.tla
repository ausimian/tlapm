---- MODULE substitutivity_unsound_test ----
(* Every theorem here is false, so none must prove. Each relies on tlapm    *)
(* treating a hidden operator as substitutive in an argument where it is    *)
(* not, so that the backends rewrite the argument x to 1 under x = 1.       *)
EXTENDS Naturals, TLAPS

CONSTANT S
VARIABLE x

(* An operator parameter instantiated with a temporal LAMBDA. Ap is         *)
(* substitutive in a only when F is.                                        *)
Ap(F(_), a) == F(a)
LEMMA ApDef == ASSUME NEW F(_), NEW a PROVE Ap(F, a) <=> F(a)
PROOF OMITTED
LEMMA ApX == ASSUME NEW F(_) PROVE Ap(F, x) <=> F(x)
PROOF OMITTED
LEMMA ApXX == Ap(LAMBDA y : [](x = y), x)
PROOF OMITTED

THEOREM CongruenceFlex == ASSUME x = 1 PROVE Ap(LAMBDA y : [](x = y), 1)
<1> HIDE DEF Ap
<1> QED BY ApXX, ApDef, ApX

THEOREM ExistsFlex == x \in S => \E t \in S : Ap(LAMBDA y : [](x = y), t)
<1> HIDE DEF Ap
<1> QED BY ApXX

(* A LAMBDA that passes its formal to a declared operator of non-constant   *)
(* level is not Leibniz: with A == LAMBDA v : v' = 0, A(x) holds when       *)
(* x = 1 and x' = 0, but A(1) is FALSE.                                     *)
THEOREM DeclaredAction == ASSUME NEW ACTION A(_), x = 1, Ap(LAMBDA y : A(y), x)
                          PROVE  Ap(LAMBDA y : A(y), 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

THEOREM DeclaredTemporal == ASSUME NEW TEMPORAL T(_), x = 1, Ap(LAMBDA y : T(y), x)
                            PROVE  Ap(LAMBDA y : T(y), 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

(* B passes its first parameter to the primed position of A. The            *)
(* substitutivity array is indexed from the last parameter.                 *)
A(p, q) == p' = q
B(u, v) == A(u, v)
LEMMA B11 == B(1, 1)
PROOF OMITTED

THEOREM ArgumentOrder == ASSUME x = 1 PROVE B(x, 1)
<1> HIDE DEF A, B
<1> QED BY B11

(* u occurs under [] in D, even though E itself is substitutive.            *)
E(v) == v = 1
D(u) == [](E(u))
LEMMA D1 == D(1)
PROOF OMITTED

THEOREM NestedScope == ASSUME x = 1 PROVE D(x)
<1> HIDE DEF D, E
<1> QED BY D1

(* The same through a wrapper that forwards F.                             *)
Wrap(F(_), a) == Ap(F, a)
LEMMA WrapDef == ASSUME NEW F(_), NEW a PROVE Wrap(F, a) <=> F(a)
PROOF OMITTED
LEMMA WrapX == ASSUME NEW F(_) PROVE Wrap(F, x) <=> F(x)
PROOF OMITTED
LEMMA WrapXX == Wrap(LAMBDA y : [](x = y), x)
PROOF OMITTED

THEOREM ForwardedFlex == ASSUME x = 1 PROVE Wrap(LAMBDA y : [](x = y), 1)
<1> HIDE DEF Wrap, Ap
<1> QED BY WrapXX, WrapDef, WrapX
====
stderr: status:failed
nostderr: status:proved
