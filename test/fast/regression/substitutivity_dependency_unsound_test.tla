---- MODULE substitutivity_dependency_unsound_test ----
(* False congruence steps, so none must prove. In each, the argument x     *)
(* reaches T, which is not Leibniz, through an operator parameter: by a    *)
(* LET or LAMBDA that applies the parameter, by a LAMBDA applied directly, *)
(* by a second operator parameter, or by a definition the parameter is     *)
(* forwarded to.                                                           *)
EXTENDS Naturals, TLAPS

VARIABLE x

Ap(F(_), a) == F(a)
T(y) == [](x = y)
L(y) == y + 1 = 2
Id(y) == y

OuterLet(F(_), a) == LET In(b) == F(b) IN Ap(In, a)
THEOREM LetPassed == ASSUME x = 1, OuterLet(T, x) PROVE OuterLet(T, 1)
<1> HIDE DEF OuterLet, Ap, T
<1> QED OBVIOUS

WrapLambda(F(_), a) == Ap(LAMBDA y : F(y), a)
THEOREM LambdaPassed == ASSUME x = 1, WrapLambda(T, x) PROVE WrapLambda(T, 1)
<1> HIDE DEF WrapLambda, Ap, T
<1> QED OBVIOUS

Mix(F(_), G(_), a) == Ap(G, a) /\ F(0)
THEOREM SecondParameter == ASSUME x = 1, Mix(L, T, x) PROVE Mix(L, T, 1)
<1> HIDE DEF Mix, Ap, T, L
<1> QED OBVIOUS

Two(P(_), Q(_), a) == Q(P(a))
THEOREM OuterParameter == ASSUME x = 1, Two(Id, T, x) PROVE Two(Id, T, 1)
<1> HIDE DEF Two, T, Id
<1> QED OBVIOUS

THEOREM InnerParameter ==
  ASSUME x = 1, Two(T, LAMBDA b : b, x) PROVE Two(T, LAMBDA b : b, 1)
<1> HIDE DEF Two, T
<1> QED OBVIOUS

Cap(F(_), a) == LET In(b) == F(a) IN In(0)
THEOREM LetBody == ASSUME x = 1, Cap(T, x) PROVE Cap(T, 1)
<1> HIDE DEF Cap, T
<1> QED OBVIOUS

Fw(F(_), a) == Ap(F, a)
Deep(F(_), a) == LET In(b) == Fw(F, b) IN In(a)
THEOREM LetForwarded == ASSUME x = 1, Deep(T, x) PROVE Deep(T, 1)
<1> HIDE DEF Deep, Fw, Ap, T
<1> QED OBVIOUS
Relay(F(_), a) == (LAMBDA y : F(y))(a)
THEOREM AppliedLambda == ASSUME x = 1, Relay(T, x) PROVE Relay(T, 1)
<1> HIDE DEF Relay, T
<1> QED OBVIOUS
====
stderr: status:failed
nostderr: status:proved
