---- MODULE substitutivity_test ----
(* Valid rewriting under x = 1 through hidden operators that are           *)
(* substitutive in the argument, with Leibniz operator arguments.           *)
EXTENDS Naturals, TLAPS

VARIABLE x

Ap(F(_), a) == F(a)

THEOREM LeibnizLambda == ASSUME x = 1, Ap(LAMBDA y : y + 1 = 2, x)
                         PROVE  Ap(LAMBDA y : y + 1 = 2, 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

THEOREM ConstantOperator == ASSUME NEW G(_), x = 1, Ap(G, x)
                            PROVE  Ap(G, 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

THEOREM ConstantOperatorLambda == ASSUME NEW G(_), x = 1, Ap(LAMBDA y : G(y), x)
                                  PROVE  Ap(LAMBDA y : G(y), 1)
<1> HIDE DEF Ap
<1> QED OBVIOUS

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

(* A wrapper that forwards its operator parameter is substitutive in a     *)
(* when the operator passed for F is Leibniz.                               *)
Wrap(F(_), a) == Ap(F, a)

THEOREM ForwardedOperator == ASSUME x = 1, Wrap(LAMBDA y : y + 1 = 2, x)
                             PROVE  Wrap(LAMBDA y : y + 1 = 2, 1)
<1> HIDE DEF Wrap, Ap
<1> QED OBVIOUS

(* A built-in operator such as \cup passed for an operator parameter is     *)
(* Leibniz.                                                                 *)
Fold(op(_, _), a, b) == op(a, b)
U(a, b) == Fold(\cup, a, b)

THEOREM BuiltinOperator == ASSUME x = {1}, U(x, {2}) = {1, 2}
                           PROVE  U({1}, {2}) = {1, 2}
<1> HIDE DEF U, Fold
<1> QED OBVIOUS
====
