---- MODULE coalesce_bound_var_unsound_test ----
(* Every theorem here is false, so none must prove. Each has a temporal     *)
(* formula or ENABLED under a binder. Coalescing used to abstract such a    *)
(* term as a nullary constant, dropping the bound variable, so that         *)
(* `\E t : F(t)` and `\A t : F(t)` became the same proposition (issue #309).*)
EXTENDS Naturals, TLAPS

CONSTANT S
VARIABLES x, y

A(t) == x = t /\ x' = t + 1

THEOREM EnabledSMT == (\E t \in S : ENABLED A(t)) => (\A t \in S : ENABLED A(t))
BY SMT
THEOREM EnabledZenon == (\E t \in S : ENABLED A(t)) => (\A t \in S : ENABLED A(t))
BY Zenon
THEOREM EnabledIsa == (\E t \in S : ENABLED A(t)) => (\A t \in S : ENABLED A(t))
BY Isa

THEOREM BoxSMT == (\E k \in Nat : [](x = k)) => (\A k \in Nat : [](x = k))
BY SMT
THEOREM BoxZenon == (\E k \in Nat : [](x = k)) => (\A k \in Nat : [](x = k))
BY Zenon
THEOREM BoxIsa == (\E k \in Nat : [](x = k)) => (\A k \in Nat : [](x = k))
BY Isa

(* An existential where the valid rule has a universal. *)
THEOREM CommuteExists == ASSUME NEW TEMPORAL F(_)
                         PROVE  (\E k \in S : [](F(k))) => [](\A k \in S : F(k))
OBVIOUS

(* <>(x = a /\ y = b) prints alike under `\A a : \A b` and `\A b : \A a`,   *)
(* but a and b have opposite de Bruijn indices in the two. Passing the      *)
(* arguments in index order would abstract the hypothesis as h(1, 0) and    *)
(* the goal as h(1, 0) too, though they say <>(x = 0 /\ y = 1) and          *)
(* <>(x = 1 /\ y = 0).                                                       *)
THEOREM Swapped ==
  (\A a \in Nat : \A b \in Nat : a = 0 /\ b = 1 => <>(x = a /\ y = b))
  => (\A b \in Nat : \A a \in Nat : a = 1 /\ b = 0 => <>(x = a /\ y = b))
OBVIOUS

(* A proof for one instance does not prove the general statement.           *)
THEOREM OneInstance == ASSUME NEW c \in S, <>(x = c)
                       PROVE  \A t \in S : <>(x = t)
OBVIOUS

(* A modal formula in the body of a LAMBDA that is passed, unreduced, to a  *)
(* hidden operator must still depend on the LAMBDA's formal.                *)
Ap(F(_), a) == F(a)
LEMMA ApDef == ASSUME NEW F(_), NEW a PROVE Ap(F, a) <=> F(a)
PROOF OMITTED

THEOREM LambdaFormal == ASSUME Ap(LAMBDA y : <>(x = y), 1)
                        PROVE  Ap(LAMBDA y : <>(x = y), 2)
<1> HIDE DEF Ap
<1> QED BY ApDef

(* A declared operator of non-constant level must keep its arguments.       *)
THEOREM TemporalOperator == ASSUME NEW TEMPORAL F(_), NEW a \in S, NEW b \in S, F(a)
                            PROVE  F(b)
OBVIOUS

THEOREM StateOperator == ASSUME NEW STATE P(_), NEW a \in S, NEW b \in S, P(a)
                         PROVE  P(b)
OBVIOUS

THEOREM TemporalOperatorBinder == ASSUME NEW TEMPORAL F(_)
                                  PROVE  (\E k \in S : F(k)) => (\A k \in S : F(k))
OBVIOUS

(* [] and <> must not move inside a quantifier whose bound is a state       *)
(* variable: here x ranges over {1} and then {2}, with y = 1 and then 2.    *)
THEOREM BoxStateBound == ASSUME [](\A t \in x : t \in S),
                                \A t \in S : [](y = t) => [](y = t + 1),
                                [](\A t \in x : y = t)
                         PROVE  [](\A t \in x : y = t + 1)
OBVIOUS

THEOREM DiamondStateBound == ASSUME <>(\E t \in x : y = t),
                                    \A t \in S : <>(y = t) => <>(y = t + 1),
                                    [](\A t \in x : t \in S)
                             PROVE  <>(\E t \in x : y = t + 1)
OBVIOUS
====
stderr: status:failed
nostderr: status:proved
