---- MODULE coalesce_bound_var_test ----
(* Valid theorems with temporal formulas under binders. Coalescing must     *)
(* abstract such a formula as a function of its bound variables, the same   *)
(* function whatever the variables are called (issues #197 and #309).       *)
EXTENDS Naturals, TLAPS

CONSTANT S
VARIABLE x

THEOREM Instantiate == ASSUME NEW c \in S, \A t \in S : <>(x = t)
                       PROVE  <>(x = c)
OBVIOUS

THEOREM Rename == (\A i \in S : [](x = i => <>(x # i)))
                  => (\A k \in S : [](x = k => <>(x # k)))
OBVIOUS

THEOREM QuantifiedHyp == ASSUME NEW k \in S, \A i \in S : [](x = i => <>(x # i))
                         PROVE  [](x = k => <>(x # k))
OBVIOUS

THEOREM Fairness == ASSUME NEW a \in S, NEW b \in S,
                           \A m, n \in S : WF_x(x' = m + n)
                    PROVE  WF_x(x' = a + b)
OBVIOUS

(* [] distributes over \A. *)
THEOREM Commute == ASSUME NEW TEMPORAL F(_)
                   PROVE  (\A k \in S : [](F(k))) => [](\A k \in S : F(k))
OBVIOUS

THEOREM ExistsDiamond == ASSUME NEW c \in S, <>(x = c)
                         PROVE  \E t \in S : <>(x = t)
OBVIOUS

(* LS4 rejects identifiers longer than 31 characters, which bounds the      *)
(* names that coalescing gives to atoms.                                    *)
THEOREM Ptl == [](x \in Nat) /\ [](x = 0 => <>(x = 1)) => (x = 0 ~> x = 1)
BY PTL
====
