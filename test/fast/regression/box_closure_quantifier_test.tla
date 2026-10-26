---- MODULE box_closure_quantifier_test ----
(* A quantifier over a rigid variable commutes with [] (the Barcan          *)
(* formula), so a quantified formula whose body is closed under [] and      *)
(* whose domains are constant is closed under [] too. PTL can then use      *)
(* such an assumption at every later point.                                 *)
EXTENDS Naturals, TLAPS

CONSTANT S
VARIABLE x

A(i) == x' = i

THEOREM BoundedWF ==
  ASSUME \A i \in S: WF_x(A(i))
  PROVE  [](\A i \in S: WF_x(A(i)))
BY PTL

THEOREM Nested ==
  ASSUME \A i \in S: \A j \in Nat: [](x # i + j)
  PROVE  [](\A i \in S: \A j \in Nat: [](x # i + j))
BY PTL

THEOREM Exists ==
  ASSUME \E i \in S: [](x = i)
  PROVE  [](\E i \in S: [](x = i))
BY PTL

(* The leads-to rule for a rigid index follows. *)
THEOREM LeadsToExists ==
  ASSUME NEW STATE p, NEW STATE g, NEW STATE G,
         \A k \in S: (p /\ g = k) ~> G
  PROVE  (p /\ g \in S) ~> G
<1>1. ASSUME NEW k \in S PROVE ((p /\ g = k) ~> G) => (p /\ g = k => <>G)
  BY PTL
<1>2. \A k \in S: (p /\ g = k => <>G)
  BY <1>1
<1>3. (\A k \in S: (p /\ g = k => <>G)) => (p /\ g \in S => <>G)
  OBVIOUS
<1> QED BY <1>2, <1>3, PTL
====
nostderr: status:failed
