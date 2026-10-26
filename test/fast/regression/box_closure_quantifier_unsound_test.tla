---- MODULE box_closure_quantifier_unsound_test ----
(* Every theorem here is false, so none must prove. A quantified formula   *)
(* is closed under [] only if its body is and its domains are constant.    *)
EXTENDS Naturals, TLAPS

CONSTANT S
VARIABLES x, y

THEOREM DiamondBody ==
  ASSUME \A i \in S: <>(x = i)
  PROVE  [](\A i \in S: <>(x = i))
BY PTL

THEOREM StateBody ==
  ASSUME \A i \in S: x # i
  PROVE  [](\A i \in S: x # i)
BY PTL

THEOREM StateDomain ==
  ASSUME \A i \in y: [](i \in y)
  PROVE  [](\A i \in y: [](i \in y))
BY PTL

THEOREM ExistsDiamond ==
  ASSUME \E i \in S: <>(x = i)
  PROVE  [](\E i \in S: <>(x = i))
BY PTL

THEOREM ExistsLeadsTo ==
  ASSUME NEW STATE p, NEW STATE g, NEW STATE G,
         \E k \in S: (p /\ g = k) ~> G
  PROVE  (p /\ g \in S) ~> G
BY PTL
====
stderr: status:failed
nostderr: status:proved
