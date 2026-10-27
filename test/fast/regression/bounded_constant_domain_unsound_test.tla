---- MODULE bounded_constant_domain_unsound_test ----
(* False: x is in y now, but y is a variable and may later stop containing *)
(* x. PTL must not treat the membership of a bounded constant in a         *)
(* state-dependent domain as true at every later point.                    *)
EXTENDS TLAPS

VARIABLE y

THEOREM DomainShift ==
  ASSUME NEW CONSTANT x \in y
  PROVE  [](x \in y)
BY PTL
====
stderr: status:failed
nostderr: status:proved
