---- MODULE box_closure_sequent_domain_unsound_test ----
(* False, so it must not prove. The hypothesis says only that y is empty  *)
(* now. A sequent declaring a constant over a state-dependent domain is   *)
(* not closed under [], even though tlapm treats the sequent as constant. *)
(* The step y = {} does prove, so the test checks only that a failure is  *)
(* reported.                                                              *)
EXTENDS TLAPS

VARIABLE y

THEOREM SequentBoundedDomain ==
  ASSUME ASSUME NEW CONSTANT x \in y PROVE FALSE
  PROVE  [](y = {})
<1>1. y = {}  OBVIOUS
<1> QED BY <1>1, PTL
====
stderr: status:failed
