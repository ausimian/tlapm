---- MODULE box_closure_sequent_unsound_test ----
(* False, so it must not prove. The hypothesis ASSUME p PROVE []FALSE says *)
(* only that p is false now; p may become true later. A sequent fact is    *)
(* closed under [] only if its hypotheses and conclusion make the          *)
(* implication closed, not because its conclusion is.                     *)
EXTENDS TLAPS

VARIABLE p

THEOREM SequentHypothesis ==
  ASSUME ASSUME p PROVE []FALSE
  PROVE  [](~p)
BY PTL
====
stderr: status:failed
nostderr: status:proved
