---------- MODULE parameterized_instance_axiom_aux -----------
EXTENDS Integers
CONSTANTS a, b, G(_, _)
(* A named theorem before the axioms: it occupies two hypotheses. *)
THEOREM Pre == TRUE
OBVIOUS
ASSUME Lt == a < b
D == a
AXIOM D > 0
THEOREM T == G(a, b)
PROOF OMITTED
====================================
