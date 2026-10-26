---------- MODULE parameterized_instance_theorem_aux -----------
CONSTANT S
VARIABLE p
(* A named theorem before the definitions: it occupies two hypotheses. *)
THEOREM Before == TRUE
PROOF OMITTED
D == p /\ S = S
THEOREM T == D => p
PROOF OMITTED
====================================
