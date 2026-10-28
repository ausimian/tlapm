---------- MODULE parameterized_instance_axiom_direct_aux -----------
EXTENDS Integers
CONSTANTS a, b, G(_, _)
(* An unnamed axiom that mentions the parameters directly, followed by a
   definition and a named theorem before T. *)
AXIOM a < b
E == b
THEOREM Mid == TRUE
OBVIOUS
THEOREM T == G(a, b)
PROOF OMITTED
====================================
