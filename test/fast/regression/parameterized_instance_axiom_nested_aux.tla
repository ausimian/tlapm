---------- MODULE parameterized_instance_axiom_nested_aux -----------
(* A module with a non-parametric instance of a module with axioms. *)
EXTENDS Integers
CONSTANTS c, d, H(_, _)
J == INSTANCE parameterized_instance_axiom_aux WITH a <- c, b <- d, G <- H
====================================
