---------- MODULE parameterized_instance_axiom_inner_aux -----------
(* A module with an axiom and a parametric instance of a module with
   axioms. *)
EXTENDS Integers
CONSTANTS c, H(_, _)
ASSUME CPos == c > 0
J(y, z) == INSTANCE parameterized_instance_axiom_aux WITH a <- y, b <- z, G <- H
====================================
