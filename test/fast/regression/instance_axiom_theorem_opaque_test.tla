---------- MODULE instance_axiom_theorem_opaque_test -----------
(* Citing a theorem of a non-parametric instance does not prove its
   statement when the theorem depends on an axiom of the instantiated
   module: J!T stays opaque. So no proved theorem of a module rests on the
   axioms of an instance in it, and a parametric instance of the module can
   expose the module's own theorems without those axioms (see
   parameterized_instance_axiom_nested_test.tla). If this test ever proves,
   revisit that. *)
EXTENDS Integers

CONSTANTS c, d, H(_, _)
J == INSTANCE parameterized_instance_axiom_aux WITH a <- c, b <- d, G <- H

THEOREM H(c, d)
BY J!T
====================================
stderr: status:failed
stderr: 1/2 obligations failed
