---------- MODULE parameterized_instance_axiom_false_test -----------
(* I(1)!T gives ASSUME 1 = 0 PROVE 1 = 0, which does not prove 1 = 0. *)
EXTENDS Naturals

I(c) == INSTANCE parameterized_instance_axiom_false_aux WITH k <- c

THEOREM 1 = 0
BY I(1)!T
====================================
stderr: status:failed
stderr: 1/2 obligations failed
