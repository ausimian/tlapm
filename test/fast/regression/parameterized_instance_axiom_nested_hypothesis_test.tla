---------- MODULE parameterized_instance_axiom_nested_hypothesis_test -----------
(* I(x, y)!J!T keeps J's axioms as hypotheses: without x > 0 it does not
   prove K(x, y). *)
EXTENDS Integers

CONSTANT K(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_nested_aux WITH c <- x, d <- y, H <- K

THEOREM ASSUME NEW x \in Int, NEW y \in Int, x < y, y > 0 PROVE K(x, y)
BY I(x, y)!J!T DEF I!J!D
====================================
stderr: status:failed
stderr: 1/2 obligations failed
