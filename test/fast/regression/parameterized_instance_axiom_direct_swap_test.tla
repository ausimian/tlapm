---------- MODULE parameterized_instance_axiom_direct_swap_test -----------
(* The axiom a < b is applied to x and y in that order: y < x does not
   give it. *)
EXTENDS Integers

CONSTANT H(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_direct_aux WITH a <- x, b <- y, G <- H

THEOREM ASSUME NEW x \in Int, NEW y \in Int, y < x PROVE H(x, y)
BY I(x, y)!T
====================================
stderr: status:failed
stderr: 1/2 obligations failed
