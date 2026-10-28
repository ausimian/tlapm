---------- MODULE parameterized_instance_axiom_named_test -----------
(* Citing I(x, y)!T needs the named ASSUME Lt applied to x and y, in that
   order: y < x does not give it. *)
EXTENDS Integers

CONSTANT H(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_aux WITH a <- x, b <- y, G <- H

THEOREM ASSUME NEW x \in Int, NEW y \in Int, y < x, x > 0, y > 0 PROVE H(x, y)
BY I(x, y)!T DEF I!D
====================================
stderr: status:failed
