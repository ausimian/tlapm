---------- MODULE parameterized_instance_axiom_direct_test -----------
(* I(x, y)!T gives ASSUME x < y PROVE H(x, y). *)
EXTENDS Integers

CONSTANT H(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_direct_aux WITH a <- x, b <- y, G <- H

THEOREM ASSUME NEW x \in Int, NEW y \in Int, x < y PROVE H(x, y)
BY I(x, y)!T
====================================
nostderr: status:failed
stderr: status:proved
