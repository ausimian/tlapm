---------- MODULE parameterized_instance_axiom_unnamed_test -----------
(* Citing I(x, y)!T needs the unnamed AXIOM D > 0 applied to x and y,
   that is x > 0: y > 0 does not give it. *)
EXTENDS Integers

CONSTANT H(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_aux WITH a <- x, b <- y, G <- H

THEOREM ASSUME NEW x \in Int, NEW y \in Int, x < y, y > 0 PROVE H(x, y)
BY I(x, y)!T DEF I!D
====================================
stderr: status:failed
stderr: 1/2 obligations failed
