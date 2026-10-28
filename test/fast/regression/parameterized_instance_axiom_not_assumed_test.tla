---------- MODULE parameterized_instance_axiom_not_assumed_test -----------
(* The axioms of a parametric instance are not assumed: citing I(x, y)!Lt
   does not prove x < y. *)
EXTENDS Integers

CONSTANT H(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_aux WITH a <- x, b <- y, G <- H

THEOREM ASSUME NEW x \in Int, NEW y \in Int PROVE x < y
BY I(x, y)!Lt
====================================
stderr: status:failed
