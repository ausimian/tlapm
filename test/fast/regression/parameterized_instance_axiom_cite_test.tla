---------- MODULE parameterized_instance_axiom_cite_test -----------
(* A theorem of a parametric instance of a module with an ASSUME or an
   AXIOM can be cited. The axioms, applied to the arguments, are
   hypotheses of the citation: I(x, y)!T gives
   ASSUME x < y, I!D(x, y) > 0 PROVE H(x, y). This used to stop tlapm
   with "Expr.Levels: ARITY". *)
EXTENDS Integers

CONSTANT H(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_aux WITH a <- x, b <- y, G <- H

THEOREM ASSUME NEW x \in Int, NEW y \in Int, x < y, x > 0 PROVE H(x, y)
BY I(x, y)!T DEF I!D
====================================
nostderr: status:failed
stderr: status:proved
