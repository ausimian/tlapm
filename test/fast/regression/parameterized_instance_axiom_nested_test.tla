---------- MODULE parameterized_instance_axiom_nested_test -----------
(* A parametric instance of a module with a non-parametric instance J of
   a module with axioms. J's theorems have J's axioms as hypotheses
   (naxs > 0). This used to stop tlapm with "naxs > #cx" as soon as the
   instance was declared. The hypotheses are now inside the LAMBDA:
   I(x, y)!J!T gives ASSUME x < y, I!J!D(x, y) > 0 PROVE K(x, y). *)
EXTENDS Integers

CONSTANT K(_, _)
I(x, y) == INSTANCE parameterized_instance_axiom_nested_aux WITH c <- x, d <- y, H <- K

THEOREM ASSUME NEW x \in Int, NEW y \in Int, x < y, x > 0 PROVE K(x, y)
BY I(x, y)!J!T DEF I!J!D
====================================
nostderr: status:failed
stderr: status:proved
