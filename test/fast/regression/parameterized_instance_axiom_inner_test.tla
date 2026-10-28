---------- MODULE parameterized_instance_axiom_inner_test -----------
(* A theorem of J(y, z), a parametric instance inside a module with an
   axiom, is LAMBDA x, y, z: ... under I(x). Citing I(x)!J(y, z)!T needs
   the outer axiom applied to x and J's axioms applied to y and z. This
   used to stop tlapm with "Expr.Levels: ARITY". *)
EXTENDS Integers

CONSTANT K(_, _)
I(x) == INSTANCE parameterized_instance_axiom_inner_aux WITH c <- x, H <- K

THEOREM ASSUME NEW x \in Int, NEW y \in Int, NEW z \in Int, x > 0, y < z, y > 0
        PROVE K(y, z)
BY I(x)!J(y, z)!T DEF I!J!D
====================================
nostderr: status:failed
stderr: status:proved
