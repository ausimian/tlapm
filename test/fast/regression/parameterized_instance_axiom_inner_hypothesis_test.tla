---------- MODULE parameterized_instance_axiom_inner_hypothesis_test -----------
(* The outer axiom c > 0 is applied to x, not to y or z: with y > 0 and
   z > 0 but not x > 0, I(x)!J(y, z)!T does not prove K(y, z). *)
EXTENDS Integers

CONSTANT K(_, _)
I(x) == INSTANCE parameterized_instance_axiom_inner_aux WITH c <- x, H <- K

THEOREM ASSUME NEW x \in Int, NEW y \in Int, NEW z \in Int, y < z, y > 0, z > 0
        PROVE K(y, z)
BY I(x)!J(y, z)!T DEF I!J!D
====================================
stderr: status:failed
stderr: 1/2 obligations failed
