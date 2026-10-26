---------- MODULE parameterized_instance_named_theorem_test -----------
(* A named theorem in the instantiated module used to shift the
   instance parameters by one, so that I(c)!D expanded with c replaced
   by another operator of the context. *)
EXTENDS Naturals

VARIABLES x, y
I(c) == INSTANCE parameterized_instance_theorem_aux WITH S <- c + 1, p <- (y = c)

THEOREM ASSUME NEW c \in Nat PROVE I(c)!D => y = c
BY DEF I!D
====================================
nostderr: status:failed
stderr: status:proved
