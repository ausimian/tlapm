---------- MODULE parameterized_instance_theorem_cite_test -----------
(* A theorem of a parametric instance can be cited with constant
   arguments, as I(c)!T. *)
EXTENDS Naturals

VARIABLES x, y
I(c) == INSTANCE parameterized_instance_theorem_aux WITH S <- c + 1, p <- (y = c)

THEOREM ASSUME NEW c \in Nat PROVE I(c)!D => y = c
<1> HIDE DEF I!D
<1> QED BY I(c)!T
====================================
nostderr: status:failed
stderr: status:proved
