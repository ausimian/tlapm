---------- MODULE parameterized_instance_theorem_nonconstant_test -----------
(* Citing a theorem of a parametric instance with a state-level
   argument is not trusted: a theorem about every constant need not
   hold for a variable. The citation is left as an obligation, which
   fails here. *)
EXTENDS Naturals

VARIABLES x, y
I(c) == INSTANCE parameterized_instance_theorem_aux WITH S <- c + 1, p <- (y = c)

THEOREM I(x)!D => y = x
<1> HIDE DEF I!D
<1> QED BY I(x)!T
====================================
stderr: status:failed
