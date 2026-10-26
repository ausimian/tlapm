---------- MODULE parameterized_instance_theorem_hypothesis_test -----------
(* Citing I(e)!Thm keeps the hypotheses of Thm: the citation gives
   ASSUME 3 = 5 PROVE 3 + 1 = 6, which does not prove 3 + 1 = 6. *)
EXTENDS Naturals

I(c) == INSTANCE parameterized_instance_hypothesis_aux WITH k <- c

THEOREM 1 = 2
<1>1. 3 + 1 = 6 BY I(3)!Hyp
<1> QED BY <1>1
====================================
stderr: status:failed
