---------- MODULE proof_instance_theorem_scope_test -----------
(* Citing a theorem of an INSTANCE inside a proof is reported as such only
   in that proof. Elsewhere the instance is not in scope, so the name is
   just unknown. *)
---------- MODULE M -----------
CONSTANT k
D == k
THEOREM Thm == k = k
====================================
THEOREM A == 1 = 1
<1> J == INSTANCE M WITH k <- 1
<1> QED BY DEF J!D
THEOREM B == 2 = 2
BY J!Thm
====================================
result: 3
stderr: Operator "J!Thm" not found
nostderr: cannot be cited
