---------- MODULE proof_instance_theorem_test -----------
(* An INSTANCE inside a proof keeps only the definitions of the
   instantiated module, so citing one of its theorems is an error,
   reported as such rather than as an internal failure. *)
---------- MODULE M -----------
CONSTANT k
THEOREM Thm == k = k
====================================
THEOREM 1 = 1
<1> J == INSTANCE M WITH k <- 1
<1> QED BY J!Thm
====================================
result: 3
stderr: Theorem "J!Thm" cannot be cited
nostderr: 1EMPTY
