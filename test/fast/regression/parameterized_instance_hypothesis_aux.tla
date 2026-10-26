---------- MODULE parameterized_instance_hypothesis_aux -----------
EXTENDS Naturals
CONSTANT k
THEOREM Hyp == ASSUME k = 5 PROVE k + 1 = 6
  OBVIOUS
====================================
