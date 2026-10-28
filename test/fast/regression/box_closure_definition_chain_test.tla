---- MODULE box_closure_definition_chain_test ----
(* Classifying a fact unfolds the definitions it applies. Each definition *)
(* here uses its parameter twice, so unfolding D30 in full would take 2^30 *)
(* steps; the classification must give up instead of hanging.            *)
EXTENDS TLAPS

VARIABLE p

D0(P) == P
D1(P) == D0(P) /\ D0(P)
D2(P) == D1(P) /\ D1(P)
D3(P) == D2(P) /\ D2(P)
D4(P) == D3(P) /\ D3(P)
D5(P) == D4(P) /\ D4(P)
D6(P) == D5(P) /\ D5(P)
D7(P) == D6(P) /\ D6(P)
D8(P) == D7(P) /\ D7(P)
D9(P) == D8(P) /\ D8(P)
D10(P) == D9(P) /\ D9(P)
D11(P) == D10(P) /\ D10(P)
D12(P) == D11(P) /\ D11(P)
D13(P) == D12(P) /\ D12(P)
D14(P) == D13(P) /\ D13(P)
D15(P) == D14(P) /\ D14(P)
D16(P) == D15(P) /\ D15(P)
D17(P) == D16(P) /\ D16(P)
D18(P) == D17(P) /\ D17(P)
D19(P) == D18(P) /\ D18(P)
D20(P) == D19(P) /\ D19(P)
D21(P) == D20(P) /\ D20(P)
D22(P) == D21(P) /\ D21(P)
D23(P) == D22(P) /\ D22(P)
D24(P) == D23(P) /\ D23(P)
D25(P) == D24(P) /\ D24(P)
D26(P) == D25(P) /\ D25(P)
D27(P) == D26(P) /\ D26(P)
D28(P) == D27(P) /\ D27(P)
D29(P) == D28(P) /\ D28(P)
D30(P) == D29(P) /\ D29(P)

THEOREM ASSUME D30([]p) PROVE D30([]p)
<1> HIDE DEF D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22, D23, D24, D25, D26, D27, D28, D29, D30
<1> QED BY PTL
====
