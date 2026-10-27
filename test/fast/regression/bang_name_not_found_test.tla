---------- MODULE bang_name_not_found_test -----------
(* An unknown name of the form A!B is reported with its location. Outside
   the Toolbox mode, the message used to be missing. tlapm fails here
   before it writes to stdout, and the test harness checks stderr only
   when stdout is not empty, so the command writes an empty line. *)
THEOREM 1 = 1
BY Undef!X
====================================
command: ${TLAPM} --nofp ${FILE}; r=$?; echo; exit $r
result: 3
stderr: Operator "Undef!X" not found
