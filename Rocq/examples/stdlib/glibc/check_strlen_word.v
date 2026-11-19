(* Object-bounded case: the real load and both strlen contracts are in one interface. *)
Require Import SimpleC.EE.stdlib.glibc.strlen_word_goal_check.
Require Import SimpleC.EE.stdlib.glibc.strlen_word_lib.

Print Assumptions strlen_word_proof_manual.proof_of_sl_load_word_entail_wit_1.
Print Assumptions strlen_word_proof_manual.proof_of_sl_load_word_return_wit_1.
Print Assumptions strlen_word_proof_manual.proof_of_strlen_word_return_wit_1.
Print Assumptions strlen_word_proof_manual.proof_of_strlen_word_capacity_spec_entail_exact_spec.
