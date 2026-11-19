From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import available_goal two_way_dynamic_lib.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_available_safety_wit_1 : available_safety_wit_1.
Proof. pre_process; entailer!; try rewrite sizeof_uchar; try lia. Qed.
Lemma proof_of_available_safety_wit_2 : available_safety_wit_2.
Proof. pre_process; entailer!; try rewrite sizeof_uchar; try lia. Qed.
Lemma proof_of_available_return_wit_1 : available_return_wit_1.
Proof. pre_process. Exists (known + retval). entailer!. Qed.
Lemma proof_of_available_return_wit_2 : available_return_wit_2.
Proof. pre_process. Exists (known + retval). entailer!. Qed.
Lemma proof_of_available_return_wit_3 : available_return_wit_3.
Proof. pre_process. Exists known. entailer!. Qed.
Lemma proof_of_available_partial_solve_wit_1_pure : available_partial_solve_wit_1_pure.
Proof. pre_process; entailer!; try rewrite sizeof_uchar; try lia. Qed.
Lemma proof_of_available_partial_solve_wit_1 : available_partial_solve_wit_1.
Proof.
  unfold available_partial_solve_wit_1, available_partial_solve_wit_1_aux.
  intros; entailer!; rewrite sizeof_uchar; lia.
Qed.
