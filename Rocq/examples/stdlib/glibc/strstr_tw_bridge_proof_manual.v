From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import strstr_tw_bridge_goal strstr_tw_bridge_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

Lemma proof_of_strstr_tw_bridge_entail_wit_1 : strstr_tw_bridge_entail_wit_1.
Proof.
 unfold strstr_tw_bridge_entail_wit_1; left; intros.
 subst hs_pre ne_pre.
 split_pure_spatial.
 - apply gs_tw_open; assumption.
 - split_pures; dump_pre_spatial; auto.
   eapply gs_tw_nonzero; exact PreH5.
Qed.

Lemma proof_of_strstr_tw_bridge_entail_wit_2 : strstr_tw_bridge_entail_wit_2.
Proof.
 unfold strstr_tw_bridge_entail_wit_2; left; intros.
 subst hs ne. rewrite sizeof_uchar in PreH2.
 split_pure_spatial.
 - apply gs_tw_close; assumption.
 - split_pures; dump_pre_spatial; auto.
   eapply gs_tw_result; eauto; lia.
Qed.

Lemma proof_of_strstr_tw_bridge_partial_solve_wit_1_pure : strstr_tw_bridge_partial_solve_wit_1_pure.
Proof.
 unfold strstr_tw_bridge_partial_solve_wit_1_pure; left; intros.
 match goal with H : gs_inputs _ _ _ _ _ _ |- _ => unfold gs_inputs in H; destruct H as (L & B & Ho & Hl & HE & No & Rest) end.
 split_pures; dump_pre_spatial; auto; lia.
Qed.

(* Also close both obligations classified automatic by QCP. *)
Lemma proof_of_strstr_tw_bridge_return_wit_1 : strstr_tw_bridge_return_wit_1.
Proof.
 unfold strstr_tw_bridge_return_wit_1; intros. entailer!.
Qed.

Lemma proof_of_strstr_tw_bridge_partial_solve_wit_1 : strstr_tw_bridge_partial_solve_wit_1.
Proof.
 unfold strstr_tw_bridge_partial_solve_wit_1, strstr_tw_bridge_partial_solve_wit_1_aux.
 intros. pose proof PreH5 as Input.
 destruct PreH5 as (L & B & Ho & Hl & HE & No & Rest).
 split_pure_spatial; [cancel|]. split_pures; dump_pre_spatial; auto; lia.
Qed.
