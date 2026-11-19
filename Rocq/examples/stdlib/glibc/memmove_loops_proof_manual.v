From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import memmove_loops_goal memmove_lib memmove_contract_lib.
Import Snaive_C_Rules64.
Local Open Scope sac.
Ltac mm_addr := repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *.
Ltac mm_finish := split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring].

Lemma proof_of_mm_copy_forward_safety_wit_1 : mm_copy_forward_safety_wit_1.
Proof. unfold mm_copy_forward_safety_wit_1; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_safety_wit_2 : mm_copy_forward_safety_wit_2.
Proof. unfold mm_copy_forward_safety_wit_2; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_safety_wit_3 : mm_copy_forward_safety_wit_3.
Proof. unfold mm_copy_forward_safety_wit_3; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_safety_wit_4 : mm_copy_forward_safety_wit_4.
Proof. unfold mm_copy_forward_safety_wit_4; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_safety_wit_5 : mm_copy_forward_safety_wit_5.
Proof. unfold mm_copy_forward_safety_wit_5; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_safety_wit_6 : mm_copy_forward_safety_wit_6.
Proof. unfold mm_copy_forward_safety_wit_6; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_safety_wit_7 : mm_copy_forward_safety_wit_7.
Proof. unfold mm_copy_forward_safety_wit_7; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_safety_wit_8 : mm_copy_forward_safety_wit_8.
Proof. unfold mm_copy_forward_safety_wit_8; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_backward_safety_wit_1 : mm_copy_backward_safety_wit_1.
Proof. unfold mm_copy_backward_safety_wit_1; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_backward_safety_wit_2 : mm_copy_backward_safety_wit_2.
Proof. unfold mm_copy_backward_safety_wit_2; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_backward_safety_wit_3 : mm_copy_backward_safety_wit_3.
Proof. unfold mm_copy_backward_safety_wit_3; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_backward_safety_wit_4 : mm_copy_backward_safety_wit_4.
Proof. unfold mm_copy_backward_safety_wit_4; intros; mm_addr; entailer!. Qed.

Lemma proof_of_mm_copy_forward_entail_wit_1_1 : mm_copy_forward_entail_wit_1_1.
Proof.
 unfold mm_copy_forward_entail_wit_1_1; intros; mm_addr.
 eapply derivable1_trans; [|apply derivable1_orp_intros1].
 Exists 0. rewrite mm_snapshot_zero. mm_finish.
Qed.

Lemma proof_of_mm_copy_forward_entail_wit_2_1 : mm_copy_forward_entail_wit_2_1.
Proof.
 unfold mm_copy_forward_entail_wit_2_1; left; intros; mm_addr.
 subst src dest remaining. unfold mm_lookup in PreH1.
 replace (n_pre-(n_pre-i_2)) with i_2 in * by ring.
 replace (n_pre-(n_pre-i_2-1)-1) with i_2 by ring.
 rewrite <- PreH1.
 rewrite (mm_forward_step m src_pre dest_pre n_pre i_2) by lia.
 Exists (i_2+1). mm_finish.
Qed.

Lemma proof_of_mm_copy_forward_return_wit_1 : mm_copy_forward_return_wit_1.
Proof.
 unfold mm_copy_forward_return_wit_1; left; intros; mm_addr.
 replace i with n_pre by lia. cancel.
Qed.

Lemma proof_of_mm_copy_forward_entail_wit_1_2 : mm_copy_forward_entail_wit_1_2.
Proof.
 unfold mm_copy_forward_entail_wit_1_2; intros; mm_addr.
 eapply derivable1_trans; [|apply derivable1_orp_intros2].
 Exists 0. rewrite mm_snapshot_zero. mm_finish.
Qed.

Lemma proof_of_mm_copy_forward_entail_wit_2_2 : mm_copy_forward_entail_wit_2_2.
Proof.
 unfold mm_copy_forward_entail_wit_2_2; left; intros; mm_addr.
 subst src dest remaining. unfold mm_lookup in PreH1.
 replace (n_pre-(n_pre-i_2)) with i_2 in * by ring.
 replace (n_pre-(n_pre-i_2-1)-1) with i_2 by ring.
 rewrite <- PreH1.
 rewrite (mm_forward_step m src_pre dest_pre n_pre i_2) by lia.
 Exists (i_2+1). mm_finish.
Qed.

Lemma proof_of_mm_copy_forward_return_wit_2 : mm_copy_forward_return_wit_2.
Proof.
 unfold mm_copy_forward_return_wit_2; left; intros; mm_addr.
 replace i with n_pre by lia. cancel.
Qed.

Lemma proof_of_mm_copy_backward_entail_wit_1 : mm_copy_backward_entail_wit_1.
Proof.
 unfold mm_copy_backward_entail_wit_1; left; intros; mm_addr.
 rewrite Z.sub_diag, mm_snapshot_zero. mm_finish.
Qed.

Lemma proof_of_mm_copy_backward_entail_wit_2 : mm_copy_backward_entail_wit_2.
Proof.
 unfold mm_copy_backward_entail_wit_2; left; intros; mm_addr.
 subst src dest. unfold mm_lookup in PreH1.
 replace (remaining-1+1) with remaining by ring.
 replace (src_pre+remaining+ -1) with (src_pre+remaining-1) in PreH1 by ring.
 replace (dest_pre+remaining+ -1) with (dest_pre+remaining-1) by ring.
 rewrite <- PreH1.
 rewrite (mm_backward_step m src_pre dest_pre n_pre remaining) by lia.
 mm_finish.
Qed.

Lemma proof_of_mm_copy_backward_return_wit_1 : mm_copy_backward_return_wit_1.
Proof.
 unfold mm_copy_backward_return_wit_1; left; intros; mm_addr.
 assert (remaining=0) by lia. subst remaining.
 rewrite !Z.add_0_r, Z.sub_0_r. cancel.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_1_pure : mm_copy_forward_partial_solve_wit_1_pure.
Proof.
 unfold mm_copy_forward_partial_solve_wit_1_pure; left; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 assert (Ready : mm_initialized (mm_snapshot m src_pre dest_pre i) (src_pre+i)).
 { destruct Hi as [v Hv]. exists v.
   rewrite (mm_forward_read m src_pre dest_pre n_pre i) by lia. exact Hv. }
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_1_aux : mm_copy_forward_partial_solve_wit_1_aux.
Proof.
 unfold mm_copy_forward_partial_solve_wit_1_aux; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 assert (Ready : mm_initialized (mm_snapshot m src_pre dest_pre i) (src_pre+i)).
 { destruct Hi as [v Hv]. exists v.
   rewrite (mm_forward_read m src_pre dest_pre n_pre i) by lia. exact Hv. }
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_1 : mm_copy_forward_partial_solve_wit_1.
Proof. intro; exact proof_of_mm_copy_forward_partial_solve_wit_1_aux. Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_2_pure : mm_copy_forward_partial_solve_wit_2_pure.
Proof.
 unfold mm_copy_forward_partial_solve_wit_2_pure; left; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 assert (Ready : mm_initialized (mm_snapshot m src_pre dest_pre i) (src_pre+i)).
 { destruct Hi as [v Hv]. exists v.
   rewrite (mm_forward_read m src_pre dest_pre n_pre i) by lia. exact Hv. }
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_2_aux : mm_copy_forward_partial_solve_wit_2_aux.
Proof.
 unfold mm_copy_forward_partial_solve_wit_2_aux; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 assert (Ready : mm_initialized (mm_snapshot m src_pre dest_pre i) (src_pre+i)).
 { destruct Hi as [v Hv]. exists v.
   rewrite (mm_forward_read m src_pre dest_pre n_pre i) by lia. exact Hv. }
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_2 : mm_copy_forward_partial_solve_wit_2.
Proof. intro; exact proof_of_mm_copy_forward_partial_solve_wit_2_aux. Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_3_pure : mm_copy_forward_partial_solve_wit_3_pure.
Proof.
 unfold mm_copy_forward_partial_solve_wit_3_pure; left; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i-1)-1) with i in * by ring.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_3_aux : mm_copy_forward_partial_solve_wit_3_aux.
Proof.
 unfold mm_copy_forward_partial_solve_wit_3_aux; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i-1)-1) with i in * by ring.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_3 : mm_copy_forward_partial_solve_wit_3.
Proof. intro; exact proof_of_mm_copy_forward_partial_solve_wit_3_aux. Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_4_pure : mm_copy_forward_partial_solve_wit_4_pure.
Proof.
 unfold mm_copy_forward_partial_solve_wit_4_pure; left; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i-1)-1) with i in * by ring.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_4_aux : mm_copy_forward_partial_solve_wit_4_aux.
Proof.
 unfold mm_copy_forward_partial_solve_wit_4_aux; intros; mm_addr.
 subst src dest remaining.
 replace (n_pre-(n_pre-i-1)-1) with i in * by ring.
 replace (n_pre-(n_pre-i)) with i in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H i ltac:(lia)) as (Hs & Hd & Hi) end.
 entailer!.
Qed.

Lemma proof_of_mm_copy_forward_partial_solve_wit_4 : mm_copy_forward_partial_solve_wit_4.
Proof. intro; exact proof_of_mm_copy_forward_partial_solve_wit_4_aux. Qed.

Lemma proof_of_mm_copy_backward_partial_solve_wit_1_pure : mm_copy_backward_partial_solve_wit_1_pure.
Proof.
 unfold mm_copy_backward_partial_solve_wit_1_pure; left; intros; mm_addr.
 subst src dest.
 replace (remaining-1+1) with remaining in * by ring.
 replace (src_pre+remaining+ -1) with (src_pre+(remaining-1)) in * by ring.
 replace (dest_pre+remaining+ -1) with (dest_pre+(remaining-1)) in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H (remaining-1) ltac:(lia)) as (Hs & Hd & Hi) end.
 assert (Ready : mm_initialized (mm_snapshot m (src_pre+remaining) (dest_pre+remaining) (n_pre-remaining)) (src_pre+(remaining-1))).
 { destruct Hi as [v Hv]. exists v.
   replace (src_pre+(remaining-1)) with (src_pre+remaining-1) in * by ring.
   rewrite mm_backward_read by lia. exact Hv. }
 entailer!.
Qed.

Lemma proof_of_mm_copy_backward_partial_solve_wit_1_aux : mm_copy_backward_partial_solve_wit_1_aux.
Proof.
 unfold mm_copy_backward_partial_solve_wit_1_aux; intros; mm_addr.
 subst src dest.
 replace (remaining-1+1) with remaining in * by ring.
 replace (src_pre+remaining+ -1) with (src_pre+(remaining-1)) in * by ring.
 replace (dest_pre+remaining+ -1) with (dest_pre+(remaining-1)) in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H (remaining-1) ltac:(lia)) as (Hs & Hd & Hi) end.
 assert (Ready : mm_initialized (mm_snapshot m (src_pre+remaining) (dest_pre+remaining) (n_pre-remaining)) (src_pre+(remaining-1))).
 { destruct Hi as [v Hv]. exists v.
   replace (src_pre+(remaining-1)) with (src_pre+remaining-1) in * by ring.
   rewrite mm_backward_read by lia. exact Hv. }
 entailer!.
Qed.

Lemma proof_of_mm_copy_backward_partial_solve_wit_1 : mm_copy_backward_partial_solve_wit_1.
Proof. intro; exact proof_of_mm_copy_backward_partial_solve_wit_1_aux. Qed.

Lemma proof_of_mm_copy_backward_partial_solve_wit_2_pure : mm_copy_backward_partial_solve_wit_2_pure.
Proof.
 unfold mm_copy_backward_partial_solve_wit_2_pure; left; intros; mm_addr.
 subst src dest.
 replace (remaining-1+1) with remaining in * by ring.
 replace (src_pre+remaining+ -1) with (src_pre+(remaining-1)) in * by ring.
 replace (dest_pre+remaining+ -1) with (dest_pre+(remaining-1)) in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H (remaining-1) ltac:(lia)) as (Hs & Hd & Hi) end.
 entailer!.
Qed.

Lemma proof_of_mm_copy_backward_partial_solve_wit_2_aux : mm_copy_backward_partial_solve_wit_2_aux.
Proof.
 unfold mm_copy_backward_partial_solve_wit_2_aux; intros; mm_addr.
 subst src dest.
 replace (remaining-1+1) with remaining in * by ring.
 replace (src_pre+remaining+ -1) with (src_pre+(remaining-1)) in * by ring.
 replace (dest_pre+remaining+ -1) with (dest_pre+(remaining-1)) in * by ring.
 match goal with H : mm_access _ _ _ _ _ _ _ _ |- _ =>
   pose proof (H (remaining-1) ltac:(lia)) as (Hs & Hd & Hi) end.
 entailer!.
Qed.

Lemma proof_of_mm_copy_backward_partial_solve_wit_2 : mm_copy_backward_partial_solve_wit_2.
Proof. intro; exact proof_of_mm_copy_backward_partial_solve_wit_2_aux. Qed.

Lemma proof_of_mm_copy_forward_default_entail_direction_spec : mm_copy_forward_default_entail_direction_spec.
Proof.
 unfold mm_copy_forward_default_entail_direction_spec; intros; Intros.
 Exists b1_direction_spec n1_direction_spec b2_direction_spec n2_direction_spec m_direction_spec.
 match goal with H : mm_forward_ok _ _ _ |- _ => destruct H as [Hdir|Hdir] end.
 - eapply derivable1_trans; [|apply derivable1_sepcon_mono; [apply derivable1_orp_intros1|reflexivity]].
   split_pure_spatial.
   + apply sepcon_cancel_res_emp. apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)). entailer!.
   + split_pures; dump_pre_spatial; auto.
 - eapply derivable1_trans; [|apply derivable1_sepcon_mono; [apply derivable1_orp_intros2|reflexivity]].
   split_pure_spatial.
   + apply sepcon_cancel_res_emp. apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)). entailer!.
   + split_pures; dump_pre_spatial; auto; rewrite sizeof_uchar; lia.
Qed.
