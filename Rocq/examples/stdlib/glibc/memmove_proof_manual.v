From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import memmove_goal memmove_contract_lib memmove_loops_proof_manual.
Import Snaive_C_Rules64.
Local Open Scope sac.
Ltac mm_addr := repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *.

Lemma proof_of_memmove_safety_wit_1 : memmove_safety_wit_1.
Proof. unfold memmove_safety_wit_1; intros; entailer!. Qed.

Lemma proof_of_memmove_safety_wit_2 : memmove_safety_wit_2.
Proof. unfold memmove_safety_wit_2; intros; entailer!. Qed.

Lemma proof_of_memmove_safety_wit_3 : memmove_safety_wit_3.
Proof. unfold memmove_safety_wit_3; intros; entailer!. Qed.

Lemma proof_of_memmove_return_wit_1 : memmove_return_wit_1.
Proof. unfold memmove_return_wit_1; intros; entailer!. Qed.

Lemma proof_of_memmove_return_wit_2 : memmove_return_wit_2.
Proof. unfold memmove_return_wit_2; intros; entailer!. Qed.

Lemma proof_of_memmove_return_wit_3 : memmove_return_wit_3.
Proof. unfold memmove_return_wit_3; left; intros; subst n_pre; rewrite mm_snapshot_zero; entailer!. Qed.

Lemma proof_of_memmove_return_wit_4 : memmove_return_wit_4.
Proof. unfold memmove_return_wit_4; left; intros; subst n_pre; rewrite mm_snapshot_zero; entailer!. Qed.

Lemma proof_of_memmove_partial_solve_wit_1_pure : memmove_partial_solve_wit_1_pure.
Proof.
 unfold memmove_partial_solve_wit_1_pure; left; intros; mm_addr.
 assert (Hd : mm_forward_ok src_pre dest_pre n_pre) by (apply mm_direction_forward; try assumption; try lia).
 entailer!.
Qed.

Lemma proof_of_memmove_partial_solve_wit_1 : memmove_partial_solve_wit_1.
Proof. unfold memmove_partial_solve_wit_1, memmove_partial_solve_wit_1_aux; intros; mm_addr.
 assert (Hd : mm_forward_ok src_pre dest_pre n_pre) by (apply (mm_direction_forward src_pre dest_pre n_pre); try assumption; try lia).
 entailer!. Qed.

Lemma proof_of_memmove_partial_solve_wit_2_pure : memmove_partial_solve_wit_2_pure.
Proof.
 unfold memmove_partial_solve_wit_2_pure; left; intros; mm_addr.
 assert (Hd : src_pre<=dest_pre) by (apply (mm_direction_backward src_pre dest_pre n_pre); try assumption; try lia).
 entailer!.
Qed.

Lemma proof_of_memmove_partial_solve_wit_2 : memmove_partial_solve_wit_2.
Proof. unfold memmove_partial_solve_wit_2, memmove_partial_solve_wit_2_aux; intros; mm_addr.
 assert (Hd : src_pre<=dest_pre) by (apply (mm_direction_backward src_pre dest_pre n_pre); try assumption; try lia).
 entailer!. Qed.

Lemma proof_of_memmove_byte_memory_spec_entail_empty_copy : memmove_byte_memory_spec_entail_empty_copy.
Proof.
 unfold memmove_byte_memory_spec_entail_empty_copy; intros; Intros; subst n_pre.
 Exists 0 0 0 0 (fun _ : Z => @None Z).
 eapply derivable1_trans; [|apply derivable1_sepcon_mono; [apply derivable1_orp_intros1|reflexivity]].
 rewrite !mm_cells_empty, !UCharArray.mixed_full_empty.
 split_pure_spatial.
 - Intros_r retval.
   apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)); rewrite !UCharArray.mixed_full_empty; entailer!.
 - split_pures; dump_pre_spatial; auto; unfold mm_separated, mm_access; intros; try lia; auto.
Qed.

Lemma proof_of_memmove_byte_memory_spec_entail_same_range : memmove_byte_memory_spec_entail_same_range.
Proof.
 unfold memmove_byte_memory_spec_entail_same_range; intros; Intros; subst dest_pre.
 Exists src_pre n_pre 0 0 (mm_initial src_pre xs_same_range).
 eapply derivable1_trans; [|apply derivable1_sepcon_mono; [apply derivable1_orp_intros2|reflexivity]].
 rewrite !mm_cells_empty, !UCharArray.mixed_full_empty.
 split_pure_spatial.
 - apply sepcon_cancel_end.
   + sep_apply (mm_heap_initial src_pre n_pre xs_same_range ltac:(lia) ltac:(lia)); entailer!.
   + Intros_r retval. apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)); rewrite !UCharArray.mixed_full_empty; Intros.
     sep_apply (mm_snapshot_target src_pre src_pre n_pre xs_same_range ltac:(lia) ltac:(lia)); entailer!.
 - split_pures; dump_pre_spatial; auto; try lia.
   + unfold mm_separated; auto.
   + unfold mm_access, mm_in, mm_initialized. intros i Hi. repeat split; try (left; lia).
     exists (Znth i xs_same_range 0). apply mm_initial_inside; lia.
Qed.

Lemma proof_of_memmove_byte_memory_spec_entail_left_overlap : memmove_byte_memory_spec_entail_left_overlap.
Proof.
 unfold memmove_byte_memory_spec_entail_left_overlap; intros; Intros; mm_addr.
 rename xs_left_overlap into xs; rename h_left_overlap into h.
 subst src_pre.
 Exists dest_pre (n_pre+h) 0 0 (mm_initial (dest_pre+h) xs).
 eapply derivable1_trans; [|apply derivable1_sepcon_mono; [apply derivable1_orp_intros2|reflexivity]].
 rewrite !mm_cells_empty, !UCharArray.mixed_full_empty.
 split_pure_spatial.
 - apply sepcon_cancel_end.
   + sep_apply (mm_heap_initial (dest_pre+h) n_pre xs ltac:(lia) ltac:(lia)).
     sep_apply (mm_heap_undef (dest_pre+h) xs dest_pre h ltac:(lia) ltac:(lia)).
     replace n_pre with (n_pre+h-h) at 1 2 by ring.
     sep_apply (mm_heap_merge dest_pre (n_pre+h) h (mm_initial (dest_pre+h) xs) ltac:(lia)); entailer!.
   + Intros_r retval. apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)).
     rewrite !UCharArray.mixed_full_empty. Intros.
     sep_apply (mm_heap_split dest_pre (n_pre+h) n_pre (mm_snapshot (mm_initial (dest_pre+h) xs) (dest_pre+h) dest_pre n_pre) ltac:(lia)).
     sep_apply (mm_snapshot_target (dest_pre+h) dest_pre n_pre xs ltac:(lia) ltac:(lia)).
     replace (n_pre+h-n_pre) with h by ring.
     pose proof (mm_snapshot_source_slice (dest_pre+h) dest_pre n_pre xs (n_pre-h) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as E.
     replace (dest_pre+h+(n_pre-h)) with (dest_pre+n_pre) in E by ring.
     replace (n_pre-(n_pre-h)) with h in E by ring.
     sep_apply E. entailer!.
 - split_pures; dump_pre_spatial; auto; try lia.
   + unfold mm_separated; auto.
   + unfold mm_access, mm_in, mm_initialized. intros i Hi. repeat split; try (left; lia).
     exists (Znth i xs 0). apply mm_initial_inside; lia.
Qed.

Lemma proof_of_memmove_byte_memory_spec_entail_right_overlap : memmove_byte_memory_spec_entail_right_overlap.
Proof.
 unfold memmove_byte_memory_spec_entail_right_overlap; intros; Intros; mm_addr.
 rename xs_right_overlap into xs; rename h_right_overlap into h.
 subst dest_pre.
 Exists src_pre (n_pre+h) 0 0 (mm_initial src_pre xs).
 eapply derivable1_trans; [|apply derivable1_sepcon_mono; [apply derivable1_orp_intros2|reflexivity]].
 rewrite !mm_cells_empty, !UCharArray.mixed_full_empty.
 split_pure_spatial.
 - apply sepcon_cancel_end.
   + sep_apply (mm_heap_initial src_pre n_pre xs ltac:(lia) ltac:(lia)).
     sep_apply (mm_heap_undef src_pre xs (src_pre+n_pre) h ltac:(lia) ltac:(lia)).
     replace h with (n_pre+h-n_pre) at 1 2 by ring.
     sep_apply (mm_heap_merge src_pre (n_pre+h) n_pre (mm_initial src_pre xs) ltac:(lia)); entailer!.
   + Intros_r retval. apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)).
     rewrite !UCharArray.mixed_full_empty. Intros.
     sep_apply (mm_heap_split src_pre (n_pre+h) h (mm_snapshot (mm_initial src_pre xs) src_pre (src_pre+h) n_pre) ltac:(lia)).
     replace (n_pre+h-h) with n_pre by ring.
     sep_apply (mm_snapshot_target src_pre (src_pre+h) n_pre xs ltac:(lia) ltac:(lia)).
     pose proof (mm_snapshot_source_slice src_pre (src_pre+h) n_pre xs 0 h ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as E.
     rewrite Z.add_0_r, Z.sub_0_r in E. sep_apply E. entailer!.
 - split_pures; dump_pre_spatial; auto; try lia.
   + unfold mm_separated; auto.
   + unfold mm_access, mm_in, mm_initialized. intros i Hi. repeat split; try (left; lia).
     exists (Znth i xs 0). apply mm_initial_inside; lia.
Qed.

Lemma proof_of_memmove_byte_memory_spec_entail_separated : memmove_byte_memory_spec_entail_separated.
Proof.
 unfold memmove_byte_memory_spec_entail_separated; intros; Intros; mm_addr.
 rename xs_separated into xs.
 sep_apply (mm_full_disjoint src_pre dest_pre n_pre xs). Intros.
 assert (Hdisj : src_pre+n_pre<=dest_pre \/ dest_pre+n_pre<=src_pre).
 { match goal with H : mm_separated _ _ _ _ |- _ => unfold mm_separated in H end. lia. }
 Exists src_pre n_pre dest_pre n_pre (mm_initial src_pre xs).
 eapply derivable1_trans; [|apply derivable1_sepcon_mono; [apply derivable1_orp_intros2|reflexivity]].
 split_pure_spatial.
 - apply sepcon_cancel_end.
   + sep_apply (mm_heap_initial src_pre n_pre xs ltac:(lia) ltac:(lia)).
     sep_apply (mm_heap_undef src_pre xs dest_pre n_pre ltac:(lia) ltac:(lia)); entailer!.
   + Intros_r retval. apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)). Intros.
     sep_apply (mm_snapshot_target src_pre dest_pre n_pre xs ltac:(lia) ltac:(lia)).
     pose proof (mm_snapshot_source_slice src_pre dest_pre n_pre xs 0 n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as E.
     rewrite Z.add_0_r, Z.sub_0_r, sublist_self in E by lia. sep_apply E. entailer!.
 - split_pures; dump_pre_spatial; auto; try lia.
   unfold mm_access, mm_in, mm_initialized. intros i Hi. repeat split; try (left; lia); try (right; lia).
   exists (Znth i xs 0). apply mm_initial_inside; lia.
Qed.

Lemma proof_of_mm_copy_forward_default_entail_direction_spec :
 memmove_goal.mm_copy_forward_default_entail_direction_spec.
Proof. exact memmove_loops_proof_manual.proof_of_mm_copy_forward_default_entail_direction_spec. Qed.
