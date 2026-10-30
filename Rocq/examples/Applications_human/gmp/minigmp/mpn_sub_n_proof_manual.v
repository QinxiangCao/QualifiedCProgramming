From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_sub_n_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_sub_n_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_1 : mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_2 : mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_3 : mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_rp_eq_ap : mpn_sub_n_entail_wit_1_rp_eq_ap.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_1_rp_eq_ap_split_goal_2.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_1 : mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_2 : mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_3 : mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_rp_eq_bp : mpn_sub_n_entail_wit_2_rp_eq_bp.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_2_rp_eq_bp_split_goal_2.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_non_alias_split_goal_1 : mpn_sub_n_entail_wit_3_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_non_alias_split_goal_2 : mpn_sub_n_entail_wit_3_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_non_alias_split_goal_3 : mpn_sub_n_entail_wit_3_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_3_non_alias : mpn_sub_n_entail_wit_3_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_3_non_alias_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_3_non_alias_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_1_rp_eq_ap : mpn_sub_n_entail_wit_4_1_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(lia).
  replace (i-i) with 0 in * by lia.
  rewrite Znth_sublist in * by lia.
  replace (0+i) with i in * by lia.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hb.
  assert (Hscalar : (forall a b c u v,
  0 <= a < UINT_MOD -> 0 <= b < UINT_MOD -> 0 <= c <= 2 ->
  (u = 0 /\ c <= IntLib.unsigned_last_nbits (b+c) 32 \/
   u = 1 /\ IntLib.unsigned_last_nbits (b+c) 32 < c) ->
  (v = 0 /\ IntLib.unsigned_last_nbits (b+c) 32 <= a \/
   v = 1 /\ a < IntLib.unsigned_last_nbits (b+c) 32) ->
  0 <= IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 < UINT_MOD /\
  IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 - (u+v)*UINT_MOD = a-b-c)%Z).
{

  intros a b c u v Hsa Hsb Hc Hu Hv.
  unfold IntLib.unsigned_last_nbits in *.
  change (2^32) with UINT_MOD in *.
  assert (Ht : 0 <= (b+c) mod UINT_MOD < UINT_MOD) by (apply Z.mod_pos_bound; exact UINT_MOD_pos).
  assert (He : (b+c) mod UINT_MOD = b+c-u*UINT_MOD).
  { destruct (Z_lt_ge_dec (b+c) UINT_MOD) as [Hlo|Hhi].
    - rewrite Z.mod_small in * by lia. destruct Hu as [[-> ?]|[-> ?]]; lia.
    - assert (E : (b+c) mod UINT_MOD = b+c-UINT_MOD).
      { replace (b+c) with ((b+c-UINT_MOD)+1*UINT_MOD) at 1 by ring.
        rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
        apply Z.mod_small. unfold UINT_MOD in *; lia. }
      rewrite E in *. destruct Hu as [[-> ?]|[-> ?]]; unfold UINT_MOD in *; lia. }
  split; [apply Z.mod_pos_bound; exact UINT_MOD_pos|].
  destruct Hv as [[-> Hv]|[-> Hv]].
  - rewrite Z.mod_small by lia. lia.
  - assert (E : (a - (b+c) mod UINT_MOD) mod UINT_MOD = a - (b+c) mod UINT_MOD + UINT_MOD).
    { replace (a - (b+c) mod UINT_MOD) with
        ((a - (b+c) mod UINT_MOD + UINT_MOD) + (-1)*UINT_MOD) at 1 by ring.
      rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
      apply Z.mod_small; lia. }
    rewrite E. lia.
}
  pose proof (Hscalar (Znth i l_a 0) (Znth i l_b 0) cy 0 0
    Ha Hb ltac:(lia) ltac:(left; split; lia) ltac:(left; split; lia)) as [Hr Hstep].
  assert (Ht : 0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32) by (pose proof (unsigned_Lastnbits_range (Znth i l_b 0 + cy) 32 ltac:(lia)); lia).
  assert (E : unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 = Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) by (unfold unsigned_last_nbits at 1; apply Z.mod_small; change (2^32) with UINT_MOD; lia).
  rewrite E in Hr, Hstep.
  set (r := (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32)) in *.
  assert (Hinv : list_to_Z UINT_MOD (l_r_2++[r]) - (0+0)*UINT_MOD^(i+1) =
    list_to_Z UINT_MOD (sublist 0 (i+1) l_a)-list_to_Z UINT_MOD (sublist 0 (i+1) l_b)).
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_single, PreH17.
    rewrite !list_to_Z_list_append by (try exact UINT_MOD_pos; try assumption; lia).
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r, PreH13, PreH11, PreH12. nia. }
  Exists (list_to_Z UINT_MOD (l_r_2++[r])) (l_r_2++[r])
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_b))
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_a)).
  split_pure_spatial.
  - rewrite replace_Znth_sublist_head by lia.
    sep_apply (UIntArray.seg_split_to_seg rp_pre i (i+1) (Zlength l_a)
      (r :: sublist (i+1) (Zlength l_a) l_a) ltac:(lia)).
    replace (i+1-i) with 1 by lia.
    rewrite sublist_cons_head.
    assert (Hlen : Zlength (r :: sublist (i+1) (Zlength l_a) l_a) = Zlength l_a-i).
    { rewrite Zlength_cons, Zlength_sublist by lia; lia. }
    rewrite <- Hlen, sublist_cons_tail_all.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 i (i+1) l_r_2 [r] ltac:(lia)).
    rewrite PreH4. cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + apply list_within_bound_app_single; assumption.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_2_rp_eq_ap : mpn_sub_n_entail_wit_4_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(lia).
  replace (i-i) with 0 in * by lia.
  rewrite Znth_sublist in * by lia.
  replace (0+i) with i in * by lia.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hb.
  assert (Hscalar : (forall a b c u v,
  0 <= a < UINT_MOD -> 0 <= b < UINT_MOD -> 0 <= c <= 2 ->
  (u = 0 /\ c <= IntLib.unsigned_last_nbits (b+c) 32 \/
   u = 1 /\ IntLib.unsigned_last_nbits (b+c) 32 < c) ->
  (v = 0 /\ IntLib.unsigned_last_nbits (b+c) 32 <= a \/
   v = 1 /\ a < IntLib.unsigned_last_nbits (b+c) 32) ->
  0 <= IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 < UINT_MOD /\
  IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 - (u+v)*UINT_MOD = a-b-c)%Z).
{

  intros a b c u v Hsa Hsb Hc Hu Hv.
  unfold IntLib.unsigned_last_nbits in *.
  change (2^32) with UINT_MOD in *.
  assert (Ht : 0 <= (b+c) mod UINT_MOD < UINT_MOD) by (apply Z.mod_pos_bound; exact UINT_MOD_pos).
  assert (He : (b+c) mod UINT_MOD = b+c-u*UINT_MOD).
  { destruct (Z_lt_ge_dec (b+c) UINT_MOD) as [Hlo|Hhi].
    - rewrite Z.mod_small in * by lia. destruct Hu as [[-> ?]|[-> ?]]; lia.
    - assert (E : (b+c) mod UINT_MOD = b+c-UINT_MOD).
      { replace (b+c) with ((b+c-UINT_MOD)+1*UINT_MOD) at 1 by ring.
        rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
        apply Z.mod_small. unfold UINT_MOD in *; lia. }
      rewrite E in *. destruct Hu as [[-> ?]|[-> ?]]; unfold UINT_MOD in *; lia. }
  split; [apply Z.mod_pos_bound; exact UINT_MOD_pos|].
  destruct Hv as [[-> Hv]|[-> Hv]].
  - rewrite Z.mod_small by lia. lia.
  - assert (E : (a - (b+c) mod UINT_MOD) mod UINT_MOD = a - (b+c) mod UINT_MOD + UINT_MOD).
    { replace (a - (b+c) mod UINT_MOD) with
        ((a - (b+c) mod UINT_MOD + UINT_MOD) + (-1)*UINT_MOD) at 1 by ring.
      rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
      apply Z.mod_small; lia. }
    rewrite E. lia.
}
  pose proof (Hscalar (Znth i l_a 0) (Znth i l_b 0) cy 0 1
    Ha Hb ltac:(lia) ltac:(left; split; lia) ltac:(right; split; lia)) as [Hr Hstep].
  
  set (r := (unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32)) in *.
  assert (Hinv : list_to_Z UINT_MOD (l_r_2++[r]) - (0+1)*UINT_MOD^(i+1) =
    list_to_Z UINT_MOD (sublist 0 (i+1) l_a)-list_to_Z UINT_MOD (sublist 0 (i+1) l_b)).
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_single, PreH17.
    rewrite !list_to_Z_list_append by (try exact UINT_MOD_pos; try assumption; lia).
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r, PreH13, PreH11, PreH12. nia. }
  Exists (list_to_Z UINT_MOD (l_r_2++[r])) (l_r_2++[r])
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_b))
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_a)).
  split_pure_spatial.
  - rewrite replace_Znth_sublist_head by lia.
    sep_apply (UIntArray.seg_split_to_seg rp_pre i (i+1) (Zlength l_a)
      (r :: sublist (i+1) (Zlength l_a) l_a) ltac:(lia)).
    replace (i+1-i) with 1 by lia.
    rewrite sublist_cons_head.
    assert (Hlen : Zlength (r :: sublist (i+1) (Zlength l_a) l_a) = Zlength l_a-i).
    { rewrite Zlength_cons, Zlength_sublist by lia; lia. }
    rewrite <- Hlen, sublist_cons_tail_all.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 i (i+1) l_r_2 [r] ltac:(lia)).
    rewrite PreH4. cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + apply list_within_bound_app_single; assumption.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_3_rp_eq_ap : mpn_sub_n_entail_wit_4_3_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(lia).
  replace (i-i) with 0 in * by lia.
  rewrite Znth_sublist in * by lia.
  replace (0+i) with i in * by lia.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hb.
  assert (Hscalar : (forall a b c u v,
  0 <= a < UINT_MOD -> 0 <= b < UINT_MOD -> 0 <= c <= 2 ->
  (u = 0 /\ c <= IntLib.unsigned_last_nbits (b+c) 32 \/
   u = 1 /\ IntLib.unsigned_last_nbits (b+c) 32 < c) ->
  (v = 0 /\ IntLib.unsigned_last_nbits (b+c) 32 <= a \/
   v = 1 /\ a < IntLib.unsigned_last_nbits (b+c) 32) ->
  0 <= IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 < UINT_MOD /\
  IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 - (u+v)*UINT_MOD = a-b-c)%Z).
{

  intros a b c u v Hsa Hsb Hc Hu Hv.
  unfold IntLib.unsigned_last_nbits in *.
  change (2^32) with UINT_MOD in *.
  assert (Ht : 0 <= (b+c) mod UINT_MOD < UINT_MOD) by (apply Z.mod_pos_bound; exact UINT_MOD_pos).
  assert (He : (b+c) mod UINT_MOD = b+c-u*UINT_MOD).
  { destruct (Z_lt_ge_dec (b+c) UINT_MOD) as [Hlo|Hhi].
    - rewrite Z.mod_small in * by lia. destruct Hu as [[-> ?]|[-> ?]]; lia.
    - assert (E : (b+c) mod UINT_MOD = b+c-UINT_MOD).
      { replace (b+c) with ((b+c-UINT_MOD)+1*UINT_MOD) at 1 by ring.
        rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
        apply Z.mod_small. unfold UINT_MOD in *; lia. }
      rewrite E in *. destruct Hu as [[-> ?]|[-> ?]]; unfold UINT_MOD in *; lia. }
  split; [apply Z.mod_pos_bound; exact UINT_MOD_pos|].
  destruct Hv as [[-> Hv]|[-> Hv]].
  - rewrite Z.mod_small by lia. lia.
  - assert (E : (a - (b+c) mod UINT_MOD) mod UINT_MOD = a - (b+c) mod UINT_MOD + UINT_MOD).
    { replace (a - (b+c) mod UINT_MOD) with
        ((a - (b+c) mod UINT_MOD + UINT_MOD) + (-1)*UINT_MOD) at 1 by ring.
      rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
      apply Z.mod_small; lia. }
    rewrite E. lia.
}
  pose proof (Hscalar (Znth i l_a 0) (Znth i l_b 0) cy 1 0
    Ha Hb ltac:(lia) ltac:(right; split; lia) ltac:(left; split; lia)) as [Hr Hstep].
  assert (Ht : 0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32) by (pose proof (unsigned_Lastnbits_range (Znth i l_b 0 + cy) 32 ltac:(lia)); lia).
  assert (E : unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 = Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) by (unfold unsigned_last_nbits at 1; apply Z.mod_small; change (2^32) with UINT_MOD; lia).
  rewrite E in Hr, Hstep.
  set (r := (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32)) in *.
  assert (Hinv : list_to_Z UINT_MOD (l_r_2++[r]) - (1+0)*UINT_MOD^(i+1) =
    list_to_Z UINT_MOD (sublist 0 (i+1) l_a)-list_to_Z UINT_MOD (sublist 0 (i+1) l_b)).
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_single, PreH17.
    rewrite !list_to_Z_list_append by (try exact UINT_MOD_pos; try assumption; lia).
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r, PreH13, PreH11, PreH12. nia. }
  Exists (list_to_Z UINT_MOD (l_r_2++[r])) (l_r_2++[r])
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_b))
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_a)).
  split_pure_spatial.
  - rewrite replace_Znth_sublist_head by lia.
    sep_apply (UIntArray.seg_split_to_seg rp_pre i (i+1) (Zlength l_a)
      (r :: sublist (i+1) (Zlength l_a) l_a) ltac:(lia)).
    replace (i+1-i) with 1 by lia.
    rewrite sublist_cons_head.
    assert (Hlen : Zlength (r :: sublist (i+1) (Zlength l_a) l_a) = Zlength l_a-i).
    { rewrite Zlength_cons, Zlength_sublist by lia; lia. }
    rewrite <- Hlen, sublist_cons_tail_all.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 i (i+1) l_r_2 [r] ltac:(lia)).
    rewrite PreH4. cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + apply list_within_bound_app_single; assumption.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_4_4_rp_eq_ap : mpn_sub_n_entail_wit_4_4_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(lia).
  replace (i-i) with 0 in * by lia.
  rewrite Znth_sublist in * by lia.
  replace (0+i) with i in * by lia.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hb.
  assert (Hscalar : (forall a b c u v,
  0 <= a < UINT_MOD -> 0 <= b < UINT_MOD -> 0 <= c <= 2 ->
  (u = 0 /\ c <= IntLib.unsigned_last_nbits (b+c) 32 \/
   u = 1 /\ IntLib.unsigned_last_nbits (b+c) 32 < c) ->
  (v = 0 /\ IntLib.unsigned_last_nbits (b+c) 32 <= a \/
   v = 1 /\ a < IntLib.unsigned_last_nbits (b+c) 32) ->
  0 <= IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 < UINT_MOD /\
  IntLib.unsigned_last_nbits (a-IntLib.unsigned_last_nbits (b+c) 32) 32 - (u+v)*UINT_MOD = a-b-c)%Z).
{

  intros a b c u v Hsa Hsb Hc Hu Hv.
  unfold IntLib.unsigned_last_nbits in *.
  change (2^32) with UINT_MOD in *.
  assert (Ht : 0 <= (b+c) mod UINT_MOD < UINT_MOD) by (apply Z.mod_pos_bound; exact UINT_MOD_pos).
  assert (He : (b+c) mod UINT_MOD = b+c-u*UINT_MOD).
  { destruct (Z_lt_ge_dec (b+c) UINT_MOD) as [Hlo|Hhi].
    - rewrite Z.mod_small in * by lia. destruct Hu as [[-> ?]|[-> ?]]; lia.
    - assert (E : (b+c) mod UINT_MOD = b+c-UINT_MOD).
      { replace (b+c) with ((b+c-UINT_MOD)+1*UINT_MOD) at 1 by ring.
        rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
        apply Z.mod_small. unfold UINT_MOD in *; lia. }
      rewrite E in *. destruct Hu as [[-> ?]|[-> ?]]; unfold UINT_MOD in *; lia. }
  split; [apply Z.mod_pos_bound; exact UINT_MOD_pos|].
  destruct Hv as [[-> Hv]|[-> Hv]].
  - rewrite Z.mod_small by lia. lia.
  - assert (E : (a - (b+c) mod UINT_MOD) mod UINT_MOD = a - (b+c) mod UINT_MOD + UINT_MOD).
    { replace (a - (b+c) mod UINT_MOD) with
        ((a - (b+c) mod UINT_MOD + UINT_MOD) + (-1)*UINT_MOD) at 1 by ring.
      rewrite Z.mod_add by (pose proof UINT_MOD_pos; lia).
      apply Z.mod_small; lia. }
    rewrite E. lia.
}
  pose proof (Hscalar (Znth i l_a 0) (Znth i l_b 0) cy 1 1
    Ha Hb ltac:(lia) ltac:(right; split; lia) ltac:(right; split; lia)) as [Hr Hstep].
  
  set (r := (unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32)) in *.
  assert (Hinv : list_to_Z UINT_MOD (l_r_2++[r]) - (1+1)*UINT_MOD^(i+1) =
    list_to_Z UINT_MOD (sublist 0 (i+1) l_a)-list_to_Z UINT_MOD (sublist 0 (i+1) l_b)).
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_single, PreH17.
    rewrite !list_to_Z_list_append by (try exact UINT_MOD_pos; try assumption; lia).
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r, PreH13, PreH11, PreH12. nia. }
  Exists (list_to_Z UINT_MOD (l_r_2++[r])) (l_r_2++[r])
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_b))
    (list_to_Z UINT_MOD (sublist 0 (i+1) l_a)).
  split_pure_spatial.
  - rewrite replace_Znth_sublist_head by lia.
    sep_apply (UIntArray.seg_split_to_seg rp_pre i (i+1) (Zlength l_a)
      (r :: sublist (i+1) (Zlength l_a) l_a) ltac:(lia)).
    replace (i+1-i) with 1 by lia.
    rewrite sublist_cons_head.
    assert (Hlen : Zlength (r :: sublist (i+1) (Zlength l_a) l_a) = Zlength l_a-i).
    { rewrite Zlength_cons, Zlength_sublist by lia; lia. }
    rewrite <- Hlen, sublist_cons_tail_all.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 i (i+1) l_r_2 [r] ltac:(lia)).
    rewrite PreH4. cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + apply list_within_bound_app_single; assumption.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_5_1_rp_eq_bp : mpn_sub_n_entail_wit_5_1_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *. apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  set (out := Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. rewrite Hulb_eq. unfold UINT_MOD in *. lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
      rewrite (sublist_single 0 i l_a); try lia.
      rewrite list_to_Z_concat; try lia; try tauto.
      rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist; try lia.
      replace (i - 0) with i by lia. unfold UINT_MOD. ring.
      all: try (apply list_within_bound_sublist; try lia; try tauto).
      all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr. ring.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_5_2_rp_eq_bp : mpn_sub_n_entail_wit_5_2_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *. apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  set (out := unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. split; [| tauto].
    unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    assert (Hdiff_neg: Znth i l_a 0 - (Znth i l_b 0 + cy) < 0) by lia.
    assert (Hdiff_bound: -4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy)) by lia.
    assert (Hmod_eq:
      (Znth i l_a 0 - (Znth i l_b 0 + cy)) mod 2 ^ 32 =
      Znth i l_a 0 - (Znth i l_b 0 + cy) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1); [left; lia | ring]. }
    unfold unsigned_last_nbits.
    try rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_5_3_rp_eq_bp : mpn_sub_n_entail_wit_5_3_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso.
      assert (Hulb_small: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy).
      { apply Z.mod_small; lia. }
      lia.
    - lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32); lia. }
  set (out := Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. rewrite Hulb_eq. unfold UINT_MOD in *. lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_5_4_rp_eq_bp : mpn_sub_n_entail_wit_5_4_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH16) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH15) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso.
      assert (Hulb_small: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy).
      { apply Z.mod_small; lia. }
      lia.
    - lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32); lia. }
  set (out := unsigned_last_nbits
    (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i)
    (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. split; [| tauto].
    unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]]. }
  rewrite Hreplace_tail.
  rewrite PreH4.
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg bp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg bp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
  + repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
    - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_a); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH11.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite (sublist_split 0 (i + 1) i); try lia.
    rewrite (sublist_single 0 i l_b); try lia.
    rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia. unfold UINT_MOD. ring.
    all: try (apply list_within_bound_sublist; try lia; try tauto).
    all: try (simpl; split; try tauto).
  - rewrite list_to_Z_concat; try lia; try tauto.
    rewrite PreH13.
    rewrite list_to_Z_cons, list_to_Z_nil.
    try rewrite PreH17.
    unfold UINT_MOD. ring.
  - apply list_within_bound_concat; try tauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold UINT_MOD in *.
    subst out. try rewrite PreH17. try rewrite Hulb_eq.
    assert (Hvr: val_r_2 = val_a_prefix_2 - val_b_prefix_2 + cy * 4294967296 ^ i) by lia.
    try rewrite Hvr.
    assert (Hdiff_neg:
      Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) < 0) by lia.
    assert (Hdiff_bound:
      -4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) by lia.
    assert (Hmod_eq:
      (Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) mod 2 ^ 32 =
      Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1); [left; lia | ring]. }
    unfold unsigned_last_nbits.
    try rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_1_non_alias_split_goal_1 : mpn_sub_n_entail_wit_6_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  assert (Hcarry : unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { apply unsigned_last_nbits_eq.
    pose proof (ulb_ge_cy_implies_no_overflow (Znth i l_b 0) cy Hb ltac:(lia) PreH2).
    change (2^32) with UINT_MOD in *. lia. }
  rewrite list_to_Z_concat_r by (try exact UINT_MOD_pos; lia).
  rewrite PreH10.
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_a i ltac:(lia) PreH11).
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_b i ltac:(lia) PreH12).
  rewrite Z.pow_add_r by lia. change (UINT_MOD ^ 1) with UINT_MOD.
  nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_1_non_alias_split_goal_2 : mpn_sub_n_entail_wit_6_1_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  apply list_within_bound_app_single; [exact PreH13|].
  lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_1_non_alias_split_goal_3 : mpn_sub_n_entail_wit_6_1_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_1_non_alias : mpn_sub_n_entail_wit_6_1_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_1_non_alias_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_1_non_alias_split_goal_2.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_1_non_alias_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_2_non_alias_split_goal_1 : mpn_sub_n_entail_wit_6_2_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  assert (Hcarry : unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { apply unsigned_last_nbits_eq.
    pose proof (ulb_ge_cy_implies_no_overflow (Znth i l_b 0) cy Hb ltac:(lia) PreH2).
    change (2^32) with UINT_MOD in *. lia. }
  assert (Hr : unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 = Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32 + UINT_MOD).
  { unfold unsigned_last_nbits at 1. change (2^32) with UINT_MOD.
    symmetry. apply Z.mod_unique with (q := -1); [left; lia|ring]. }
  rewrite list_to_Z_concat_r by (try exact UINT_MOD_pos; lia).
  rewrite PreH10.
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_a i ltac:(lia) PreH11).
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_b i ltac:(lia) PreH12).
  rewrite Z.pow_add_r by lia. change (UINT_MOD ^ 1) with UINT_MOD.
  nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_2_non_alias_split_goal_2 : mpn_sub_n_entail_wit_6_2_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  apply list_within_bound_app_single; [exact PreH13|].
  unfold unsigned_last_nbits at 1. change (2^32) with UINT_MOD.
  apply Z.mod_pos_bound. exact UINT_MOD_pos.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_2_non_alias_split_goal_3 : mpn_sub_n_entail_wit_6_2_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_2_non_alias : mpn_sub_n_entail_wit_6_2_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_2_non_alias_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_2_non_alias_split_goal_2.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_2_non_alias_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_3_non_alias_split_goal_1 : mpn_sub_n_entail_wit_6_3_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  assert (Hover : UINT_MOD <= Znth i l_b 0 + cy).
  { destruct (Z_lt_dec (Znth i l_b 0 + cy) UINT_MOD); [|lia].
    rewrite unsigned_last_nbits_eq in PreH2 by (change (2^32) with UINT_MOD; lia). lia. }
  assert (Hcarry : unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { apply unsigned_last_nbits_overflow_32. change UINT_MOD with 4294967296 in *. lia. }
  rewrite list_to_Z_concat_r by (try exact UINT_MOD_pos; lia).
  rewrite PreH10.
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_a i ltac:(lia) PreH11).
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_b i ltac:(lia) PreH12).
  rewrite Z.pow_add_r by lia. change (UINT_MOD ^ 1) with UINT_MOD.
  nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_3_non_alias_split_goal_2 : mpn_sub_n_entail_wit_6_3_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  apply list_within_bound_app_single; [exact PreH13|].
  lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_3_non_alias_split_goal_3 : mpn_sub_n_entail_wit_6_3_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_3_non_alias : mpn_sub_n_entail_wit_6_3_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_3_non_alias_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_3_non_alias_split_goal_2.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_3_non_alias_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_4_non_alias_split_goal_1 : mpn_sub_n_entail_wit_6_4_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  assert (Hover : UINT_MOD <= Znth i l_b 0 + cy).
  { destruct (Z_lt_dec (Znth i l_b 0 + cy) UINT_MOD); [|lia].
    rewrite unsigned_last_nbits_eq in PreH2 by (change (2^32) with UINT_MOD; lia). lia. }
  assert (Hcarry : unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { apply unsigned_last_nbits_overflow_32. change UINT_MOD with 4294967296 in *. lia. }
  assert (Hr : unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 = Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32 + UINT_MOD).
  { unfold unsigned_last_nbits at 1. change (2^32) with UINT_MOD.
    symmetry. apply Z.mod_unique with (q := -1); [left; lia|ring]. }
  rewrite list_to_Z_concat_r by (try exact UINT_MOD_pos; lia).
  rewrite PreH10.
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_a i ltac:(lia) PreH11).
  rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_b i ltac:(lia) PreH12).
  rewrite Z.pow_add_r by lia. change (UINT_MOD ^ 1) with UINT_MOD.
  nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_4_non_alias_split_goal_2 : mpn_sub_n_entail_wit_6_4_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Ha.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hb.
  pose proof (Z.mod_pos_bound (Znth i l_b 0 + cy) UINT_MOD UINT_MOD_pos) as Ht.
  change (0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD) in Ht.
  apply list_within_bound_app_single; [exact PreH13|].
  unfold unsigned_last_nbits at 1. change (2^32) with UINT_MOD.
  apply Z.mod_pos_bound. exact UINT_MOD_pos.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_4_non_alias_split_goal_3 : mpn_sub_n_entail_wit_6_4_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_6_4_non_alias : mpn_sub_n_entail_wit_6_4_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_4_non_alias_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_4_non_alias_split_goal_2.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_6_4_non_alias_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_return_wit_1_rp_eq_ap : mpn_sub_n_return_wit_1_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  replace i with n_pre in * by lia.
  rewrite sublist_self in PreH9 by lia.
  rewrite sublist_self in PreH10 by lia.
  rewrite PreH16, Zsublist_nil by lia.
  rewrite UIntArray.seg_empty.
  Intros_p Hempty.
  sep_apply_l_atomic (UIntArray.seg_to_full rp_pre 0 n_pre l_r).
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists val_r_2.
  unfold mpd_store_Z, mpd_store_list.
  Exists l_r l_b.
  rewrite ?PreH15, ?PreH17, ?PreH16.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try tauto; lia.
Qed.

Lemma proof_of_mpn_sub_n_return_wit_2_rp_eq_bp : mpn_sub_n_return_wit_2_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  replace i with n_pre in * by lia.
  rewrite sublist_self in PreH9 by lia.
  rewrite sublist_self in PreH10 by lia.
  rewrite PreH16, Zsublist_nil by lia.
  rewrite UIntArray.seg_empty.
  Intros_p Hempty.
  sep_apply_l_atomic (UIntArray.seg_to_full rp_pre 0 n_pre l_r).
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists val_r_2.
  unfold mpd_store_Z, mpd_store_list.
  Exists l_a l_r.
  rewrite ?PreH15, ?PreH17, ?PreH16.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try tauto; lia.
Qed.

Lemma proof_of_mpn_sub_n_return_wit_3_non_alias : mpn_sub_n_return_wit_3_non_alias.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  replace i with n_pre in * by lia.
  rewrite !sublist_self in PreH14 by lia.
  rewrite UIntArray.undef_seg_empty.
  sep_apply_l_atomic (UIntArray.seg_to_full rp_pre 0 n_pre data_rp_partial).
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists (list_to_Z UINT_MOD data_rp_partial).
  unfold mpd_store_Z, mpd_store_list.
  Exists l_a l_b data_rp_partial.
  rewrite PreH6, PreH7, PreH8.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try tauto; lia.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_1 : mpn_sub_n_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros la lb.
  Exists lb la.
  replace (Zlength la) with n by lia.
  replace (Zlength lb) with n by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_2 : mpn_sub_n_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros la lb.
  Exists lb la.
  replace (Zlength la) with n by lia.
  replace (Zlength lb) with n by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_3 : mpn_sub_n_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros la lb.
  Exists lb la.
  replace (Zlength la) with n by lia.
  replace (Zlength lb) with n by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_4_split_goal_spatial : mpn_sub_n_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (UIntArray.full_Zlength ap n l_a).
  Intros_p Hlen.
  rewrite sublist_self by reflexivity.
  rewrite Hlen.
  apply UIntArray.full_to_seg.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_4 : mpn_sub_n_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_n_which_implies_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_5_split_goal_spatial : mpn_sub_n_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (UIntArray.full_Zlength bp n l_b).
  Intros_p Hlen.
  rewrite sublist_self by lia.
  rewrite PreH3.
  apply UIntArray.full_to_seg.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_5 : mpn_sub_n_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_n_which_implies_wit_5_split_goal_spatial.
Qed.

