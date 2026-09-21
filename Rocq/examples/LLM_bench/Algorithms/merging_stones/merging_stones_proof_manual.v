Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.merging_stones Require Import merging_stones_goal.
From SimpleC.EE.LLM_bench.Algorithms.merging_stones Require Import merging_stones_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib.
Local Open Scope sac.

(* Complete VCs retain the array resources needed to recover list dimensions.
   Arithmetic and table transitions reuse the original helper proofs. *)


Lemma scratch_flat_to_rows_rec : forall (k : nat) x lo m l,
  0 <= m ->
  IntArray.seg x (lo * m) ((lo + Z.of_nat k) * m) l |--
  EX rows, “ Zlength rows = Z.of_nat k /\ Forall (fun row => Zlength row = m) rows ” &&
    store_array_rec (IntArray2.row_store m) x lo (lo + Z.of_nat k) rows.
Proof.
  induction k as [|k IH]; intros x lo m l Hm.
  - simpl. replace (lo + 0) with lo by lia.
    prop_apply (IntArray.seg_Zlength x (lo*m) (lo*m) l). Intros.
    assert (l = nil) by (apply Zlength_nil_inv; lia). subst l.
    rewrite IntArray.seg_empty.
    Exists (@nil (list Z)). simpl. entailer!.
  - rewrite Nat2Z.inj_succ.
    replace (lo + Z.succ (Z.of_nat k)) with ((lo + 1) + Z.of_nat k) by lia.
    sep_apply (IntArray.seg_split_to_seg x (lo*m) ((lo+1)*m)
      (((lo+1)+Z.of_nat k)*m) l); [|nia].
    sep_apply (IH x (lo+1) m (sublist ((lo+1)*m-lo*m)
      (((lo+1)+Z.of_nat k)*m-lo*m) l) Hm).
    Intros rows.
    sep_apply (IntArray.seg_to_full x (lo*m) ((lo+1)*m)
      (sublist 0 ((lo+1)*m-lo*m) l)).
    replace ((lo+1)*m-lo*m) with m by ring.
    prop_apply IntArray.full_Zlength. Intros.
    Exists ((sublist 0 m l) :: rows).
    rewrite Zlength_cons. simpl store_array_rec.
    unfold IntArray2.row_store, IntArray2.row_addr.
    entailer!.
Qed.

Lemma scratch_flat_to_rows : forall x n m l,
  0 <= n -> 0 <= m ->
  IntArray.full x (n*m) l |--
  EX rows, “ Zlength rows = n /\ Forall (fun row => Zlength row = m) rows ” &&
    IntArray2.full x n m rows.
Proof.
  intros x n m l Hn Hm.
  sep_apply IntArray.full_to_seg.
  replace 0 with (0*m) at 1 by ring.
  replace (n*m) with ((0+Z.of_nat (Z.to_nat n))*m) by (rewrite Z2Nat.id by lia; ring).
  sep_apply (scratch_flat_to_rows_rec (Z.to_nat n) x 0 m l Hm).
  Intros rows. Exists rows.
  unfold IntArray2.full, store_array.
  rewrite Z2Nat.id by lia. replace (0+n) with n by lia.
  entailer!.
Qed.

Lemma scratch_row_to_undef_seg : forall x lo m row,
  IntArray2.row_store m x lo row |--
  IntArray.undef_seg x (lo*m) ((lo+1)*m).
Proof.
  intros. unfold IntArray2.row_store, IntArray2.row_addr.
  change (IntArray.full (x+lo*m*sizeof(INT)) m row |-- IntArray.undef_seg x (lo*m) ((lo+1)*m)).
  sep_apply IntArray.full_to_undef_full.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite <- IntArray.undef_seg_shift.
  replace (lo*m+0) with (lo*m) by ring.
  replace (lo*m+m) with ((lo+1)*m) by ring.
  entailer!.
Qed.

Lemma scratch_rows_rec_to_undef_seg : forall rows x lo hi m,
  0 <= m ->
  store_array_rec (IntArray2.row_store m) x lo hi rows |--
  IntArray.undef_seg x (lo*m) (hi*m).
Proof.
  induction rows as [|row rows IH]; intros x lo hi m Hm.
  - simpl. Intros. subst hi. rewrite IntArray.undef_seg_empty. entailer!.
  - simpl store_array_rec.
    prop_apply (store_array_rec_valid (list Z) (IntArray2.row_store m) x (lo+1) hi rows).
    Intros.
    sep_apply (IH x (lo+1) hi m Hm).
    sep_apply (scratch_row_to_undef_seg x lo m row).
    sep_apply (IntArray.undef_seg_merge_to_undef_seg x (lo*m) ((lo+1)*m) (hi*m)); [|nia].
    entailer!.
Qed.

Lemma scratch_rows_to_flat_undef : forall x n m rows,
  0 <= m ->
  IntArray2.full x n m rows |-- IntArray.undef_full x (n*m).
Proof.
  intros x n m rows Hm. unfold IntArray2.full, store_array.
  sep_apply (scratch_rows_rec_to_undef_seg rows x 0 n m Hm).
  replace (0*m) with 0 by ring.
  sep_apply IntArray.undef_seg_to_undef_full.
  replace (x+0*sizeof(INT)) with x by lia.
  replace (n*m-0) with (n*m) by ring.
  entailer!.
Qed.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg IntArray2.full IntArray2.missing_i.

Lemma scratch_full_tail_undef : forall x k cap l,
  0 <= k <= cap ->
  IntArray.full x k l ** IntArray.undef_seg x k cap |-- IntArray.undef_full x cap.
Proof.
  intros x k cap l Hk.
  sep_apply (IntArray.full_to_undef_full x k l).
  sep_apply (IntArray.undef_full_to_undef_seg x k).
  sep_apply (IntArray.undef_seg_merge_to_undef_full x 0 k cap Hk).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (cap - 0) with cap by lia. entailer!.
Qed.
Lemma scratch_undef_full_split : forall x k cap,
  0 <= k <= cap ->
  IntArray.undef_full x cap |-- IntArray.undef_full x k ** IntArray.undef_seg x k cap.
Proof.
  intros x k cap Hk.
  sep_apply (IntArray.undef_full_split_to_undef_seg x k cap Hk).
  sep_apply (IntArray.undef_seg_to_undef_full x 0 k).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (k - 0) with k by lia. entailer!.
Qed.

Require Import AUXLib.MonotonicList.


Lemma stone_cell_store : forall dp n table row col value,
  0 <= row < n -> 0 <= col < n ->
  (dp + (row * n + col) * sizeof(INT)) # Int |-> value **
  IntArray.missing_i (dp + row * n * sizeof(INT)) col 0 n
    (Znth row table nil) **
  IntArray2.missing_i dp row 0 n n table |--
  IntArray2.full dp n n
    (replace_Znth row (replace_Znth col value (Znth row table nil)) table).
Proof.
  intros dp n table row col value Hrow Hcol.
  replace (dp + (row * n + col) * sizeof(INT)) with
    (dp + row * n * sizeof(INT) + col * sizeof(INT)) by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    (dp + row * n * sizeof(INT)) col n value (Znth row table nil)); try lia.
  change (IntArray.full (dp + row * n * sizeof(INT)) n
    (replace_Znth col value (Znth row table nil))) with
    (IntArray2.ElemArray.full (IntArray2.row_addr dp n row) n
      (replace_Znth col value (Znth row table nil))).
  sep_apply (IntArray2.missing_i_merge_to_full dp row n n table
    (replace_Znth col value (Znth row table nil))); try lia.
  repeat cancel.
Qed.

Lemma stone_cell_read : forall dp n table row col,
  Zlength table = n -> Forall (eq n) (map (@Zlength Z) table) ->
  0 <= row < n -> 0 <= col < n ->
  (dp + (row * n + col) * sizeof(INT)) # Int |-> Znth col (Znth row table nil) 0 **
  IntArray.missing_i (dp + row * n * sizeof(INT)) col 0 n
    (Znth row table nil) **
  IntArray2.missing_i dp row 0 n n table |-- IntArray2.full dp n n table.
Proof.
  intros dp n table row col Hlen Hrows Hrow Hcol.
  sep_apply (stone_cell_store dp n table row col
    (Znth col (Znth row table nil) 0)); try lia.
  rewrite replace_Znth_Znth by
    (rewrite (stone_row_length table n row nil Hlen Hrows Hrow); lia).
  rewrite replace_Znth_Znth by lia. repeat cancel.
Qed.











































Lemma proof_of_mergingStones_safety_wit_10 : mergingStones_safety_wit_10.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  pose proof (stone_mass_bounds stones_l PreH4 PreH5) as Hmass.
  pose proof (StoneMassesBounded_Znth__prefix_math stones_l n_pre i
    (conj Hstones Hmass) ltac:(lia)) as Hvalue.
  pose proof (StonePrefixProgress_value_bounds__prefix_math
    stones_l prefix_l n_pre i i Hstones Hmass PreH3 PreH8 PreH9 ltac:(lia)) as Hprefix.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648);
    replace (i - 0) with i by lia; lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_25 : mergingStones_safety_wit_25.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  pose proof (stone_mass_bounds stones_l PreH4 PreH5) as Hmass.
  pose proof (StonePrefixDone_interval_bounds__prefix_math
    stones_l prefix_l n_pre left (left + len)
    (conj Hstones Hmass) PreH7 ltac:(lia) ltac:(lia)) as Hbounds.
  replace (left + len - 1 + 1) with (left + len) by lia.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_35 : mergingStones_safety_wit_35.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) (split + 1) 0 n_pre n_pre dp_l).
  Intros. rename H into Htable. replace (n_pre - 0) with n_pre in Htable by lia.
  pose proof (stone_mass_bounds stones_l PreH3 PreH4) as Hmass.
  pose proof (StoneSplitProgress_child_bounds__interval_min_core
    stones_l dp_l n_pre len left split right best __default__List_Z
    (conj Hstones Hmass) PreH2 Htable PreH9 PreH19 PreH11
    ltac:(lia) ltac:(lia)) as [[Hlo1 Hhi1] [Hlo2 Hhi2]].
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_36 : mergingStones_safety_wit_36.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) (split + 1) 0 n_pre n_pre dp_l).
  Intros. rename H into Htable. replace (n_pre - 0) with n_pre in Htable by lia.
  pose proof (stone_mass_bounds stones_l PreH3 PreH4) as Hmass.
  pose proof (StoneSplitProgress_child_bounds__interval_min_core
    stones_l dp_l n_pre len left split right best __default__List_Z
    (conj Hstones Hmass) PreH2 Htable PreH9 PreH19 PreH11
    ltac:(lia) ltac:(lia)) as [[Hlo1 Hhi1] [Hlo2 Hhi2]].
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3.
Proof.
  unfold mergingStones_entail_wit_3; right; intros.
  assert (k = n_pre*n_pre) by lia. subst k.
  sep_apply (IntArray.seg_to_full (&("dp")) 0 (n_pre*n_pre) dp_flat).
  replace ((&("dp")) + 0*sizeof(INT)) with (&("dp")) by lia.
  rewrite Z.sub_0_r.
  sep_apply (scratch_flat_to_rows (&("dp")) n_pre n_pre dp_flat ltac:(lia) ltac:(lia)).
  Intros rows.
  Exists (0 :: nil) rows.
  sep_apply (IntArray.undef_seg_split_to_undef_seg (&("prefix")) 1 (n_pre+1) 9 ltac:(lia)).
  split_pure_spatial.
  - change (0 + 1) with 1.
    sep_apply_l_atomic (IntArray.seg_single (&("prefix")) 0 0).
    change (0 + 1) with 1. repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + apply Forall_map.
      eapply Forall_impl with (P := fun row : list Z => Zlength row = n_pre).
      * intros row Hrow. simpl. lia.
      * tauto.
    + intros j Hj. assert (j = 0) by lia. subst j. reflexivity.
Qed.

Lemma proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  prop_apply (IntArray.seg_Zlength (&("prefix")) 0 (i + 1 + 1)
    (prefix_l_2 ++ [Znth (i - 0) prefix_l_2 0 + Znth i stones_l 0])). Intros. rename H into Hprefix.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hprefix.
  replace (i - 0) with i in * by lia.
  Exists (prefix_l_2 ++ [Znth i prefix_l_2 0 + Znth i stones_l 0]) dp_init_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply StonePrefixProgress_extend__prefix_math; eauto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5.
Proof.
  aggressive_pre_process.
  - unfold StoneZeroRows. constructor.
  - assert (i = n_pre) by lia. subst i. exact PreH9.
Qed.

Lemma proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6.
Proof.
  aggressive_pre_process.
  split; [exact PreH10 | constructor].
Qed.

Lemma proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) row 0 n_pre n_pre dp_l_2).
  Intros. rename H into Htable. replace (n_pre - 0) with n_pre in Htable by lia.
  rewrite (Znth_indep dp_l_2 row __default__List_Z [] ltac:(lia)) in *.
  Exists prefix_l_2 (replace_Znth row (replace_Znth col 0 (Znth row dp_l_2 [])) dp_l_2).
  split_pure_spatial.
  - sep_apply (stone_cell_store (&("dp")) n_pre dp_l_2 row col 0); try lia. repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + eapply stone_table_store_shape; eauto; lia.
    + eapply StoneZeroProgress_store__zero_table; eauto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray2.full_Zlength (&("dp")) n_pre n_pre dp_l_2).
  Intros. rename H into Htable.
  Exists prefix_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    apply (stone_zero_next_row dp_l_2 n_pre row col Htable PreH6
      ltac:(lia) ltac:(lia) PreH12).
Qed.

Lemma proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  prop_apply (IntArray2.full_Zlength (&("dp")) n_pre n_pre dp_l_2).
  Intros. rename H into Htable.
  assert (row = n_pre) by lia. subst row.
  Exists prefix_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply StoneLenDone_two_of_zero__zero_table; eauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_10 : mergingStones_entail_wit_10.
Proof.
  aggressive_pre_process.
  apply StoneLenDone_to_initial_left_progress__table_progress. exact PreH10.
Qed.

Lemma proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  pose proof (stone_mass_bounds stones_l PreH4 PreH5) as Hmass.
  pose proof (StonePrefixDone_interval_bounds__prefix_math
    stones_l prefix_l n_pre left (left + len)
    (conj Hstones Hmass) PreH7 ltac:(lia) ltac:(lia)) as Hbounds.
  pose proof (StonePrefixDone_interval_sum__prefix_math
    stones_l prefix_l n_pre left (left + len) Hstones PreH7
    ltac:(lia) ltac:(lia)) as Hsum.
  replace (left + len - 1 + 1) with (left + len) in * by lia.
  Exists prefix_l dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    apply StoneSplitProgress_initial__prefix_math. exact PreH12.
Qed.

Lemma proof_of_mergingStones_entail_wit_12 : mergingStones_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) left 0 n_pre n_pre dp_l).
  Intros. rename H into Htable. replace (n_pre - 0) with n_pre in Htable by lia.
  rewrite (Znth_indep dp_l left __default__List_Z [] ltac:(lia)) in *.
  Exists prefix_l_2 dp_l.
  rewrite (Znth_indep dp_l left __default__List_Z [] ltac:(lia)) in *.
  split_pure_spatial.
  - sep_apply (stone_cell_read (&("dp")) n_pre dp_l left split); try assumption; try lia.
    repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_13_1 : mergingStones_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) (split + 1) 0 n_pre n_pre dp_l_2).
  Intros. rename H into Htable. replace (n_pre - 0) with n_pre in Htable by lia.
  rewrite (Znth_indep dp_l_2 left __default__List_Z [] ltac:(lia)) in *.
  rewrite (Znth_indep dp_l_2 (split + 1) __default__List_Z [] ltac:(lia)) in *.
  pose proof (stone_mass_bounds stones_l PreH4 PreH5) as Hmass.
  pose proof (StoneSplitProgress_candidate_facts__interval_min_core
    stones_l dp_l_2 n_pre len left split right best interval_sum []
    (conj Hstones Hmass) PreH3 Htable PreH10 PreH20 PreH12
    ltac:(lia) ltac:(lia) PreH15) as Hcandidate.
  cbn in Hcandidate. rewrite <- PreH22 in Hcandidate.
  destruct Hcandidate as [Hbounds Hcandidate].
  assert (Hnext : StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1)
    (left_value + Znth right (Znth (split + 1) dp_l_2 []) 0 + interval_sum)).
  { eapply StoneSplitProgress_replace_best__split_loop_step; eauto; lia. }
  Exists prefix_l_2 dp_l_2.
  split_pure_spatial.
  - sep_apply (stone_cell_read (&("dp")) n_pre dp_l_2 (split + 1) right);
      try assumption; try lia. repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_13_2 : mergingStones_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) (split + 1) 0 n_pre n_pre dp_l_2).
  Intros. rename H into Htable. replace (n_pre - 0) with n_pre in Htable by lia.
  rewrite (Znth_indep dp_l_2 left __default__List_Z [] ltac:(lia)) in *.
  rewrite (Znth_indep dp_l_2 (split + 1) __default__List_Z [] ltac:(lia)) in *.
  pose proof (stone_mass_bounds stones_l PreH4 PreH5) as Hmass.
  pose proof (StoneSplitProgress_candidate_facts__interval_min_core
    stones_l dp_l_2 n_pre len left split right best interval_sum []
    (conj Hstones Hmass) PreH3 Htable PreH10 PreH20 PreH12
    ltac:(lia) ltac:(lia) PreH15) as Hcandidate.
  cbn in Hcandidate. rewrite <- PreH22 in Hcandidate.
  destruct Hcandidate as [Hbounds Hcandidate].
  assert (Hnext : StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1)
    best).
  { eapply StoneSplitProgress_keep_best__split_loop_step
      with (right := right)
        (candidate := left_value + Znth right (Znth (split + 1) dp_l_2 []) 0 + interval_sum);
      eauto; lia. }
  Exists prefix_l_2 dp_l_2.
  split_pure_spatial.
  - sep_apply (stone_cell_read (&("dp")) n_pre dp_l_2 (split + 1) right);
      try assumption; try lia. repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros. rename H into Hstones.
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) left 0 n_pre n_pre dp_l_2).
  Intros. rename H into Htable. replace (n_pre - 0) with n_pre in Htable by lia.
  rewrite (Znth_indep dp_l_2 left __default__List_Z [] ltac:(lia)) in *.
  assert (Heq : split = right) by lia. subst split.
  pose proof (StoneSplitProgress_complete__interval_min_core
    stones_l dp_l_2 n_pre len left right best Hstones PreH10 PreH12
    ltac:(lia) ltac:(lia) PreH20) as Hminimum.
  pose proof (proj1 PreH20) as Hprogress.
  Exists prefix_l_2 (replace_Znth left (replace_Znth right best (Znth left dp_l_2 [])) dp_l_2).
  split_pure_spatial.
  - sep_apply (stone_cell_store (&("dp")) n_pre dp_l_2 left right best); try lia.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + eapply stone_table_store_shape; eauto; lia.
    + eapply StoneUpdatedCell_to_next_left_progress__table_progress; eauto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_15 : mergingStones_entail_wit_15.
Proof.
  aggressive_pre_process.
  eapply StoneLeftProgress_to_next_len_done__table_progress; eauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16.
Proof.
  unfold mergingStones_entail_wit_16; left; intros.
  prop_apply (IntArray.full_Zlength stones_pre n_pre stones_l). Intros_p Hstones.
  prop_apply (IntArray2.missing_i_Zlength (&("dp")) 0 0 n_pre n_pre dp_l).
  Intros_p Htable. rewrite Z.sub_0_r in Htable.
  rewrite (Znth_indep dp_l 0 __default__List_Z nil ltac:(lia)) in *.
  assert (Hresult : StoneMinimumCost stones_l (Znth (n_pre-1) (Znth 0 dp_l nil) 0)).
  { unfold StoneMinimumCost. rewrite Hstones. apply (PreH10 n_pre 0 (n_pre-1)); lia. }
  sep_apply (stone_cell_read (&("dp")) n_pre dp_l 0 (n_pre-1)); try assumption; try lia.
  sep_apply (scratch_rows_to_flat_undef (&("dp")) n_pre n_pre dp_l ltac:(lia)).
  sep_apply (IntArray.undef_full_to_undef_seg (&("dp")) (n_pre*n_pre)).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("dp")) 0 (n_pre*n_pre) 64 ltac:(nia)).
  replace ((&("dp")) + 0*sizeof(INT)) with (&("dp")) by lia.
  replace (64-0) with 64 by lia.
  sep_apply (scratch_full_tail_undef (&("prefix")) (n_pre+1) 9 prefix_l ltac:(lia)).
  sep_apply (store_int_undef_store_int (&("width")) n_pre).
  entailer!.
Qed.
