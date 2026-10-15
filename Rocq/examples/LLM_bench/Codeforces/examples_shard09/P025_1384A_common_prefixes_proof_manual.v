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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P025_1384A_common_prefixes_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P025_1384A_common_prefixes_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P025_1384A_common_prefixes_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (repeat None (Z.to_nat 201) ::
    repeat UnwrittenRow (Z.to_nat n_pre)).
  sep_apply_l_atomic
    (Array2Convert.char_undef_full_to_mixed_full out_pre (n_pre + 1) 201).
  unfold Array2Convert.undef_rows.
  rewrite undef_to_initial_mixed__initialization by lia.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre prefix_lengths).
    cancel.
  - split_pures.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold InitialRowProgress.
      split; [lia |].
      rewrite Z2Nat.inj_0.
      simpl.
      reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply initial_row_write_step__initialization.
  - lia.
  - assumption.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj : j = 200) by lia.
  subst j.
  unfold Array2.replace_mixed_row.
  apply (initial_row_finish__initialization n_pre prefix_lengths rows_2
    __default__List__App_option_Z).
  - lia.
  - assumption.
  - assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply produced_rows_to_copy_start__copy_progress.
  - lia.
  - auto.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyProgress in PreH10 |- *.
  destruct PreH10 as [Hi [Hj [out [Hspec Hrows]]]].
  destruct Hspec as [Houtlen [Houtbin Hrel]].
  assert (Hspec' : PrefixSpec prefix_lengths (i + 1) out).
  { repeat split; assumption. }
  assert (Hmaplen : Zlength (map EncodedRow out) = i + 1).
  { rewrite Zlength_correct, length_map, <- Zlength_correct, Houtlen.
    reflexivity. }
  assert
    (Hsrcrow :
      Znth i rows_2 __default__List__App_option_Z =
        EncodedRow (Znth i out nil)).
  { apply
      (copy_progress_source_row__copy_progress prefix_lengths i j rows_2 out
        __default__List__App_option_Z);
      try assumption; try lia. }
  assert (Hbin : BinaryAnswerString (Znth i out nil)).
  { apply BinaryAnswer_Znth__copy_progress with (out := out).
    - exact Houtbin.
    - rewrite Houtlen.
      lia. }
  destruct Hbin as [Hslen _].
  assert
    (Hsrcdef :
      Array2.mixed_def (Znth i rows_2 __default__List__App_option_Z) j).
  { rewrite Hsrcrow.
    unfold Array2.mixed_def.
    exists (Znth j (Znth i out nil ++ 0 :: nil) 0).
    unfold EncodedRow.
    rewrite Znth_map_Some__copy_progress by
      (rewrite Zlength_app_cons, Hslen; lia).
    reflexivity. }
  pose proof (Array2.mixed_def_val _ _ Hsrcdef) as Hsrcval.
  assert
    (Hround :
      Array2.replace_mixed_row i
        (replace_Znth j
          (Some
            (Array2.mixed_val
              (Znth i rows_2 __default__List__App_option_Z) j))
          (Znth i rows_2 __default__List__App_option_Z)) rows_2 = rows_2).
  { unfold Array2.replace_mixed_row.
    rewrite <- Hsrcval.
    rewrite replace_Znth_Znth.
    apply replace_Znth_Znth. }
  assert
    (Hmixed :
      Array2.mixed_val (EncodedRow (Znth i out nil)) j =
        Znth j (Znth i out nil ++ 0 :: nil) 0).
  { unfold Array2.mixed_val, EncodedRow.
    rewrite Znth_map_Some__copy_progress by
      (rewrite Zlength_app_cons, Hslen; lia).
    reflexivity. }
  assert
    (Hnew :
      Array2.replace_mixed_row (i + 1)
        (replace_Znth j
          (Some
            (Array2.mixed_val
              (Znth i rows_2 __default__List__App_option_Z) j))
          (Znth (i + 1)
            (Array2.replace_mixed_row i
              (replace_Znth j
                (Some
                  (Array2.mixed_val
                    (Znth i rows_2 __default__List__App_option_Z) j))
                (Znth i rows_2 __default__List__App_option_Z)) rows_2)
            __default__List__App_option_Z))
        (Array2.replace_mixed_row i
          (replace_Znth j
            (Some
              (Array2.mixed_val
                (Znth i rows_2 __default__List__App_option_Z) j))
            (Znth i rows_2 __default__List__App_option_Z)) rows_2) =
      map EncodedRow out ++ CopyRowPrefix (Znth i out nil) (j + 1) ::
        repeat UnwrittenRow (Z.to_nat (Zlength prefix_lengths - i - 1))).
  { rewrite Hround.
    rewrite Hsrcrow, Hmixed.
    unfold Array2.replace_mixed_row.
    rewrite Hrows.
    assert (Hindex : i + 1 >= Zlength (map EncodedRow out)) by lia.
    rewrite
      (@app_Znth2 (list (option Z)) __default__List__App_option_Z
        (map EncodedRow out)
        (CopyRowPrefix (Znth i out nil) j ::
          repeat UnwrittenRow
            (Z.to_nat (Zlength prefix_lengths - i - 1))) (i + 1)) by
      exact Hindex.
    replace (i + 1 - Zlength (map EncodedRow out)) with 0 by lia.
    simpl.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (i + 1 - Zlength (map EncodedRow out)) with 0 by lia.
    simpl.
    rewrite CopyRowPrefix_step__copy_progress by lia.
    reflexivity. }
  split; [exact Hi |].
  split; [lia |].
  exists out; split.
  - repeat split; assumption.
  - exact Hnew.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = 201) by lia.
  subst j.
  exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyProgress in PreH11.
  destruct PreH11 as [Hcopyi [Hcopyj [out [Hprefix Hrows]]]].
  unfold PrefixSpec in Hprefix.
  destruct Hprefix as [Houtlen [Houtbin Hold]].
  assert (Hsi : BinaryAnswerString (Znth i out (nil : list Z))).
  {
    apply (proj1 (Forall_nth BinaryAnswerString out) Houtbin
      (Z.to_nat i) (nil : list Z)).
    assert (Hnatlen : Z.to_nat (Zlength out) = length out).
    { rewrite Zlength_correct. lia. }
    rewrite <- Hnatlen.
    apply (proj1 (Z2Nat.inj_lt i (Zlength out) ltac:(lia)
      ltac:(apply Zlength_nonneg))).
    rewrite Houtlen. lia.
  }
  destruct Hsi as [Hslen Hsbin].
  assert (Hcopy : CopyRowPrefix (Znth i out (nil : list Z)) 201 =
    EncodedRow (Znth i out (nil : list Z))).
  {
    unfold CopyRowPrefix, EncodedRow.
    assert (Hsub : sublist 0 201 (Znth i out (nil : list Z) ++ (0 :: nil)) =
      Znth i out (nil : list Z) ++ (0 :: nil)).
    {
      apply sublist_self.
      rewrite Zlength_app, Zlength_cons, Zlength_nil, Hslen. lia.
    }
    rewrite Hsub.
    replace (201 - 201) with 0 by lia.
    simpl. rewrite <- app_nil_r. reflexivity.
  }
  assert (Hmapoutlen : Zlength (map EncodedRow out) = i + 1).
  {
    assert (Hmap : Zlength (map EncodedRow out) = Zlength out).
    { rewrite !Zlength_correct. rewrite length_map. reflexivity. }
    rewrite Hmap, Houtlen. reflexivity.
  }
  assert (Hrowi : Znth i rows_2 __default__List__App_option_Z =
    EncodedRow (Znth i out (nil : list Z))).
  {
    rewrite Hrows, Hcopy.
    rewrite (app_Znth1 __default__List__App_option_Z (map EncodedRow out)
      (EncodedRow (Znth i out (nil : list Z)) ::
        repeat UnwrittenRow (Z.to_nat (Zlength prefix_lengths - i - 1))) i)
      by (rewrite Hmapoutlen; lia).
    rewrite Znth_map_EncodedRow__row_flip by (rewrite Houtlen; lia).
    reflexivity.
  }
  assert (Hmixed : Array2.mixed_val (EncodedRow (Znth i out (nil : list Z))) k = 97).
  { rewrite <- Hrowi. exact PreH1. }
  assert (Hcell : Znth k (EncodedRow (Znth i out (nil : list Z))) None = Some 97).
  {
    unfold Array2.mixed_val in Hmixed.
    destruct (Znth k (EncodedRow (Znth i out (nil : list Z))) None) as [x|]
      eqn:Hcell; simpl in Hmixed.
    - subst x. reflexivity.
    - lia.
  }
  assert (Hchar : Znth k (Znth i out (nil : list Z)) 0 = 97).
  {
    rewrite encoded_Znth__row_flip in Hcell by (rewrite Hslen; lia).
    injection Hcell as Hchar. exact Hchar.
  }
  assert (Hround :
    Array2.replace_mixed_row i
      (replace_Znth k
        (Some (Array2.mixed_val (Znth i rows_2 __default__List__App_option_Z) k))
        (Znth i rows_2 __default__List__App_option_Z)) rows_2 = rows_2).
  {
    assert (Hcellrows :
      Znth k (Znth i rows_2 __default__List__App_option_Z) None = Some 97).
    { rewrite Hrowi. exact Hcell. }
    rewrite PreH1.
    rewrite <- Hcellrows.
    apply Array2.replace_mixed_row_roundtrip.
  }
  assert (Hfinal :
    Array2.replace_mixed_row (i + 1)
      (replace_Znth k (Some 98) (Znth (i + 1) rows_2 __default__List__App_option_Z))
      rows_2 =
    map EncodedRow out ++
      EncodedRow (replace_Znth k 98 (Znth i out (nil : list Z))) ::
      repeat UnwrittenRow (Z.to_nat (Zlength prefix_lengths - i - 1))).
  {
    unfold Array2.replace_mixed_row.
    rewrite Hrows, Hcopy.
    rewrite (app_Znth2 __default__List__App_option_Z (map EncodedRow out)
      (EncodedRow (Znth i out (nil : list Z)) ::
        repeat UnwrittenRow (Z.to_nat (Zlength prefix_lengths - i - 1))) (i + 1))
      by (rewrite Hmapoutlen; lia).
    replace (i + 1 - Zlength (map EncodedRow out)) with 0 by
      (rewrite Hmapoutlen; lia).
    rewrite Znth0_cons.
    rewrite <- encoded_replace__row_flip by (rewrite Hslen; lia).
    rewrite replace_Znth_app_r by (rewrite Hmapoutlen; lia).
    rewrite replace_Znth_nothing by (rewrite Hmapoutlen; lia).
    replace (i + 1 - Zlength (map EncodedRow out)) with 0 by
      (rewrite Hmapoutlen; lia).
    simpl. reflexivity.
  }
  assert (Htoggle :
    BinaryAnswerString (replace_Znth k 98 (Znth i out (nil : list Z))) /\
    LCP (Znth i out (nil : list Z))
      (replace_Znth k 98 (Znth i out (nil : list Z))) k).
  {
    apply toggle_binary_row_lcp__row_flip; try assumption.
    - split; [exact PreH9|lia].
    - right. reflexivity.
    - rewrite Hchar. lia.
  }
  destruct Htoggle as [Hbinarynew Hlcpnew].
  rewrite Hround.
  rewrite Hfinal.
  apply (append_toggled_row__row_flip prefix_lengths out i
    (replace_Znth k 98 (Znth i out (nil : list Z)))).
  - exact Hcopyi.
  - unfold PrefixSpec. repeat split; assumption.
  - exact Hbinarynew.
  - rewrite <- PreH8. exact Hlcpnew.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyProgress in PreH11.
  destruct PreH11 as [Hcopyi [Hcopyj [out [Hprefix Hrows]]]].
  unfold PrefixSpec in Hprefix.
  destruct Hprefix as [Houtlen [Houtbin Hold]].
  assert (Hsi : BinaryAnswerString (Znth i out (nil : list Z))).
  {
    apply (proj1 (Forall_nth BinaryAnswerString out) Houtbin
      (Z.to_nat i) (nil : list Z)).
    assert (Hnatlen : Z.to_nat (Zlength out) = length out).
    { rewrite Zlength_correct. lia. }
    rewrite <- Hnatlen.
    apply (proj1 (Z2Nat.inj_lt i (Zlength out) ltac:(lia)
      ltac:(apply Zlength_nonneg))).
    rewrite Houtlen. lia.
  }
  destruct Hsi as [Hslen Hsbin].
  assert (Hcopy : CopyRowPrefix (Znth i out (nil : list Z)) 201 =
    EncodedRow (Znth i out (nil : list Z))).
  {
    unfold CopyRowPrefix, EncodedRow.
    assert (Hsub : sublist 0 201 (Znth i out (nil : list Z) ++ (0 :: nil)) =
      Znth i out (nil : list Z) ++ (0 :: nil)).
    {
      apply sublist_self.
      rewrite Zlength_app, Zlength_cons, Zlength_nil, Hslen. lia.
    }
    rewrite Hsub.
    replace (201 - 201) with 0 by lia.
    simpl. rewrite <- app_nil_r. reflexivity.
  }
  assert (Hmapoutlen : Zlength (map EncodedRow out) = i + 1).
  {
    assert (Hmap : Zlength (map EncodedRow out) = Zlength out).
    { rewrite !Zlength_correct. rewrite length_map. reflexivity. }
    rewrite Hmap, Houtlen. reflexivity.
  }
  assert (Hrowi : Znth i rows_2 __default__List__App_option_Z =
    EncodedRow (Znth i out (nil : list Z))).
  {
    rewrite Hrows, Hcopy.
    rewrite (app_Znth1 __default__List__App_option_Z (map EncodedRow out)
      (EncodedRow (Znth i out (nil : list Z)) ::
        repeat UnwrittenRow (Z.to_nat (Zlength prefix_lengths - i - 1))) i)
      by (rewrite Hmapoutlen; lia).
    rewrite Znth_map_EncodedRow__row_flip by (rewrite Houtlen; lia).
    reflexivity.
  }
  assert (Hchar : Znth k (Znth i out (nil : list Z)) 0 = 98).
  {
    destruct (Hsbin k ltac:(split; [exact PreH9|lia])) as [H97 | H98].
    - exfalso. apply PreH1.
      rewrite Hrowi.
      unfold Array2.mixed_val.
      rewrite encoded_Znth__row_flip by (rewrite Hslen; lia).
      rewrite H97. reflexivity.
    - exact H98.
  }
  assert (Hcell : Znth k (EncodedRow (Znth i out (nil : list Z))) None = Some 98).
  {
    rewrite encoded_Znth__row_flip by (rewrite Hslen; lia).
    rewrite Hchar. reflexivity.
  }
  assert (Hmixed : Array2.mixed_val (EncodedRow (Znth i out (nil : list Z))) k = 98).
  {
    unfold Array2.mixed_val.
    rewrite Hcell. reflexivity.
  }
  assert (Hround :
    Array2.replace_mixed_row i
      (replace_Znth k
        (Some (Array2.mixed_val (Znth i rows_2 __default__List__App_option_Z) k))
        (Znth i rows_2 __default__List__App_option_Z)) rows_2 = rows_2).
  {
    assert (Hmixedrows :
      Array2.mixed_val (Znth i rows_2 __default__List__App_option_Z) k = 98).
    { rewrite Hrowi. exact Hmixed. }
    assert (Hcellrows :
      Znth k (Znth i rows_2 __default__List__App_option_Z) None = Some 98).
    { rewrite Hrowi. exact Hcell. }
    rewrite Hmixedrows.
    rewrite <- Hcellrows.
    apply Array2.replace_mixed_row_roundtrip.
  }
  assert (Hfinal :
    Array2.replace_mixed_row (i + 1)
      (replace_Znth k (Some 97) (Znth (i + 1) rows_2 __default__List__App_option_Z))
      rows_2 =
    map EncodedRow out ++
      EncodedRow (replace_Znth k 97 (Znth i out (nil : list Z))) ::
      repeat UnwrittenRow (Z.to_nat (Zlength prefix_lengths - i - 1))).
  {
    unfold Array2.replace_mixed_row.
    rewrite Hrows, Hcopy.
    rewrite (app_Znth2 __default__List__App_option_Z (map EncodedRow out)
      (EncodedRow (Znth i out (nil : list Z)) ::
        repeat UnwrittenRow (Z.to_nat (Zlength prefix_lengths - i - 1))) (i + 1))
      by (rewrite Hmapoutlen; lia).
    replace (i + 1 - Zlength (map EncodedRow out)) with 0 by
      (rewrite Hmapoutlen; lia).
    rewrite Znth0_cons.
    rewrite <- encoded_replace__row_flip by (rewrite Hslen; lia).
    rewrite replace_Znth_app_r by (rewrite Hmapoutlen; lia).
    rewrite replace_Znth_nothing by (rewrite Hmapoutlen; lia).
    replace (i + 1 - Zlength (map EncodedRow out)) with 0 by
      (rewrite Hmapoutlen; lia).
    simpl. reflexivity.
  }
  assert (Htoggle :
    BinaryAnswerString (replace_Znth k 97 (Znth i out (nil : list Z))) /\
    LCP (Znth i out (nil : list Z))
      (replace_Znth k 97 (Znth i out (nil : list Z))) k).
  {
    apply toggle_binary_row_lcp__row_flip; try assumption.
    - split; [exact PreH9|lia].
    - left. reflexivity.
    - rewrite Hchar. lia.
  }
  destruct Htoggle as [Hbinarynew Hlcpnew].
  rewrite Hround.
  rewrite Hfinal.
  apply (append_toggled_row__row_flip prefix_lengths out i
    (replace_Znth k 97 (Znth i out (nil : list Z)))).
  - exact Hcopyi.
  - unfold PrefixSpec. repeat split; assumption.
  - exact Hbinarynew.
  - rewrite <- PreH8. exact Hlcpnew.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i_3 = n_pre) by lia.
  subst i_3.
  assert (Hprod : ProducedRows prefix_lengths (Zlength prefix_lengths + 1) rows).
  { rewrite <- PreH4. exact PreH8. }
  destruct (produced_rows_to_spec__final_return prefix_lengths rows Hprod)
    as [out [Hrows [Hspec [Houtlen [Hrowlen [Houtrowslen Houtrows]]]]]].
  assert (Hsome :
    rows = Array2.some_rows (map (fun s : list Z => s ++ (0 :: nil)) out)).
  { unfold Array2.some_rows. exact Hrows. }
  Exists (map (fun s : list Z => s ++ (0 :: nil)) out) out.
  rewrite Hsome.
  sep_apply_l_atomic
    (Array2Convert.char_mixed_full_to_full out_pre (n_pre + 1) 201
      (map (fun s : list Z => s ++ (0 :: nil)) out)).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. rewrite PreH4. exact Houtlen.
    + dump_pre_spatial. intros j Hj.
      rewrite (Znth_indep out j __default__List_Z (@nil Z)) by
        (rewrite Houtlen; rewrite PreH4 in Hj; exact Hj).
      apply Hrowlen.
      rewrite PreH4 in Hj. exact Hj.
    + dump_pre_spatial. rewrite PreH4. exact Houtrowslen.
    + dump_pre_spatial. intros j Hj.
      apply (Houtrows __default__List_Z j).
      rewrite PreH4 in Hj. exact Hj.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_1 : solver_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.mixed_def.
  dump_pre_spatial.
  eapply copy_progress_mixed_defined__mixed_definedness.
  - exact PreH16.
  - lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure_split_goal_1 : solver_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.mixed_def.
  dump_pre_spatial.
  eapply copy_progress_mixed_defined__mixed_definedness.
  - exact PreH16.
  - lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_6_pure_split_goal_1.
Qed.
