From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P093_1750F_majority_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P093_1750F_majority_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P093_1750F_majority_lib.
Local Open Scope sac.



Lemma proof_of_solver_safety_wit_33_split_goal_1 : solver_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH17 (i - 1)) by lia.
  unfold Pow2Mod.
  pose proof (Z.mod_pos_bound (2 ^ (i - 1)) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_2 : solver_safety_wit_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH17 (i - 1)) by lia.
  unfold Pow2Mod.
  pose proof (Z.mod_pos_bound (2 ^ (i - 1)) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_48_split_goal_1 : solver_safety_wit_48_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (quot_div_nonneg_bridge__inner_j_entail (i - j) j ltac:(lia)).
  pose proof (Z.div_pos (i - j + j + 2) 2 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_48_split_goal_2 : solver_safety_wit_48_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (quot_div_nonneg_bridge__inner_j_entail (i - j) j ltac:(lia)).
  pose proof (Z.div_le_upper_bound (i - j + j + 2) 2 2501 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_48_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_48_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_51_split_goal_1 : solver_safety_wit_51_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH36 _ (conj PreH1 PreH2)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_51_split_goal_2 : solver_safety_wit_51_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH36 _ (conj PreH1 PreH2)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_51_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_51_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_52_split_goal_1 : solver_safety_wit_52_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH36 _ (conj PreH1 PreH2)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_52_split_goal_2 : solver_safety_wit_52_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH36 _ (conj PreH1 PreH2)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_52_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_52_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_54_split_goal_1 : solver_safety_wit_54_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH36 _ (conj PreH1 PreH2)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  pose proof (Z.rem_bound_pos 1 m_pre ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound 1 m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_54_split_goal_2 : solver_safety_wit_54_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH36 _ (conj PreH1 PreH2)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  pose proof (Z.rem_bound_pos 1 m_pre ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound 1 m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_54_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_54_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_65_split_goal_1 : solver_safety_wit_65_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH45.
  rewrite (PreH43 _ (conj PreH8 PreH9)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  match goal with
  | |- context [Znth ?d (DPQ m_pre n_pre (i - 1)) 0] =>
      pose proof (DPQ_entry_bound__w_value_safety m_pre n_pre (i - 1) d ltac:(lia))
  end.
  match goal with
  | |- context [Z.rem (?a + m_pre) m_pre] =>
      pose proof (Z.rem_bound_pos (a + m_pre) m_pre ltac:(lia) ltac:(lia))
  | |- context [Z.modulo (?a + m_pre) m_pre] =>
      pose proof (Z.mod_pos_bound (a + m_pre) m_pre ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_65_split_goal_2 : solver_safety_wit_65_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH45.
  rewrite (PreH43 _ (conj PreH8 PreH9)).
  match goal with
  | |- context [Pow2Mod ?k m_pre] =>
      pose proof (Pow2Mod_bound__w_value_safety k m_pre ltac:(lia))
  end.
  match goal with
  | |- context [Znth ?d (DPQ m_pre n_pre (i - 1)) 0] =>
      pose proof (DPQ_entry_bound__w_value_safety m_pre n_pre (i - 1) d ltac:(lia))
  end.
  match goal with
  | |- context [Z.rem (?a + m_pre) m_pre] =>
      pose proof (Z.rem_bound_pos (a + m_pre) m_pre ltac:(lia) ltac:(lia))
  | |- context [Z.modulo (?a + m_pre) m_pre] =>
      pose proof (Z.mod_pos_bound (a + m_pre) m_pre ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_65_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_67_split_goal_1 : solver_safety_wit_67_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH41.
  match goal with
  | |- context [Znth ?d (DPQ m_pre n_pre (i - 1)) 0] =>
      pose proof (DPQ_entry_bound__w_value_safety m_pre n_pre (i - 1) d ltac:(lia))
  end.
  pose proof (Z.rem_bound_pos 1 m_pre ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound 1 m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_67_split_goal_2 : solver_safety_wit_67_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH41.
  match goal with
  | |- context [Znth ?d (DPQ m_pre n_pre (i - 1)) 0] =>
      pose proof (DPQ_entry_bound__w_value_safety m_pre n_pre (i - 1) d ltac:(lia))
  end.
  pose proof (Z.rem_bound_pos 1 m_pre ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound 1 m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_67_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_67_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_1 : solver_safety_wit_69_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_69_split_goal_2 : solver_safety_wit_69_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_69_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_1 : solver_safety_wit_71_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_71_split_goal_2 : solver_safety_wit_71_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_71_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_73_split_goal_1 : solver_safety_wit_73_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_73_split_goal_2 : solver_safety_wit_73_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_73_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_73_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_1 : solver_safety_wit_75_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_75_split_goal_2 : solver_safety_wit_75_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Ha : 0 <= Znth j lA 0 < m_pre).
  { match goal with H : lA = DPA _ _ _ |- _ => rewrite H end.
    apply DPA_entry_bound__brow_product_safety. lia. }
  match goal with
  | |- context [ Znth j lA 0 * Z.rem ?x m_pre ] =>
      pose proof (mul_mod_fits_int64__brow_product_safety (Znth j lA 0) (Z.rem x m_pre) m_pre
        Ha (rem_abs_bound__brow_product_safety x m_pre ltac:(lia)) ltac:(lia)) as Hfit
  end.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_75_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_77_split_goal_1 : solver_safety_wit_77_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_max__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_77_split_goal_2 : solver_safety_wit_77_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_min__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_77_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_77_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_79_split_goal_1 : solver_safety_wit_79_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_max__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_79_split_goal_2 : solver_safety_wit_79_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_min__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_79_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_79_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_81_split_goal_1 : solver_safety_wit_81_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_max__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_81_split_goal_2 : solver_safety_wit_81_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_min__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_81 : solver_safety_wit_81.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_81_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_81_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_83_split_goal_1 : solver_safety_wit_83_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_max__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_83_split_goal_2 : solver_safety_wit_83_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply blocked_add_row_min__blocked_acc_safety; lia.
Qed.

Lemma proof_of_solver_safety_wit_83 : solver_safety_wit_83.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_83_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_83_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_89_split_goal_1 : solver_safety_wit_89_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (rem_bounds__row_value (Znth (i - 1) lpow2 0 - blocked) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_89_split_goal_2 : solver_safety_wit_89_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (rem_bounds__row_value (Znth (i - 1) lpow2 0 - blocked) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_89 : solver_safety_wit_89.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_89_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_89_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_91_split_goal_1 : solver_safety_wit_91_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH17 (i - 1) ltac:(lia)).
  unfold Pow2Mod.
  pose proof (Z.mod_pos_bound (2 ^ (i - 1)) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_91_split_goal_2 : solver_safety_wit_91_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH17 (i - 1) ltac:(lia)).
  unfold Pow2Mod.
  pose proof (Z.mod_pos_bound (2 ^ (i - 1)) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_91 : solver_safety_wit_91.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_91_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_91_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_101_split_goal_1 : solver_safety_wit_101_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH26 q) by lia.
  pose proof (RowBrow_bound__prefix_sum_safety m_pre n_pre i q ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_101_split_goal_2 : solver_safety_wit_101_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (PreH26 q) by lia.
  pose proof (RowBrow_bound__prefix_sum_safety m_pre n_pre i q ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_101 : solver_safety_wit_101.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_101_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_101_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_103_split_goal_1 : solver_safety_wit_103_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH22.
  pose proof (DPA_entry_bound__prefix_sum_safety m_pre n_pre i i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_103_split_goal_2 : solver_safety_wit_103_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite PreH22.
  pose proof (DPA_entry_bound__prefix_sum_safety m_pre n_pre i i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_103 : solver_safety_wit_103.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_103_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_103_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_114_split_goal_1 : solver_safety_wit_114_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (QPartial_entry_bound__q_update m_pre n_pre i t (i + t) ltac:(lia) ltac:(lia)) as HQ.
  pose proof (RowP_bound__q_update m_pre n_pre i t ltac:(lia)) as HP.
  rewrite PreH22.
  rewrite (PreH25 t ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_114_split_goal_2 : solver_safety_wit_114_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (QPartial_entry_bound__q_update m_pre n_pre i t (i + t) ltac:(lia) ltac:(lia)) as HQ.
  pose proof (RowP_bound__q_update m_pre n_pre i t ltac:(lia)) as HP.
  rewrite PreH22.
  rewrite (PreH25 t ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_114 : solver_safety_wit_114.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_114_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_114_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_6 : solver_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Zlength_Zeros__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Zlength_Zeros__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Zlength_Zeros__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH13.
  apply Zeros_snoc__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_5 : solver_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH12.
  apply Zeros_snoc__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_6 : solver_entail_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH11.
  apply Zeros_snoc__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply Zlength_Zeros__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply Zlength_Zeros__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply Zlength_Zeros__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_5 : solver_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre + 2) by lia.
  rewrite Hi in PreH11, PreH12, PreH13.
  rewrite PreH11, PreH12, PreH13.
  rewrite Hi.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Zlength_Zeros__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH15.
  apply Zeros_snoc__init_fill. lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = 2 * n_pre + 4) by lia.
  rewrite Hi in PreH14, PreH15 |- *.
  Exists (cons (Z.rem 1 m_pre) (@nil Z)) lQ_2 lP_2 lBrow_2 lA_2.
  rewrite Int64Array.full_unfold.
  rewrite Int64Array.seg_empty.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + intros k [Hk1 Hk2].
      assert (Hk : k = 0) by lia.
      subst k.
      change (Znth 0 (cons (Z.rem 1 m_pre) (@nil Z)) 0) with (Z.rem 1 m_pre).
      unfold Pow2Mod.
      rewrite Z.pow_0_r.
      rewrite Z.rem_small by lia.
      rewrite Z.mod_small by lia.
      reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_4 : solver_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_5 : solver_entail_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre + 1) by lia.
  rewrite Hi in PreH17 |- *.
  Exists lP_2 lBrow_2 lQ_2 lpow2_2 lA_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    1-11: lia.
    + exact PreH17.
    + rewrite PreH11. replace (1 - 1) with 0 by lia.
      symmetry. apply (proj1 (DP_init_state__pow2_table m_pre n_pre)).
    + rewrite PreH15. replace (1 - 1) with 0 by lia.
      symmetry. apply (proj2 (DP_init_state__pow2_table m_pre n_pre)).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (quot_div_nonneg__inner_j_entail (i - j + j + 2) 2 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (i - j + j + 2) 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound (i - j + j + 2) 2 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_eq__inner_j_entail with (lQ := lQ_2); try lia; try assumption.
  - rewrite PreH45.
    pose proof (DPQ_entry_bound__inner_j_entail m_pre n_pre (i - 1) (i - j - j - 1) ltac:(lia)).
    rewrite (PreH43 (i - j - (i - j + j + 2) ÷ 2) ltac:(lia)).
    pose proof (Pow2Mod_nonneg__inner_j_entail (i - j - (i - j + j + 2) ÷ 2) m_pre ltac:(lia)).
    pose proof (rem_nonneg__inner_j_entail
                  (Z.rem 1 m_pre + Pow2Mod (i - j - (i - j + j + 2) ÷ 2) m_pre
                   - Z.rem 1 m_pre + m_pre) m_pre ltac:(lia) ltac:(lia)).
    lia.
  - apply (Wfun_case1__inner_j_entail lQ_2 lpow2_2 m_pre n_pre i j); try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_2 : solver_entail_wit_11_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_3 : solver_entail_wit_11_1_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_4 : solver_entail_wit_11_1_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_5 : solver_entail_wit_11_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply rem_lt__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_6 : solver_entail_wit_11_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_nonneg__inner_j_entail; try lia.
  - rewrite PreH44.
    pose proof (DPA_entry_bound__inner_j_entail m_pre n_pre (i - 1) j ltac:(lia)). lia.
  - rewrite PreH45.
    pose proof (DPQ_entry_bound__inner_j_entail m_pre n_pre (i - 1) (i - j - j - 1) ltac:(lia)).
    rewrite (PreH43 (i - j - (i - j + j + 2) ÷ 2) ltac:(lia)).
    pose proof (Pow2Mod_nonneg__inner_j_entail (i - j - (i - j + j + 2) ÷ 2) m_pre ltac:(lia)).
    pose proof (rem_nonneg__inner_j_entail
                  (Z.rem 1 m_pre + Pow2Mod (i - j - (i - j + j + 2) ÷ 2) m_pre
                   - Z.rem 1 m_pre + m_pre) m_pre ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_eq__inner_j_entail with (lQ := lQ_2); try lia; try assumption.
  - rewrite PreH41.
    pose proof (DPQ_entry_bound__inner_j_entail m_pre n_pre (i - 1) (i - j - j - 1) ltac:(lia)).
    pose proof (rem_nonneg__inner_j_entail 1 m_pre ltac:(lia) ltac:(lia)).
    lia.
  - apply (Wfun_case2__inner_j_entail lQ_2 m_pre i j); try lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_2 : solver_entail_wit_11_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_3 : solver_entail_wit_11_2_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_4 : solver_entail_wit_11_2_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_5 : solver_entail_wit_11_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply rem_lt__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_6 : solver_entail_wit_11_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_nonneg__inner_j_entail; try lia.
  - rewrite PreH40.
    pose proof (DPA_entry_bound__inner_j_entail m_pre n_pre (i - 1) j ltac:(lia)). lia.
  - rewrite PreH41.
    pose proof (DPQ_entry_bound__inner_j_entail m_pre n_pre (i - 1) (i - j - j - 1) ltac:(lia)).
    pose proof (rem_nonneg__inner_j_entail 1 m_pre ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_1 : solver_entail_wit_11_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_eq__inner_j_entail with (lQ := lQ_2); try lia; try assumption.
  - rewrite (PreH37 (i - j - (i - j + j + 2) ÷ 2) ltac:(lia)).
    pose proof (Pow2Mod_nonneg__inner_j_entail (i - j - (i - j + j + 2) ÷ 2) m_pre ltac:(lia)).
    lia.
  - apply (Wfun_case3__inner_j_entail lQ_2 lpow2_2 m_pre n_pre i j); try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_2 : solver_entail_wit_11_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_3 : solver_entail_wit_11_3_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_4 : solver_entail_wit_11_3_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_5 : solver_entail_wit_11_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply rem_lt__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_6 : solver_entail_wit_11_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_nonneg__inner_j_entail; try lia.
  - rewrite PreH38.
    pose proof (DPA_entry_bound__inner_j_entail m_pre n_pre (i - 1) j ltac:(lia)). lia.
  - rewrite (PreH37 (i - j - (i - j + j + 2) ÷ 2) ltac:(lia)).
    pose proof (Pow2Mod_nonneg__inner_j_entail (i - j - (i - j + j + 2) ÷ 2) m_pre ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_11_3_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_1 : solver_entail_wit_11_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_eq__inner_j_entail with (lQ := lQ_2); try lia; try assumption.
  apply (Wfun_case4__inner_j_entail lQ_2 m_pre i j); try lia.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_2 : solver_entail_wit_11_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_3 : solver_entail_wit_11_4_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_4 : solver_entail_wit_11_4_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_5 : solver_entail_wit_11_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply rem_lt__inner_j_entail. lia.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_6 : solver_entail_wit_11_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply blocked_step_nonneg__inner_j_entail; try lia.
  rewrite PreH20.
  pose proof (DPA_entry_bound__inner_j_entail m_pre n_pre (i - 1) j ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_11_4_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = i) by lia.
  rewrite Hj in PreH21.
  apply PreH21. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = i) by lia.
  rewrite Hj in PreH20.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_4 : solver_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_5 : solver_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply DPA_length__row_value. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_6 : solver_entail_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = i) by lia.
  rewrite Hj in PreH20.
  unfold RowBlocked in PreH20.
  rewrite (DPA_step__row_value m_pre n_pre i ltac:(lia)).
  rewrite PreH18.
  f_equal.
  rewrite (PreH17 (i - 1) ltac:(lia)).
  unfold ARowVal.
  rewrite <- PreH20.
  apply rem_mod_shift__row_value; [lia |].
  unfold Pow2Mod.
  pose proof (Z.mod_pos_bound (2 ^ (i - 1)) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_3 : solver_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_4 : solver_entail_wit_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_5 : solver_entail_wit_13_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_6 : solver_entail_wit_13_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH24, PreH1.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__prefix_sum_entail.
  exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_4 : solver_entail_wit_14_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_5 : solver_entail_wit_14_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  pose proof (Z.mod_pos_bound (run + 0) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_6 : solver_entail_wit_14_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  pose proof (Z.mod_pos_bound (run + 0) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH26 q ltac:(lia)) as HB.
  pose proof (RowBrow_bound__prefix_sum_entail m_pre n_pre i q ltac:(lia)) as HBb.
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  rewrite HB.
  rewrite RowRun_step__prefix_sum_entail by lia.
  rewrite <- PreH25.
  unfold RowC, RowBrow.
  rewrite (proj2 (Z.eqb_neq q 0)) by lia.
  rewrite (proj2 (Z.ltb_lt q i)) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__prefix_sum_entail.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_4 : solver_entail_wit_14_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_5 : solver_entail_wit_14_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH26 q ltac:(lia)) as HB.
  pose proof (RowBrow_bound__prefix_sum_entail m_pre n_pre i q ltac:(lia)) as HBb.
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  pose proof (Z.mod_pos_bound (run + Znth q lBrow_2 0) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_6 : solver_entail_wit_14_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH26 q ltac:(lia)) as HB.
  pose proof (RowBrow_bound__prefix_sum_entail m_pre n_pre i q ltac:(lia)) as HBb.
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  pose proof (Z.mod_pos_bound (run + Znth q lBrow_2 0) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_1 : solver_entail_wit_14_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH22.
  rewrite (DPA_step_Znth__prefix_sum_entail m_pre n_pre i ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (ARowVal_bound__prefix_sum_entail (DPA m_pre n_pre (i - 1))
                (DPQ m_pre n_pre (i - 1)) i m_pre ltac:(lia)) as HA.
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  rewrite RowRun_step__prefix_sum_entail by lia.
  rewrite <- PreH25.
  unfold RowC.
  rewrite (proj2 (Z.eqb_neq q 0)) by lia.
  rewrite (proj2 (Z.ltb_ge q i)) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_2 : solver_entail_wit_14_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__prefix_sum_entail.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_3 : solver_entail_wit_14_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_4 : solver_entail_wit_14_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_5 : solver_entail_wit_14_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH22.
  rewrite (DPA_step_Znth__prefix_sum_entail m_pre n_pre i ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (ARowVal_bound__prefix_sum_entail (DPA m_pre n_pre (i - 1))
                (DPQ m_pre n_pre (i - 1)) i m_pre ltac:(lia)) as HA.
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  pose proof (Z.mod_pos_bound
                (run + ARowVal (DPA m_pre n_pre (i - 1)) (DPQ m_pre n_pre (i - 1)) i m_pre)
                m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_6 : solver_entail_wit_14_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH22.
  rewrite (DPA_step_Znth__prefix_sum_entail m_pre n_pre i ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (ARowVal_bound__prefix_sum_entail (DPA m_pre n_pre (i - 1))
                (DPQ m_pre n_pre (i - 1)) i m_pre ltac:(lia)) as HA.
  rewrite Zrem_mod_nonneg__prefix_sum_entail by lia.
  pose proof (Z.mod_pos_bound
                (run + ARowVal (DPA m_pre n_pre (i - 1)) (DPQ m_pre n_pre (i - 1)) i m_pre)
                m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH25. lia.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i + 1) with q by lia.
  exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_3 : solver_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_4 : solver_entail_wit_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite QPartial_zero__prefix_sum_entail.
  rewrite <- PreH21.
  exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_5 : solver_entail_wit_15_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_6 : solver_entail_wit_15_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_1 : solver_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_2 : solver_entail_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply DPQ_length__q_update; lia.
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_3 : solver_entail_wit_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_4 : solver_entail_wit_16_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH21.
  replace t with i by lia.
  apply QPartial_full__q_update; lia.
Qed.

Lemma proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_16_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_16_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_1 : solver_entail_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (QPartial_length_bound__q_update m_pre n_pre i (t + 1) ltac:(lia) ltac:(lia)) as [HL _].
  exact HL.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_2 : solver_entail_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_3 : solver_entail_wit_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (QAfterNat_step__q_update m_pre n_pre i t ltac:(lia)).
  assert (Hle : Z.leb (i + t) (2 * n_pre) = true) by (apply Z.leb_le; lia).
  rewrite Hle.
  rewrite PreH22.
  rewrite (PreH25 t ltac:(lia)).
  unfold RowP.
  f_equal.
  apply Z.rem_mod_nonneg.
  - pose proof (QPartial_entry_bound__q_update m_pre n_pre i t (i + t) ltac:(lia) ltac:(lia)) as HQ.
    pose proof (PEntry_bound__q_update (DPA m_pre n_pre (i - 1)) (DPQ m_pre n_pre (i - 1)) i m_pre t ltac:(lia)) as HP.
    lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_1 : solver_entail_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_2 : solver_entail_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply DPQ_length__q_update; lia.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_3 : solver_entail_wit_18_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply DPA_length__row_value; lia.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_4 : solver_entail_wit_18_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i + 1 - 1) with i by lia.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_5 : solver_entail_wit_18_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i + 1 - 1) with i by lia.
  exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_18 : solver_entail_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_19 : solver_entail_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre + 1) by lia.
  subst i.
  replace (n_pre + 1 - 1) with n_pre in PreH14 by lia.
  Exists (SomeList lP_2) (SomeList lBrow_2) (SomeListUndefTail lpow2_2)
         (SomeList lQ_2) (SomeList lA).
  Exists lP_2 lBrow_2 lpow2_2 lQ_2 lA.
  assert (HcA : Zlength (SomeList lA) = n_pre + 2)
    by (unfold SomeList; rewrite Zlength_map_L2; lia).
  assert (HcQ : Zlength (SomeList lQ_2) = 2 * n_pre + 4)
    by (unfold SomeList; rewrite Zlength_map_L2; lia).
  assert (HcB : Zlength (SomeList lBrow_2) = n_pre + 2)
    by (unfold SomeList; rewrite Zlength_map_L2; lia).
  assert (HcP : Zlength (SomeList lP_2) = n_pre + 2)
    by (unfold SomeList; rewrite Zlength_map_L2; lia).
  assert (Hcpow2 : Zlength (SomeListUndefTail lpow2_2) = n_pre + 2)
    by (unfold SomeListUndefTail, SomeList;
        rewrite Zlength_app, Zlength_map_L2, Zlength_cons, Zlength_nil; lia).
  rewrite HcA, HcQ, HcB, HcP, Hcpow2.
  unfold SomeListUndefTail, SomeList.
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.full_to_mixed_full A (n_pre + 2) lA).
    sep_apply_l_atomic (Int64Array.full_to_mixed_full Q (2 * n_pre + 4) lQ_2).
    sep_apply_l_atomic (Int64Array.full_to_mixed_full Brow (n_pre + 2) lBrow_2).
    sep_apply_l_atomic (Int64Array.full_to_mixed_full P (n_pre + 2) lP_2).
    sep_apply_l_atomic (Int64Array.full_to_mixed_full pow2 (n_pre + 1) lpow2_2).
    sep_apply_l_atomic (Int64Array.undef_seg_to_mixed_seg pow2 (n_pre + 1) (n_pre + 2)).
    replace (Z.to_nat (n_pre + 2 - (n_pre + 1))) with 1%nat by lia.
    cbn [repeat].
    sep_apply_l_atomic
      (Int64Array.mixed_seg_to_mixed_full pow2 (n_pre + 1) (n_pre + 2) (@None Z :: nil)).
    sep_apply_l_atomic
      (Int64Array.mixed_full_merge_to_mixed_full pow2 (n_pre + 1) (n_pre + 2)
         (map Some lpow2_2) (@None Z :: nil)).
    + dump_pre_spatial. lia.
    + cancel (Int64Array.mixed_full A (n_pre + 2) (map Some lA)).
      cancel (Int64Array.mixed_full Q (2 * n_pre + 4) (map Some lQ_2)).
      cancel (Int64Array.mixed_full pow2 (n_pre + 2) (map Some lpow2_2 +:: None)).
      cancel (Int64Array.mixed_full Brow (n_pre + 2) (map Some lBrow_2)).
      cancel (Int64Array.mixed_full P (n_pre + 2) (map Some lP_2)).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try reflexivity.
    all: try exact PreH14.
    rewrite PreH14. apply DPA_spec; lia.
Qed.

