From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P064_1992F_valuable_cards_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P064_1992F_valuable_cards_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P064_1992F_valuable_cards_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH28 j ltac:(lia)).
  destruct PreH28 as [Hproduct_pos Hproduct_bound].
  assert (Hmul :
    Znth (j - 0) products_before_append 0 * v <=
    (x_pre ÷ v) * v).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  pose proof (Z.mul_quot_le x_pre v ltac:(lia) ltac:(lia)) as Hquot.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH28 j ltac:(lia)).
  destruct PreH28 as [Hproduct_pos Hproduct_bound].
  dump_pre_spatial.
  replace (j - 0) with j by lia.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH28 j ltac:(lia)).
  destruct PreH28 as [Hproduct_pos Hproduct_bound].
  assert (Hmul :
    Znth (j - 0) products_before_append 0 * v <=
    (x_pre ÷ v) * v).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  pose proof (Z.mul_quot_le x_pre v ltac:(lia) ltac:(lia)) as Hquot.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH28 j ltac:(lia)).
  destruct PreH28 as [Hproduct_pos Hproduct_bound].
  dump_pre_spatial.
  replace (j - 0) with j by lia.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH29 j ltac:(lia)).
  destruct PreH29 as [Hproduct_pos Hproduct_bound].
  assert (Hmul :
    Znth (j - 0) products_before_append 0 * v <=
    (x_pre ÷ v) * v).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  pose proof (Z.mul_quot_le x_pre v ltac:(lia) ltac:(lia)) as Hquot.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH29 j ltac:(lia)).
  destruct PreH29 as [Hproduct_pos Hproduct_bound].
  dump_pre_spatial.
  replace (j - 0) with j by lia.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH29 j ltac:(lia)).
  destruct PreH29 as [Hproduct_pos Hproduct_bound].
  assert (Hmul :
    Znth (j - 0) products_before_append 0 * v <=
    (x_pre ÷ v) * v).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  pose proof (Z.mul_quot_le x_pre v ltac:(lia) ltac:(lia)) as Hquot.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH29 j ltac:(lia)).
  destruct PreH29 as [Hproduct_pos Hproduct_bound].
  dump_pre_spatial.
  replace (j - 0) with j by lia.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  Exists (replace_Znth 1 1 (repeat 0 (Z.to_nat (x_pre + 1))))
    (1 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single retval_2 0 1).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg retval_2 0 1 (1 :: nil)).
    cancel (IntArray.undef_seg retval_2 1 (x_pre + 1)).
    cancel (UCharArray.full retval (x_pre + 1)
      (replace_Znth 1 1 (repeat 0 (Z.to_nat (x_pre + 1))))).
  - pose proof (valuable_initial_states__initialization x_pre values PreH3)
      as [Houter [Hforced [Haligned [Hbitmap_len Hbitmap]]]].
    split_pures; dump_pre_spatial; try assumption; try lia.
    + reflexivity.
    + intros k Hk.
      destruct Hk as [Hk0 Hk1].
      assert (k = 0) by lia. subst k.
      rewrite Znth0_cons. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH7 i ltac:(lia)) as Hvalue.
  destruct Hvalue as [Hvalue_pos Hvalue_bound].
  pose proof (positive_remainder_divisor_le__initialization
    x_pre (Znth i values 0) ltac:(lia) ltac:(lia) PreH22) as Hvalue_x.
  destruct (valuable_closure_initial__initialization
    x_pre values i segments products_2 (Znth i values 0) PreH20)
    as [segment Hclosure].
  Exists segment bitmap_2 products_2 products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_2).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite PreH13.
    symmetry. apply sublist_self. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  replace (j - 0) with j in * by lia.
  pose proof (PreH29 j ltac:(lia)) as Hjbound.
  pose proof (valuable_product_quot_bound__control_routing
    x_pre v (Znth j products_before_append 0)
    ltac:(lia) ltac:(lia) PreH2) as Hproduct.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  replace (j_2 - 0) with j_2 in * by lia.
  pose proof (PreH29 j_2 ltac:(lia)) as Hjbound.
  pose proof (valuable_product_quot_bound__control_routing
    x_pre v_2 (Znth j_2 products_before_append 0)
    ltac:(lia) ltac:(lia) PreH2) as Hproduct.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = old) by lia.
  subst j.
  Exists segment_2 bitmap_2 products_2 base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_2).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = old) by lia.
  subst j.
  Exists segment_2 bitmap_2 products_2 base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_2).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hp : Znth j products_before_append 0 * v = x_pre) by exact PreH1.
  assert (Hzero : Znth (Znth j products_before_append 0 * v) bitmap_2 0 = 0)
    by exact PreH2.
  assert (Hbase : sublist 0 old (products_before_append ++
      (Znth j products_before_append 0 * v) :: nil) = base_products_2).
  { rewrite sublist_split_app_l by lia. symmetry. exact PreH40. }
  assert (Hfresh : ~ In (Znth j products_before_append 0 * v)
      products_before_append).
  {
    intro Hin.
    assert (Hpbound : 0 <= Znth j products_before_append 0 * v <= x_pre)
      by (rewrite Hp; lia).
    specialize (PreH54 (Znth j products_before_append 0 * v) Hpbound).
    destruct (in_dec Z.eq_dec (Znth j products_before_append 0 * v)
      products_before_append); [rewrite PreH54 in Hzero; discriminate | contradiction].
  }
  assert (Hdiv : exists k, x_pre =
      (Znth j products_before_append 0 * v) * k) by (exists 1; nia).
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) (products_before_append ++
        (Znth j products_before_append 0 * v) :: nil) 1).
  {
    assert (Hbase_z : Znth j base_products_2 0 =
        Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_append_fresh__append_cycle
      x_pre segment_2 v base_products_2 j products_before_append reaches
      (Znth j products_before_append 0 * v)) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(rewrite Hbase_z; reflexivity)
      ltac:(rewrite Hp; lia) Hdiv Hfresh PreH53).
    destruct (Z.eq_dec (Znth j products_before_append 0 * v) x_pre);
      [exact Hstep | lia].
  }
  assert (Hbitmap : ValuableBitmap x_pre
      (products_before_append ++ (Znth j products_before_append 0 * v) :: nil)
      (replace_Znth (Znth j products_before_append 0 * v) 1 bitmap_2)).
  { eapply valuable_bitmap_fresh__append_cycle; eauto; lia. }
  assert (Hcount_lt : count < x_pre).
  {
    assert (Hxnot : ~ In x_pre products_before_append)
      by (rewrite <- Hp; exact Hfresh).
    pose proof PreH53 as Hstate.
    unfold ValuableClosureState in Hstate.
    destruct Hstate as [Hreachable [Hnodup [Hmembers Hreaches]]].
    destruct Hreachable as [Hbase_nodup Hbase_members].
    assert (Hrange : forall p, In p products_before_append -> 1 <= p < x_pre).
    {
      intros p Hin.
      assert (Hpne : p <> x_pre) by (intro Heq; subst p; contradiction).
      apply Hmembers in Hin.
      destruct Hin as [Hinbase | [q [Hinq [Heq [Hbounds Hdivides]]]]].
      - apply Hbase_members in Hinbase. lia.
      - lia.
    }
    pose proof (valuable_nodup_positive_bounded_length__append_cycle
      x_pre products_before_append ltac:(lia) Hnodup Hrange) as Hlen.
    lia.
  }
  Exists segment_2
    (replace_Znth (Znth j products_before_append 0 * v) 1 bitmap_2)
    (products_before_append ++ (Znth j products_before_append 0 * v) :: nil)
    base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 (count + 1)
      (products_before_append ++ (Znth j products_before_append 0 * v) :: nil)).
    cancel (IntArray.undef_seg products_buf (count + 1) (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1)
      (replace_Znth (Znth j products_before_append 0 * v) 1 bitmap_2)).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite Zlength_app_cons.
    all: try rewrite Hbase.
    all: try rewrite PreH33 in *.
    all: try lia.
    all: try reflexivity.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k (Zlength products_before_append)).
    + rewrite app_Znth1 by lia. apply PreH49. lia.
    + assert (k = Zlength products_before_append) by lia.
      subst k. rewrite app_Znth2 by lia.
      replace (Zlength products_before_append - Zlength products_before_append)
        with 0 by lia. rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hp : Znth j products_before_append 0 * v = x_pre) by exact PreH1.
  assert (Hzero : Znth (Znth j products_before_append 0 * v) bitmap_2 0 = 0)
    by exact PreH2.
  assert (Hbase : sublist 0 old (products_before_append ++
      (Znth j products_before_append 0 * v) :: nil) = base_products_2).
  { rewrite sublist_split_app_l by lia. symmetry. exact PreH40. }
  assert (Hfresh : ~ In (Znth j products_before_append 0 * v)
      products_before_append).
  {
    intro Hin.
    assert (Hpbound : 0 <= Znth j products_before_append 0 * v <= x_pre)
      by (rewrite Hp; lia).
    specialize (PreH54 (Znth j products_before_append 0 * v) Hpbound).
    destruct (in_dec Z.eq_dec (Znth j products_before_append 0 * v)
      products_before_append); [rewrite PreH54 in Hzero; discriminate | contradiction].
  }
  assert (Hdiv : exists k, x_pre =
      (Znth j products_before_append 0 * v) * k) by (exists 1; nia).
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) (products_before_append ++
        (Znth j products_before_append 0 * v) :: nil) 1).
  {
    assert (Hbase_z : Znth j base_products_2 0 =
        Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_append_fresh__append_cycle
      x_pre segment_2 v base_products_2 j products_before_append reaches
      (Znth j products_before_append 0 * v)) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(rewrite Hbase_z; reflexivity)
      ltac:(rewrite Hp; lia) Hdiv Hfresh PreH53).
    destruct (Z.eq_dec (Znth j products_before_append 0 * v) x_pre);
      [exact Hstep | lia].
  }
  assert (Hbitmap : ValuableBitmap x_pre
      (products_before_append ++ (Znth j products_before_append 0 * v) :: nil)
      (replace_Znth (Znth j products_before_append 0 * v) 1 bitmap_2)).
  { eapply valuable_bitmap_fresh__append_cycle; eauto; lia. }
  assert (Hcount_lt : count < x_pre).
  {
    assert (Hxnot : ~ In x_pre products_before_append)
      by (rewrite <- Hp; exact Hfresh).
    pose proof PreH53 as Hstate.
    unfold ValuableClosureState in Hstate.
    destruct Hstate as [Hreachable [Hnodup [Hmembers Hreaches]]].
    destruct Hreachable as [Hbase_nodup Hbase_members].
    assert (Hrange : forall p, In p products_before_append -> 1 <= p < x_pre).
    {
      intros p Hin.
      assert (Hpne : p <> x_pre) by (intro Heq; subst p; contradiction).
      apply Hmembers in Hin.
      destruct Hin as [Hinbase | [q [Hinq [Heq [Hbounds Hdivides]]]]].
      - apply Hbase_members in Hinbase. lia.
      - lia.
    }
    pose proof (valuable_nodup_positive_bounded_length__append_cycle
      x_pre products_before_append ltac:(lia) Hnodup Hrange) as Hlen.
    lia.
  }
  Exists segment_2
    (replace_Znth (Znth j products_before_append 0 * v) 1 bitmap_2)
    (products_before_append ++ (Znth j products_before_append 0 * v) :: nil)
    base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 (count + 1)
      (products_before_append ++ (Znth j products_before_append 0 * v) :: nil)).
    cancel (IntArray.undef_seg products_buf (count + 1) (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1)
      (replace_Znth (Znth j products_before_append 0 * v) 1 bitmap_2)).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite Zlength_app_cons.
    all: try rewrite Hbase.
    all: try rewrite PreH33 in *.
    all: try lia.
    all: try reflexivity.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k (Zlength products_before_append)).
    + rewrite app_Znth1 by lia. apply PreH49. lia.
    + assert (k = Zlength products_before_append) by lia.
      subst k. rewrite app_Znth2 by lia.
      replace (Zlength products_before_append - Zlength products_before_append)
        with 0 by lia. rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hp : Znth j products_before_append 0 * v = x_pre) by exact PreH1.
  assert (Hin : In (Znth j products_before_append 0 * v)
      products_before_append).
  {
    specialize (PreH54 (Znth j products_before_append 0 * v) ltac:(lia)).
    destruct (in_dec Z.eq_dec (Znth j products_before_append 0 * v)
      products_before_append) as [Hin | Hnotin].
    - exact Hin.
    - rewrite PreH54 in PreH2. contradiction.
  }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append 1).
  {
    assert (Hbase_z : Znth j base_products_2 0 =
        Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_duplicate__append_cycle
      x_pre segment_2 v base_products_2 j products_before_append reaches
      (Znth j products_before_append 0 * v)) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(rewrite Hbase_z; reflexivity)
      Hin PreH53).
    destruct (Z.eq_dec (Znth j products_before_append 0 * v) x_pre);
      [exact Hstep | lia].
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH33 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_4 : solver_entail_wit_6_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hp : Znth j products_before_append 0 * v = x_pre) by exact PreH1.
  assert (Hin : In (Znth j products_before_append 0 * v)
      products_before_append).
  {
    specialize (PreH54 (Znth j products_before_append 0 * v) ltac:(lia)).
    destruct (in_dec Z.eq_dec (Znth j products_before_append 0 * v)
      products_before_append) as [Hin | Hnotin].
    - exact Hin.
    - rewrite PreH54 in PreH2. contradiction.
  }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append 1).
  {
    assert (Hbase_z : Znth j base_products_2 0 =
        Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_duplicate__append_cycle
      x_pre segment_2 v base_products_2 j products_before_append reaches
      (Znth j products_before_append 0 * v)) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(rewrite Hbase_z; reflexivity)
      Hin PreH53).
    destruct (Z.eq_dec (Znth j products_before_append 0 * v) x_pre);
      [exact Hstep | lia].
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH33 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_5 : solver_entail_wit_6_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  set (p := Znth j products_before_append 0 * v) in *.
  assert (Hbase : sublist 0 old (products_before_append ++ p :: nil) =
      base_products_2).
  { rewrite sublist_split_app_l by lia. symmetry. exact PreH40. }
  assert (Hfresh : ~ In p products_before_append).
  {
    intro Hin. specialize (PreH54 p ltac:(lia)).
    destruct (in_dec Z.eq_dec p products_before_append).
    - rewrite PreH54 in PreH2. discriminate.
    - contradiction.
  }
  assert (Hdiv : exists k, x_pre = p * k).
  { exists (Z.quot x_pre p). pose proof (Z.quot_rem x_pre p ltac:(lia)); nia. }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) (products_before_append ++ p :: nil) reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_append_fresh__append_cycle x_pre segment_2 v
      base_products_2 j products_before_append reaches p) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(unfold p; rewrite Hbase_z; reflexivity)
      ltac:(lia) Hdiv Hfresh PreH53).
    destruct (Z.eq_dec p x_pre); [contradiction | exact Hstep].
  }
  assert (Hbitmap : ValuableBitmap x_pre (products_before_append ++ p :: nil)
      (replace_Znth p 1 bitmap_2)).
  { eapply valuable_bitmap_fresh__append_cycle; eauto; lia. }
  assert (Hcount_bound : count + 1 <= x_pre).
  {
    pose proof Hclosure as Hstate. unfold ValuableClosureState in Hstate.
    destruct Hstate as [Hreachable [Hnodup [Hmembers Hreaches]]].
    destruct Hreachable as [Hbase_nodup Hbase_members].
    assert (Hrange : forall z, In z (products_before_append ++ p :: nil) ->
        1 <= z <= x_pre).
    {
      intros z Hin. apply Hmembers in Hin.
      destruct Hin as [Hinbase | [q [Hinq [Heq [Hbounds Hdivides]]]]].
      - apply Hbase_members in Hinbase. lia.
      - lia.
    }
    pose proof (valuable_nodup_bounded_length__append_cycle x_pre
      (products_before_append ++ p :: nil) ltac:(lia) Hnodup Hrange) as Hlen.
    rewrite Zlength_app_cons in Hlen. lia.
  }
  Exists segment_2 (replace_Znth p 1 bitmap_2)
    (products_before_append ++ p :: nil) base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 (count + 1)
      (products_before_append ++ p :: nil)).
    cancel (IntArray.undef_seg products_buf (count + 1) (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) (replace_Znth p 1 bitmap_2)).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite Zlength_app_cons.
    all: try rewrite Hbase.
    all: try rewrite PreH33 in *.
    all: try lia.
    all: try reflexivity.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try lia.
    intros k Hk. destruct (Z_lt_ge_dec k (Zlength products_before_append)).
    + rewrite app_Znth1 by lia. apply PreH49. lia.
    + assert (k = Zlength products_before_append) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (Zlength products_before_append - Zlength products_before_append)
        with 0 by lia. rewrite Znth0_cons. unfold p. lia.
Qed.

Lemma proof_of_solver_entail_wit_6_6 : solver_entail_wit_6_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  set (p := Znth j products_before_append 0 * v) in *.
  assert (Hbase : sublist 0 old (products_before_append ++ p :: nil) =
      base_products_2).
  { rewrite sublist_split_app_l by lia. symmetry. exact PreH40. }
  assert (Hfresh : ~ In p products_before_append).
  {
    intro Hin. specialize (PreH54 p ltac:(lia)).
    destruct (in_dec Z.eq_dec p products_before_append).
    - rewrite PreH54 in PreH2. discriminate.
    - contradiction.
  }
  assert (Hdiv : exists k, x_pre = p * k).
  { exists (Z.quot x_pre p). pose proof (Z.quot_rem x_pre p ltac:(lia)); nia. }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) (products_before_append ++ p :: nil) reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_append_fresh__append_cycle x_pre segment_2 v
      base_products_2 j products_before_append reaches p) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(unfold p; rewrite Hbase_z; reflexivity)
      ltac:(lia) Hdiv Hfresh PreH53).
    destruct (Z.eq_dec p x_pre); [contradiction | exact Hstep].
  }
  assert (Hbitmap : ValuableBitmap x_pre (products_before_append ++ p :: nil)
      (replace_Znth p 1 bitmap_2)).
  { eapply valuable_bitmap_fresh__append_cycle; eauto; lia. }
  assert (Hcount_bound : count + 1 <= x_pre).
  {
    pose proof Hclosure as Hstate. unfold ValuableClosureState in Hstate.
    destruct Hstate as [Hreachable [Hnodup [Hmembers Hreaches]]].
    destruct Hreachable as [Hbase_nodup Hbase_members].
    assert (Hrange : forall z, In z (products_before_append ++ p :: nil) ->
        1 <= z <= x_pre).
    {
      intros z Hin. apply Hmembers in Hin.
      destruct Hin as [Hinbase | [q [Hinq [Heq [Hbounds Hdivides]]]]].
      - apply Hbase_members in Hinbase. lia.
      - lia.
    }
    pose proof (valuable_nodup_bounded_length__append_cycle x_pre
      (products_before_append ++ p :: nil) ltac:(lia) Hnodup Hrange) as Hlen.
    rewrite Zlength_app_cons in Hlen. lia.
  }
  Exists segment_2 (replace_Znth p 1 bitmap_2)
    (products_before_append ++ p :: nil) base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 (count + 1)
      (products_before_append ++ p :: nil)).
    cancel (IntArray.undef_seg products_buf (count + 1) (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) (replace_Znth p 1 bitmap_2)).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite Zlength_app_cons.
    all: try rewrite Hbase.
    all: try rewrite PreH33 in *.
    all: try lia.
    all: try reflexivity.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try lia.
    intros k Hk. destruct (Z_lt_ge_dec k (Zlength products_before_append)).
    + rewrite app_Znth1 by lia. apply PreH49. lia.
    + assert (k = Zlength products_before_append) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (Zlength products_before_append - Zlength products_before_append)
        with 0 by lia. rewrite Znth0_cons. unfold p. lia.
Qed.

Lemma proof_of_solver_entail_wit_6_7 : solver_entail_wit_6_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  set (p := Znth j products_before_append 0 * v) in *.
  assert (Hin : In p products_before_append).
  {
    specialize (PreH54 p ltac:(lia)).
    destruct (in_dec Z.eq_dec p products_before_append) as [Hin | Hnotin].
    - exact Hin.
    - rewrite PreH54 in PreH2. contradiction.
  }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_duplicate__append_cycle x_pre segment_2 v
      base_products_2 j products_before_append reaches p) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(unfold p; rewrite Hbase_z; reflexivity)
      Hin PreH53).
    destruct (Z.eq_dec p x_pre); [contradiction | exact Hstep].
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH33 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_8 : solver_entail_wit_6_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  set (p := Znth j products_before_append 0 * v) in *.
  assert (Hin : In p products_before_append).
  {
    specialize (PreH54 p ltac:(lia)).
    destruct (in_dec Z.eq_dec p products_before_append) as [Hin | Hnotin].
    - exact Hin.
    - rewrite PreH54 in PreH2. contradiction.
  }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH40, Znth_sublist0 by lia. reflexivity. }
    pose proof (valuable_closure_duplicate__append_cycle x_pre segment_2 v
      base_products_2 j products_before_append reaches p) as Hstep.
    specialize (Hstep ltac:(lia) ltac:(unfold p; rewrite Hbase_z; reflexivity)
      Hin PreH53).
    destruct (Z.eq_dec p x_pre); [contradiction | exact Hstep].
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH33 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_9 : solver_entail_wit_6_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hlarge : x_pre < Znth j products_before_append 0 * v).
  {
    eapply quotient_and_remainder_product_bounds__append_cycle.
    - lia.
    - lia.
    - exact PreH15.
    - lia.
  }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH19, Znth_sublist0 by lia. reflexivity. }
    eapply valuable_closure_skip__append_cycle.
    - lia.
    - exact PreH32.
    - left. rewrite Hbase_z. exact Hlarge.
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH12 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_10 : solver_entail_wit_6_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hlarge : x_pre < Znth j products_before_append 0 * v).
  {
    eapply quotient_and_remainder_product_bounds__append_cycle.
    - lia.
    - lia.
    - exact PreH15.
    - lia.
  }
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH19, Znth_sublist0 by lia. reflexivity. }
    eapply valuable_closure_skip__append_cycle.
    - lia.
    - exact PreH32.
    - left. rewrite Hbase_z. exact Hlarge.
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH12 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_11 : solver_entail_wit_6_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH20, Znth_sublist0 by lia. reflexivity. }
    eapply valuable_closure_skip__append_cycle.
    - lia.
    - exact PreH33.
    - right. rewrite Hbase_z. exact PreH1.
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH13 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_6_12 : solver_entail_wit_6_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hclosure : ValuableClosureState x_pre segment_2 v base_products_2
      (j + 1) products_before_append reaches).
  {
    assert (Hbase_z : Znth j base_products_2 0 = Znth j products_before_append 0).
    { rewrite PreH20, Znth_sublist0 by lia. reflexivity. }
    eapply valuable_closure_skip__append_cycle.
    - lia.
    - exact PreH33.
    - right. rewrite Hbase_z. exact PreH1.
  }
  Exists segment_2 bitmap_2 products_before_append base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_before_append).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try rewrite PreH13 in *.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst reaches.
  assert (Hclearing : ValuableClearingState x_pre products_2 0 bitmap_2).
  {
    unfold ValuableClearingState.
    rewrite sublist_self by reflexivity.
    exact PreH29.
  }
  replace (segments + 1 - 1) with segments by lia.
  Exists segment_2 bitmap_2 products_2 base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_2).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1) bitmap_2).
  - repeat split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnodup : NoDup products_2).
  { unfold ValuableClosureState in PreH30. tauto. }
  assert (Hstep : ValuableClearingState x_pre products_2 (j + 1)
      (replace_Znth (Znth j products_2 0) 0 bitmap_2)).
  {
    eapply valuable_clearing_step__clearing_reset.
    - lia.
    - exact PreH25.
    - exact Hnodup.
    - intros k Hk. apply PreH26. lia.
    - exact PreH31.
  }
  replace (j - 0) with j by lia.
  Exists segment_2
    (replace_Znth (Znth j products_2 0) 0 bitmap_2)
    products_2 base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.seg products_buf 0 count products_2).
    cancel (IntArray.undef_seg products_buf count (x_pre + 1)).
    cancel (UCharArray.full used (x_pre + 1)
      (replace_Znth (Znth j products_2 0) 0 bitmap_2)).
  - repeat split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia;
      try (rewrite Zlength_replace_Znth; assumption).
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hreset :
      Zlength (replace_Znth 1 1 bitmap_2) = x_pre + 1 /\
      ValuableBitmap x_pre (1 :: nil) (replace_Znth 1 1 bitmap_2)).
  {
    apply (valuable_clearing_reset__clearing_reset
      x_pre products bitmap_2 j).
    - lia.
    - exact PreH25.
    - lia.
    - lia.
    - exact PreH31.
  }
  destruct Hreset as [Hreset_len Hreset_bitmap].
  assert (Hprefix :
      sublist 0 1 (replace_Znth 0 1 products) = (1 :: nil)).
  {
    change (sublist 0 (0 + 1) (replace_Znth 0 1 products) = (1 :: nil)).
    rewrite (sublist_single 0 0 (replace_Znth 0 1 products))
      by (rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  Exists (replace_Znth 1 1 bitmap_2) segment_2 products base_products_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (UCharArray.full used (x_pre + 1)
      (replace_Znth 1 1 bitmap_2)).
    sep_apply_l_atomic
      (IntArray.full_split_to_seg products_buf 1 count
        (replace_Znth 0 1 products)).
    + dump_pre_spatial. lia.
    + rewrite Hprefix.
      sep_apply_l_atomic
        (IntArray.seg_to_undef_seg products_buf 1 count
          (sublist 1 count (replace_Znth 0 1 products))).
      sep_apply_l_atomic
        (IntArray.undef_seg_merge_to_undef_seg
          products_buf 1 count (x_pre + 1)).
      * dump_pre_spatial. lia.
      * cancel (IntArray.seg products_buf 0 1 (1 :: nil)).
        cancel (IntArray.undef_seg products_buf 1 (x_pre + 1)).
  - repeat split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ValuableBitmap in *.
  intros p Hp.
  destruct (Z.eq_dec p v) as [Heq | Hneq].
  - subst p.
    rewrite Znth_replace_Znth_Same by (rewrite PreH41; lia).
    destruct (in_dec Z.eq_dec v (1 :: v :: nil)); [reflexivity|].
    exfalso. apply n. simpl. tauto.
  - assert (Hvbound : 0 <= v < Zlength bitmap_2) by
      (rewrite PreH41; lia).
    assert (Hpbound : 0 <= p < Zlength bitmap_2) by
      (rewrite PreH41; lia).
    rewrite Znth_replace_Znth_Diff by auto.
    specialize (PreH42 p Hp).
    destruct (in_dec Z.eq_dec p (1 :: v :: nil)) as [Hin | Hnotin];
      destruct (in_dec Z.eq_dec p (1 :: nil)) as [Hin1 | Hnotin1].
    + rewrite PreH42. reflexivity.
    + exfalso. simpl in Hin.
      destruct Hin as [Heq1 | [Heqv | []]]; subst;
        [apply Hnotin1; simpl; auto | contradiction].
    + exfalso. simpl in Hin1.
      destruct Hin1 as [Heq1 | []]. subst.
      apply Hnotin. simpl. auto.
    + rewrite PreH42. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 <= i < Zlength values) by lia.
  assert (Hvnotx : v <> x_pre).
  {
    rewrite PreH25.
    apply pre_value_not_x__outer_transition with (i := i); assumption.
  }
  assert (Hvnotone : v <> 1).
  {
    intro Heq. subst v.
    pose proof (valuable_bitmap_zero_not_member__outer_transition
      x_pre (1 :: nil) bitmap_2 1 PreH42) as Hnotin.
    specialize (Hnotin ltac:(lia)).
    apply Hnotin. rewrite <- Heq. exact PreH1.
    simpl. auto.
  }
  assert (Hdiv : exists k, x_pre = v * k).
  { apply rem_zero_divides__outer_transition. exact PreH28. }
  assert (Hsingle : sublist i (i + 1) values = v :: nil).
  {
    rewrite (sublist_single 0 i values) by exact Hi.
    rewrite <- PreH25. reflexivity.
  }
  pose proof (reachable_singleton_products__outer_transition
    x_pre v PreH17 ltac:(lia) Hdiv) as Htables.
  destruct Htables as [Hfresh _]. specialize (Hfresh Hvnotone).
  assert (Hnewreach : ReachableDivisorProducts x_pre
    (sublist i (i + 1) values) (1 :: v :: nil)).
  { rewrite Hsingle. exact Hfresh. }
  assert (Hnewbad : BadCardSegment x_pre (sublist i (i + 1) values)).
  {
    eapply reachable_table_absent_bad__outer_transition.
    - lia.
    - exact Hnewreach.
    - simpl. intros [Heq | [Heq | []]]; lia.
  }
  assert (Htrigger : forall starts,
    ValuablePrefixCuts x_pre values i (segments - 1) starts ->
    ReachableDivisorProducts x_pre
      (sublist (Znth (Zlength starts - 1) starts 0) i values)
      base_products ->
    ProductReachable
      (sublist (Znth (Zlength starts - 1) starts 0) (i + 1) values)
      x_pre).
  {
    intros starts Hcuts Hreach.
    pose proof Hcuts as Hcuts0.
    unfold ValuablePrefixCuts in Hcuts0.
    destruct Hcuts0 as
      (_ & _ & _ & _ & Hlast & _ & _ & Hbadlive & _).
    pose proof PreH40 as Hclosure.
    rewrite PreH31 in Hclosure.
    pose proof (closure_to_reachable_snoc__outer_transition
      x_pre
      (sublist (Znth (Zlength starts - 1) starts 0) i values)
      segment v base_products old_products 1
      PreH17 PreH26 Hclosure Hreach Hbadlive) as Hextended.
    destruct Hextended as [_ [_ Hnotbad]].
    specialize (Hnotbad eq_refl).
    apply not_bad_product_reachable__outer_transition.
    rewrite (sublist_snoc__outer_transition Z 0 values
      (Znth (Zlength starts - 1) starts 0) i) by lia.
    rewrite <- PreH25. exact Hnotbad.
  }
  replace segments with ((segments - 1) + 1) by lia.
  eapply valuable_aligned_forced_cut__outer_transition;
    eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_forced.
  exact (proof_of_solver_entail_wit_14_1_split_goal_2
    values n_pre x_pre segment base_products old_products bitmap_2 i
    v segments old count reaches
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
    PreH38 PreH39 PreH40 PreH41 PreH42).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_4 : solver_entail_wit_14_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_outer.
  exact (proof_of_solver_entail_wit_14_1_split_goal_2
    values n_pre x_pre segment base_products old_products bitmap_2 i
    v segments old count reaches
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
    PreH38 PreH39 PreH40 PreH41 PreH42).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_5 : solver_entail_wit_14_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (k_2 = 0 \/ k_2 = 1) as [-> | ->] by lia.
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_6 : solver_entail_wit_14_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__outer_transition.
  exact PreH41.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_7 : solver_entail_wit_14_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_8 : solver_entail_wit_14_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH21. assumption.
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
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_7.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_8.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 <= i < Zlength values) by lia.
  assert (Hvone : v = 1).
  {
    pose proof (valuable_bitmap_nonzero_member__outer_transition
      x_pre (1 :: nil) bitmap_2 v PreH42 ltac:(lia) PreH1) as Hin.
    simpl in Hin. destruct Hin as [Heq | []]. symmetry. exact Heq.
  }
  assert (Hdiv : exists k, x_pre = v * k).
  { apply rem_zero_divides__outer_transition. exact PreH28. }
  assert (Hsingle : sublist i (i + 1) values = v :: nil).
  {
    rewrite (sublist_single 0 i values) by exact Hi.
    rewrite <- PreH25. reflexivity.
  }
  pose proof (reachable_singleton_products__outer_transition
    x_pre v PreH17 ltac:(lia) Hdiv) as Htables.
  destruct Htables as [_ Hduplicate]. specialize (Hduplicate Hvone).
  assert (Hnewreach : ReachableDivisorProducts x_pre
    (sublist i (i + 1) values) (1 :: nil)).
  { rewrite Hsingle. exact Hduplicate. }
  assert (Hnewbad : BadCardSegment x_pre (sublist i (i + 1) values)).
  {
    eapply reachable_table_absent_bad__outer_transition.
    - lia.
    - exact Hnewreach.
    - simpl. intros [Heq | []]. lia.
  }
  assert (Htrigger : forall starts,
    ValuablePrefixCuts x_pre values i (segments - 1) starts ->
    ReachableDivisorProducts x_pre
      (sublist (Znth (Zlength starts - 1) starts 0) i values)
      base_products ->
    ProductReachable
      (sublist (Znth (Zlength starts - 1) starts 0) (i + 1) values)
      x_pre).
  {
    intros starts Hcuts Hreach.
    pose proof Hcuts as Hcuts0.
    unfold ValuablePrefixCuts in Hcuts0.
    destruct Hcuts0 as
      (_ & _ & _ & _ & Hlast & _ & _ & Hbadlive & _).
    pose proof PreH40 as Hclosure.
    rewrite PreH31 in Hclosure.
    pose proof (closure_to_reachable_snoc__outer_transition
      x_pre
      (sublist (Znth (Zlength starts - 1) starts 0) i values)
      segment v base_products old_products 1
      PreH17 PreH26 Hclosure Hreach Hbadlive) as Hextended.
    destruct Hextended as [_ [_ Hnotbad]].
    specialize (Hnotbad eq_refl).
    apply not_bad_product_reachable__outer_transition.
    rewrite (sublist_snoc__outer_transition Z 0 values
      (Znth (Zlength starts - 1) starts 0) i) by lia.
    rewrite <- PreH25. exact Hnotbad.
  }
  replace segments with ((segments - 1) + 1) by lia.
  eapply valuable_aligned_forced_cut__outer_transition;
    eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_forced.
  exact (proof_of_solver_entail_wit_14_2_split_goal_1
    values n_pre x_pre segment base_products old_products bitmap_2 i
    v segments old count reaches
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
    PreH38 PreH39 PreH40 PreH41 PreH42).
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_outer.
  exact (proof_of_solver_entail_wit_14_2_split_goal_1
    values n_pre x_pre segment base_products old_products bitmap_2 i
    v segments old count reaches
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
    PreH38 PreH39 PreH40 PreH41 PreH42).
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_4 : solver_entail_wit_14_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (k_2 = 0) by lia. subst k_2. rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_5 : solver_entail_wit_14_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_6 : solver_entail_wit_14_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH21. assumption.
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
  assert (Hi : 0 <= i < Zlength values) by lia.
  eapply valuable_aligned_no_cut__outer_transition.
  - exact Hi.
  - exact PreH27.
  - intros starts Hcuts Hreach.
    pose proof Hcuts as Hcuts0.
    unfold ValuablePrefixCuts in Hcuts0.
    destruct Hcuts0 as
      (_ & _ & _ & _ & Hlast & _ & _ & Hbadlive & _).
    pose proof PreH28 as Hclosure.
    rewrite PreH16 in Hclosure.
    pose proof (closure_to_reachable_snoc__outer_transition
      x_pre
      (sublist (Znth (Zlength starts - 1) starts 0) i values)
      segment v base_products products_2 reaches
      PreH2 PreH11 Hclosure Hreach Hbadlive) as Hextended.
    destruct Hextended as [Hreach' [Hbad' _]].
    specialize (Hbad' PreH22).
    rewrite (sublist_snoc__outer_transition Z 0 values
      (Znth (Zlength starts - 1) starts 0) i) by lia.
    rewrite <- PreH10. split; assumption.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_2 : solver_entail_wit_14_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_forced.
  exact (proof_of_solver_entail_wit_14_3_split_goal_1
    values n_pre x_pre segment base_products products_2 bitmap_2 i v
    segments old count reaches
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30).
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_3 : solver_entail_wit_14_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_outer.
  exact (proof_of_solver_entail_wit_14_3_split_goal_1
    values n_pre x_pre segment base_products products_2 bitmap_2 i v
    segments old count reaches
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30).
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_4 : solver_entail_wit_14_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH24. assumption.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_5 : solver_entail_wit_14_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6. assumption.
Qed.

Lemma proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_14_4_split_goal_1 : solver_entail_wit_14_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 <= i < Zlength values) by lia.
  pose proof (PreH7 i Hi) as Hvrange.
  eapply valuable_aligned_no_cut__outer_transition.
  - exact Hi.
  - exact PreH20.
  - intros starts Hcuts Hreach.
    pose proof Hcuts as Hcuts0.
    unfold ValuablePrefixCuts in Hcuts0.
    destruct Hcuts0 as
      (_ & _ & _ & _ & Hlast & _ & _ & Hbadlive & _).
    assert (Habsent : ~ In x_pre products_2).
    {
      intro Hin.
      pose proof Hreach as Hreach0.
      destruct Hreach0 as [_ Hmembers].
      apply Hmembers in Hin.
      destruct Hin as [_ [_ [ids Hids]]].
      exact (Hbadlive ids Hids).
    }
    assert (Hreach' : ReachableDivisorProducts x_pre
      (sublist (Znth (Zlength starts - 1) starts 0) i values ++
       Znth i values 0 :: nil) products_2).
    {
      eapply reachable_products_nondivisible_snoc__outer_transition.
      - lia.
      - exact PreH22.
      - exact Hreach.
    }
    assert (Hbad' : BadCardSegment x_pre
      (sublist (Znth (Zlength starts - 1) starts 0) i values ++
       Znth i values 0 :: nil)).
    {
      eapply reachable_table_absent_bad__outer_transition.
      - lia.
      - exact Hreach'.
      - exact Habsent.
    }
    rewrite (sublist_snoc__outer_transition Z 0 values
      (Znth (Zlength starts - 1) starts 0) i) by lia.
    split; assumption.
Qed.

Lemma proof_of_solver_entail_wit_14_4_split_goal_2 : solver_entail_wit_14_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_forced.
  eapply proof_of_solver_entail_wit_14_4_split_goal_1; eauto.
  all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_14_4_split_goal_3 : solver_entail_wit_14_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply valuable_aligned_history_to_outer.
  eapply proof_of_solver_entail_wit_14_4_split_goal_1; eauto.
  all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_14_4 : solver_entail_wit_14_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = Zlength values) by lia.
  subst i.
  eapply valuable_aligned_history_complete__final_result; eauto.
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
Qed.
