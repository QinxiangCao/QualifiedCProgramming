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
From SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem Require Import chinese_remainder_theorem_goal.
From SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem Require Import chinese_remainder_theorem_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib.
Local Open Scope sac.

Lemma proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1 : chinese_remainder_theorem_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (crt_prefix_product_bounds__product_progress
       remainders_l moduli_l (i + 1) PreH3 ltac:(lia)) as Hbounds.
  pose proof (crt_prefix_product_step__product_progress moduli_l i ltac:(lia))
    as Hstep.
  destruct Hbounds as [[_ Hbound] _].
  rewrite PreH7, <- Hstep.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2 : chinese_remainder_theorem_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH3 as [_ [_ [Hvalues _]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [Hmodulus _].
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_3 : chinese_remainder_theorem_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1 : chinese_remainder_theorem_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2 : chinese_remainder_theorem_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CRTInputValid in PreH3.
  destruct PreH3 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_7 : chinese_remainder_theorem_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_1 : chinese_remainder_theorem_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_int_range (&( "coefficient" )) x_callee_v).
  Intros_p Hcoefficient_range.
  change Int.min_signed with (-2147483648) in Hcoefficient_range.
  change Int.max_signed with 2147483647 in Hcoefficient_range.
  unfold CRTMachineSafe in PreH6.
  rewrite <- PreH7 in PreH6.
  destruct PreH6 as [_ Hcoefficient].
  pose proof
    (Hcoefficient i x_callee_v ltac:(lia) Hcoefficient_range) as Hbound.
  unfold CRTInputValid in PreH5.
  destruct PreH5 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus _].
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_2 : chinese_remainder_theorem_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_int_range (&( "coefficient" )) x_callee_v).
  Intros_p Hcoefficient_range.
  change Int.min_signed with (-2147483648) in Hcoefficient_range.
  change Int.max_signed with 2147483647 in Hcoefficient_range.
  unfold CRTMachineSafe in PreH6.
  rewrite <- PreH7 in PreH6.
  destruct PreH6 as [_ Hcoefficient].
  pose proof
    (Hcoefficient i x_callee_v ltac:(lia) Hcoefficient_range) as Hbound.
  unfold CRTInputValid in PreH5.
  destruct PreH5 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus _].
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_9 : chinese_remainder_theorem_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1 : chinese_remainder_theorem_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (CRTInputValid_modulus_upper_bound__machine_safety
       remainders_l moduli_l i PreH5 ltac:(lia)) as Hmodulus_upper.
  unfold CRTInputValid in PreH5.
  destruct PreH5 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus Hremainder].
  pose proof
    (crt_c_rem_mul_int_bounds__machine_safety
       (x_callee_v * (product ÷ Znth i moduli_l 0)) product
       (Znth i remainders_l 0) PreH8 PreH9
       ltac:(lia) ltac:(lia)) as Hbound.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2 : chinese_remainder_theorem_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (CRTInputValid_modulus_upper_bound__machine_safety
       remainders_l moduli_l i PreH5 ltac:(lia)) as Hmodulus_upper.
  unfold CRTInputValid in PreH5.
  destruct PreH5 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus Hremainder].
  pose proof
    (crt_c_rem_mul_int_bounds__machine_safety
       (x_callee_v * (product ÷ Znth i moduli_l 0)) product
       (Znth i remainders_l 0) PreH8 PreH9
       ltac:(lia) ltac:(lia)) as Hbound.
  dump_pre_spatial.
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_11 : chinese_remainder_theorem_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1 : chinese_remainder_theorem_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs
       ((Z.rem
           (x_callee_v * (product ÷ Znth i moduli_l 0)) product) *
        Znth i remainders_l 0)
       product ltac:(lia)) as Hterm.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2 : chinese_remainder_theorem_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_17 : chinese_remainder_theorem_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 : chinese_remainder_theorem_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CRTMachineSafe in PreH3.
  destruct PreH3 as [[_ Hupper] _].
  exact Hupper.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 : chinese_remainder_theorem_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CRTMachineSafe in PreH3.
  destruct PreH3 as [[Hlower _] _].
  exact Hlower.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_3 : chinese_remainder_theorem_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_4 : chinese_remainder_theorem_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Zlength_nonneg moduli_l).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1 : chinese_remainder_theorem_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 : chinese_remainder_theorem_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (crt_prefix_product_bounds__product_progress
       remainders_l moduli_l (i + 1) PreH3 ltac:(lia)) as Hbounds.
  pose proof (crt_prefix_product_step__product_progress moduli_l i ltac:(lia))
    as Hstep.
  destruct Hbounds as [[_ Hbound] _].
  rewrite PreH7, <- Hstep.
  exact Hbound.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 : chinese_remainder_theorem_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH3 as [_ [_ [Hvalues _]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [Hmodulus _].
  nia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 : chinese_remainder_theorem_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH7.
  symmetry.
  apply crt_prefix_product_step__product_progress.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2 : chinese_remainder_theorem_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 : chinese_remainder_theorem_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 : chinese_remainder_theorem_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CRTProcessedCongruences.
  intros k Hk.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 : chinese_remainder_theorem_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) as Hi by lia.
  subst i.
  rewrite PreH2 in PreH7.
  rewrite sublist_self in PreH7 by reflexivity.
  exact PreH7.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3 : chinese_remainder_theorem_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : chinese_remainder_theorem_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hupdate :
    CRTProcessedCongruences remainders_l moduli_l (i + 1)
      ((result +
        ((((x_callee_v * (product / Znth i moduli_l 0)) mod product) *
          Znth i remainders_l 0) mod product)) mod product)).
  {
    eapply
      (crt_update_processed__crt_transition
        remainders_l moduli_l result i product x_callee_v y_callee_v).
    - exact PreH6.
    - lia.
    - exact PreH8.
    - lia.
    - exact PreH15.
    - intros k Hk.
      pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds k ltac:(lia)) as [Hmodulus _].
      rewrite <- Z.rem_mod_nonneg by lia.
      apply PreH16. lia.
    - pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
      rewrite <-
        (crt_quot_div_pos__crt_transition
          product (Znth i moduli_l 0)) by lia.
      exact PreH3.
  }
  unfold CRTProcessedCongruences in Hupdate |-.
  intros j Hj.
  specialize (Hupdate j Hj).
  pose proof PreH6 as [_ [_ [Hbounds _]]].
  pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    in PreH1 by lia.
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    by lia.
  assert (Hterm_mod :
    (Z.rem
      (Z.rem
        (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) product) mod product =
    (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
      Znth i remainders_l 0) mod product)).
  {
    rewrite crt_rem_mod__crt_transition by lia.
    apply crt_rem_mul_mod__crt_transition. lia.
  }
  pose proof
    (Z.rem_bound_abs
      (Z.rem (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) product) as Hterm_bound.
  rewrite
    (Z.abs_neq
      (Z.rem
        (Z.rem (x_callee_v * (product / Znth i moduli_l 0)) product *
          Znth i remainders_l 0) product))
    in Hterm_bound by lia.
  rewrite (Z.abs_eq product) in Hterm_bound by lia.
  assert (Houter_nonnegative :
    0 <= result +
      (Z.rem
        (Z.rem
          (x_callee_v * (product / Znth i moduli_l 0)) product *
          Znth i remainders_l 0) product + product)) by lia.
  assert (Hupdate_eq :
    Z.rem
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product + product)) product =
    (result +
      (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
        Znth i remainders_l 0) mod product)) mod product).
  {
    rewrite crt_rem_eq_mod_of_nonnegative_dividend__crt_transition by lia.
    replace
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product + product))
      with
      ((result +
        Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product) + 1 * product)
      by ring.
    rewrite Z.mod_add by lia.
    transitivity
      ((result mod product +
        (Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product) mod product) mod product).
    - apply Zplus_mod.
    - rewrite Hterm_mod.
      symmetry.
      rewrite Zplus_mod, Zmod_mod.
      reflexivity.
  }
  rewrite Hupdate_eq.
  exact Hupdate.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : chinese_remainder_theorem_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs
      (Z.rem
        (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
        Znth i remainders_l 0) product) as Hterm_bound.
  rewrite
    (Z.abs_neq
      (Z.rem
        (Z.rem
          (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
          Znth i remainders_l 0) product))
    in Hterm_bound by lia.
  rewrite (Z.abs_eq product) in Hterm_bound by lia.
  pose proof
    (Z.rem_bound_pos
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product + product))
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : chinese_remainder_theorem_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs
      (Z.rem
        (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
        Znth i remainders_l 0) product) as Hterm_bound.
  rewrite
    (Z.abs_neq
      (Z.rem
        (Z.rem
          (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
          Znth i remainders_l 0) product))
    in Hterm_bound by lia.
  rewrite (Z.abs_eq product) in Hterm_bound by lia.
  pose proof
    (Z.rem_bound_pos
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product + product))
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1 : chinese_remainder_theorem_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : chinese_remainder_theorem_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hupdate :
    CRTProcessedCongruences remainders_l moduli_l (i + 1)
      ((result +
        ((((x_callee_v * (product / Znth i moduli_l 0)) mod product) *
          Znth i remainders_l 0) mod product)) mod product)).
  {
    eapply
      (crt_update_processed__crt_transition
        remainders_l moduli_l result i product x_callee_v y_callee_v).
    - exact PreH6.
    - lia.
    - exact PreH8.
    - lia.
    - exact PreH15.
    - intros k Hk.
      pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds k ltac:(lia)) as [Hmodulus _].
      rewrite <- Z.rem_mod_nonneg by lia.
      apply PreH16. lia.
    - pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
      rewrite <-
        (crt_quot_div_pos__crt_transition
          product (Znth i moduli_l 0)) by lia.
      exact PreH3.
  }
  unfold CRTProcessedCongruences in Hupdate |-.
  intros j Hj.
  specialize (Hupdate j Hj).
  pose proof PreH6 as [_ [_ [Hbounds _]]].
  pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    in PreH1 by lia.
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    by lia.
  assert (Hterm_eq :
    Z.rem
      (Z.rem
        (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) product =
    (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
      Znth i remainders_l 0) mod product)).
  {
    transitivity
      ((Z.rem
        (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) mod product).
    - apply crt_nonnegative_rem_eq_mod__crt_transition; lia.
    - apply crt_rem_mul_mod__crt_transition. lia.
  }
  assert (Hupdate_eq :
    Z.rem
      (result +
        Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product) product =
    (result +
      (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
        Znth i remainders_l 0) mod product)) mod product).
  {
    rewrite crt_rem_eq_mod_of_nonnegative_dividend__crt_transition by lia.
    rewrite Hterm_eq. reflexivity.
  }
  rewrite Hupdate_eq.
  exact Hupdate.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : chinese_remainder_theorem_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_pos
      (result +
        Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product)
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : chinese_remainder_theorem_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_pos
      (result +
        Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product)
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2 : chinese_remainder_theorem_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3.
Qed.

Lemma proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 : chinese_remainder_theorem_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanonicalCRTSolution.
  split.
  - rewrite <- PreH5.
    lia.
  - intros k Hk.
    apply PreH12.
    lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_return_wit_1 : chinese_remainder_theorem_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (crt_factor_quotient_bounds__product_progress
       remainders_l moduli_l i PreH13 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[Hmodulus _] [Hquotient _]].
  dump_pre_spatial.
  rewrite PreH15.
  rewrite Z.quot_div_nonneg by lia.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH13 as [_ [_ [Hvalues _]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [Hmodulus _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (crt_factor_quotient_bounds__product_progress
       remainders_l moduli_l i PreH13 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[_ Hmodulus] _].
  dump_pre_spatial.
  rewrite <- PreH15 in Hmodulus.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure : chinese_remainder_theorem_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3.
Qed.
