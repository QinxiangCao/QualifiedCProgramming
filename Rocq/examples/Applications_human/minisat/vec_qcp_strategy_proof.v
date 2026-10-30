From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.
Require Import SimpleC.EE.Applications_human.minisat.vec_qcp_lib.

Lemma vec_qcp_strategy70_correctness : vec_qcp_strategy70.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (Veci.rep_bounds v l) at 1. Intros.
  cancel. apply_sepcon_adjoint. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma vec_qcp_strategy71_correctness : vec_qcp_strategy71.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (Vecp.rep_bounds v l) at 1. Intros.
  cancel. apply_sepcon_adjoint. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma vec_qcp_strategy35_correctness : vec_qcp_strategy35.
Proof.
  LLM_pre_process ltac:(lia).
  subst closed_v required_cut.
  Intros.
  sep_apply (Vecp.header_fold raw_v p (Zlength (sublist 0 actual_cut words)) cap).
  sep_apply (Vecp.rep_intro raw_v p (sublist 0 actual_cut words) cap
    (Zlength (sublist 0 actual_cut words)) (Zlength (sublist 0 actual_cut words))
    (Zlength (sublist 0 actual_cut words))).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy2_correctness : vec_qcp_strategy2.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Veci.rep_open v l). Intros p cap.
  sep_apply (Veci.rep_at_open v p l cap). Intros.
  sep_apply (Veci.header_open v p (Zlength l) cap).
  Exists p cap.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  Intros_r y.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy5_correctness : vec_qcp_strategy5.
Proof.
  LLM_pre_process ltac:(lia).
  cancel.
  Intros_r p cap l.
  apply_sepcon_adjoint.
  Intros.
  sep_apply (Veci.header_fold v p (Zlength l) cap).
  sep_apply (Veci.rep_intro v p l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy7_correctness : vec_qcp_strategy7.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Veci.shell_open v).
  cancel.
  Intros_r y.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy8_correctness : vec_qcp_strategy8.
Proof.
  LLM_pre_process ltac:(lia).
  cancel.
  apply_sepcon_adjoint.
  Intros.
  sep_apply (Veci.shell_fold v).
  cancel.
Qed.

Lemma vec_qcp_strategy102_correctness : vec_qcp_strategy102.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Vecp.rep_open v l). Intros p cap.
  sep_apply (Vecp.rep_at_open v p l cap). Intros.
  sep_apply (Vecp.header_open v p (Zlength l) cap).
  Exists p cap.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  Intros_r y.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy105_correctness : vec_qcp_strategy105.
Proof.
  LLM_pre_process ltac:(lia).
  cancel.
  Intros_r p cap l.
  apply_sepcon_adjoint.
  Intros.
  sep_apply (Vecp.header_fold v p (Zlength l) cap).
  sep_apply (Vecp.rep_intro v p l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy116_correctness : vec_qcp_strategy116.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hw.
  Intros_p Hij.
  subst j.
  split_pure_spatial.
  - Intros_r l.
    apply_sepcon_adjoint.
    Intros.
    subst l.
    replace (Vecp.slot base i) with w by (destruct Hw; congruence).
    cancel.
  - dump_pre_spatial.
    exact Hw.
Qed.

Lemma vec_qcp_strategy107_correctness : vec_qcp_strategy107.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Vecp.shell_open v).
  cancel.
  Intros_r y.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy108_correctness : vec_qcp_strategy108.
Proof.
  LLM_pre_process ltac:(lia).
  cancel.
  apply_sepcon_adjoint.
  Intros.
  sep_apply (Vecp.shell_fold v).
  cancel.
Qed.

Lemma vec_qcp_strategy9_correctness : vec_qcp_strategy9.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma vec_qcp_strategy10_correctness : vec_qcp_strategy10.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma vec_qcp_strategy109_correctness : vec_qcp_strategy109.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma vec_qcp_strategy110_correctness : vec_qcp_strategy110.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma vec_qcp_strategy208_correctness : vec_qcp_strategy208.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (Veci.rep_ptr_bounds v p l) at 1. Intros.
  cancel. apply_sepcon_adjoint. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma vec_qcp_strategy308_correctness : vec_qcp_strategy308.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (Vecp.rep_ptr_bounds v p l) at 1. Intros.
  cancel. apply_sepcon_adjoint. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma vec_qcp_strategy207_correctness : vec_qcp_strategy207.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Veci.rep_rep_ptr v l).
  Intros p.
  Exists p.
  (Intros; cancel).
  Intros_r target_l target_p.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy307_correctness : vec_qcp_strategy307.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Vecp.rep_rep_ptr v l).
  Intros p.
  Exists p.
  (Intros; cancel).
  Intros_r target_l target_p.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy201_correctness : vec_qcp_strategy201.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Veci.rep_ptr_open v p l). Intros cap.
  sep_apply (Veci.rep_at_open v p l cap). Intros.
  sep_apply (Veci.header_open v p (Zlength l) cap).
  Exists cap.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  Intros_r y.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy202_correctness : vec_qcp_strategy202.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Veci.rep_ptr_open v p l). Intros cap.
  sep_apply (Veci.rep_at_open v p l cap). Intros.
  Exists cap.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  Intros_r y ll i hi lo.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy203_correctness : vec_qcp_strategy203.
Proof.
  LLM_pre_process ltac:(lia).
  cancel.
  Intros_r p cap l.
  apply_sepcon_adjoint.
  Intros.
  sep_apply (Veci.header_fold v p (Zlength l) cap).
  sep_apply (Veci.rep_ptr_intro v p l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy205_correctness : vec_qcp_strategy205.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst.
  cancel.
Qed.

Lemma vec_qcp_strategy206_correctness : vec_qcp_strategy206.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst.
  apply Veci.rep_ptr_rep.
Qed.

Lemma vec_qcp_strategy301_correctness : vec_qcp_strategy301.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Vecp.rep_ptr_open v p l). Intros cap.
  sep_apply (Vecp.rep_at_open v p l cap). Intros.
  sep_apply (Vecp.header_open v p (Zlength l) cap).
  Exists cap.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  Intros_r y.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy302_correctness : vec_qcp_strategy302.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (Vecp.rep_ptr_open v p l). Intros cap.
  sep_apply (Vecp.rep_at_open v p l cap). Intros.
  Exists cap.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  Intros_r y ll i hi lo.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy303_correctness : vec_qcp_strategy303.
Proof.
  LLM_pre_process ltac:(lia).
  cancel.
  Intros_r p cap l.
  apply_sepcon_adjoint.
  Intros.
  sep_apply (Vecp.header_fold v p (Zlength l) cap).
  sep_apply (Vecp.rep_ptr_intro v p l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy305_correctness : vec_qcp_strategy305.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst.
  cancel.
Qed.

Lemma vec_qcp_strategy306_correctness : vec_qcp_strategy306.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst.
  apply Vecp.rep_ptr_rep.
Qed.

Lemma vec_qcp_strategy209_correctness : vec_qcp_strategy209.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst p k n.
  sep_apply (Veci.header_fold v q (Zlength l) cap).
  sep_apply (Veci.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy210_correctness : vec_qcp_strategy210.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  sep_apply (IntArray.full_to_seg q n k).
  subst p k n.
  sep_apply (Veci.header_fold v q (Zlength l) cap).
  sep_apply (Veci.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy309_correctness : vec_qcp_strategy309.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst p k n.
  sep_apply (Vecp.header_fold v q (Zlength l) cap).
  sep_apply (Vecp.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy310_correctness : vec_qcp_strategy310.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  sep_apply (PtrArray.full_to_seg q n k).
  subst p k n.
  sep_apply (Vecp.header_fold v q (Zlength l) cap).
  sep_apply (Vecp.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy211_correctness : vec_qcp_strategy211.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst q n.
  sep_apply (Veci.rep_ptr_open v p l). Intros cap.
  sep_apply (Veci.rep_at_open v p l cap). Intros.
  Exists cap.
  sep_apply (IntArray.seg_to_full p 0 (Zlength l) l).
  rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy311_correctness : vec_qcp_strategy311.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst q n.
  sep_apply (Vecp.rep_ptr_open v p l). Intros cap.
  sep_apply (Vecp.rep_at_open v p l cap). Intros.
  Exists cap.
  sep_apply (PtrArray.seg_to_full p 0 (Zlength l) l).
  rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia | tauto] ..]).
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy212_correctness : vec_qcp_strategy212.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst p k n.
  sep_apply (Veci.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy213_correctness : vec_qcp_strategy213.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  sep_apply (IntArray.full_to_seg q n k).
  subst p k n.
  sep_apply (Veci.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy214_correctness : vec_qcp_strategy214.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst q n.
  sep_apply (Veci.rep_ptr_intro v p l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy215_correctness : vec_qcp_strategy215.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst n.
  sep_apply (Veci.rep_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy312_correctness : vec_qcp_strategy312.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst p k n.
  sep_apply (Vecp.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy313_correctness : vec_qcp_strategy313.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  sep_apply (PtrArray.full_to_seg q n k).
  subst p k n.
  sep_apply (Vecp.rep_ptr_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy314_correctness : vec_qcp_strategy314.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst q n.
  sep_apply (Vecp.rep_ptr_intro v p l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy315_correctness : vec_qcp_strategy315.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst n.
  sep_apply (Vecp.rep_intro v q l cap (Zlength l) (Zlength l) (Zlength l)).
  all: solve [cancel | lia | vec_buf_solve | tauto].
Qed.

Lemma vec_qcp_strategy95_correctness : vec_qcp_strategy95.
Proof.
  LLM_pre_process ltac:(lia).
  repeat rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (Hindex : read_index = index) by (intuition congruence).
  assert (Hpointer : requested = Vecp.slot base read_index) by (intuition congruence).
  subst requested read_index.
  split_pure_spatial;
    [ Intros_r l; apply_sepcon_adjoint; Intros; subst n;
      sep_apply (Vecp.rep_intro (Vecp.slot base index) q l cap (Zlength l) (Zlength l) (Zlength l));
      solve [cancel | lia | vec_buf_solve | tauto]
    | split_pures; dump_pre_spatial; solve [auto | intuition congruence] .. ].
Qed.

Lemma vec_qcp_strategy401_correctness : vec_qcp_strategy401.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (VecpArray.full_split_to_slot b i n ls nil ltac:(lia)).
  cancel (VecpArray.missing_i b i 0 n ls).
  Intros_r l.
  apply_sepcon_adjoint.
  Intros.
  subst l.
  cancel.
Qed.

Lemma vec_qcp_strategy402_correctness : vec_qcp_strategy402.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply (VecpArray.full_split_to_slot b i n ls nil ltac:(lia)).
  cancel.
  Intros_r p l y.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma vec_qcp_strategy403_correctness : vec_qcp_strategy403.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hw.
  Intros.
  assert (Hslot : w = Vecp.slot b i) by (destruct Hw; congruence).
  subst w.
  sep_apply (VecpArray.full_split_to_slot b i n ls nil ltac:(lia)).
  split_pure_spatial.
  - cancel (VecpArray.missing_i b i 0 n ls).
    Intros_r l.
    apply_sepcon_adjoint.
    Intros.
    subst l.
    cancel.
  - dump_pre_spatial.
    tauto.
Qed.

Lemma vec_qcp_strategy404_correctness : vec_qcp_strategy404.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hw.
  Intros.
  assert (Hslot : w = Vecp.slot b i) by (destruct Hw; congruence).
  subst w.
  sep_apply (VecpArray.full_split_to_slot b i n ls nil ltac:(lia)).
  split_pure_spatial.
  - cancel.
    Intros_r p l y.
    apply_sepcon_adjoint.
    Intros.
    cancel.
  - dump_pre_spatial.
    tauto.
Qed.

Lemma vec_qcp_strategy405_correctness : vec_qcp_strategy405.
Proof.
  exact vec_qcp_strategy401_correctness.
Qed.

Lemma vec_qcp_strategy406_correctness : vec_qcp_strategy406.
Proof.
  exact vec_qcp_strategy402_correctness.
Qed.

Lemma vec_qcp_strategy407_correctness : vec_qcp_strategy407.
Proof.
  LLM_pre_process ltac:(lia).
  subst m.
  sep_apply (VecpArray.full_split_to_slot b i n ls nil ltac:(lia)).
  cancel (Vecp.rep (Vecp.slot b i) (Znth i ls nil)).
  Intros_r ms.
  apply_sepcon_adjoint.
  Intros.
  subst ms.
  cancel.
Qed.

Lemma vec_qcp_strategy408_correctness : vec_qcp_strategy408.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst m l2.
  cancel.
Qed.

Lemma vec_qcp_strategy409_correctness : vec_qcp_strategy409.
Proof.
  LLM_pre_process ltac:(lia).
  Intros.
  subst j lo2 hi2 l2.
  cancel.
Qed.

Lemma vec_qcp_strategy411_correctness : vec_qcp_strategy411.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (VecpArray.missing_i_index_range b i 0 n ls).
  Intros.
  sep_apply (VecpArray.slot_merge_to_full b i n (Znth i ls nil) ls ltac:(lia)).
  rewrite replace_Znth_Znth.
  cancel.
Qed.

Lemma vec_qcp_strategy412_correctness : vec_qcp_strategy412.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (VecpArray.missing_i_index_range b i 0 n ls).
  Intros.
  sep_apply (VecpArray.slot_merge_to_full b i n l ls ltac:(lia)).
  cancel.
Qed.

Lemma vec_qcp_strategy413_correctness : vec_qcp_strategy413.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hw.
  assert (Hslot : w = Vecp.slot b i) by (destruct Hw; congruence).
  subst w.
  prop_apply_p (VecpArray.missing_i_index_range b i 0 n ls).
  Intros.
  sep_apply (VecpArray.slot_merge_to_full b i n (Znth i ls nil) ls ltac:(lia)).
  rewrite replace_Znth_Znth.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    tauto.
Qed.

Lemma vec_qcp_strategy414_correctness : vec_qcp_strategy414.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hw.
  assert (Hslot : w = Vecp.slot b i) by (destruct Hw; congruence).
  subst w.
  prop_apply_p (VecpArray.missing_i_index_range b i 0 n ls).
  Intros.
  sep_apply (VecpArray.slot_merge_to_full b i n l ls ltac:(lia)).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    tauto.
Qed.

Lemma vec_qcp_strategy415_correctness : vec_qcp_strategy415.
Proof.
  exact vec_qcp_strategy411_correctness.
Qed.

Lemma vec_qcp_strategy416_correctness : vec_qcp_strategy416.
Proof.
  exact vec_qcp_strategy412_correctness.
Qed.

Lemma vec_qcp_strategy60_correctness : vec_qcp_strategy60.
Proof.
  LLM_pre_process ltac:(lia).
  subst q.
  cancel.
Qed.

Lemma vec_qcp_strategy68_correctness : vec_qcp_strategy68.
Proof.
  LLM_pre_process ltac:(lia).
  subst q lo2 hi2.
  cancel.
Qed.
