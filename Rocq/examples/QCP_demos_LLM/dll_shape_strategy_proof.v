Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import dll_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import dll_shape_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma dll_shape_strategy1_correctness : dll_shape_strategy1.
Proof.
  pre_process_default.
  sep_apply_l_atomic (dlistrep_zero 0 x eq_refl).
  cancel.
Qed.

Lemma dll_shape_strategy2_correctness : dll_shape_strategy2.
Proof.
  pre_process_default.
  unfold dlistrep_shape.
  Exists (@nil Z).
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma dll_shape_strategy3_correctness : dll_shape_strategy3.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  split_pure_spatial.
  - Intros_r x.
    apply_sepcon_adjoint.
    cancel.
    destruct H as [H | H].
    + subst p.
      unfold dlistrep_shape.
      Exists (@nil Z).
      simpl.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        reflexivity.
    + subst p.
      unfold dlistrep_shape.
      Exists (@nil Z).
      simpl.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        reflexivity.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma dll_shape_strategy4_correctness : dll_shape_strategy4.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  split_pure_spatial.
  - destruct H as [H | H].
    + subst p.
      sep_apply_l_atomic (dlistrep_zero 0 x eq_refl).
      cancel.
    + subst p.
      sep_apply_l_atomic (dlistrep_zero 0 x eq_refl).
      cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma dll_shape_strategy12_correctness : dll_shape_strategy12.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  subst r x.
  unfold dllseg_shape.
  Exists (@nil Z).
  simpl.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma dll_shape_strategy7_correctness : dll_shape_strategy7.
Proof.
  pre_process_default.
  subst x.
  sep_apply_l_atomic (dllseg_dlistrep_shape p s q r).
  cancel.
Qed.


Lemma dll_shape_strategy13_correctness : dll_shape_strategy13.
Proof.
  pre_process_default.
  cancel (&( s # "list" ->ₛ "next") # Ptr |-> n).
  Intros_r x.
  Intros_r p.
  Intros_r y.
  Intros_r q.
  apply_sepcon_adjoint.
  cancel.
  subst m.
  sep_apply_l_atomic (dllseg_shape_len1 s y n x H0).
  sep_apply_l_atomic (dllseg_dllseg_shape p s n q y s).
  cancel.
Qed.

Lemma dll_shape_strategy14_correctness : dll_shape_strategy14.
Proof.
  pre_process_default.
  assert (Hpm : p <> m).
  {
    intro Heq.
    apply H.
    symmetry.
    exact Heq.
  }
  sep_apply_l_atomic (dllseg_split_tail p q s m Hpm).
  Intros y.
  Intros x.
  Exists x.
  Exists y.
  split_pure_spatial.
  - cancel (dllseg_shape p q y s).
    cancel (&( s # "list" ->ₛ "prev") # Ptr |-> y).
    cancel (&( s # "list" ->ₛ "next") # Ptr |-> m).
    cancel (&( s # "list" ->ₛ "data") # Int |-> x).
    Intros_r n.
    apply_sepcon_adjoint.
    cancel (&(s # "list" ->ₛ "prev") # Ptr |-> n).
    cancel.
  - dump_pre_spatial.
    exact H0.
Qed.

Lemma dll_shape_strategy8_correctness : dll_shape_strategy8.
Proof.
  pre_process_default.
  Intros_p H.
  subst y.
  cancel.
Qed.

Lemma dll_shape_strategy11_correctness : dll_shape_strategy11.
Proof.
  pre_process_default.
  subst r s.
  unfold dllseg_shape.
  Exists (@nil Z).
  simpl.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma dll_shape_strategy15_correctness : dll_shape_strategy15.
Proof.
  pre_process_default.
  subst t x.
  sep_apply_l_atomic (dllseg_dlistrep_shape p s q r).
  cancel.
Qed.

Lemma dll_shape_strategy5_correctness : dll_shape_strategy5.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  assert (Hp : p <> 0).
  {
    destruct Hnz as [Hnz | Hnz].
    - exact Hnz.
    - intro Hp0.
      apply Hnz.
      symmetry.
      exact Hp0.
  }
  sep_apply_l_atomic (dlistrep_not_zero p prev Hp).
  Intros x.
  Intros y.
  Exists x.
  Exists y.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel (dlistrep_shape y p).
    cancel (&( p # "list" ->ₛ "prev") # Ptr |-> prev).
    cancel (&( p # "list" ->ₛ "next") # Ptr |-> y).
    cancel (&( p # "list" ->ₛ "data") # Int |-> x).
    Intros_r q.
    apply_sepcon_adjoint.
    cancel ((&(p # "list" ->ₛ "data") # Int |-> q) || (&(p # "list" ->ₛ "next") # Ptr |-> q) || (&(p # "list" ->ₛ "prev") # Ptr |-> q)).
    normalize.
    cancel.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma dll_shape_strategy6_correctness : dll_shape_strategy6.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - Intros_r prev.
    Intros_r x.
    Intros_r y.
    apply_sepcon_adjoint.
    cancel.
    unfold dlistrep_shape.
    Intros l.
    Exists (x :: l).
    simpl.
    Exists y.
    split_pure_spatial.
    + cancel.
      cancel.
    + dump_pre_spatial.
      destruct Hnz as [Hnz | Hnz].
      * exact Hnz.
      * intro Hp0.
        apply Hnz.
        symmetry.
        exact Hp0.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma dll_shape_strategy16_correctness : dll_shape_strategy16.
Proof.
  pre_process_default.
  assert (Hqs : q <> s).
  {
    intro Heq.
    apply H.
    symmetry.
    exact Heq.
  }
  sep_apply_l_atomic (dllseg_split_tail' p q s m Hqs).
  Intros y.
  Intros x.
  Exists x.
  Exists y.
  normalize.
  cancel (dllseg_shape p q y s).
  cancel (&( s # "list" ->ₛ "prev") # Ptr |-> y).
  cancel (&( s # "list" ->ₛ "next") # Ptr |-> m).
  cancel (&( s # "list" ->ₛ "data") # Int |-> x).
  Intros_r n.
  apply_sepcon_adjoint.
  cancel (&(s # "list" ->ₛ "next") # Ptr |-> n).
  cancel.
Qed.
