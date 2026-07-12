Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import dll_data_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import dll_shape_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma dll_data_strategy1_correctness : dll_data_strategy1.
Proof.
  pre_process_default.
  sep_apply_l_atomic (dll_zero 0 prev l eq_refl).
  cancel.
Qed.

Lemma dll_data_strategy2_correctness : dll_data_strategy2.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l.
  simpl.
  entailer!.
Qed.

Lemma dll_data_strategy3_correctness : dll_data_strategy3.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  split_pure_spatial.
  - Intros_r l. Intros_r prev.
    apply_sepcon_adjoint.
    Intros_p Hl. subst l.
    destruct H as [H | H]; subst p; simpl; entailer!.
  - dump_pre_spatial. exact H.
Qed.

Lemma dll_data_strategy4_correctness : dll_data_strategy4.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  assert (Hp : p = 0) by (destruct H; lia).
  sep_apply (dll_zero p prev l Hp).
  entailer!.
Qed.

Lemma dll_data_strategy12_correctness : dll_data_strategy12.
Proof.
  pre_process_default.
  Intros_p Hqr. Intros_p Hxq. Intros_p Hl.
  subst r x l1. simpl.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma dll_data_strategy7_correctness : dll_data_strategy7.
Proof.
  pre_process_default.
  subst x.
  Intros_p Hl2. subst l2.
  sep_apply_l_atomic (dllseg_dlistrep p s q r l1 l3).
  cancel.
Qed.

Lemma dll_data_strategy13_correctness : dll_data_strategy13.
Proof.
  pre_process_default.
  cancel (&( s # "list" ->ₛ "next") # Ptr |-> n).
  Intros_r l. Intros_r l0. Intros_r x.
  Intros_r p. Intros_r q. Intros_r y.
  apply_sepcon_adjoint. elim_emp.
  subst m.
  Intros_p Hl. subst l.
  sep_apply_l_atomic (dllseg_len1 s y n x H0).
  sep_apply_l_atomic (dllseg_dllseg p s n q y s l0 (x :: nil)%list).
  cancel.
Qed.

Lemma dll_data_strategy14_correctness : dll_data_strategy14.
Proof.
  pre_process_default.
  assert (Hpm : p <> m).
  { intro Heq. apply H. symmetry. exact Heq. }
  sep_apply_l_atomic (dllseg_head_neq_destruct_tail p m q s l Hpm).
  Intros y. Intros l0. Intros x.
  Exists x. Exists y. Exists l0.
  split_pure_spatial.
  - cancel (dllseg p s q y l0).
    cancel (&( s # "list" ->ₛ "prev") # Ptr |-> y).
    cancel (&( s # "list" ->ₛ "next") # Ptr |-> m).
    cancel (&( s # "list" ->ₛ "data") # Int |-> x).
    Intros_r n. apply_sepcon_adjoint. elim_emp. cancel.
  - split_pures.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H0.
Qed.

Lemma dll_data_strategy15_correctness : dll_data_strategy15.
Proof.
  pre_process_default.
  subst t x.
  Intros_p Hl2. subst l2.
  sep_apply_l_atomic (dllseg_dlistrep p s q r l1 l3).
  cancel.
Qed.

Lemma dll_data_strategy16_correctness : dll_data_strategy16.
Proof.
  pre_process_default.
  assert (Hqs : q <> s).
  { intro Heq. apply H. symmetry. exact Heq. }
  sep_apply_l_atomic (dllseg_head_neq_destruct_tail' p m q s l Hqs).
  Intros y. Intros l0. Intros x.
  Exists x. Exists y. Exists l0.
  split_pure_spatial.
  - cancel (dllseg p s q y l0).
    cancel (&( s # "list" ->ₛ "prev") # Ptr |-> y).
    cancel (&( s # "list" ->ₛ "next") # Ptr |-> m).
    cancel (&( s # "list" ->ₛ "data") # Int |-> x).
    Intros_r n. apply_sepcon_adjoint. elim_emp. cancel.
  - dump_pre_spatial. exact H1.
Qed.

Lemma dll_data_strategy8_correctness : dll_data_strategy8.
Proof.
  pre_process_default.
  Intros_p Hxy. Intros_p Hll.
  subst y l2. cancel.
Qed.

Lemma dll_data_strategy11_correctness : dll_data_strategy11.
Proof.
  pre_process_default.
  subst r s.
  Intros_p Hl. subst l. simpl.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma dll_data_strategy5_correctness : dll_data_strategy5.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  assert (Hp : p <> 0).
  { destruct Hnz as [Hnz | Hnz]; [exact Hnz|].
    intro Hp0. apply Hnz. symmetry. exact Hp0. }
  sep_apply_l_atomic (dll_not_zero p prev l Hp).
  Intros y. Intros x. Intros l0.
  Exists x. Exists y. Exists l0.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel (dlistrep y p l0).
    cancel (&( p # "list" ->ₛ "prev") # Ptr |-> prev).
    cancel (&( p # "list" ->ₛ "next") # Ptr |-> y).
    cancel (&( p # "list" ->ₛ "data") # Int |-> x).
    Intros_r q. apply_sepcon_adjoint. elim_emp. cancel.
  - entailer!.
Qed.

Lemma dll_data_strategy6_correctness : dll_data_strategy6.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - Intros_r l. Intros_r x. Intros_r l0.
    Intros_r prev. Intros_r y.
    apply_sepcon_adjoint.
    Intros_p Hl. subst l. simpl.
    Exists y.
    split_pure_spatial.
    + cancel.
      cancel.
      cancel.
    + dump_pre_spatial.
      destruct Hnz as [Hnz | Hnz]; [exact Hnz|].
      intro Hp0. apply Hnz. symmetry. exact Hp0.
  - dump_pre_spatial. exact Hnz.
Qed.
