Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
Require Import SetsClass.SetsClass. Import SetsNotation.
From FP Require Export PartialOrder_Setoid BourbakiWitt.
Export PO_lift CPO_Prop.
From SimpleC.SL Require Import Mem SeparationLogic IntLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Export GmpNumber.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Export GmpAux.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Export GmpMul.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Export GmpDiv.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Export GmpGcd.
Export Aux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

From MonadLib Require Import MonadLib.
Export StateRelMonadErr.
From MonadLib.Examples Require Export fme_rel.
Export MonadNotation.
Local Open Scope monad.

Import naive_C_Rules.
Local Open Scope sac.

Definition applyf {A B: Type} (f: A -> B) (a: A) := f a.

Definition makepair (ret: Z) (lp: LP): Z * LP := (ret, lp).

Definition mpz_sizeof : Z := sizeof("__mpz_struct").

Definition mpz_store (x: addr) (lo: Z) (z: Z): Assertion :=
  store_Z (x + lo * mpz_sizeof) z.

Module MpzArray.
  Definition full (x: addr) (n: Z) (l: list Z): Assertion :=
    store_array mpz_store x n l.

  Definition missing_i (x: addr) (i lo hi: Z) (l: list Z): Assertion :=
    store_array_missing_i_rec mpz_store x i lo hi l.

  Lemma full_length: forall x n (l: list Z),
    full x n l |-- “ Z.of_nat (length l) = n ”.
  Proof.
    intros.
    unfold full.
    apply store_array_length.
  Qed.

  Lemma full_Zlength: forall x n (l: list Z),
    full x n l |-- “ Zlength l = n ”.
  Proof.
    intros.
    rewrite Zlength_correct.
    apply full_length.
  Qed.

  Lemma missing_i_merge_to_full: forall x n m a (l: list Z),
    0 <= n < m ->
    mpz_store x n a ** missing_i x n 0 m l |-- full x m (replace_Znth n a l).
  Proof.
    intros.
    unfold full, missing_i.
    apply store_array_missing_i_merge_to_array.
    exact H.
  Qed.

  Lemma full_split_to_missing_i: forall x n m (l: list Z) a,
    0 <= n < m ->
    full x m l |-- mpz_store x n (Znth n l a) ** missing_i x n 0 m l.
  Proof.
    intros.
    unfold full, missing_i.
    apply store_array_split_to_missing_i.
    exact H.
  Qed.
End MpzArray.

Definition mpz_coef_array (x: addr) (n: Z) (c: Constraint): Assertion :=
  “ x = NULL ” && emp ||
  “ x <> NULL ” && MpzArray.full x n (Constraint_list c).

Definition mpz_coef_array_missing_i_rec (x: addr) (i lo hi: Z) (c: Constraint): Assertion :=
  MpzArray.missing_i x i lo hi (Constraint_list c).

Definition coef_array (x: addr) (n: Z) (c: Constraint): Assertion :=
  mpz_coef_array x n c.

Definition coef_array_missing_i_rec (x: addr) (i lo hi: Z) (c: Constraint): Assertion :=
  mpz_coef_array_missing_i_rec x i lo hi c.

Definition coef_pre_eq (i: Z) (c1 c2: Constraint): Prop :=
  forall i0, 0 <= i0 /\ i0 < i -> coef_Znth i0 c1 0 = coef_Znth i0 c2 0.

Fixpoint InequList (x: addr) (coef_len: Z) (lp: LP): Assertion :=
  match lp with
  | nil => “ x = NULL ” && emp
  | a :: lp' =>
      “ x <> NULL ” &&
      EX c y: addr,
        “ c <> NULL ” &&
        &(x # "InequList" ->ₛ "coef") # Ptr |-> c **
        mpz_coef_array c coef_len a **
        &(x # "InequList" ->ₛ "next") # Ptr |-> y **
        InequList y coef_len lp'
  end.

Fixpoint InequList_seg (x y: addr) (coef_len: Z) (lp: LP): Assertion :=
  match lp with
  | nil => “ x = y ” && emp
  | a :: lp' =>
      “ x <> NULL ” &&
      EX c z: addr,
        “ c <> NULL ” &&
        &(x # "InequList" ->ₛ "coef") # Ptr |-> c **
        mpz_coef_array c coef_len a **
        &(x # "InequList" ->ₛ "next") # Ptr |-> z **
        InequList_seg z y coef_len lp'
  end.

Definition InequList_nth_pos (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> coef_Znth n c 0 > 0.

Definition InequList_nth_neg (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> coef_Znth n c 0 < 0.

Definition InequList_nth_zero (n : Z) (lp : LP) : Prop :=
  forall c, In c lp -> coef_Znth n c 0 = 0.

Definition BoundPair (x: addr) (coef_len: Z) (bp: BP): Assertion :=
  EX u l r,
    &(x # "BoundPair" ->ₛ "upper") # Ptr |-> u **
    &(x # "BoundPair" ->ₛ "lower") # Ptr |-> l **
    &(x # "BoundPair" ->ₛ "remain") # Ptr |-> r **
    InequList u coef_len bp.(upper) **
    InequList l coef_len bp.(lower) **
    InequList r coef_len bp.(remain).

Definition form_BP (up lo re: LP) (bp: BP): Prop :=
  up = bp.(upper) /\ lo = bp.(lower) /\ re = bp.(remain).

Definition real_shadow_after_generate (cnt: Z) (lp: LP):
  program unit LP :=
  real_shadow_loop_prog (cnt - 1) lp.

Definition real_shadow_after_eliminate (cnt: Z) (bp: BP):
  program unit LP :=
  bind
    (generate_new_constraint_list_prog cnt bp.(upper) bp.(lower) bp.(remain))
    (real_shadow_after_generate cnt).

Definition lia_deduction_after_check (lp: LP) (found: bool):
  program unit (Z * LP) :=
  choice
    (assume!! (found = true);; return (1, lp))
    (assume!! (found = false);; return (0, lp)).

Definition lia_deduction_scan_from (lp todo: LP) (found: bool):
  program unit (Z * LP) :=
  found' <- list_iter lia_deduction_check_body todo found;;
  lia_deduction_after_check lp found'.

Definition lia_deduction_scan_from_false (lp todo: LP):
  program unit (Z * LP) :=
  lia_deduction_scan_from lp todo false.

Definition lia_deduction_after_real_shadow (lp: LP): program unit (Z * LP) :=
  lia_deduction_scan_from_false lp lp.

Lemma coef_Znth_nth:
  forall n c,
    n >= 1 ->
    coef_Znth n c 0 = nth_coef n c.
Proof.
  intros.
  unfold coef_Znth, nth_coef.
  unfold Constraint_list.
  rewrite Znth_cons by lia.
  unfold Znth.
  reflexivity.
Qed.

Lemma eliminate_pos_neg:
  forall (l : LP) (b : BP) (n : Z),
    eliminate_xn n l b ->
    1 <= n ->
    forall up low re, form_BP up low re b ->
      InequList_nth_pos n up /\ InequList_nth_neg n low.
Proof.
  intros l b n Helim Hn up low re Hform.
  destruct Hform as [? [? ?]].
  subst.
  split.
  - unfold InequList_nth_pos.
    intros c Hc.
    rewrite (elim_upper _ _ _ Helim c) in Hc.
    destruct Hc as [_ Hpos].
    rewrite coef_Znth_nth by lia.
    exact Hpos.
  - unfold InequList_nth_neg.
    intros c Hc.
    rewrite (elim_lower _ _ _ Helim c) in Hc.
    destruct Hc as [_ Hneg].
    rewrite coef_Znth_nth by lia.
    exact Hneg.
Qed.

Lemma mpz_coef_array_length:
  forall x n c, x <> NULL ->
    mpz_coef_array x n c |-- “ coef_Zlength c = n ”.
Proof.
  intros.
  unfold mpz_coef_array.
  Split.
  - Intros. lia.
  - Intros.
    unfold coef_Zlength.
    prop_apply MpzArray.full_length.
    Intros_p Hlen.
    dump_pre_spatial.
    exact Hlen.
Qed.

Lemma mpz_coef_array_split:
  forall x i n c,
    0 <= i < n ->
    x <> NULL ->
    mpz_coef_array x n c
    |-- mpz_store x i (coef_Znth i c 0) **
        mpz_coef_array_missing_i_rec x i 0 n c.
Proof.
  intros.
  unfold mpz_coef_array, mpz_coef_array_missing_i_rec.
  Split.
  - Intros.
    subst x.
    unfold NULL in H0.
    lia.
  - Intros.
    sep_apply_l_atomic (MpzArray.full_split_to_missing_i x i n (Constraint_list c) 0).
    + dump_pre_spatial.
      lia.
    + unfold coef_Znth.
      cancel.
Qed.

Lemma InequList_coef_Zlength:
  forall p n lp,
    InequList p n lp |-- “ forall c, In c lp -> coef_Zlength c = n ”.
Proof.
  intros p n lp.
  revert p.
  induction lp as [| a lp IH]; intros p; simpl.
  - dump_pre_spatial.
    intros c Hin.
    contradiction.
  - Intros coef next.
    sep_apply_l_atomic (mpz_coef_array_length coef n a H0).
    sep_apply_l_atomic (IH next).
    Intros_p Hlen.
    Intros_p Htail.
    dump_pre_spatial.
    intros c Hin.
    destruct Hin as [Heq | Hin].
    + subst. reflexivity.
    + apply Htail. exact Hin.
Qed.

Lemma mpz_coef_array_merge:
  forall x i n v c,
    0 <= i < n ->
    x <> NULL ->
    mpz_store x i v **
    mpz_coef_array_missing_i_rec x i 0 n c
    |-- mpz_coef_array x n (coef_replace_Znth i v c).
Proof.
  intros.
  unfold mpz_coef_array, mpz_coef_array_missing_i_rec.
  sep_apply MpzArray.missing_i_merge_to_full; try lia.
  Right.
  unfold coef_replace_Znth.
  destruct i; try lia.
  - unfold Constraint_list.
    simpl.
    change (replace_Znth 0 v (const c :: coef c)) with (v :: coef c).
    split_pure_spatial.
    + cancel; dump_pre_spatial; reflexivity.
    + dump_pre_spatial; assumption.
  - rewrite constr_list_constr.
    2:{
      unfold Constraint_list.
      rewrite replace_Znth_cons by lia.
      discriminate.
    }
    unfold Constraint_list.
    simpl const.
    set (k := Z.pos p).
    set (t := k - 1).
    simpl coef.
    unfold t.
    rewrite replace_Znth_cons; try lia.
    split_pure_spatial.
    + cancel; dump_pre_spatial; reflexivity.
    + dump_pre_spatial; assumption.
Qed.

Lemma coef_replace_Znth_eq:
  forall c i v,
    0 <= i < coef_Zlength c ->
    coef_Znth i (coef_replace_Znth i v c) 0 = v.
Proof.
  intros.
  unfold coef_Znth, coef_replace_Znth.
  assert (Hnonempty: replace_Znth i v (Constraint_list c) <> nil).
  { intro Hnil.
    destruct c as [c0 ccoef].
    unfold Constraint_list in Hnil.
    unfold replace_Znth in Hnil.
    destruct (Z.to_nat i); simpl in Hnil; discriminate.
  }
  rewrite constr_list_constr by exact Hnonempty.
  apply Znth_replace_Znth_Same.
  unfold coef_Zlength in H.
  rewrite Zlength_correct.
  exact H.
Qed.

Lemma coef_replace_Znth_length:
  forall c i v,
    coef_Zlength (coef_replace_Znth i v c) = coef_Zlength c.
Proof.
  intros.
  unfold coef_Zlength, coef_replace_Znth.
  assert (Hnonempty: replace_Znth i v (Constraint_list c) <> nil).
  { intro Hnil.
    destruct c as [c0 ccoef].
    unfold Constraint_list in Hnil.
    unfold replace_Znth in Hnil.
    destruct (Z.to_nat i); simpl in Hnil; discriminate.
  }
  rewrite constr_list_constr by exact Hnonempty.
  rewrite <- !Zlength_correct.
  rewrite Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma coef_replace_Znth_diff:
  forall c i j v,
    0 <= i < coef_Zlength c ->
    0 <= j < coef_Zlength c ->
    i <> j ->
    coef_Znth j (coef_replace_Znth i v c) 0 = coef_Znth j c 0.
Proof.
  intros.
  unfold coef_Znth, coef_replace_Znth.
  assert (Hnonempty: replace_Znth i v (Constraint_list c) <> nil).
  { intro Hnil.
    destruct c as [c0 ccoef].
    unfold Constraint_list in Hnil.
    unfold replace_Znth in Hnil.
    destruct (Z.to_nat i); simpl in Hnil; discriminate.
  }
  rewrite constr_list_constr by exact Hnonempty.
  apply Znth_replace_Znth_Diff.
  - unfold coef_Zlength in H.
    rewrite Zlength_correct.
    exact H.
  - unfold coef_Zlength in H0.
    rewrite Zlength_correct.
    exact H0.
  - exact H1.
Qed.

Lemma coef_pre_eq_extend:
  forall i c prefix v,
    i = Zlength prefix ->
    0 <= i < coef_Zlength c ->
    coef_pre_eq i c (list_Constraint prefix) ->
    coef_pre_eq (i + 1) (coef_replace_Znth i v c)
      (list_Constraint (prefix ++ v :: nil)).
Proof.
  intros i c prefix v Hi Hilen Hpre.
  unfold coef_pre_eq in *.
  intros j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j.
    rewrite (coef_replace_Znth_eq c i v) by exact Hilen.
    rewrite Hi.
    rewrite coef_Znth_list_Constraint_app_eq.
    reflexivity.
  - rewrite (coef_replace_Znth_diff c i j v) by (try exact Hilen; lia).
    rewrite coef_Znth_list_Constraint_app_lt by lia.
    apply Hpre. lia.
Qed.

Lemma coef_pre_eq_complete:
  forall i c prefix,
    i = Zlength prefix ->
    coef_Zlength c = i ->
    coef_pre_eq i c (list_Constraint prefix) ->
    c = list_Constraint prefix.
Proof.
  intros i c prefix Hi Hlen Hpre.
  destruct prefix as [|a prefix'].
  - rewrite Zlength_nil in Hi.
    destruct c as [c0 coef0].
    unfold coef_Zlength in Hlen.
    simpl in Hlen.
    lia.
  - destruct c as [c0 coef0].
    assert (Hclen : length (c0 :: coef0) = length (a :: prefix')).
    { apply Nat2Z.inj.
      simpl in Hlen.
      rewrite Hi in Hlen.
      rewrite Zlength_correct in Hlen.
      exact Hlen. }
    assert (Hceq : c0 :: coef0 = a :: prefix').
    {
      apply list_eq_ext_nat with (d := 0); auto.
      intros k Hk.
      assert (0 <= Z.of_nat k /\ Z.of_nat k < i)
        by (rewrite Hi, Zlength_correct; lia).
      specialize (Hpre (Z.of_nat k) H).
      unfold coef_Znth, Znth in Hpre.
      rewrite constr_list_constr in Hpre by congruence.
      rewrite Nat2Z.id in Hpre.
      exact Hpre.
    }
    inversion Hceq; subst.
    reflexivity.
Qed.

Lemma inequlist_0_implies_nil:
  forall l n,
    InequList 0 n l |-- “ l = nil ” && emp.
Proof.
  LLM_pre_process ltac:(lia).
  destruct l.
  - simpl.
    Intros_p Hnull.
    split_pure_spatial.
    + normalize; cancel.
    + dump_pre_spatial; reflexivity.
  - simpl. Intros c0 y. tauto.
Qed.

Lemma InequList_seg_append:
  forall l x n p1 p2 p3 coef,
    p2 <> NULL ->
    coef <> NULL ->
    mpz_coef_array coef n x **
    &(p2 # "InequList" ->ₛ "coef") # Ptr |-> coef **
    &(p2 # "InequList" ->ₛ "next") # Ptr |-> p3 **
    InequList_seg p1 p2 n l
    |-- InequList_seg p1 p3 n (l ++ x :: nil).
Proof.
  intros.
  revert p1 p2 p3 H.
  induction l; simpl; intros.
  - Intros_p Hp12.
    subst p1.
    Exists coef p3.
    split_pure_spatial.
    + normalize; repeat cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; reflexivity.
  - Intros.
    Intros x0 z.
    Intros.
    pose proof (IHl z p2 p3 H) as Htail.
    sep_apply Htail.
    Exists x0 z.
    split_pure_spatial.
    + normalize; repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma InequList_seg_append_list:
  forall l1 l2 x n p1 p2 p3 coef,
    p2 <> NULL ->
    coef <> NULL ->
    mpz_coef_array coef n x **
    &(p2 # "InequList" ->ₛ "coef") # Ptr |-> coef **
    &(p2 # "InequList" ->ₛ "next") # Ptr |-> p3 **
    InequList_seg p1 p2 n l1 **
    InequList p3 n l2
    |-- InequList p1 n (l1 ++ x :: l2).
Proof.
  intros.
  sep_apply InequList_seg_append; try easy.
  revert p1 p3 l2.
  induction l1; intros; simpl.
  - Intros x0 z.
    repeat Intros.
    subst z.
    Exists x0 p3.
    split_pure_spatial.
    + normalize; repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
  - Intros x0 z.
    repeat Intros.
    sep_apply (IHl1 z p3 l2).
    Exists x0 z.
    split_pure_spatial.
    + normalize; repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma InequList_seg_app:
  forall l1 l2 n p1 p2,
    InequList_seg p1 p2 n l1 **
    InequList p2 n l2
    |-- InequList p1 n (l1 ++ l2).
Proof.
  intros.
  revert p1 p2 l2.
  induction l1; intros; simpl.
  - Intros_p Hp12.
    subst p1.
    normalize; cancel.
  - Intros x0 z.
    repeat Intros.
    sep_apply (IHl1 z p2 l2).
    Exists x0 z.
    split_pure_spatial.
    + normalize; repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma generate_new_constraint_list_loop_nil_lower:
  forall cur_num lp1 init,
    equiv (generate_new_constraint_list_loop cur_num lp1 nil init) (return init).
Proof.
  intros cur_num lp1.
  induction lp1 as [| c1 lp1 IH]; intros init; simpl.
  - reflexivity.
  - prog_nf.
    apply IH.
Qed.

Lemma real_shadow_step_nil_equiv:
  forall cnt,
    equiv (real_shadow_step_prog cnt nil) (return nil).
Proof.
  intros.
  unfold real_shadow_step_prog, eliminate_prog, eliminate_from, empty_bp.
  simpl.
  prog_nf.
  unfold generate_new_constraint_list_prog.
  simpl.
  prog_nf.
  reflexivity.
Qed.

Lemma real_shadow_loop_nil_safeExec_nat:
  forall n X,
    safeExec ATrue (real_shadow_loop_prog (Z.of_nat n) nil) X ->
    safeExec ATrue (return nil) X.
Proof.
  induction n as [| n IH]; intros X Hsafe.
  - unfold real_shadow_loop_prog in Hsafe at 1.
    unfold_loop in Hsafe.
    prog_nf in Hsafe.
    unfold real_shadow_loop_body in Hsafe.
    prog_nf in Hsafe.
    safe_choice_r Hsafe.
    + unfold break in Hsafe.
      prog_nf in Hsafe.
      simpl in Hsafe.
      exact Hsafe.
    + lia.
  - unfold real_shadow_loop_prog in Hsafe at 1.
    unfold_loop in Hsafe.
    prog_nf in Hsafe.
    unfold real_shadow_loop_body in Hsafe.
    prog_nf in Hsafe.
    safe_choice_l Hsafe; [| lia].
    unfold real_shadow_body_prog in Hsafe.
    rewrite real_shadow_step_nil_equiv in Hsafe.
    prog_nf in Hsafe.
    unfold continue in Hsafe.
    prog_nf in Hsafe.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) in Hsafe by lia.
    fold (real_shadow_loop_prog (Z.of_nat n) nil) in Hsafe.
    eapply IH; exact Hsafe.
Qed.

Lemma real_shadow_loop_nil_safeExec:
  forall cnt X,
    0 <= cnt ->
    safeExec ATrue (real_shadow_loop_prog cnt nil) X ->
    safeExec ATrue (return nil) X.
Proof.
  intros cnt X Hcnt Hsafe.
  replace cnt with (Z.of_nat (Z.to_nat cnt)) in Hsafe by lia.
  eapply real_shadow_loop_nil_safeExec_nat.
  exact Hsafe.
Qed.

Lemma real_shadow_loop_step_equiv:
  forall cnt lp,
    1 <= cnt ->
    equiv (real_shadow_loop_prog cnt lp) (bind (eliminate_prog cnt lp) (real_shadow_after_eliminate cnt)).
Proof.
  intros cnt lp Hcnt.
  assert (bind_bot_equiv_local:
    forall (A B: Type) (k: A -> program unit B),
      equiv (bind ProgramPO.bot k) ProgramPO.bot).
  {
    intros A B k.
    constructor; simpl; sets_unfold; intros.
    - split; intros H.
      + destruct H as [? [? [? _]]]; tauto.
      + tauto.
    - split; intros H.
      + unfold MonadErr.nrm_err in H.
        destruct H as [H | H]; [tauto |].
        destruct H as [? [? [? ?]]]; tauto.
      + tauto.
  }
  unfold real_shadow_loop_prog.
  unfold_loop.
  unfold real_shadow_loop_body at 1.
  prog_nf.
  rewrite (assume_equiv (1 <= cnt) _ Hcnt).
  rewrite (assume_false_equiv (cnt < 1) (break (snd (cnt, lp))) ltac:(lia)).
  rewrite choice_l_equiv.
  2: { apply bind_bot_equiv_local. }
  unfold real_shadow_body_prog, real_shadow_step_prog, real_shadow_after_eliminate, real_shadow_after_generate.
  prog_nf.
  unfold continue.
  prog_nf.
  monad_equiv.
  monad_equiv.
  intro bp.
  monad_equiv.
Qed.
