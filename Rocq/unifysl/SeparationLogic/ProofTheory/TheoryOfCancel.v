Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.

Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Morphisms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import SeparationLogicNotation.

Section StructOfCancel.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {empAX: EmpAxiomatization L Gamma}.

Inductive expr_deep: Type :=
  | impp_deep : expr_deep -> expr_deep -> expr_deep
  | sepcon_deep : expr_deep -> expr_deep -> expr_deep
  | emp_deep : expr_deep
  | varp_deep : nat -> expr_deep.

Fixpoint beq e1 e2 :=
  match e1, e2 with
  | emp_deep, emp_deep => true
  | varp_deep x, varp_deep y => Nat.eqb x y
  | sepcon_deep p11 p12, sepcon_deep p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | impp_deep p11 p12, impp_deep p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | _, _ => false
  end.

Inductive tree_pos: Type :=
  | var_pos : expr -> option positive -> tree_pos
  | sepcon_pos : tree_pos -> tree_pos -> tree_pos.

Fixpoint cancel_mark_context dep q tep key : tree_pos * bool:=
  match dep, tep with
  | sepcon_deep dp dq, sepcon_pos tp tq =>
    match cancel_mark_context dp q tp key with
    | (tp', true) => ((sepcon_pos tp' tq), true)
    | (tp', false) =>
      match cancel_mark_context dq q tq key with
      | (tq', true) => ((sepcon_pos tp tq'), true)
      | (tq', false) => (tep, false)
      end
    end
  | p, (var_pos sp o) =>
    match (beq p q) with
    | true =>
      match o with
      | None => ((var_pos sp (Some key)), true)
      | _ => (tep, false)
      end
    | false => (tep, false)
    end
  | _, _ => (tep, false)
  end.

Fixpoint cancel_mark' dep deq tep teq key : tree_pos * tree_pos * positive :=
  match deq, teq with
  | sepcon_deep dp dq, sepcon_pos tp tq =>
    match (cancel_mark' dep dp tep tp key) with
    | (tep', tp', key') =>
      match (cancel_mark' dep dq tep' tq key') with
      | (tep'', tq', key'') => (tep'', sepcon_pos tp' tq', key'')
      end
    end
  | q, (var_pos sq o) =>
    match (cancel_mark_context dep q tep key) with
    | (tep', true) => (tep', (var_pos sq (Some key)), Pos.succ key)
    | (tep', false) => (tep', var_pos sq None, key)
    end
  | _, _ => (tep, teq, key)
  end.

Definition cancel_mark dep deq tep teq : tree_pos * tree_pos :=
  match (cancel_mark' dep deq tep teq xH) with
  | (tep', teq', key') => (tep', teq')
  end.

Fixpoint unmark_sort' tep : option expr :=
  match tep with
  | sepcon_pos tp tq =>
    match unmark_sort' tp with
    | None => unmark_sort' tq
    | Some sp =>
      match unmark_sort' tq with
      | None => Some sp
      | Some sq => Some (sp * sq)
      end
    end
  | var_pos sq o =>
    match o with
    | None => Some sq
    | _ => None
    end
  end.
Definition unmark_sort tep : expr :=
  match unmark_sort' tep with
  | Some sp => sp
  | None => emp
  end.

Definition cancel_different tep teq : expr :=
  (unmark_sort tep) --> (unmark_sort teq).

Fixpoint mark_sort' tep m: PTree.tree expr :=
  match tep with
  | sepcon_pos tp tq =>
    match mark_sort' tp m with
    | m' => mark_sort' tq m'
    end
  | var_pos sq o =>
    match o with
    | None => m
    | Some pos =>
      match PTree.get_rec expr pos m with
      | None => PTree.set_rec expr pos sq m
      | Some sp => PTree.set_rec expr pos (sp * sq) m
      end
    end
  end.
Definition mark_sort tep : PTree.tree expr :=
  mark_sort' tep PTree.empty.

Definition cancel_same tep teq : Prop :=
  mark_sort tep = mark_sort teq.

Fixpoint restore' tep : expr :=
  match tep with
  | sepcon_pos tp tq => (restore' tp) * (restore' tq)
  | var_pos sp o => sp
  end.
Definition restore tep teq : expr :=
  (restore' tep) --> (restore' teq).

End StructOfCancel.

Section ProofOfLemma.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {empAX: EmpAxiomatization L Gamma}.

Lemma provable_sepcon_assoc2 : forall x y z,
  |-- (x * y) * z --> (x * (y * z)).
Proof.
  intros.
  rewrite (provable_sepcon_comm_impp (x * y) z).
  rewrite (provable_sepcon_assoc1 z x y).
  rewrite (provable_sepcon_comm_impp (z * x) y).
  rewrite (provable_sepcon_assoc1 y z x).
  rewrite (provable_sepcon_comm_impp (y * z) x).
  apply provable_impp_refl.
Qed.

Lemma switch : forall x y p q,
  |-- x * y * (p * q) --> x * p * (y * q).
Proof.
  intros.
  rewrite <- (provable_sepcon_assoc1 x p (y * q)).
  rewrite <- (provable_sepcon_comm_impp (y * q) p).
  rewrite <- (provable_sepcon_assoc1 y q p).
  rewrite <- (provable_sepcon_comm_impp p q).
  apply provable_sepcon_assoc2.
Qed.

Fixpoint build l : expr :=
  match l with
  | nil => emp
  | p :: l' => p * build l'
  end.

Lemma build_cons : forall l1 l2 e,
  |-- build (l1 ++ e :: l2) --> build (l1 ++ l2) * e.
Proof.
  intros.
  induction l1; simpl.
  - apply provable_sepcon_comm_impp.
  - rewrite IHl1.
    apply provable_sepcon_assoc1.
Qed.

Lemma sepcon_build : forall l1 l2 e,
  |-- build (l1 ++ l2) * e --> build (l1 ++ e :: l2).
Proof.
  intros.
  induction l1; simpl.
  - apply provable_sepcon_comm_impp.
  - rewrite <- IHl1.
    apply provable_sepcon_assoc2.
Qed.

Lemma add1 : forall e' p m,
  |-- build (PTree.elements expr (mark_sort' (var_pos e' (Some p)) m))
  --> build (PTree.elements expr m) * e'.
Proof.
  intros.
  unfold mark_sort'.
  destruct (PTree.get_rec expr p m) eqn:?H.
  - pose proof (PTree.elements_set_some expr p e (e * e') m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite build_cons. rewrite <- sepcon_build.
    apply provable_sepcon_assoc1.
  - pose proof (PTree.elements_set_none expr p e' m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite build_cons.
    apply provable_impp_refl.
Qed.

Lemma add2 : forall e' p m,
  |-- build (PTree.elements expr m) * e'
  --> build (PTree.elements expr (mark_sort' (var_pos e' (Some p)) m)).
Proof.
  intros.
  unfold mark_sort'.
  destruct (PTree.get_rec expr p m) eqn:?H.
  - pose proof (PTree.elements_set_some expr p e (e * e') m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite build_cons. rewrite <- sepcon_build.
    apply provable_sepcon_assoc2.
  - pose proof (PTree.elements_set_none expr p e' m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite <- sepcon_build.
    apply provable_impp_refl.
Qed.

Lemma L1_before1 : forall sp p,
  |-- sp --> build (PTree.elements expr (mark_sort (var_pos sp (Some p)))).
Proof.
  intros.
  unfold mark_sort, mark_sort'.
  rewrite PTree.get_empty.
  rewrite PTree.elements_set_empty.
  unfold build.
  apply provable_derives_sepcon_emp.
Qed.

Lemma L1_before2 : forall p1 p2,
  |-- unmark_sort p1 * unmark_sort p2 --> unmark_sort (sepcon_pos p1 p2).
Proof.
  intros.
  unfold unmark_sort.
  unfold unmark_sort'; fold unmark_sort'.
  destruct (unmark_sort' p1), (unmark_sort' p2).
  - apply provable_impp_refl.
  - apply provable_sepcon_emp_derives.
  - rewrite provable_sepcon_comm_impp; apply provable_sepcon_emp_derives.
  - apply provable_sepcon_emp_derives.
Qed.

Lemma L1_before3 : forall p1 p2,
  |-- build (PTree.elements expr (mark_sort p1)) * build (PTree.elements expr (mark_sort p2)) --> build (PTree.elements expr (mark_sort (sepcon_pos p1 p2))).
Proof.
  intros.
  unfold  mark_sort.
  unfold mark_sort'; fold mark_sort'.
  set (m1 := mark_sort' p1 PTree.empty) at 1.
  set (m3 := mark_sort' p1 PTree.empty).
  set (m2 := PTree.empty).
  assert (|-- build (PTree.elements expr m1) * build (PTree.elements expr m2) --> build (PTree.elements expr m3)).
  { unfold m2, PTree.empty, PTree.elements, PTree.xelements. apply provable_sepcon_emp_derives. }
  clearbody m1 m2 m3.
  revert m1 m2 m3 H.
  induction p2; intros.
  - destruct o.
    + rewrite add1.
      rewrite <- add2.
      rewrite provable_sepcon_assoc1.
      rewrite H.
      apply provable_impp_refl.
    + auto.
  - apply IHp2_1 in H.
    apply IHp2_2 in H.
    auto.
Qed.

Lemma L1 : forall tep,
  |-- restore' tep --> unmark_sort tep * (build (PTree.elements expr (mark_sort tep))).
Proof.
  intros.
  induction tep as [sp op|p1 IH1 p2 IH2]; unfold restore'; fold restore'.
  - unfold unmark_sort, unmark_sort'.
    destruct op.
    + pose proof (L1_before1 sp p) as L1_before1; compute in L1_before1.
      rewrite <- L1_before1; clear L1_before1.
      rewrite <- provable_sepcon_comm_impp.
      apply provable_derives_sepcon_emp.
    + apply provable_derives_sepcon_emp.
  - rewrite IH1, IH2.
    rewrite <- L1_before2, <- L1_before3.
    apply switch.
Qed.

Lemma L2_before1 : forall sq p,
  |-- build (PTree.elements expr (mark_sort (var_pos sq (Some p)))) --> sq.
Proof.
  intros.
  unfold mark_sort, mark_sort'.
  rewrite PTree.get_empty.
  rewrite PTree.elements_set_empty.
  unfold build.
  apply provable_sepcon_emp_derives.
Qed.

Lemma L2_before2 : forall q1 q2,
  |-- unmark_sort (sepcon_pos q1 q2) --> unmark_sort q1 * unmark_sort q2.
Proof.
  intros.
  unfold unmark_sort.
  unfold unmark_sort'; fold unmark_sort'.
  destruct (unmark_sort' q1), (unmark_sort' q2).
  - apply provable_impp_refl.
  - apply provable_derives_sepcon_emp.
  - rewrite <- provable_sepcon_comm_impp; apply provable_derives_sepcon_emp.
  - apply provable_derives_sepcon_emp.
Qed.

Lemma L2_before3 : forall q1 q2,
  |-- build (PTree.elements expr (mark_sort (sepcon_pos q1 q2))) --> build (PTree.elements expr (mark_sort q1)) * build (PTree.elements expr (mark_sort q2)).
Proof.
  intros.
  unfold  mark_sort.
  unfold mark_sort'; fold mark_sort'.
  set (m1 := mark_sort' q1 PTree.empty) at 2.
  set (m3 := mark_sort' q1 PTree.empty).
  set (m2 := PTree.empty).
  assert (|-- build (PTree.elements expr m3) --> build (PTree.elements expr m1) * build (PTree.elements expr m2)).
  { unfold m2, PTree.empty, PTree.elements, PTree.xelements. apply provable_derives_sepcon_emp. }
  clearbody m1 m2 m3.
  revert m1 m2 m3 H.
  induction q2; intros.
  - destruct o.
    + rewrite add1.
      rewrite <- add2.
      rewrite <- provable_sepcon_assoc2.
      rewrite H.
      apply provable_impp_refl.
    + auto.
  - apply IHq2_1 in H.
    apply IHq2_2 in H.
    auto.
Qed.

Lemma L2 : forall teq,
  |-- unmark_sort teq * build (PTree.elements expr (mark_sort teq)) --> restore' teq.
Proof.
  intros.
  induction teq as [sq oq|q1 IH1 q2 IH2]; unfold restore'; fold restore'.
  - unfold unmark_sort, unmark_sort'.
    destruct oq.
    + pose proof (L2_before1 sq p) as L2_before1; compute in L2_before1.
      rewrite L2_before1; clear L2_before1.
      rewrite provable_sepcon_comm_impp.
      apply provable_sepcon_emp_derives.
    + apply provable_sepcon_emp_derives.
  - rewrite <- IH1, <- IH2.
    rewrite L2_before2, L2_before3.
    apply switch.
Qed.

Lemma L3 : forall m1 m2,
  m1 = m2 ->
  |-- build (PTree.elements expr m1) --> build (PTree.elements expr m2).
Proof.
  intros.
  rewrite H.
  apply provable_impp_refl.
Qed.

End ProofOfLemma.

Section TheoryOfCancel.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {empAX: EmpAxiomatization L Gamma}.

Lemma cancel_sound : forall tep teq,
  cancel_same tep teq ->
  |-- cancel_different tep teq ->
  |-- restore tep teq.
Proof.
  unfold restore, cancel_same, cancel_different.
  intros tep teq CS CD.
  apply L3 in CS.
  rewrite L1, CS, CD.
  apply L2.
Qed.

End TheoryOfCancel.