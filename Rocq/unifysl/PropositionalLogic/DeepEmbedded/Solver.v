Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.

Require Logic.PropositionalLogic.DeepEmbedded.Deep.

Local Open Scope list_scope.

Ltac length_cont ls k :=
  match ls with
  | nil => k O
  | _ :: ?ls' => length_cont ls' ltac:(fun n => k (S n))
  end.
Ltac length ls := length_cont ls ltac:(fun l => l).

Definition rev (l: list nat): list nat :=
  (fix rev (l: list nat) (cont: list nat -> list nat): list nat :=
    match l with
    | nil => cont nil
    | a :: l0 => rev l0 (fun l => a :: cont l)
    end) l (fun l => l).

Ltac reverse_cont l k :=
  match l with
  | @nil ?T => k (@nil T)
  | @cons _ ?h ?t =>
    let k' l :=
        let t' := k l in
        constr:(cons h t')
    in reverse_cont t k'
  end.
Ltac reverse l := reverse_cont l ltac:(fun l => l).

Ltac pred n :=
  match n with
  | O => O
  | S ?m => m
  end.

Ltac search_expr' n i l l0 :=
  match l with
  | nil => let len := length l0 in constr:((S len, n :: l0))
  | n :: ?t => constr:((i, l0))
  | _ :: ?t => let pi := pred i in search_expr' n pi t l0
  end.
Ltac search_expr n l := let len := length l in search_expr' n len l l.

Section Temp.
  Context {L : Language}
          {minL : MinimumLanguage L}
          {andpL : AndLanguage L}
          (default: Base.expr)
          (tbl : list Base.expr).

  Fixpoint reflect (e : Deep.expr) : Base.expr :=
    match e with
    | Deep.varp n => List.nth (pred n) tbl default
    | Deep.andp e1 e2 => Syntax.andp (reflect e1) (reflect e2)
    | Deep.impp e1 e2 => Syntax.impp (reflect e1) (reflect e2)
    end.
End Temp.

Ltac shallowToDeep' se l0 :=
  match se with
  | Syntax.andp ?sp ?sq =>
    match shallowToDeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowToDeep' sq l1 with
      | (?dq, ?l2) => constr:((Deep.andp dp dq, l2))
      end
    end
  | Syntax.impp ?sp ?sq =>
    match shallowToDeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowToDeep' sq l1 with
      | (?dq, ?l2) => constr:((Deep.impp dp dq, l2))
      end
    end
  | ?sp => match search_expr sp l0 with
          | (?i, ?l1) => constr:((Deep.varp i, l1))
          end
  end.

Ltac shallowToDeep se :=
  match shallowToDeep' se constr:(@nil Base.expr) with
  | (?de, ?tbl) =>
    let tbl' := reverse tbl in
    assert (reflect se tbl' de = se) by reflexivity
  end.

Section Temp.
  Context (L : Base.Language)
          (minL : Syntax.MinimumLanguage L)
          (andL : Syntax.AndLanguage L).
  Context (P Q R : Base.expr).
  Goal False.
    let n := search_expr 1 (1 :: 2 :: 3 :: 4 :: nil) in pose n.
    let n := search_expr 5 (1 :: 2 :: 3 :: 4 :: nil) in pose n.
    shallowToDeep (Syntax.impp (Syntax.andp P Q) (Syntax.andp Q P)).
  Abort.
End Temp.

Section Temp.
  Context {L: Language}
          {minL: MinimumLanguage L}
          {andpL: AndLanguage L}
          {GammaP: Provable L}
          {minAX: MinimumAxiomatization L GammaP}
          {andpAX: AndAxiomatization L GammaP}.

  Theorem reify_sound :
    forall table (default: Base.expr) (e : Deep.expr),
      Deep.provable e -> provable (reflect default table e).
  Proof.
    induction 1.
    - apply (modus_ponens (reflect default table x) (reflect default table y)); assumption.
    - apply (provable_axiom1 (reflect default table x) (reflect default table y)); assumption.
    - apply (axiom2 (reflect default table x) (reflect default table y)); assumption.
    - apply (provable_andp_intros (reflect default table x) (reflect default table y)); assumption.
    - apply (provable_andp_elim1 (reflect default table x) (reflect default table y)); assumption.
    - apply (provable_andp_elim2 (reflect default table x) (reflect default table y)); assumption.
  Qed.
End Temp.

Module DSolver.
  Local Existing Instances Deep.L Deep.minL Deep.andpL Deep.truepL Deep.iffpL Deep.iter_andp_L Deep.iter_andp_DL Deep.GP Deep.minAX Deep.andpAX Deep.truepAX Deep.iffpAX Deep.iter_andp_AXL.

  #[export] Instance Adj : P.Adjointness _ _ andp impp.
  Proof.
    constructor. split; intros.
    - rewrite <- provable_impp_uncurry. auto.
    - rewrite <- provable_impp_curry. auto.
  Qed.

  #[export] Instance Comm : P.Commutativity _ _ andp.
  Proof.
    apply andp_Comm.
  Qed.

  #[export] Instance Mono : P.Monotonicity _ _ andp.
  Proof.
    apply andp_Mono.
  Qed.

  #[export] Instance Assoc : P.Associativity _ _ andp.
  Proof.
    apply andp_Assoc.
  Qed.

  #[export] Instance LUnit : P.LeftUnit _ _ truep andp.
  Proof.
    constructor; intros; rewrite provable_truep_andp; apply provable_impp_refl.
  Qed.

  #[export] Instance RUnit : P.RightUnit _ _ truep andp.
  Proof.
    constructor; intros; rewrite provable_andp_truep; apply provable_impp_refl.
  Qed.

  Fixpoint flatten_imp (e : expr) : list expr * expr :=
    match e with
    | Deep.impp p q => let (cxt, fq) := flatten_imp q in (p :: cxt, fq)
    | _ => (nil, e)
    end.

  Definition flatten_imp_inv (p : list Deep.expr * Deep.expr) :=
    let (ctx, r) := p in multi_imp ctx r.

  Lemma flatten_imp_sound :
    forall e, e = flatten_imp_inv (flatten_imp e).
  Proof.
    intros. induction e; auto.
    simpl.
    destruct (flatten_imp e2) as [ctx fq].
    simpl. rewrite IHe2. auto.
  Qed.

  Fixpoint flatten_and (e : expr) : list expr :=
    match e with
    | Deep.andp p q => (flatten_and p ++ flatten_and q)
    | s => s :: nil
    end.

  Lemma flatten_and_sound :
    forall e, provable (iffp e (iter_andp (flatten_and e))).
  Proof.
    intros.
    rewrite iter_andp_def_l.
    induction e; simpl flatten_and
        (*;
      [ change (flatten_and_inv _) with (fold_left andp (flatten_and e1 ++ flatten_and e2) truep)
      | change (flatten_and_inv _) with (andp truep (orp e1 e2))
      | change (flatten_and_inv _) with (andp truep (impp e1 e2))
      | change (flatten_and_inv _) with (andp truep falsep)
      | change (flatten_and_inv _) with (andp truep (Deep.varp n))
      ]*).
    {
      apply provables_iffp_intros. 
      {
        rewrite <- P.assoc_prodp_fold_left.
        rewrite provable_iffp_elim1 in IHe1.
        rewrite provable_iffp_elim1 in IHe2.
        apply P.prodp_mono; auto.
      }
      {
        rewrite P.assoc_fold_left_app.
        rewrite provable_iffp_elim2 in IHe1.
        rewrite provable_iffp_elim2 in IHe2.
        apply P.prodp_mono; auto.
      }
    }
    all: apply provables_iffp_intros;
      cbv [fold_left];
      [rewrite <- P.left_unit2 | rewrite P.left_unit1];
      apply provable_impp_refl.
  Qed.

  Definition flatten (e : expr) : list expr * list expr :=
    let (ctx, r) := flatten_imp e in
    (List.flat_map flatten_and ctx, flatten_and r).

  Definition AllInContext (es1 es2 : list expr) : Prop :=
    Forall (fun e => In e es1) es2.

  Lemma multi_imp_weaken :
    forall x y xs, provable (impp x y) -> provable (impp x (multi_imp xs y)).
  Proof.
    induction xs; intros.
    - auto.
    - change (multi_imp _ _) with (impp a (multi_imp xs y)).
      rewrite <- aux_minimun_theorem01. auto.
  Qed.

  Lemma flatten_imp_inv_In : forall es r, In r es -> provable (flatten_imp_inv (es,r)).
  Proof.
    intros. induction es.
    - contradiction.
    - inversion H; subst.
      + change (flatten_imp_inv _) with (impp r (multi_imp es r)).
        apply multi_imp_weaken. apply provable_impp_refl.
      + change (flatten_imp_inv _) with (impp a (multi_imp es r)).
        apply aux_minimun_rule00. auto.
  Qed.

  Lemma multi_imp_andp_intros :
    forall es x y, provable (multi_imp es x) ->
              provable (multi_imp es y) ->
              provable (multi_imp es (andp x y)).
  Proof.
    intros es x y Hx Hy.
    pose proof provable_multi_imp_weaken es x (impp y (andp x y)) (provable_andp_intros x y).
    pose proof provables_modus_ponens _ _ H Hx.
    pose proof provable_multi_imp_modus_ponens es y (andp x y).
    pose proof provables_modus_ponens _ _ H1 Hy.
    pose proof provables_modus_ponens _ _ H2 H0.
    exact H3.
  Qed.

  Lemma flatten_inv_left_In :
    forall es r, In r (List.flat_map flatten_and es) -> provable (flatten_imp_inv (es, r)).
  Proof.
    intros.
    induction es; [contradiction|].
    simpl in H.
    apply in_app_or in H.
    destruct H.
    + clear IHes.
      apply flatten_imp_inv_In in H.
      change (flatten_imp_inv _) with (multi_imp (flatten_and a) r) in H.
      rewrite <- iter_andp_multi_imp in H.
      pose proof flatten_and_sound a.
      change (flatten_imp_inv _) with (impp a (multi_imp es r)).
      apply multi_imp_weaken.
      apply provables_iffp_elim1 in H0.
      eapply aux_minimun_rule02; eauto.
    + apply aux_minimun_rule00, IHes, H.
  Qed.

  Lemma flatten_inv_All :
    forall es r, AllInContext (List.flat_map flatten_and es) (flatten_and r) ->
            provable (flatten_imp_inv (es, r)).
  Proof.
    intros.
    assert (Forall (fun e => provable (flatten_imp_inv (es, e)))
                   (flatten_and r)).
    { unfold AllInContext in H. rewrite Forall_forall in *. intros e ?.
      specialize (H e H0). clear H0.
      apply flatten_inv_left_In, H.
    } clear H. rename H0 into H.
    induction r; try apply (Forall_inv H).
    simpl in H; apply Coqlib.Forall_app_iff in H; destruct H as [H1 H2].
    apply IHr1 in H1. apply IHr2 in H2.
    apply multi_imp_andp_intros; auto.
  Qed.
  
  Lemma flatten_sound :
    forall es rs e, (es, rs) = flatten e -> AllInContext es rs -> provable e.
  Proof.
    unfold flatten. intros.
    pose proof flatten_imp_sound e.
    rewrite H1. destruct (flatten_imp e) as [es' r].
    inversion H. clear H. subst. apply flatten_inv_All, H0.
  Qed.

  Definition all_in_context e :=
    let (es, rs) := flatten e in forallb (fun r => existsb (Deep.beq r) es) rs.

  Lemma all_in_AllIn :
    forall es rs e, (es, rs) = flatten e -> all_in_context e = true -> AllInContext es rs.
  Proof.
    intros. unfold all_in_context in H0.
    rewrite <- H in H0. clear H. rename H0 into H.
    rewrite forallb_forall in H.
    unfold AllInContext. rewrite Forall_forall.
    intros. apply H in H0. clear H.
    apply existsb_exists in H0. destruct H0 as [y [H1 H2]].
    apply Deep.beq_eq in H2. subst y. exact H1.
  Qed.

  Lemma all_in_provable :
    forall e, all_in_context e = true -> provable e.
  Proof.
    intros. remember (flatten e) as fe.
    destruct fe as [es rs].
    pose proof all_in_AllIn _ _ _ Heqfe H.
    eapply flatten_sound; eauto.
  Qed.
End DSolver.

Module SolverSound.
  Ltac ipSolver' L se :=
    match shallowToDeep' se constr:(@nil Base.expr) with
    | (?de, ?tbl) =>
      let tbl' := reverse tbl in
      let b := eval hnf in (DSolver.all_in_context de) in
      assert (DSolver.all_in_context de = b) by reflexivity;
      assert (@eq (@Base.expr L) (reflect se tbl' de) (se)) by reflexivity;
      apply (@reify_sound L _ _ _ _ _ tbl' se de);
      apply DSolver.all_in_provable;
      match goal with
      | [H : DSolver.all_in_context _ = true |- _] => apply H
      end
    end.

  Ltac ipSolver :=
    match goal with
    | [|- @Base.provable ?L ?GammaP ?e] => ipSolver' L e
    end.

  Section Temp.
    Context {L: Language}
            {minL: MinimumLanguage L}
            {andpL: AndLanguage L}
            {GammaP: Provable L}
            {minAX: MinimumAxiomatization L GammaP}
            {andpAX: AndAxiomatization L GammaP}.
    Parameter (P Q R : expr).
    Goal (provable (impp (andp P Q) (andp Q P))).
      ipSolver.
    Qed.
  End Temp.
End SolverSound.
