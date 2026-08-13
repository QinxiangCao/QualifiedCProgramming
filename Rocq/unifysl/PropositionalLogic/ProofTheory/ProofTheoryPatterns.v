Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Require Export Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Module P.
Export Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.P.
  
Section DerivableRulesFromPatterns1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {iffpL: IffLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {prodp: expr -> expr -> expr}.

Lemma prodp_comm {Comm: Commutativity L Gamma prodp}: forall x y,
  |-- prodp x y <--> prodp y x.
Proof.
  intros.
  apply provables_iffp_intros; apply prodp_comm_impp.
Qed.

Section UnitTheorems.

Context {e: expr}.

Lemma left_unit {LU: LeftUnit L Gamma e prodp} : forall x, |-- prodp e x <--> x.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply left_unit1.
  + apply left_unit2.
Qed.

Lemma right_unit {RU: RightUnit L Gamma e prodp} : forall x, |-- prodp x e <--> x.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply right_unit1.
  + apply right_unit2.
Qed.

End UnitTheorems.

Section DistrTheorems.

Context {sump: expr -> expr -> expr}.

Lemma prodp_sump_distr_l {LDistr: LeftDistr L Gamma prodp sump}: forall x y z,
  |-- prodp x (sump y z) <--> sump (prodp x y) (prodp x z).
Proof.
  intros.
  apply provables_iffp_intros.
  + apply left_distr1.
  + apply left_distr2.
Qed.

Lemma prodp_sump_distr_r {RDistr: RightDistr L Gamma prodp sump}: forall x y z,
  |-- prodp (sump y z) x <--> sump (prodp y x) (prodp z x).
Proof.
  intros.
  apply provables_iffp_intros.
  + apply right_distr1.
  + apply right_distr2.
Qed.

End DistrTheorems.

End DerivableRulesFromPatterns1.

Section DerivableRulesFromPatterns2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {prodp: expr -> expr -> expr}.

Section AdjointTheorems.

Context {funcp: expr -> expr -> expr}
        {Adj: Adjointness L Gamma prodp funcp}.

Lemma Adjoint2RDistr: RightDistr L Gamma prodp orp.
Proof.
  constructor; intros.
  + apply adjoint.
    apply provables_orp_impp_fold; apply adjoint.
    - apply provable_orp_intros1.
    - apply provable_orp_intros2.
  + apply provables_orp_impp_fold.
    - apply prodp_mono1.
      apply provable_orp_intros1.
    - apply prodp_mono1.
      apply provable_orp_intros2.
Qed.

Lemma Adjoint2LDistr {Comm: Commutativity L Gamma prodp}:
  LeftDistr L Gamma prodp orp.
Proof.
  apply @RightDistr2LeftDistr; auto.
  + apply orp_Mono.
  + apply Adjoint2RDistr.
Qed.

Context {iffpL: IffLanguage L}
        {iffpAX: IffAxiomatization L Gamma}.

(* TODO: l/r wrong *)
Lemma prodp_orp_distr_l:
  forall x y z: expr, |-- prodp (x || y) z <--> (prodp x z || prodp y z).
Proof.
  intros.
  apply (@prodp_sump_distr_r _ _ _ _ _ _ _ _ Adjoint2RDistr).
Qed.

(* TODO: l/r wrong *)
Lemma prodp_orp_distr_r
      {Comm: Commutativity L Gamma prodp}:
  forall x y z: expr, |-- prodp x (y || z) <--> (prodp x y || prodp x z).
Proof.
  intros.
  apply (@prodp_sump_distr_l _ _ _ _ _ _ _ _ Adjoint2LDistr).
Qed.

Lemma orp_funcp
      {andpL: AndLanguage L}
      {andpAX: AndAxiomatization L Gamma}
      {Comm: Commutativity L Gamma prodp}:
  forall x y z: expr, |-- funcp (x || y) z <--> (funcp x z && funcp y z).
Proof.
  pose proof Adjoint2Mono as Mono.
  intros.
  apply provables_iffp_intros.
  + apply provables_impp_andp_fold.
    - apply funcp_mono.
      * apply provable_orp_intros1.
      * apply provable_impp_refl.
    - apply funcp_mono.
      * apply provable_orp_intros2.
      * apply provable_impp_refl.
  + apply adjoint.
    rewrite prodp_orp_distr_r.
    apply provables_orp_impp_fold; apply adjoint.
    - apply provable_andp_elim1.
    - apply provable_andp_elim2.
Qed.

(* TODO: l/r wrong *)
Lemma funcp_andp_distr_r
      {andpL: AndLanguage L}
      {andpAX: AndAxiomatization L Gamma}:
  forall x y z: expr, |-- funcp x (y && z)  <--> (funcp x y && funcp x z).
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provables_impp_andp_fold.
    - apply funcp_mono2.
      apply provable_andp_elim1.
    - apply funcp_mono2.
      apply provable_andp_elim2.
  + apply adjoint.
    apply provables_impp_andp_fold; apply adjoint.
    - apply provable_andp_elim1.
    - apply provable_andp_elim2.
Qed.

Lemma falsep_prodp
      {falsepL: FalseLanguage L}
      {falsepAX: FalseAxiomatization L Gamma}:
  forall x: expr, |-- prodp falsep x <--> falsep.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply adjoint.
    apply provable_falsep_elim.
  + apply provable_falsep_elim.
Qed.

Lemma prodp_falsep
      {falsepL: FalseLanguage L}
      {falsepAX: FalseAxiomatization L Gamma}
      {Comm: Commutativity L Gamma prodp}:
  forall x: expr, |-- prodp x falsep <--> falsep.
Proof.
  intros.
  rewrite prodp_comm.
  rewrite falsep_prodp.
  apply provable_iffp_refl.
Qed.

End AdjointTheorems.

Section MonoTheorems.

Context {iffpL: IffLanguage L}
        {iffpAX: IffAxiomatization L Gamma}
        {Mono: Monotonicity L Gamma prodp}.

Lemma prodp_iffp: forall x1 x2 y1 y2,
  |-- x1 <--> x2 ->
  |-- y1 <--> y2 ->
  |-- prodp x1 y1 <--> prodp x2 y2.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply prodp_mono.
    - apply provables_iffp_elim1; exact H.
    - apply provables_iffp_elim1; exact H0.
  + apply prodp_mono.
    - apply provables_iffp_elim2; exact H.
    - apply provables_iffp_elim2; exact H0.
Qed.

Lemma fold_left_iffp: forall x1 x2 xs1 xs2,
  (Forall2 (fun x1 x2 => |-- x1 <--> x2) xs1 xs2) ->
  |-- x1 <--> x2 ->
  |-- fold_left prodp xs1 x1 <--> fold_left prodp xs2 x2.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply fold_left_mono.
    - revert H; apply Forall2_impl.
      intros.
      apply provables_iffp_elim1; exact H.
    - apply provables_iffp_elim1; exact H0.
  + apply fold_left_mono.
    - apply Forall2_rev.
      revert H; apply Forall2_impl.
      intros.
      eapply provables_iffp_elim2; exact H.
    - eapply provables_iffp_elim2; exact H0.
Qed.

Context {e: expr}.

Lemma fold_left_prodp_unfold {LU: LeftUnit L Gamma e prodp}: forall xs,
  |-- fold_left prodp xs e <-->
      match xs with
      | nil => e
      | x :: xs0 => fold_left prodp xs0 x
      end.
Proof.
  intros.
  destruct xs.
  + simpl.
    apply provable_iffp_refl.
  + simpl.
    apply fold_left_iffp.
    - induction xs.
      * constructor.
      * constructor; auto.
        apply provable_iffp_refl.
    - apply left_unit.
Qed.

Lemma fold_right_prodp_unfold {RU: RightUnit L Gamma e prodp}: forall xs,
  |-- fold_right prodp e xs <-->
      (fix f xs :=
         match xs with
         | nil => e
         | x :: nil => x
         | x :: xs0 => prodp x (f xs0)
         end) xs.
Proof.
  intros.
  set (f := (fix f xs :=
             match xs with
             | nil => e
             | x :: nil => x
             | x :: xs0 => prodp x (f xs0)
             end)).
  destruct xs.
  + apply provable_iffp_refl.
  + simpl fold_right.
    revert e0; induction xs; intros.
    - simpl.
      rewrite right_unit.
      apply provable_iffp_refl.
    - change (f (e0 :: a :: xs)) with (prodp e0 (f (a :: xs))).
      apply prodp_iffp.
      * apply provable_iffp_refl.
      * apply IHxs.
Qed.

End MonoTheorems.

Section AssocTheorems.

Context {iffpL: IffLanguage L}
        {iffpAX: IffAxiomatization L Gamma}
        {e: expr}
        {Mono: Monotonicity L Gamma prodp}
        {Assoc: Associativity L Gamma prodp}.

Lemma prodp_assoc: forall x y z, |-- prodp x (prodp y z) <--> prodp (prodp x y) z.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply prodp_assoc1.
  + apply prodp_assoc2.
Qed.

Context {LU: LeftUnit L Gamma e prodp}
        {RU: RightUnit L Gamma e prodp}.

Lemma assoc_fold_left_fold_right_equiv: forall xs,
  |-- fold_left prodp xs e <--> fold_right prodp e xs.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply assoc_fold_left_fold_right.
  + apply assoc_fold_right_fold_left.
Qed.

Lemma assoc_prodp_fold_left_equiv: forall xs1 xs2,
  |-- prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e) <--> fold_left prodp (xs1 ++ xs2) e.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply assoc_prodp_fold_left.
  + apply assoc_fold_left_app.
Qed.

End AssocTheorems.

Section CommAssocTheorems.

Context {iffpL: IffLanguage L}
        {iffpAX: IffAxiomatization L Gamma}
        {e: expr}
        {Mono: Monotonicity L Gamma prodp}
        {Comm: Commutativity L Gamma prodp}
        {Assoc: Associativity L Gamma prodp}.

Lemma assoc_fold_left_Permutation: forall x ys1 ys2,
  Permutation ys1 ys2 ->
  |-- fold_left prodp ys1 x <--> fold_left prodp ys2 x.
Proof.
  intros.
  pose proof @proper_permutation_fold_left _ _ _ _ prodp.
  assert (forall x y, |-- x <--> y -> forall z1 z2, z1 = z2 -> |-- prodp x z1 <--> prodp y z2)
    by (intros; subst; apply prodp_iffp; [auto | apply provable_iffp_refl]).
  specialize (H0 H1); clear H1.
  assert (forall x1 x2 y z, |-- x1 <--> x2 -> |-- prodp (prodp x1 y) z <--> prodp (prodp x2 z) y).
  {
    intros.
    rewrite <- !prodp_assoc.
    apply prodp_iffp; [auto | apply prodp_comm].
  }
  specialize (H0 H1); clear H1.
  apply H0; auto.
  apply provable_iffp_refl.
Qed.

End CommAssocTheorems.

End DerivableRulesFromPatterns2.

Section ProofTheoryPatterns.

Context {L: Language}
        {minL: MinimumLanguage L}
        {iffpL: IffLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}.

Lemma Build_LeftUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, |-- prodp e x <--> x) ->
  LeftUnit L Gamma e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x); revert H.
  + apply provables_iffp_elim1; auto.
  + apply provables_iffp_elim2; auto.
Qed.

Lemma Build_RightUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, |-- prodp x e <--> x) ->
  RightUnit L Gamma e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x); revert H.
  + apply provables_iffp_elim1; auto.
  + apply provables_iffp_elim2; auto.
Qed.

Lemma Build_Associativity': forall {prodp: expr -> expr -> expr},
  (forall x y z: expr, |-- prodp (prodp x y) z <--> prodp x (prodp y z)) ->
  Associativity L Gamma prodp.
Proof.
  intros.
  constructor; intros; specialize (H x y z); revert H.
  + apply provables_iffp_elim2; auto.
  + apply provables_iffp_elim1; auto.
Qed.

End ProofTheoryPatterns.

End P.

Section DerivableRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}.

Lemma falsep_andp: forall x: expr,
  |-- FF && x <--> FF.
Proof.
  intros.
  apply (@P.falsep_prodp _ _ _ _ _ _ impp_andp_Adjoint _ _ _ _ x).
Qed.

Lemma andp_falsep: forall x: expr,
  |-- x && FF <--> FF.
Proof.
  intros.
  apply (@P.prodp_falsep _ _ _ _ _ _ impp_andp_Adjoint _ _ _ _ andp_Comm x).
Qed.

Lemma andp_orp_distr_l: forall x y z: expr,
  |-- (x || y) && z <--> (x && z) || (y && z).
Proof.
  intros.
  pose proof @P.prodp_orp_distr_l.
  apply (@P.prodp_orp_distr_l _ _ _ _ _ _ _ _ impp_andp_Adjoint _ _ x y z).
Qed.

Lemma andp_orp_distr_r: forall x y z: expr,
  |-- x && (y || z) <--> (x && y) || (x && z).
Proof.
  intros.
  apply (@P.prodp_orp_distr_r _ _ _ _ _ _ _ _ impp_andp_Adjoint _ _ andp_Comm x y z).
Qed.

Context {iter_andp_L: IterAndLanguage L}
        {iter_andp_AXL: IterAndAxiomatization_left L Gamma}.

Lemma provable_iter_andp_sepc_right: forall (xs: list expr),
  |-- iter_andp xs <--> fold_right andp TT xs.
Proof.
  intros.
  rewrite provable_iter_andp_spec_left.
  pose proof @P.assoc_fold_left_fold_right_equiv _ _ _ _ andp _ _ TT andp_Mono andp_Assoc andp_LU andp_RU xs.
  auto.
Qed.

Lemma provable_iter_andp_unfold_right_assoc:  forall (xs: list expr),
  |-- iter_andp xs <-->
      (fix f xs :=
         match xs with
         | nil => TT
         | x :: nil => x
         | x :: xs0 => x && (f xs0)
         end) xs.
Proof.
  intros.
  rewrite provable_iter_andp_sepc_right.
  pose proof @P.fold_right_prodp_unfold _ _ _ _ andp _ _ andp_Mono TT andp_RU xs.
  auto.
Qed.

Lemma provable_iter_andp_unfold_left_assoc:  forall (xs: list expr),
  |-- iter_andp xs <-->
      match xs with
      | nil => TT
      | x :: xs0 =>
        (fix f xs x :=
           match xs with
           | nil => x
           | x0 :: xs0 => f xs0 (x && x0)
           end) xs0 x
      end.
Proof.
  intros.
  rewrite provable_iter_andp_spec_left.
  pose proof @P.fold_left_prodp_unfold _ _ _ _  andp _ _ andp_Mono TT andp_LU xs.
  apply H.
Qed.

Lemma iter_andp_multi_imp: forall (xs: list expr) (y: expr),
  |-- (iter_andp xs --> y) <--> (multi_imp xs y).
Proof.
  clear dependent orpL.
  clear dependent falsepL.
  intros.
  unfold multi_imp.
  rewrite provable_iter_andp_sepc_right.
  induction xs as [| x xs].
  + simpl.
    apply provable_truep_impp.
  + simpl.
    rewrite <- provable_andp_impp.
    apply provables_impp_proper_iffp; [apply provable_iffp_refl |].
    auto.
Qed.

End DerivableRules.

Module D1.
Export Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.D1.

Section DerivableRulesFromPatterns1.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {bD: BasicDeduction L GammaD1}
        {bE: BasicLogicEquiv L GammaE}
        {prodp: expr -> expr -> expr}.

Lemma prodp_comm {Comm: Commutativity L GammaD1 prodp}: forall x y,
  prodp x y --||-- prodp y x.
Proof.
  intros.
  apply __logic_equiv_derivable1; split; apply derivable1_prodp_comm.
Qed.

Section UnitTheorems.

Context {e: expr}.

Lemma left_unit {LU: LeftUnit L GammaD1 e prodp} : forall x, prodp e x --||-- x.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply left_unit1.
  + apply left_unit2.
Qed.

Lemma right_unit {RU: RightUnit L GammaD1 e prodp} : forall x, prodp x e --||-- x.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply right_unit1.
  + apply right_unit2.
Qed.

End UnitTheorems.

Section DistrTheorems.

Context {sump: expr -> expr -> expr}.

Lemma prodp_sump_distr_l {LDistr: LeftDistr L GammaD1 prodp sump}: forall x y z,
  prodp x (sump y z) --||-- sump (prodp x y) (prodp x z).
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply left_distr1.
  + apply left_distr2.
Qed.

Lemma prodp_sump_distr_r {RDistr: RightDistr L GammaD1 prodp sump}: forall x y z,
  prodp (sump y z) x --||-- sump (prodp y x) (prodp z x).
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply right_distr1.
  + apply right_distr2.
Qed.

End DistrTheorems.

End DerivableRulesFromPatterns1.

Section DerivableRulesFromPatterns2.

Context {L: Language}
        {orpL: OrLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {bD: BasicDeduction L GammaD1}
        {bE: BasicLogicEquiv L GammaE}
        {orpD: OrDeduction L GammaD1}
        {prodp: expr -> expr -> expr}.

Section AdjointTheorems.

Context {funcp: expr -> expr -> expr}
        {Adj: Adjointness L GammaD1 prodp funcp}.

Lemma Adjoint2RDistr: RightDistr L GammaD1 prodp orp.
Proof.
  constructor; intros.
  + apply adjoint.
    apply derivable1_orp_elim; apply adjoint.
    - apply derivable1_orp_intros1.
    - apply derivable1_orp_intros2.
  + apply derivable1_orp_elim.
    - apply prodp_mono1.
      apply derivable1_orp_intros1.
    - apply prodp_mono1.
      apply derivable1_orp_intros2.
Qed.

Lemma Adjoint2LDistr {Comm: Commutativity L GammaD1 prodp}:
  LeftDistr L GammaD1 prodp orp.
Proof.
  apply @RightDistr2LeftDistr; auto.
  + apply derivable1_orp_Mono.
  + apply Adjoint2RDistr.
Qed.

(* TODO: l/r wrong *)
Lemma prodp_orp_distr_l:
  forall x y z: expr, prodp (x || y) z --||-- (prodp x z || prodp y z).
Proof.
  intros.
  apply (@prodp_sump_distr_r _ _ _ _ _ _ Adjoint2RDistr).
Qed.

(* TODO: l/r wrong *)
Lemma prodp_orp_distr_r
      {Comm: Commutativity L GammaD1 prodp}:
  forall x y z: expr, prodp x (y || z) --||-- (prodp x y || prodp x z).
Proof.
  intros.
  apply (@prodp_sump_distr_l _ _ _ _ _ _ Adjoint2LDistr).
Qed.

Lemma orp_funcp
      {andpL: AndLanguage L}
      {andpD: AndDeduction L GammaD1}
      {Comm: Commutativity L GammaD1 prodp}:
  forall x y z: expr, funcp (x || y) z --||-- (funcp x z && funcp y z).
Proof.
  pose proof Adjoint2Mono as Mono.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply derivable1s_truep_intros.
    - apply funcp_mono.
      * apply derivable1_orp_intros1.
      * reflexivity.
    - apply funcp_mono.
      * apply derivable1_orp_intros2.
      * reflexivity.
  + apply adjoint.
    rewrite prodp_orp_distr_r.
    apply derivable1_orp_elim; apply adjoint.
    - apply derivable1_andp_elim1.
    - apply derivable1_andp_elim2.
Qed.

(* TODO: l/r wrong *)
Lemma funcp_andp_distr_r
      {andpL: AndLanguage L}
      {andpD: AndDeduction L GammaD1}:
  forall x y z: expr, funcp x (y && z)  --||-- (funcp x y && funcp x z).
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply derivable1s_truep_intros.
    - apply funcp_mono2.
      apply derivable1_andp_elim1.
    - apply funcp_mono2.
      apply derivable1_andp_elim2.
  + apply adjoint.
    apply derivable1s_truep_intros; apply adjoint.
    - apply derivable1_andp_elim1.
    - apply derivable1_andp_elim2.
Qed.

Lemma falsep_prodp
      {falsepL: FalseLanguage L}
      {falsepD: FalseDeduction L GammaD1}:
  forall x: expr, prodp falsep x --||-- falsep.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply adjoint.
    apply derivable1_falsep_elim.
  + apply derivable1_falsep_elim.
Qed.

Lemma prodp_falsep
      {falsepL: FalseLanguage L}
      {falsepD: FalseDeduction L GammaD1}
      {Comm: Commutativity L GammaD1 prodp}:
  forall x: expr, prodp x falsep --||-- falsep.
Proof.
  intros.
  rewrite prodp_comm.
  rewrite falsep_prodp.
  reflexivity.
Qed.

End AdjointTheorems.

Section MonoTheorems.

Context {Mono: Monotonicity L GammaD1 prodp}.

(* TODO: remove iffp from the name *)
Lemma prodp_iffp: forall x1 x2 y1 y2,
  x1 --||-- x2 ->
  y1 --||-- y2 ->
  prodp x1 y1 --||-- prodp x2 y2.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply prodp_mono.
    - apply __logic_equiv_derivable1 in H; tauto.
    - apply __logic_equiv_derivable1 in H0; tauto.
  + apply prodp_mono.
    - apply __logic_equiv_derivable1 in H; tauto.
    - apply __logic_equiv_derivable1 in H0; tauto.
Qed.

(* TODO: remove iffp from the name *)
Lemma fold_left_iffp: forall x1 x2 xs1 xs2,
  (Forall2 (fun x1 x2 => x1 --||-- x2) xs1 xs2) ->
  x1 --||-- x2 ->
  fold_left prodp xs1 x1 --||-- fold_left prodp xs2 x2.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply fold_left_mono.
    - revert H; apply Forall2_impl.
      intros.
      apply __logic_equiv_derivable1 in H; tauto.
    - apply __logic_equiv_derivable1 in H0; tauto.
  + apply fold_left_mono.
    - apply Forall2_rev.
      revert H; apply Forall2_impl.
      intros.
      apply __logic_equiv_derivable1 in H; tauto.
    - apply __logic_equiv_derivable1 in H0; tauto.
Qed.

Context {e: expr}.

Lemma fold_left_prodp_unfold {LU: LeftUnit L GammaD1 e prodp}: forall xs,
  fold_left prodp xs e --||--
      match xs with
      | nil => e
      | x :: xs0 => fold_left prodp xs0 x
      end.
Proof.
  intros.
  destruct xs.
  + simpl.
    reflexivity.
  + simpl.
    apply fold_left_iffp.
    - induction xs.
      * constructor.
      * constructor; auto.
        reflexivity.
    - apply left_unit.
Qed.

Lemma fold_right_prodp_unfold {RU: RightUnit L GammaD1 e prodp}: forall xs,
  fold_right prodp e xs --||--
      (fix f xs :=
         match xs with
         | nil => e
         | x :: nil => x
         | x :: xs0 => prodp x (f xs0)
         end) xs.
Proof.
  intros.
  set (f := (fix f xs :=
             match xs with
             | nil => e
             | x :: nil => x
             | x :: xs0 => prodp x (f xs0)
             end)).
  destruct xs.
  + reflexivity.
  + simpl fold_right.
    revert e0; induction xs; intros.
    - simpl.
      rewrite right_unit.
      reflexivity.
    - change (f (e0 :: a :: xs)) with (prodp e0 (f (a :: xs))).
      apply prodp_iffp.
      * reflexivity.
      * apply IHxs.
Qed.

End MonoTheorems.

Section AssocTheorems.

Context {e: expr}
        {Mono: Monotonicity L GammaD1 prodp}
        {Assoc: Associativity L GammaD1 prodp}.

Lemma prodp_assoc: forall x y z, prodp x (prodp y z) --||-- prodp (prodp x y) z.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply prodp_assoc1.
  + apply prodp_assoc2.
Qed.

Context {LU: LeftUnit L GammaD1 e prodp}
        {RU: RightUnit L GammaD1 e prodp}.

Lemma assoc_fold_left_fold_right_equiv: forall xs,
  fold_left prodp xs e --||-- fold_right prodp e xs.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply assoc_fold_left_fold_right.
  + apply assoc_fold_right_fold_left.
Qed.

Lemma assoc_prodp_fold_left_equiv: forall xs1 xs2,
  prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e) --||-- fold_left prodp (xs1 ++ xs2) e.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply assoc_prodp_fold_left.
  + apply assoc_fold_left_app.
Qed.

End AssocTheorems.

Section CommAssocTheorems.

Context {e: expr}
        {Mono: Monotonicity L GammaD1 prodp}
        {Comm: Commutativity L GammaD1 prodp}
        {Assoc: Associativity L GammaD1 prodp}.

Lemma assoc_fold_left_Permutation: forall x ys1 ys2,
  Permutation ys1 ys2 ->
  fold_left prodp ys1 x --||-- fold_left prodp ys2 x.
Proof.
  intros.
  pose proof @proper_permutation_fold_left _ _ logic_equiv _ prodp.
  assert (forall x y, x --||-- y -> forall z1 z2, z1 = z2 -> prodp x z1 --||-- prodp y z2)
    by (intros; subst; apply prodp_iffp; [auto | reflexivity]).
  unfold Morphisms.Proper, Morphisms.respectful in H0.
  specialize (H0 H1); clear H1.
  assert (forall x1 x2 y z, x1 --||-- x2 -> prodp (prodp x1 y) z --||-- prodp (prodp x2 z) y).
  {
    intros.
    rewrite <- !prodp_assoc.
    apply prodp_iffp; [auto | apply prodp_comm].
  }
  specialize (H0 H1); clear H1.
  apply H0; auto.
  reflexivity.
Qed.

End CommAssocTheorems.

End DerivableRulesFromPatterns2.

Section ProofTheoryPatterns.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {bD: BasicDeduction L GammaD1}
        {bE: BasicLogicEquiv L GammaE}.

Lemma Build_LeftUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, prodp e x --||-- x) ->
  LeftUnit L GammaD1 e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x).
  + apply __logic_equiv_derivable1 in H; tauto.
  + apply __logic_equiv_derivable1 in H; tauto.
Qed.

Lemma Build_RightUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, prodp x e --||-- x) ->
  RightUnit L GammaD1 e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x).
  + apply __logic_equiv_derivable1 in H; tauto.
  + apply __logic_equiv_derivable1 in H; tauto.
Qed.

Lemma Build_Associativity': forall {prodp: expr -> expr -> expr},
  (forall x y z: expr, prodp (prodp x y) z --||-- prodp x (prodp y z)) ->
  Associativity L GammaD1 prodp.
Proof.
  intros.
  constructor; intros; specialize (H x y z).
  + apply __logic_equiv_derivable1 in H; tauto.
  + apply __logic_equiv_derivable1 in H; tauto.
Qed.

End ProofTheoryPatterns.

End D1.
