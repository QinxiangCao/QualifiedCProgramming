Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class IterAndDefinition_left
      (L: Language)
      {andpL: AndLanguage L}
      {truepL: TrueLanguage L}
      {iter_andp_L: IterAndLanguage L}: Prop := {
  iter_andp_def_l: forall xs, 
    iter_andp xs = fold_left andp xs truep
}.

Class IterAndDefinition_right
      (L: Language)
      {andpL: AndLanguage L}
      {truepL: TrueLanguage L}
      {iter_andp_L: IterAndLanguage L}: Prop := {
  iter_andp_def_r: forall xs, 
    iter_andp xs = fold_right andp truep xs
}.

Class IterOrDefinition_left
      (L: Language)
      {orpL: OrLanguage L}
      {falsepL: FalseLanguage L}
      {iter_orp_L: IterOrLanguage L}: Prop := {
  iter_orp_def_l: forall xs, 
    iter_orp xs = fold_left orp xs falsep
}.

Class IterOrDefinition_right
      (L: Language)
      {orpL: OrLanguage L}
      {falsepL: FalseLanguage L}
      {iter_orp_L: IterOrLanguage L}: Prop := {
  iter_orp_def_r: forall xs, 
    iter_orp xs = fold_right orp falsep xs
}.

Definition FoldLeftAnd2IterAnd
           {L: Language}
           {andpL: AndLanguage L}
           {truepL: TrueLanguage L}: IterAndLanguage L :=
  Build_IterAndLanguage _ (fun xs => fold_left andp xs truep).

Definition FoldRightAnd2IterAnd
           {L: Language}
           {andpL: AndLanguage L}
           {truepL: TrueLanguage L}: IterAndLanguage L :=
  Build_IterAndLanguage _ (fun xs => fold_right andp truep xs).

Lemma FoldLeftAnd2IterAnd_Normal
      {L: Language}
      {andpL: AndLanguage L}
      {truepL: TrueLanguage L}:
  @IterAndDefinition_left L _ _ FoldLeftAnd2IterAnd.
Proof. constructor. reflexivity. Qed.

Lemma FoldRightAnd2IterAnd_Normal
      {L: Language}
      {andpL: AndLanguage L}
      {truepL: TrueLanguage L}:
  @IterAndDefinition_right L _ _ FoldRightAnd2IterAnd.
Proof. constructor. reflexivity. Qed.

Lemma IterAndFromDefToAX_L2L
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {truepL: TrueLanguage L}
      {iter_andp_L: IterAndLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {andpAX: AndAxiomatization L GammaP}
      {iffpAX: IffAxiomatization L GammaP}
      {truepAX: TrueAxiomatization L GammaP}
      {iter_andp_DL: IterAndDefinition_left L}:
  IterAndAxiomatization_left L GammaP.
Proof.
  intros.
  constructor.
  intros.
  rewrite iter_andp_def_l.
  apply provable_iffp_refl.
Qed.

Lemma IterAndFromDefToAX_R2L
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {truepL: TrueLanguage L}
      {iter_andp_L: IterAndLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {andpAX: AndAxiomatization L GammaP}
      {iffpAX: IffAxiomatization L GammaP}
      {truepAX: TrueAxiomatization L GammaP}
      {iter_andp_DR: IterAndDefinition_right L}:
  IterAndAxiomatization_left L GammaP.
Proof.
  intros.
  constructor.
  intros.
  rewrite iter_andp_def_r.
  pose proof @P.assoc_fold_left_fold_right_equiv _ _ _ _ andp _ _ TT andp_Mono andp_Assoc andp_LU andp_RU xs.
  rewrite H.
  apply provable_iffp_refl.
Qed.

Ltac AddConnective_iter_andp :=
  let iter_andp_L := fresh "iter_andp_L" in
  let iter_andp_DL := fresh "iter_andp_DL" in
  let iter_andp_AXL := fresh "iter_andp_AXL" in
  set (iter_andp_L := FoldLeftAnd2IterAnd);
  set (iter_andp_DL := FoldLeftAnd2IterAnd_Normal);
  set (iter_andp_AXL := IterAndFromDefToAX_L2L);
  clearbody iter_andp_AXL;
  clear iter_andp_DL;
  clearbody iter_andp_L.
