Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.

Section DerivedRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {GammaP: Provable L}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}.

Lemma provable_andp_sepcon_derives: forall (x y z: expr),
  |-- (x && y) * z --> (x * z) && (y * z).
Proof.
  intros.
  apply provables_impp_andp_fold.
  + apply provable_sepcon_mono.
    - apply provable_andp_elim1.
    - apply provable_impp_refl.
  + apply provable_sepcon_mono.
    - apply provable_andp_elim2.
    - apply provable_impp_refl.
Qed.

Lemma provable_sepcon_andp_derives: forall (x y z: expr),
  |-- x * (y && z) --> (x * y) && (x * z).
Proof.
  intros.
  rewrite !(provable_sepcon_comm_impp x), <- !(provable_sepcon_comm_impp _ x).
  apply provable_andp_sepcon_derives.
Qed.

Lemma provable_truep_sepcon_truep {ExtsGammaP: ExtSeparationLogic L GammaP}:
  |-- TT * TT <--> TT.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provables_impp_elim.
    apply provable_truep_intros.
  + apply provable_derives_sepcon_truep.
Qed.

Section CoqProp.

Context {coq_prop_L: CoqPropLanguage L}
        {sepcon_coq_prop_AX: SepconCoqPropAxiomatization L GammaP}.

Lemma provable_coq_prop_sepcon_andp1: forall P Q R,
 |-- Q * (R && !! P) <--> !! P && (Q * R).
Proof.
  intros.
  rewrite ! (provable_sepcon_impp_comm Q).
  rewrite (provable_andp_comm R).
  apply provable_coq_prop_andp_sepcon1; auto.
Qed.

Lemma provable_coq_prop_sepcon_andp2: forall P Q R,
  |-- Q * (!! P && R) <--> !! P && (Q * R).
Proof.
  intros.
  rewrite !(provable_sepcon_impp_comm Q).
  apply provable_coq_prop_andp_sepcon1; auto.
Qed.

Lemma provable_coq_prop_andp_sepcon2: forall P Q R,
  |-- Q && !! P * R <--> !! P && (Q * R).
Proof.
  intros.
  rewrite (provable_andp_comm Q).
  apply provable_coq_prop_andp_sepcon1; auto.
Qed.

End CoqProp.

(* TODO: move this to TheoryOfSeparationAxioms. *)
Lemma GC_Ext_Classical_collapse_aux
      {sepcon_orp_AX: SepconOrAxiomatization L GammaP}
      {cpGammaP: ClassicalAxiomatization L GammaP}
      {gcsGammaP: GarbageCollectSeparationLogic L GammaP}
      {ExtsGammaP: ExtSeparationLogic L GammaP}:
  forall (x: expr), |-- x --> x * x.
Proof.
  intros.
  rewrite (provable_derives_sepcon_truep x) at 1.
  assert (|-- TT --> x || ~~ x) by (apply provables_impp_elim, provable_excluded_middle).
  rewrite H; clear H.
  rewrite provable_sepcon_orp.
  apply provables_orp_impp_fold; [apply provable_impp_refl |].
  rewrite <- (provable_andp_dup (x * ~~ x)).
  rewrite provable_sepcon_elim1 at 1.
  rewrite provable_sepcon_elim2 at 1.
  AddSequentCalculus.
  rewrite __provable_derivable.
  rewrite <- derivables_impp_theorem.
  apply derivables_falsep_elim.
  apply derivables_modus_ponens with x.
  + apply derivables_andp_elim1 with (~~x).
    solve_assum.
  + apply derivables_andp_elim2 with x.
    rewrite <- (provable_negp x).
    solve_assum.
Qed.

(* TODO: move this to TheoryOfSeparationAxioms. *)
Theorem GC_Ext_Classical_collapse
        {sepcon_orp_AX: SepconOrAxiomatization L GammaP}
        {cpAX: ClassicalAxiomatization L GammaP}
        {gcsAX: GarbageCollectSeparationLogic L GammaP}
        {ExtsAX: ExtSeparationLogic L GammaP}:
  forall (x y: expr), |-- x * y <--> x && y.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provables_impp_andp_fold.
    - apply provable_sepcon_elim1.
    - apply provable_sepcon_elim2.
  + rewrite (GC_Ext_Classical_collapse_aux (x && y)).
    apply provable_sepcon_mono.
    - apply provable_andp_elim1.
    - apply provable_andp_elim2.
Qed.

Context {empL: EmpLanguage L}
        {empAX: EmpAxiomatization L GammaP}.

Lemma derivable_emp {gcsGammaP: GarbageCollectSeparationLogic L GammaP}:
  forall (x y: expr), |-- emp.
Proof.
  intros.
  rewrite <- (provable_sepcon_elim2 TT emp).
  rewrite provable_sepcon_emp.
  apply provable_truep_intros.
Qed.

End DerivedRules.
