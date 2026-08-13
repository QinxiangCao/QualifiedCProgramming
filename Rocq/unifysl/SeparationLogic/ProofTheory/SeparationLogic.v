Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.

Class SepconAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  provable_sepcon_comm_impp: forall x y, |-- x * y --> y * x;
  provable_sepcon_assoc1: forall x y z, |-- x * (y * z) --> (x * y) * z;
  provable_sepcon_mono: forall x1 x2 y1 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- (x1 * y1) --> (x2 * y2);
}.

Class SepconOrAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  provable_orp_sepcon_derives: forall (x y z: expr),
    |-- (x || y) * z --> x * z || y * z
}.

Class SepconCoqPropAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  provable_coq_prop_andp_sepcon1: forall P Q R,
    |-- (!! P && Q) * R <--> !! P && (Q * R)
}.

Class SepconFalseAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {falsepL: FalseLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  provable_falsep_sepcon_derives: forall (x: expr),
    |-- FF * x --> FF
}.

Class EmpAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
    provable_sepcon_emp_derives: forall x, |-- x * emp --> x;
    provable_derives_sepcon_emp: forall x, |-- x --> x * emp
}.

Class WandAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        (Gamma: Provable L) := {
  provables_wand_sepcon_adjoint: forall x y z, |-- x * y --> z <-> |-- x --> (y -* z)
}.

Class ExtSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {trueL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  provable_derives_sepcon_truep: forall x, |-- x --> x * TT
}.

Class NonsplitEmpSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
  provable_sepcon_truep_andp_emp_derives: forall x, |-- (x * TT) && emp --> x
}.

Class DupEmpSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
  provable_emp_dup: forall x, |-- x && emp --> x * x
}.

(* Only for documentation *)
Class MallocFreeSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
  MallocFreeSeparationLogic_NonsplitEmpSeparationLogic ::
    NonsplitEmpSeparationLogic L Gamma;
  MallocFreeSeparationLogic_DupEmpSeparationLogic ::
    DupEmpSeparationLogic L Gamma
}.

Class GarbageCollectSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  provable_sepcon_elim1: forall x y, |-- x * y --> x
}.

Class SepconDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_sepcon_comm: forall x y, x * y |-- y * x;
  derivable1_sepcon_assoc1: forall x y z, x * (y * z) |-- (x * y) * z;
  derivable1_sepcon_mono: forall x1 x2 y1 y2, x1 |-- x2 -> y1 |-- y2 
               -> (x1 * y1) |-- (x2 * y2);
}.

Class SepconOrDeduction
        (L: Language)
        {orpL: OrLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_orp_sepcon_l: forall x y z,
     (x || y) * z |-- x * z || y * z
}.

Class SepconFalseDeduction
        (L: Language)
        {falsepL: FalseLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_falsep_sepcon_l: forall x,
     FF * x |-- FF
}.

Class EmpDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
    derivable1_sepcon_emp_l: forall x,  x * emp |-- x;
    derivable1_sepcon_emp_r: forall x, x |-- x * emp
}.

Class WandDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1s_wand_sepcon_adjoint: forall x y z, x * y  |-- z <-> x |-- (y -* z)
}.

Class ExtSeparationLogicDeduction
        (L: Language)
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_sepcon_truep_r: forall x, x |-- x * TT
}.

Class NonsplitEmpSeparationLogicDeduction
        (L: Language)
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_sepcon_truep_andp_emp_l: forall x, (x * TT) && emp |-- x
}.

Class DupEmpSeparationLogicDeduction
        (L: Language)
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_emp_dup: forall x, x && emp |-- x * x
}.

Class GarbageCollectSeparationLogicDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_sepcon_elim1: forall x y, x * y |-- x
}.

Section SepconRules.

Context {L: Language}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}.

Lemma derivable1_sepcon_Comm: D1.Commutativity L GammaD1 sepcon.
Proof.
  constructor.
  intros.
  apply derivable1_sepcon_comm.
Qed.

Lemma derivable1_sepcon_Mono: D1.Monotonicity L GammaD1 sepcon.
Proof.
  constructor.
  intros.
  apply derivable1_sepcon_mono; auto.
Qed.

Lemma derivable1_sepcon_Assoc: D1.Associativity L GammaD1 sepcon.
Proof.
  apply @D1.Build_Associativity1; auto.
  + apply derivable1_sepcon_Comm.
  + apply derivable1_sepcon_Mono.
  + intros.
    apply derivable1_sepcon_assoc1.
Qed.

Lemma derivable1_sepcon_assoc2: forall x y z, (x * y) * z |-- x * (y * z).
Proof.
  intros.
  apply (@D1.prodp_assoc2 _ _ _ derivable1_sepcon_Assoc).
Qed.

Lemma derivable1_sepcon_orp_l
  {orpL: OrLanguage L}
  {orpD: OrDeduction L GammaD1}
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sepcon_orp_D: SepconOrDeduction L GammaD1}:
  forall (x y z: expr), z * (x || y)  |-- (z * x) || (z * y).
Proof.
  intros.
  pose proof derivable1_orp_sepcon_l x y z. pose proof (derivable1_sepcon_comm z (x||y)). pose proof derivable1_trans _ _ _ H0 H. apply (derivable1_trans _ _ _ H1). apply derivable1_orp_mono; apply derivable1_sepcon_comm.
Qed.

Lemma derivable1_sepcon_orp_r
  {orpL: OrLanguage L}
  {orpD: OrDeduction L GammaD1}
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sepcon_orp_D: SepconOrDeduction L GammaD1}:
  forall (x y z: expr), z * x || z * y |-- z * (x || y) .
Proof.
  intros.
  apply derivable1_orp_elim; apply derivable1_sepcon_mono.
  - reflexivity.
  - apply derivable1_orp_intros1.
  - reflexivity.
  - apply derivable1_orp_intros2.
Qed.

Lemma derivable1_orp_sepcon_r
  {orpL: OrLanguage L}
  {orpD: OrDeduction L GammaD1}
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sepcon_orp_D: SepconOrDeduction L GammaD1}:
  forall (x y z: expr), (x * z) || (y * z) |--  (x || y) * z.
Proof.
  intros.
  apply derivable1_orp_elim; apply derivable1_sepcon_mono.
  - apply derivable1_orp_intros1.
  - reflexivity.
  - apply derivable1_orp_intros2.
  - reflexivity.
Qed.

Lemma logic_equiv_sepcon_orp
  {orpL: OrLanguage L}
  {orpD: OrDeduction L GammaD1}
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sepcon_orp_D: SepconOrDeduction L GammaD1}:
forall (x y z: expr), z * ( x || y ) --||-- (z * x) || (z * y) .
Proof.
  intros. apply __logic_equiv_derivable1.
  split . apply derivable1_sepcon_orp_l. apply derivable1_sepcon_orp_r.
Qed.

Lemma logic_equiv_orp_sepcon
  {orpL: OrLanguage L}
  {orpD: OrDeduction L GammaD1}
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sepcon_orp_D: SepconOrDeduction L GammaD1}:
forall (x y z: expr), ( x || y ) * z --||-- (x * z) || (y * z) .
Proof.
  intros. apply __logic_equiv_derivable1.
  split . apply derivable1_orp_sepcon_l. apply derivable1_orp_sepcon_r.
Qed.

Lemma derivable1_falsep_sepcon_r
      {falsepL: FalseLanguage L}
      {falsepD: FalseDeduction L GammaD1}:
  forall (x: expr), FF |-- FF * x.
Proof.
  intros.
  apply derivable1_falsep_elim.
Qed.

Section emp.

Context {empL: EmpLanguage L}
        {empD: EmpDeduction L GammaD1}.

Lemma derivable1_sepcon_LU: D1.LeftUnit L GammaD1 emp sepcon.
Proof.
  constructor; intros.
  + rewrite derivable1_sepcon_comm.
    apply derivable1_sepcon_emp_l.
  + rewrite <- derivable1_sepcon_comm.
    apply derivable1_sepcon_emp_r.
Qed.

Lemma derivable1_sepcon_RU: D1.RightUnit L GammaD1 emp sepcon.
Proof.
  constructor; intros.
  intros.
  + apply derivable1_sepcon_emp_l.
  + apply derivable1_sepcon_emp_r.
Qed.

End emp.

Context {GammaE: LogicEquiv L}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}
        {bE: BasicLogicEquiv L GammaE}.

Lemma __logic_equiv_sepcon_comm:
  forall (x y: expr), x * y --||-- y * x.
Proof.
  intros.
  apply (@D1.prodp_comm _ _ _ _ _ derivable1_sepcon_Comm).
Qed.

Lemma __logic_equiv_sepcon_assoc:
  forall x y z, x * (y * z) --||-- (x * y) * z.
Proof.
  intros.
  apply (@D1.prodp_assoc _ _ _ _ _ derivable1_sepcon_Assoc).
Qed.

Section emp.

Context {empL: EmpLanguage L}
        {empD: EmpDeduction L GammaD1}.

Lemma provable_sepcon_emp_logic_equiv: forall x, x * emp --||-- x.
Proof. apply (@D1.right_unit _ _ _ _ _ _ derivable1_sepcon_RU). Qed.

Lemma emp_sepcon_logic_equiv: forall x, emp * x --||-- x.
Proof. apply (@D1.left_unit _ _ _ _ _ _ derivable1_sepcon_LU). Qed.

End emp.

Context {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {orpD: OrDeduction L GammaD1}
        {falsepD: FalseDeduction L GammaD1}
        {sepcon_orp_D: SepconOrDeduction L GammaD1}
        {sepcon_falsep_D: SepconFalseDeduction L GammaD1}.

Lemma derivable1_sepcon_orp_RDistr: D1.RightDistr L GammaD1 sepcon orp.
Proof.
  constructor; intros.
  + apply derivable1_orp_sepcon_l.
  + apply derivable1_orp_sepcon_r.
Qed.

Lemma derivable1_sepcon_orp_LDistr: D1.LeftDistr L GammaD1 sepcon orp.
Proof.
  apply @D1.RightDistr2LeftDistr; auto.
  + apply derivable1_sepcon_Comm.
  + apply derivable1_orp_Mono.
  + apply derivable1_sepcon_orp_RDistr.
Qed.

Lemma logic_equiv_orp_sepcon_distr: forall (x y z: expr),
  (x || y) * z --||-- x * z || y * z.
Proof.
  intros.
  apply (@D1.prodp_sump_distr_r _ _ _ _ _ _ derivable1_sepcon_orp_RDistr).
Qed.

Lemma logic_equiv_sepcon_orp_distr: forall (x y z: expr),
  x * (y || z) --||-- x * y || x * z.
Proof.
  intros.
  apply (@D1.prodp_sump_distr_l _ _ _ _ _ _ derivable1_sepcon_orp_LDistr).
Qed.

Lemma logic_equiv_falsep_sepcon: forall (x: expr),
  FF * x --||-- FF.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply derivable1_falsep_sepcon_l.
  + apply derivable1_falsep_sepcon_r.
Qed.

Lemma logic_equiv_sepcon_falsep: forall (x: expr),
  x * FF --||-- FF.
Proof.
  intros.
  rewrite __logic_equiv_sepcon_comm.
  apply logic_equiv_falsep_sepcon.
Qed.

End SepconRules.

(*
(** Proof rules for cancel. **)

Lemma provables_emp_sepcon_unfold: forall x y, |-- x * emp --> y -> |-- x --> y.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- provable_derives_sepcon_emp in H.
  auto.
Qed.

Lemma provables_sepcon_impp_unfold: forall u x y z,
  |-- x * y --> z -> |-- (u * x) * y --> u * z.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite provable_sepcon_assoc2.
  apply provable_sepcon_mono; auto.
  apply provable_impp_refl.
Qed.

Lemma provables_sepcon_sepcon_unfold: forall x y z w v,
  |-- x * (y * z) --> w * v-> |-- (y * x) * z --> w * v.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- H.
  pose proof provable_sepcon_comm_impp y x.
  pose proof provable_sepcon_mono _ _ _ _ H0 (provable_impp_refl z).
  rewrite H1.
  apply provable_sepcon_assoc2.
Qed.

Lemma provables_sepcon_assoc: forall x y z w,  |-- (y * x) * z --> w -> |-- x * (y * z) --> w.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- H.
  pose proof provable_sepcon_comm_impp x y.
  pose proof provable_sepcon_mono _ _ _ _ H0 (provable_impp_refl z).
  rewrite <- H1.
  apply provable_sepcon_assoc1.
Qed.

Lemma provable_sepcon_emp_derives: forall x, |-- x * emp --> x.
Proof.
  apply provable_sepcon_emp_derives.
Qed.

End SepconRules.
*)
Section WandRules.

Context {L: Language}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}.

Lemma derivable1_wand_sepcon_Adj: D1.Adjointness L GammaD1 sepcon wand.
Proof.
  constructor.
  intros.
  apply derivable1s_wand_sepcon_adjoint.
Qed.

Lemma derivable1_wand_elim1: forall (x y: expr),
  (x -* y) * x |-- y.
Proof.
  intros.
  apply (@D1.adjoint_modus_ponens _ _ _ _ _ derivable1_wand_sepcon_Adj).
Qed.

Context {sepconD: SepconDeduction L GammaD1}.

Lemma derivable1_wand_elim2: forall (x y: expr),
  x * (x -* y) |-- y.
Proof.
  intros.
  rewrite (derivable1_sepcon_comm x (x -* y)).
  apply derivable1_wand_elim1.
Qed.

Lemma derivable1_wand_mono: forall x1 x2 y1 y2,
  x2 |-- x1 -> y1 |-- y2 -> x1 -* y1 |-- x2 -* y2.
Proof.
  intros.
  apply (@D1.funcp_mono _ _ _ _ _ derivable1_wand_sepcon_Adj derivable1_sepcon_Mono); auto.
Qed.

Context {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {GammaE: LogicEquiv L}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}
        {bE: BasicLogicEquiv L GammaE}
        {andpD: AndDeduction L GammaD1}
        {orpD: OrDeduction L GammaD1}
        {sepcon_orp_D: SepconOrDeduction L GammaD1}.

Lemma logic_equiv_wand : forall x y x' y',
        x --||-- x' ->
        y --||-- y' ->
        x -* y --||-- x' -* y'.
Proof.
  intros. rewrite __logic_equiv_derivable1 in *. split.
  -destruct H. destruct H0. eapply derivable1_wand_mono; eauto.
  -destruct H. destruct H0. eapply derivable1_wand_mono; eauto.
Qed. 

Lemma logic_equiv_provable_wand_andp: forall x y z: expr,
  x -* y && z --||-- (x -* y) && (x -* z).
Proof.
  intros.
  apply (@D1.funcp_andp_distr_r _ _ _ _ _ _ _ derivable1_wand_sepcon_Adj); auto.
Qed.

Lemma logic_equiv_provable_wand_orp: forall x y z: expr,
  (x || y) -* z --||-- (x -* z) && (y -* z).
Proof.
  intros.
  apply (@D1.orp_funcp _ _ _ _ _ _ _ _ _ _ derivable1_wand_sepcon_Adj _ _ derivable1_sepcon_Comm); auto.
Qed.

Lemma derivable1_sepcon_elim2: forall {gcsD: GarbageCollectSeparationLogicDeduction L GammaD1} (x y: expr),
  x * y |-- y.
Proof.
  intros.
  rewrite (derivable1_sepcon_comm x y).
  apply derivable1_sepcon_elim1.
Qed.

Lemma derivable1_provable_sepcon_andp_emp_derives
      {truepL: TrueLanguage L}
      {empL: EmpLanguage L}
      {truepD: TrueDeduction L GammaD1}
      {empD: EmpDeduction L GammaD1}
      {nssD: NonsplitEmpSeparationLogicDeduction L GammaD1}:
  forall x y, x * y && emp |-- x.
Proof.
  intros.
  rewrite <- (derivable1_sepcon_truep_andp_emp_l x) at 2.
  apply derivable1s_andp_proper; [| reflexivity].
  apply derivable1_sepcon_mono; [reflexivity |].
  apply derivable1_truep_intros.
Qed.

Lemma derivable1_provable_emp_sepcon_elim2
      {truepL: TrueLanguage L}
      {empL: EmpLanguage L}
      {truepD: TrueDeduction L GammaD1}
      {empD: EmpDeduction L GammaD1}
      {nssD: NonsplitEmpSeparationLogicDeduction L GammaD1}:
  forall x y, x * y && emp |-- y.
Proof.
  intros.
  rewrite derivable1_sepcon_comm.
  apply derivable1_provable_sepcon_andp_emp_derives.
Qed.

Lemma derivable1s_emp_l_unfold
  {empL: EmpLanguage L}
  {empD: EmpDeduction L GammaD1}:
  forall x y, emp |-- y -> x |-- x * y.
Proof.
  intros. pose proof emp_sepcon_logic_equiv x. rewrite __logic_equiv_derivable1 in H0. destruct H0. pose proof derivable1_trans x (emp*x) (x*y) H1. apply H2. rewrite derivable1_sepcon_comm. apply derivable1_sepcon_mono. apply derivable1_refl. apply H.
Qed.

Lemma derivable1s_emp_sepcon_unfold
  {empL: EmpLanguage L}
  {empD: EmpDeduction L GammaD1}:
  forall x y z, x |-- z -> emp |-- y -> x |-- z * y.
Proof.
  intros. pose proof emp_sepcon_logic_equiv x. rewrite __logic_equiv_derivable1 in H1. destruct H1. pose proof derivable1_trans x (emp*x) (z*y) H2. apply H3. rewrite derivable1_sepcon_comm. apply derivable1_sepcon_mono. apply H. apply H0.
Qed.

End WandRules.

Section Axiomatization2Deduction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}
        {minAX: MinimumAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}.

Lemma Axiomatization2Deduction_sepconD: SepconDeduction L GammaD1.
Proof.
  constructor; intros.
  + apply __derivable1_provable.
    apply provable_sepcon_comm_impp.
  + apply __derivable1_provable.
    apply provable_sepcon_assoc1.
  + rewrite __derivable1_provable in H, H0 |- *.
    apply provable_sepcon_mono; auto.
Qed.

Lemma Axiomatization2Deduction_wandD
      {wandL: WandLanguage L}
      {wandAX: WandAxiomatization L GammaP}:
  WandDeduction L GammaD1.
Proof.
  constructor; intros.
  rewrite !__derivable1_provable.
  apply provables_wand_sepcon_adjoint.
Qed.

Lemma Axiomatization2Deduction_empD
      {empL: EmpLanguage L}
      {empAX: EmpAxiomatization L GammaP}:
  EmpDeduction L GammaD1.
Proof.
  constructor; intros.
  + rewrite __derivable1_provable.
    apply provable_sepcon_emp_derives.
  + rewrite __derivable1_provable.
    apply provable_derives_sepcon_emp.
Qed.

End Axiomatization2Deduction.

Section SepconRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}.

Lemma sepcon_Comm: P.Commutativity L Gamma sepcon.
Proof.
  constructor.
  intros.
  apply provable_sepcon_comm_impp.
Qed.

Lemma sepcon_Mono: P.Monotonicity L Gamma sepcon.
Proof.
  constructor.
  intros.
  apply provable_sepcon_mono; auto.
Qed.

Lemma sepcon_Assoc: P.Associativity L Gamma sepcon.
Proof.
  apply @P.Build_Associativity1; auto.
  + apply sepcon_Comm.
  + apply sepcon_Mono.
  + intros.
    apply provable_sepcon_assoc1.
Qed.

Lemma provable_sepcon_assoc2: forall x y z, |-- (x * y) * z --> x * (y * z).
Proof.
  intros.
  apply (@P.prodp_assoc2 _ _ _ _ sepcon_Assoc).
Qed.

Context {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}.

Lemma provable_sepcon_impp_comm:
  forall (x y: expr), |-- x * y <--> y * x.
Proof.
  intros.
  apply (@P.prodp_comm _ _ _ _ _ _ _ sepcon_Comm).
Qed.

Lemma provable_sepcon_assoc:
  forall x y z, |-- x * (y * z) <--> (x * y) * z.
Proof.
  intros.
  apply (@P.prodp_assoc _ _ _ _ _ _ _ sepcon_Assoc).
Qed.

Lemma provable_derives_orp_sepcon:
  forall (x y z: expr), |-- x * z || y * z --> (x || y) * z.
Proof.
  intros.
  apply provables_orp_impp_fold; apply provable_sepcon_mono.
  - apply provable_orp_intros1.
  - apply provable_impp_refl.
  - apply provable_orp_intros2.
  - apply provable_impp_refl.
Qed.

Lemma provable_derives_falsep_sepcon:
  forall (x: expr),|-- FF --> FF * x.
Proof.
  intros.
  apply provable_falsep_elim.
Qed.

Context {sepcon_orp_AX: SepconOrAxiomatization L Gamma}
        {sepcon_false_AX: SepconFalseAxiomatization L Gamma}.

Lemma sepcon_orp_RDistr: P.RightDistr L Gamma sepcon orp.
Proof.
  constructor; intros.
  + apply provable_orp_sepcon_derives.
  + apply provable_derives_orp_sepcon.
Qed.

Lemma sepcon_orp_LDistr: P.LeftDistr L Gamma sepcon orp.
Proof.
  apply @P.RightDistr2LeftDistr; auto.
  + apply sepcon_Comm.
  + apply orp_Mono.
  + apply sepcon_orp_RDistr.
Qed.

Lemma provable_orp_sepcon: forall (x y z: expr),
  |-- (x || y) * z <--> x * z || y * z.
Proof.
  intros.
  apply (@P.prodp_sump_distr_r _ _ _ _ _ _ _ _ sepcon_orp_RDistr).
Qed.

Lemma provable_sepcon_orp: forall (x y z: expr),
  |-- x * (y || z) <--> x * y || x * z.
Proof.
  intros.
  apply (@P.prodp_sump_distr_l _ _ _ _ _ _ _ _ sepcon_orp_LDistr).
Qed.

Lemma provable_falsep_sepcon: forall (x: expr),
  |-- FF * x <--> FF.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provable_falsep_sepcon_derives.
  + apply provable_derives_falsep_sepcon.
Qed.

Lemma provable_sepcon_falsep: forall (x: expr),
  |-- x * FF <--> FF.
Proof.
  intros.
  rewrite provable_sepcon_impp_comm.
  apply provable_falsep_sepcon.
Qed.

Context {empL: EmpLanguage L}
        {empAX: EmpAxiomatization L Gamma}.

Lemma provable_sepcon_emp: forall x, |-- x * emp <--> x.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provable_sepcon_emp_derives.
  + apply provable_derives_sepcon_emp.
Qed.

Lemma sepcon_LU: P.LeftUnit L Gamma emp sepcon.
Proof.
  apply P.Build_LeftUnit; intros.
  + rewrite provable_sepcon_comm_impp.
    apply provable_sepcon_emp_derives.
  + rewrite <- provable_sepcon_comm_impp.
    apply provable_derives_sepcon_emp.
Qed.

Lemma sepcon_RU: P.RightUnit L Gamma emp sepcon.
Proof.
  apply P.Build_RightUnit.
  intros.
  + apply provable_sepcon_emp_derives.
  + apply provable_derives_sepcon_emp.
Qed.

(** Proof rules for cancel. **)

Lemma provables_emp_sepcon_unfold: forall x y, |-- x * emp --> y -> |-- x --> y.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- provable_derives_sepcon_emp in H.
  auto.
Qed.

Lemma provables_sepcon_impp_unfold: forall u x y z,
  |-- x * y --> z -> |-- (u * x) * y --> u * z.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite provable_sepcon_assoc2.
  apply provable_sepcon_mono; auto.
  apply provable_impp_refl.
Qed.

Lemma provables_sepcon_sepcon_unfold: forall x y z w v,
  |-- x * (y * z) --> w * v-> |-- (y * x) * z --> w * v.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- H.
  pose proof provable_sepcon_comm_impp y x.
  pose proof provable_sepcon_mono _ _ _ _ H0 (provable_impp_refl z).
  rewrite H1.
  apply provable_sepcon_assoc2.
Qed.

Lemma provables_sepcon_assoc: forall x y z w,  |-- (y * x) * z --> w -> |-- x * (y * z) --> w.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- H.
  pose proof provable_sepcon_comm_impp x y.
  pose proof provable_sepcon_mono _ _ _ _ H0 (provable_impp_refl z).
  rewrite <- H1.
  apply provable_sepcon_assoc1.
Qed.



End SepconRules.

Section WandRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}.

Lemma wand_sepcon_Adj: P.Adjointness L Gamma sepcon wand.
Proof.
  constructor.
  intros.
  apply provables_wand_sepcon_adjoint.
Qed.

Lemma provable_wand_elim1: forall (x y: expr),
  |-- (x -* y) * x --> y.
Proof.
  intros.
  apply (@P.adjoint_modus_ponens _ _ _ _ _ _ wand_sepcon_Adj).
Qed.

Context {sepconAX: SepconAxiomatization L Gamma}.

Lemma provable_wand_elim2: forall (x y: expr),
  |-- x * (x -* y) --> y.
Proof.
  intros.
  rewrite (provable_sepcon_comm_impp x (x -* y)).
  apply provable_wand_elim1.
Qed.

Lemma provables_wand_mono: forall x1 x2 y1 y2,
  |-- x2 --> x1 -> |-- y1 --> y2 -> |-- (x1 -* y1) --> (x2 -* y2).
Proof.
  intros.
  apply (@P.funcp_mono _ _ _ _ _ _ wand_sepcon_Adj sepcon_Mono); auto.
Qed.

Context {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {sepcon_orp_AX: SepconOrAxiomatization L Gamma}
        {sepcon_false_AX: SepconFalseAxiomatization L Gamma}.

Lemma provable_wand_andp: forall x y z: expr,
  |-- x -* y && z <--> (x -* y) && (x -* z).
Proof.
  intros.
  apply (@P.funcp_andp_distr_r _ _ _ _ _ _ wand_sepcon_Adj); auto.
Qed.

Lemma provable_wand_orp: forall x y z: expr,
  |-- (x || y) -* z <--> (x -* z) && (y -* z).
Proof.
  intros.
  apply (@P.orp_funcp _ _ _ _ _ _ _ _ wand_sepcon_Adj _ _ _ _ sepcon_Comm); auto.
Qed.

Lemma provable_sepcon_elim2: forall {gcsGamma: GarbageCollectSeparationLogic L Gamma} (x y: expr),
  |-- x * y --> y.
Proof.
  intros.
  rewrite (provable_sepcon_comm_impp x y).
  apply provable_sepcon_elim1.
Qed.

Lemma provable_sepcon_andp_emp_derives: forall {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y,
  |-- x * y && emp --> x.
Proof.
  intros.
  rewrite <- (provable_sepcon_truep_andp_emp_derives x) at 2.
  apply provables_andp_proper_impp; [| apply provable_impp_refl].
  apply provable_sepcon_mono; [apply provable_impp_refl |].
  apply provables_impp_elim, provable_truep.
Qed.

Lemma provable_emp_sepcon_elim2: forall {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y,
  |-- x * y && emp --> y.
Proof.
  intros.
  rewrite provable_sepcon_impp_comm.
  apply provable_sepcon_andp_emp_derives.
Qed.

End WandRules.
