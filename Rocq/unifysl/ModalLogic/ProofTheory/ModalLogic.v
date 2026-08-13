Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Class SystemK (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) := {
  axiom_K: forall x y, |-- boxp (x --> y) --> (boxp x --> boxp y); (* a.k.a. Distribution Axiom *)
  rule_N: forall x, |-- x -> |-- boxp x (* a.k.a. Necessitation Rule *)
}.

Class SystemT (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) := {
  axiom_T: forall x, |-- boxp x --> x
}.

Class System4 (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} (Gamma: Provable L):= {
  axiom_4: forall x, |-- boxp x --> boxp (boxp x)
}.

Class SystemD (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) := {
  axiom_D: forall x, |-- boxp x --> diamondp x
}.

Class SystemB (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) := {
  axiom_B: forall x, |-- x --> boxp (diamondp x)
}.

Class System5 (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) := {
  axiom_5: forall x, |-- diamondp x --> boxp (diamondp x)
}.

Class PropositionalTransparentModality (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {iffpL: IffLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) := {
  boxp_orp: forall x y, |-- boxp (x || y) <--> boxp x || boxp y
}.

Class StrongPropositionalTransparentModality (L: Language) {minL: MinimumLanguage L} {iffpL: IffLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) := {
  boxp_impp: forall x y, |-- boxp (x --> y) <--> (boxp x --> boxp y)
}.

(* 
(* TODO: Add Sequnt Calculus for it. *)
Lemma MakeSequentCalculus_DeMorganPropositionalLogic {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} (minAX': MinimumAxiomatization L (Build_AxiomaticProvable (@provable L Gamma))) (ipGamma: IntuitionisticPropositionalLogic L Gamma) {ipGamma': IntuitionisticPropositionalLogic L (Build_AxiomaticProvable (@provable L Gamma))} {dmpGamma: DeMorganPropositionalLogic L Gamma}:
  Typeclass_Rewrite (exist (fun X: Prop => X) (IntuitionisticPropositionalLogic L (Build_AxiomaticProvable (@provable L Gamma))) ipGamma' :: nil) ->
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (dmpGamma: DeMorganPropositionalLogic L (Build_AxiomaticProvable (@provable L Gamma))),
     OpaqueProp (Typeclass_Rewrite l -> G)) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (DeMorganPropositionalLogic L Gamma) dmpGamma) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros _.
  intros.
  split; intros.
  + clear H0.
    apply H; auto.
    - destruct dmpGamma; constructor; auto.
    - apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

Hint Rewrite <- @MakeSequentCalculus_DeMorganPropositionalLogic using (instantiate (1 := _); apply Typeclass_Rewrite_I): AddSC.


Section ModalLogic.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: Provable L}
        {AX: NormalAxiomatization L Gamma}
        {minAX: MinimumAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {KmGamma: SystemK L Gamma}.

Lemma derivable_axiom_K: forall Phi x y,
  Phi |-- boxp (x --> y) --> (boxp x --> boxp y).
Proof.
  intros.
  apply derivables_weaken0.
  apply axiom_K.
Qed.

Lemma deduction_axiom_K: forall Phi x y,
  Phi |-- boxp (x --> y) ->
  Phi |-- boxp x --> boxp y.
Proof.
  intros.
  eapply derivables_modus_ponens; eauto.
  apply derivable_axiom_K.
Qed.

Lemma derivable_axiom_T {TmGamma: SystemT L Gamma}: forall Phi x ,
  Phi |-- boxp x --> x.
Proof.
  intros.
  apply derivables_weaken0.
  apply axiom_T.
Qed.

Lemma deduction_axiom_T {TmGamma: SystemT L Gamma}: forall Phi x ,
  Phi |-- boxp x ->
  Phi |-- x.
Proof.
  intros.
  eapply derivables_modus_ponens; eauto.
  apply derivable_axiom_T.
Qed.

End ModalLogic.

*)
