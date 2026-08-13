Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Module IntuitionisticPropositionalLogic.

Section IntuitionisticPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

(* TODO: why this "existing instance" is in fact no longer needed. *)
Existing Instances PropositionalLanguage.L
                   PropositionalLanguage.minL
                   PropositionalLanguage.andpL
                   PropositionalLanguage.orpL
                   PropositionalLanguage.falsepL.

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| provable_andp_intros: forall x y, provable (x --> y --> x && y)
| provable_andp_elim1: forall x y, provable (x && y --> x)
| provable_andp_elim2: forall x y, provable (x && y --> y)
| provable_orp_intros1: forall x y, provable (x --> x || y)
| provable_orp_intros2: forall x y, provable (y --> x || y)
| provable_orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| provable_falsep_elim: forall x, provable (FF --> x).

#[export] Instance GP: Provable PropositionalLanguage.L := Build_Provable _ provable.

#[export] Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.

#[export] Instance GammaDP: DerivableFromProvable PropositionalLanguage.L GP GD :=
  Provable2Derivable_Normal.

#[export] Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provables_modus_ponens.
  + apply provable_axiom1.
  + apply provable_axiom2.
Qed.

#[export] Instance andpAX: AndAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_andp_intros.
  + apply provable_andp_elim1.
  + apply provable_andp_elim2.
Qed.

#[export] Instance orpAX: OrAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_orp_intros1.
  + apply provable_orp_intros2.
  + apply provable_orp_elim.
Qed.

#[export] Instance falsepAX: FalseAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  apply provable_falsep_elim.
Qed.

End IntuitionisticPropositionalLogic.

End IntuitionisticPropositionalLogic.

Module DeMorganPropositionalLogic.

Section DeMorganPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L
                   PropositionalLanguage.minL
                   PropositionalLanguage.andpL
                   PropositionalLanguage.orpL
                   PropositionalLanguage.falsepL
                   PropositionalLanguage.negpL
                   PropositionalLanguage.negpDef.

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| provable_andp_intros: forall x y, provable (x --> y --> x && y)
| provable_andp_elim1: forall x y, provable (x && y --> x)
| provable_andp_elim2: forall x y, provable (x && y --> y)
| provable_orp_intros1: forall x y, provable (x --> x || y)
| provable_orp_intros2: forall x y, provable (y --> x || y)
| provable_orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| provable_falsep_elim: forall x, provable (FF --> x)
| provable_weak_excluded_middle: forall x, provable (~~ x || ~~ ~~ x).

#[export] Instance GP: Provable  PropositionalLanguage.L :=
  Build_Provable _ provable.

#[export] Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.

#[export] Instance GammaDP: DerivableFromProvable PropositionalLanguage.L GP GD :=
  Provable2Derivable_Normal.

#[export] Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provables_modus_ponens.
  + apply provable_axiom1.
  + apply provable_axiom2.
Qed.

#[export] Instance andpAX: AndAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_andp_intros.
  + apply provable_andp_elim1.
  + apply provable_andp_elim2.
Qed.

#[export] Instance orpAX: OrAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_orp_intros1.
  + apply provable_orp_intros2.
  + apply provable_orp_elim.
Qed.

#[export] Instance falsepAX: FalseAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  apply provable_falsep_elim.
Qed.

#[export] Instance inegpAX: IntuitionisticNegAxiomatization PropositionalLanguage.L GP :=
  NegFromDefToAX_False_Imp.

#[export] Instance dmpAX: DeMorganAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  apply provable_weak_excluded_middle.
Qed.

End DeMorganPropositionalLogic.

End DeMorganPropositionalLogic.

Module GodelDummettPropositionalLogic.

Section GodelDummettPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L
                   PropositionalLanguage.minL
                   PropositionalLanguage.andpL
                   PropositionalLanguage.orpL
                   PropositionalLanguage.falsepL
                   PropositionalLanguage.negpL
                   PropositionalLanguage.negpDef.

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| provable_andp_intros: forall x y, provable (x --> y --> x && y)
| provable_andp_elim1: forall x y, provable (x && y --> x)
| provable_andp_elim2: forall x y, provable (x && y --> y)
| provable_orp_intros1: forall x y, provable (x --> x || y)
| provable_orp_intros2: forall x y, provable (y --> x || y)
| provable_orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| provable_falsep_elim: forall x, provable (FF --> x)
| impp_choice: forall x y, provable ((x --> y) || (y --> x)).

#[export] Instance GP: Provable PropositionalLanguage.L :=
  Build_Provable _ provable.

#[export] Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.

#[export] Instance GammaDP: DerivableFromProvable PropositionalLanguage.L GP GD :=
  Provable2Derivable_Normal.

#[export] Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provables_modus_ponens.
  + apply provable_axiom1.
  + apply provable_axiom2.
Qed.

#[export] Instance andpAX: AndAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_andp_intros.
  + apply provable_andp_elim1.
  + apply provable_andp_elim2.
Qed.

#[export] Instance orpAX: OrAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_orp_intros1.
  + apply provable_orp_intros2.
  + apply provable_orp_elim.
Qed.

#[export] Instance falsepAX: FalseAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  apply provable_falsep_elim.
Qed.

#[export] Instance inegpAX: IntuitionisticNegAxiomatization PropositionalLanguage.L GP :=
  NegFromDefToAX_False_Imp.

#[export] Instance gdpAX: GodelDummettAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  apply impp_choice.
Qed.

#[export] Instance dmpAX: DeMorganAxiomatization PropositionalLanguage.L GP :=
  GodelDummett2DeMorgan.

End GodelDummettPropositionalLogic.

End GodelDummettPropositionalLogic.

Module ClassicalPropositionalLogic.

Section ClassicalPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L
                   PropositionalLanguage.minL
                   PropositionalLanguage.andpL
                   PropositionalLanguage.orpL
                   PropositionalLanguage.falsepL
                   PropositionalLanguage.negpL
                   PropositionalLanguage.negpDef.

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| provable_andp_intros: forall x y, provable (x --> y --> x && y)
| provable_andp_elim1: forall x y, provable (x && y --> x)
| provable_andp_elim2: forall x y, provable (x && y --> y)
| provable_orp_intros1: forall x y, provable (x --> x || y)
| provable_orp_intros2: forall x y, provable (y --> x || y)
| provable_orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| provable_falsep_elim: forall x, provable (FF --> x)
| provable_peirce_law: forall x y, provable (((x --> y) --> x) --> x).

#[export] Instance GP: Provable PropositionalLanguage.L := Build_Provable _ provable.

#[export] Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.

#[export] Instance GammaDP: DerivableFromProvable PropositionalLanguage.L GP GD :=
  Provable2Derivable_Normal.

#[export] Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provables_modus_ponens.
  + apply provable_axiom1.
  + apply provable_axiom2.
Qed.

#[export] Instance andpAX: AndAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_andp_intros.
  + apply provable_andp_elim1.
  + apply provable_andp_elim2.
Qed.

#[export] Instance orpAX: OrAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  + apply provable_orp_intros1.
  + apply provable_orp_intros2.
  + apply provable_orp_elim.
Qed.

#[export] Instance falsepAX: FalseAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  apply provable_falsep_elim.
Qed.

#[export] Instance inegpAX: IntuitionisticNegAxiomatization PropositionalLanguage.L GP :=
  NegFromDefToAX_False_Imp.

#[export] Instance cpAX: ClassicalAxiomatization PropositionalLanguage.L GP.
Proof.
  constructor.
  apply provable_peirce_law.
Qed.

#[export] Instance gdpAX: GodelDummettAxiomatization PropositionalLanguage.L GP :=
  Classical2GodelDummett.

#[export] Instance dmpAX: DeMorganAxiomatization PropositionalLanguage.L GP :=
  GodelDummett2DeMorgan.

End ClassicalPropositionalLogic.

End ClassicalPropositionalLogic.

