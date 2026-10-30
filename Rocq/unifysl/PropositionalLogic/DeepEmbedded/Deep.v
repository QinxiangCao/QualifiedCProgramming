Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Inductive expr : Type :=
| andp : expr -> expr -> expr
| impp : expr -> expr -> expr
| varp : nat -> expr
.

Definition truep: expr := impp (varp 0) (varp 0).
Definition iffp x y: expr := andp (impp x y) (impp y x).

Fixpoint beq e1 e2 :=
  match e1, e2 with
  | varp x, varp y => EqNat.beq_nat x y
  | andp p11 p12, andp p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | impp p11 p12, impp p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | _, _ => false
  end.

Theorem beq_eq : forall e1 e2, beq e1 e2 = true <-> e1 = e2.
Proof.
  split.
  - generalize dependent e2.
    induction e1; intros; destruct e2; simpl in H;
      try congruence; auto using EqNat.beq_nat_true.
    all: apply andb_prop in H; destruct H;
      rewrite (IHe1_1 _ H); rewrite (IHe1_2 _ H0); reflexivity.
  - intros. subst e2.
    induction e1; simpl; auto using andb_true_intro, EqNat.beq_nat_refl.
Qed.

Local Instance L : Language := Build_Language expr .

Local Instance minL : MinimumLanguage L := Build_MinimumLanguage L impp.

Local Instance andpL : AndLanguage L :=
  Build_AndLanguage L andp.

Local Instance truepL : TrueLanguage L :=
  Build_TrueLanguage L truep.

Local Instance iffpL : IffLanguage L :=
  Build_IffLanguage L iffp.

Local Instance iffpDef : IffDefinition_And_Imp L :=
  AndImp2Iff_Normal.

Local Instance iter_andp_L: IterAndLanguage L :=
  Build_IterAndLanguage L (fun es => fold_left andp es truep).

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| provable_andp_intros: forall x y, provable (x --> y --> x && y)
| provable_andp_elim1: forall x y, provable (x && y --> x)
| provable_andp_elim2: forall x y, provable (x && y --> y)
.

Local Instance GP: Provable L := Build_Provable _ provable.

Local Instance minAX: MinimumAxiomatization L GP.
Proof.
  constructor.
  + apply provables_modus_ponens.
  + apply provable_axiom1.
  + apply provable_axiom2.
Qed.

Local Instance andpAX: AndAxiomatization L GP.
Proof.
  constructor.
  + apply provable_andp_intros.
  + apply provable_andp_elim1.
  + apply provable_andp_elim2.
Qed.

Local Instance truepAX: TrueAxiomatization L GP.
Proof.
  constructor.
  simpl.
  unfold truep.
  pose proof provable_impp_refl (varp 0).
  exact H.
Qed.

Local Instance iffpAX: IffAxiomatization L GP :=
  IffFromDefToAX_And_Imp.

Local Instance iter_andp_DL: IterAndDefinition_left L :=
  Build_IterAndDefinition_left L _ _ _ (fun es => eq_refl).

Local Instance iter_andp_AXL: IterAndAxiomatization_left L GP :=
  IterAndFromDefToAX_L2L.
