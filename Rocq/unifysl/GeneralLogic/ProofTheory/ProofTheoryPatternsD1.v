Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.

Local Open Scope logic_base.
Local Open Scope syntax.

Class Adjointness (L: Language) (GammaD1: Derivable1 L) (prodp funcp: expr -> expr -> expr): Prop := {
  adjoint: forall x y z, prodp x y |-- z <-> x |-- funcp y z
}.

Class Commutativity (L: Language) (GammaD1: Derivable1 L) (prodp: expr -> expr -> expr): Prop := {
  derivable1_prodp_comm: forall x y, prodp x y |-- prodp y x
}.

Class Monotonicity (L: Language) (GammaD1: Derivable1 L) (prodp: expr -> expr -> expr): Prop := {
  prodp_mono: forall x1 y1 x2 y2, x1 |-- x2 -> y1 |-- y2 -> prodp x1 y1 |-- prodp x2 y2
}.

Class Associativity (L: Language) (GammaD1: Derivable1 L) (prodp: expr -> expr -> expr): Prop := {
  prodp_assoc1: forall x y z, prodp x (prodp y z) |-- prodp (prodp x y) z;
  prodp_assoc2: forall x y z, prodp (prodp x y) z |-- prodp x (prodp y z)
}.

Class LeftUnit (L: Language) (GammaD1: Derivable1 L) (e: expr) (prodp: expr -> expr -> expr): Prop := {
  left_unit1: forall x, prodp e x |-- x;
  left_unit2: forall x, x |-- prodp e x
}.

Class RightUnit (L: Language) (GammaD1: Derivable1 L) (e: expr) (prodp: expr -> expr -> expr): Prop := {
  right_unit1: forall x, prodp x e |-- x;
  right_unit2: forall x, x |-- prodp x e
}.

Class LeftDistr (L: Language) (GammaD1: Derivable1 L) (prodp sump: expr -> expr -> expr): Prop := {
  left_distr1: forall x y z, prodp x (sump y z) |-- sump (prodp x y) (prodp x z);
  left_distr2: forall x y z, sump (prodp x y) (prodp x z) |-- prodp x (sump y z);
}.

Class RightDistr (L: Language) (GammaD1: Derivable1 L) (prodp sump: expr -> expr -> expr): Prop := {
  right_distr1: forall x y z, prodp (sump y z) x |-- sump (prodp y x) (prodp z x);
  right_distr2: forall x y z, sump (prodp y x) (prodp z x) |-- prodp (sump y z) x;
}.

Section AdjointTheorems.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {prodp funcp: expr -> expr -> expr}
        {Adj: Adjointness L GammaD1 prodp funcp}.

Lemma prodp_mono1: forall x1 x2 y, x1 |-- x2 -> prodp x1 y |-- prodp x2 y.
Proof.
  intros.
  apply adjoint.
  rewrite H.
  apply adjoint.
  apply derivable1_refl.
Qed.

Lemma funcp_mono2: forall x y1 y2, y1 |-- y2 -> funcp x y1 |-- funcp x y2.
Proof.
  intros.
  apply adjoint.
  rewrite <- H.
  apply adjoint.
  apply derivable1_refl.
Qed.

Lemma adjoint_modus_ponens:
  forall x y, prodp (funcp x y) x |-- y.
Proof.
  intros.
  apply adjoint.
  apply derivable1_refl.
Qed.

Lemma adjoint_iter:
  forall x xs y,
    fold_left prodp xs x |-- y <-> x |-- (fold_right funcp y xs).
Proof.
  intros.
  revert x; induction xs; intros; simpl in *.
  + reflexivity.
  + rewrite <- adjoint.
    auto.
Qed.

Section AdjointCommutativeTheorems.

Context {Comm: Commutativity L GammaD1 prodp}.

Lemma Adjoint2Mono: Monotonicity L GammaD1 prodp.
Proof.
  constructor.
  intros.
  apply adjoint.
  rewrite H.
  apply adjoint.
  rewrite derivable1_prodp_comm.
  apply adjoint.
  rewrite H0.
  apply adjoint.
  rewrite derivable1_prodp_comm.
  reflexivity.
Qed.

End AdjointCommutativeTheorems.

Section AdjointMonoTheorems.

Context {Mono: Monotonicity L GammaD1 prodp}.

Lemma funcp_mono: forall x1 y1 x2 y2, x2 |-- x1 -> y1 |-- y2 -> funcp x1 y1 |-- funcp x2 y2.
Proof.
  intros.
  apply adjoint.
  rewrite <- H0.
  rewrite <- (adjoint_modus_ponens x1 y1) at 2.
  apply prodp_mono.
  + reflexivity.
  + auto.
Qed.

End AdjointMonoTheorems.

End AdjointTheorems.

Section MonoTheorems.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {prodp: expr -> expr -> expr}
        {Mono: Monotonicity L GammaD1 prodp}.

Lemma fold_left_mono: forall x1 x2 xs1 xs2,
  (Forall2 derivable1 xs1 xs2) ->
  x1 |-- x2 ->
  fold_left prodp xs1 x1 |-- fold_left prodp xs2 x2.
Proof.
  intros.
  revert x1 x2 H0.
  induction H; intros.
  + simpl; auto.
  + simpl.
    apply IHForall2.
    apply prodp_mono; auto.
Qed.

Lemma fold_right_mono: forall x1 x2 xs1 xs2,
  (Forall2 derivable1 xs1 xs2) ->
  x1 |-- x2 ->
  fold_right prodp x1 xs1 |-- fold_right prodp x2 xs2.
Proof.
  intros.
  induction H; intros.
  + simpl; auto.
  + simpl.
    apply prodp_mono; auto.
Qed.

Lemma fold_left_mono2: forall x1 x2 xs,
  x1 |-- x2 ->
  fold_left prodp xs x1 |-- fold_left prodp xs x2.
Proof.
  intros.
  apply fold_left_mono; auto.
  induction xs.
  + constructor.
  + constructor; auto.
    reflexivity.
Qed.

Lemma fold_right_mono2: forall x1 x2 xs,
  x1 |-- x2 ->
  fold_right prodp x1 xs |-- fold_right prodp x2 xs.
Proof.
  intros.
  apply fold_right_mono; auto.
  induction xs.
  + constructor.
  + constructor; auto.
    reflexivity.
Qed.

End MonoTheorems.

Section AssocTheorems.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {prodp: expr -> expr -> expr}
        {e: expr}
        {Mono: Monotonicity L GammaD1 prodp}
        {Assoc: Associativity L GammaD1 prodp}
        {LU: LeftUnit L GammaD1 e prodp}
        {RU: RightUnit L GammaD1 e prodp}.

(* Since the left unit and right unit can only be identical, we can just assume that directly. *)

Lemma assoc_fold_left_cons: forall x xs,
  fold_left prodp xs (prodp e x) |-- prodp x (fold_right prodp e xs).
Proof.
  intros.
  revert x; induction xs; intros.
  + simpl.
    rewrite left_unit1.
    rewrite <- right_unit2.
    reflexivity.
  + simpl.
    rewrite <- prodp_assoc2.
    rewrite <- IHxs.
    apply fold_left_mono2.
    apply prodp_assoc2.
Qed.

Lemma assoc_fold_right_cons: forall x xs,
  prodp x (fold_right prodp e xs) |-- fold_left prodp xs (prodp e x).
Proof.
  intros.
  revert x; induction xs; intros.
  + simpl.
    rewrite <- left_unit2.
    rewrite right_unit1.
    reflexivity.
  + simpl.
    rewrite prodp_assoc1.
    rewrite IHxs.
    apply fold_left_mono2.
    apply prodp_assoc1.
Qed.

Lemma assoc_fold_left_fold_right: forall xs,
   fold_left prodp xs e |-- fold_right prodp e xs.
Proof.
  intros.
  induction xs.
  + simpl.
    reflexivity.
  + simpl.
    apply assoc_fold_left_cons.
Qed.

Lemma assoc_fold_right_fold_left: forall xs,
   fold_right prodp e xs |-- fold_left prodp xs e.
Proof.
  intros.
  induction xs.
  + simpl.
    reflexivity.
  + simpl.
    apply assoc_fold_right_cons.
Qed.

Lemma assoc_prodp_fold_left: forall xs1 xs2,
   prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e) |-- fold_left prodp (xs1 ++ xs2) e.
Proof.
  intros.
  eapply derivable1_trans; [apply prodp_mono; apply assoc_fold_left_fold_right |].
  rewrite <- assoc_fold_right_fold_left.
  induction xs1.
  + simpl.
    rewrite left_unit1.
    reflexivity.
  + simpl.
    rewrite prodp_assoc2.
    apply prodp_mono; [reflexivity |].
    auto.
Qed.

Lemma assoc_fold_left_app: forall xs1 xs2,
   fold_left prodp (xs1 ++ xs2) e |-- prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e).
Proof.
  intros.
  eapply derivable1_trans; [| apply prodp_mono; apply assoc_fold_right_fold_left].
  rewrite assoc_fold_left_fold_right.
  induction xs1.
  + simpl.
    rewrite <- left_unit2.
    reflexivity.
  + simpl.
    rewrite <- prodp_assoc1.
    apply prodp_mono; [reflexivity |].
    auto.
Qed.

End AssocTheorems.

Section DistrCommTheorems.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {prodp sump: expr -> expr -> expr}
        {Comm: Commutativity L GammaD1 prodp}
        {Mono: Monotonicity L GammaD1 sump}.

Lemma LeftDistr2RightDistr {LDistr: LeftDistr L GammaD1 prodp sump}:
      RightDistr L GammaD1 prodp sump.
Proof.
  constructor.
  + intros.
    rewrite (derivable1_prodp_comm _ x).
    pose proof derivable1_prodp_comm x y.
    pose proof derivable1_prodp_comm x z.
    pose proof prodp_mono _ _ _ _ H H0.
    rewrite <- H1.
    apply left_distr1.
  + intros.
    rewrite <- (derivable1_prodp_comm x (sump y z)).
    pose proof derivable1_prodp_comm y x.
    pose proof derivable1_prodp_comm z x.
    pose proof prodp_mono _ _ _ _ H H0.
    rewrite H1.
    apply left_distr2.
Qed.

Lemma RightDistr2LeftDistr {RDistr: RightDistr L GammaD1 prodp sump}:
      LeftDistr L GammaD1 prodp sump.
Proof.
  constructor.
  + intros.
    rewrite (derivable1_prodp_comm x (sump y z)).
    pose proof derivable1_prodp_comm y x.
    pose proof derivable1_prodp_comm z x.
    pose proof prodp_mono _ _ _ _ H H0.
    rewrite <- H1.
    apply right_distr1.
  + intros.
    rewrite <- (derivable1_prodp_comm (sump y z) x).
    pose proof derivable1_prodp_comm x y.
    pose proof derivable1_prodp_comm x z.
    pose proof prodp_mono _ _ _ _ H H0.
    rewrite H1.
    apply right_distr2.
Qed.

End DistrCommTheorems.

Section CommForSimpleAssocConstruction.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {prodp: expr -> expr -> expr}
        {Comm: Commutativity L GammaD1 prodp}
        {Mono: Monotonicity L GammaD1 prodp}.

Lemma Build_Associativity1:
      (forall x y z, prodp x (prodp y z) |-- prodp (prodp x y) z) ->
      Associativity L GammaD1 prodp.
Proof.
  intros.
  constructor; auto.
  intros.
  rewrite <- (derivable1_prodp_comm (prodp y z) x).
  rewrite (derivable1_prodp_comm (prodp x y) z).
  pose proof derivable1_prodp_comm x y.
  pose proof derivable1_refl z.
  pose proof prodp_mono _ _ _ _ H1 H0.
  rewrite H2.
  clear H0 H1 H2.
  pose proof derivable1_prodp_comm z y.
  pose proof derivable1_refl x.
  pose proof prodp_mono _ _ _ _ H0 H1.
  rewrite <- H2.
  clear H0 H1 H2.
  apply H.
Qed.

Lemma Build_Associativity2:
      (forall x y z, prodp (prodp x y) z |-- prodp x (prodp y z)) ->
      Associativity L GammaD1 prodp.
Proof.
  intros.
  constructor; auto.
  intros.
  rewrite <- (derivable1_prodp_comm z (prodp x y)).
  rewrite (derivable1_prodp_comm x (prodp y z)).
  pose proof derivable1_prodp_comm y z.
  pose proof derivable1_refl x.
  pose proof prodp_mono _ _ _ _ H0 H1.
  rewrite H2.
  clear H0 H1 H2.
  pose proof derivable1_prodp_comm y x.
  pose proof derivable1_refl z.
  pose proof prodp_mono _ _ _ _ H1 H0.
  rewrite <- H2.
  clear H0 H1 H2.
  apply H.
Qed.

End CommForSimpleAssocConstruction.
