Require Import Coq.Init.Nat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.

From SetsClass Require Import SetsClass.

Local Open Scope bool.
Local Open Scope Z.

Import SetsNotation.
Local Open Scope sets.

From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope order_scope.

Definition is_lb
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a <= a'.

Definition is_ub
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a' <= a.

Definition is_omega_lb
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, a <= l n.

Definition is_omega_ub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, l n <= a.

Definition is_omega_lub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  is_omega_ub l a /\ is_lb (is_omega_ub l) a.

Lemma is_omega_lub_sound:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_omega_ub l a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

Lemma is_omega_lub_tight:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_lb (is_omega_ub l) a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

Class Reflexive_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  reflexivity_setoid:
    forall a b, a == b -> a <= b.

Class AntiSymmetric_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  antisymmetricity_setoid:
    forall a b, a <= b -> b <= a -> a == b.

Class PartialOrder_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
{
  PO_Reflexive_Setoid:: Reflexive_Setoid A;
  PO_Transitive:: Transitive order_rel;
  PO_AntiSymmetric_Setoid:: AntiSymmetric_Setoid A
}.

#[export] Instance PartialOrder_Setoid_Proper
           {A: Type} `{POA: PartialOrder_Setoid A} {EquivA: Equivalence equiv}:
  Proper (equiv ==> equiv ==> iff) order_rel.
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  + transitivity x0; [| apply reflexivity_setoid; tauto].
    transitivity x; [apply reflexivity_setoid; symmetry; tauto |].
    tauto.
  + transitivity y0; [| apply reflexivity_setoid; symmetry; tauto].
    transitivity y; [apply reflexivity_setoid; tauto |].
    tauto.
Qed.

Lemma same_omega_ub_same_omega_lub:
  forall
    {A: Type}
    `{POA: PartialOrder_Setoid A}
    (l1 l2: nat -> A)
    (a1 a2: A),
  (is_omega_ub l1 == is_omega_ub l2)%sets ->
  is_omega_lub l1 a1 ->
  is_omega_lub l2 a2 ->
  a1 == a2.
Proof.
  intros A ? ? POA.
  sets_unfold.
  intros.
  apply antisymmetricity_setoid.
  + apply (is_omega_lub_tight H0).
    apply H.
    apply (is_omega_lub_sound H1).
  + apply (is_omega_lub_tight H1).
    apply H.
    apply (is_omega_lub_sound H0).
Qed.

Class OmegaLub (A: Type): Type :=
  omega_lub: (nat -> A) -> A.

Class Bot (A: Type): Type :=
  bot: A.


Definition increasing
             {A: Type} {RA: Order A} (l: nat -> A): Prop :=
  forall n, l n <= l (S n).

Definition is_least {A: Type} {RA: Order A} (a: A): Prop :=
  forall a', a <= a'.

Class OmegaCompletePartialOrder_Setoid
        (A: Type)
        {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}: Prop :=
{
  oCPO_PartialOrder:: PartialOrder_Setoid A;
  oCPO_completeness: forall T,
    increasing T -> is_omega_lub T (omega_lub T);
  bot_is_least: is_least bot
}.

Lemma same_omega_ub_same_omega_lub':
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (l1 l2: nat -> A),
  (is_omega_ub l1 == is_omega_ub l2)%sets ->
  increasing l1 ->
  increasing l2 ->
  omega_lub l1 == omega_lub l2.
Proof.
  intros.
  apply (same_omega_ub_same_omega_lub _ _ _ _ H).
  + apply oCPO_completeness.
    apply H0.
  + apply oCPO_completeness.
    apply H1.
Qed.

Definition mono
             {A B: Type}
             `{POA: PartialOrder_Setoid A}
             `{POB: PartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall a1 a2, a1 <= a2 -> f a1 <= f a2.


Definition continuous
             {A B: Type}
             `{oCPOA: OmegaCompletePartialOrder_Setoid A}
             `{oCPOB: OmegaCompletePartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall l: nat -> A,
    increasing l ->
    f (omega_lub l) == omega_lub (fun n => f (l n)).

Lemma id_mono:
  forall {A: Type}
         `{POA: PartialOrder_Setoid A},
  mono (fun x => x).
Proof.
  intros.
  unfold mono. intros.
  auto.
Qed.

Lemma compose_mono:
  forall {A B C: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         `{POC: PartialOrder_Setoid C}
         (f: A -> B)
         (g: B -> C),
  mono f -> mono g -> mono (fun x => g (f x)).
Proof.
  intros.
  unfold mono. intros.
  apply H0. apply H. apply H1.
Qed.

Lemma id_continuous:
  forall {A: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         {EquivA: Equivalence equiv},
  continuous (fun x => x).
Proof.
  intros.
  unfold continuous. intros.
  reflexivity.
Qed.

Lemma increasing_mono_increasing:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         (f: A -> B)
         (l: nat -> A),
  increasing l -> mono f -> increasing (fun n => f (l n)).
Proof.
  intros.
  unfold increasing. intros.
  apply H0. apply H.
Qed.

Lemma mono_equiv_congr:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
          {EquivA: Equivalence (equiv: A -> A -> Prop)}
         (f: A -> B),
  mono f -> Proper (equiv ==> equiv) f.
Proof.
  intros.
  unfold Proper, respectful. intros.
  apply antisymmetricity_setoid.
  - apply H. rewrite H0. apply reflexivity_setoid. reflexivity.
  - apply H. rewrite H0. apply reflexivity_setoid. reflexivity.
Qed.

Lemma compose_continuous:
  forall {A B C: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         `{oCPOB: OmegaCompletePartialOrder_Setoid B}
         `{oCPOC: OmegaCompletePartialOrder_Setoid C}
          {EquivB: Equivalence (equiv: B -> B -> Prop)}
          {EquivC: Equivalence (equiv: C -> C -> Prop)}
         (f: A -> B)
         (g: B -> C),
  mono f ->
  mono g ->
  continuous f ->
  continuous g ->
  continuous (fun x => g (f x)).
Proof.
  intros.
  unfold continuous. intros.
  pose proof (mono_equiv_congr g H0).
  rewrite H1; auto.
  apply H2. apply increasing_mono_increasing; auto.
Qed.

Lemma iter_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => Nat.iter n f bot).
Proof.
  unfold increasing.
  intros.
  induction n; simpl.
  + apply bot_is_least.
  + apply H.
    apply IHn.
Qed.

Lemma iter_S_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => f (Nat.iter n f bot)).
Proof.
  unfold increasing.
  intros.
  apply H.
  apply iter_bot_increasing.
  apply H.
Qed.

Definition BW_LFix
             {A: Type}
             `{CPOA: OmegaCompletePartialOrder_Setoid A}
             (f: A -> A): A :=
  omega_lub (fun n => Nat.iter n f bot).


Lemma BW_LFix_is_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    continuous f ->
    f (BW_LFix f) == BW_LFix f.
Proof.
  unfold BW_LFix; intros.
  rewrite H0 by (apply iter_bot_increasing; tauto).
  apply same_omega_ub_same_omega_lub'.
  + intros; unfold is_omega_ub.
    split; intros.
    - destruct n.
      * apply bot_is_least.
      * apply H1.
    - specialize (H1 (S n)).
      apply H1.
  + apply iter_S_bot_increasing.
    apply H.
  + apply iter_bot_increasing.
    apply H.
Qed.

Lemma BW_LFix_is_least_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A)
    (a: A),
    mono f ->
    continuous f ->
    f a == a ->
    BW_LFix f <= a.
Proof.
  unfold BW_LFix; intros.
  pose proof iter_bot_increasing f H.
  pose proof oCPO_completeness (fun n => Nat.iter n f bot) H2.
  apply (is_omega_lub_tight H3).
  unfold is_omega_ub.
  induction n; simpl.
  + apply bot_is_least.
  + rewrite <- H1.
    apply H.
    apply IHn.
Qed.

Local Close Scope order_scope.

#[export] Instance R_while_err {A: Type}: Order (A -> Prop) :=
  Sets.included.

#[export] Instance Equiv_while_err {A: Type}: Equiv (A -> Prop) :=
  Sets.equiv.

#[export] Instance PO_while_err {A: Type}: PartialOrder_Setoid (A ->  Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_while_err, Equiv_while_err; simpl.
    sets_unfold; intros a b H x.
    specialize (H x).
    tauto.
  + unfold Transitive.
    unfold equiv, order_rel, R_while_err, Equiv_while_err; simpl.
    sets_unfold; intros a b c H H0 x.
    specialize (H x).
    specialize (H0 x).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_while_err, Equiv_while_err; simpl.
    sets_unfold; intros a b H H0 x.
    specialize (H x).
    specialize (H0 x).
    tauto.
Qed.

#[export] Instance oLub_while_err {A: Type}: OmegaLub (A -> Prop) :=
  Sets.indexed_union.

#[export] Instance Bot_while_err {A: Type}: Bot (A -> Prop) :=
  ∅: A -> Prop.

#[export] Instance oCPO_while_err {A: Type}:
  OmegaCompletePartialOrder_Setoid (A ->  Prop).
Proof.
  split.
  + apply PO_while_err.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_while_err, oLub_while_err; simpl.
    sets_unfold; intros T H.
    split.
    - intros n x; intros.
      exists n.
      tauto.
    - intros a H0 x H1.
      destruct H1 as [n ?].
      specialize (H0 n x).
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_while_err, Bot_while_err; simpl.
    sets_unfold; intros a.
    tauto.
Qed.

#[export] Instance R_while_fin {A B: Type}: Order (A -> B -> Prop) :=
  Sets.included.

#[export] Instance Equiv_while_fin {A B: Type}: Equiv (A -> B -> Prop) :=
  Sets.equiv.

#[export] Instance PO_while_fin {A B: Type}: PartialOrder_Setoid (A -> B -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b H x y.
    specialize (H x y).
    tauto.
  + unfold Transitive.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b c H H0 x y.
    specialize (H x y).
    specialize (H0 x y).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b H H0 x y.
    specialize (H x y).
    specialize (H0 x y).
    tauto.
Qed.

#[export] Instance oLub_while_fin {A B: Type}: OmegaLub (A -> B -> Prop) :=
  Sets.indexed_union.

#[export] Instance Bot_while_fin {A B: Type}: Bot (A -> B -> Prop) :=
  ∅: A -> B -> Prop.

#[export] Instance oCPO_while_fin {A B: Type}:
  OmegaCompletePartialOrder_Setoid (A -> B -> Prop).
Proof.
  split.
  + apply PO_while_fin.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_while_fin, oLub_while_fin; simpl.
    sets_unfold; intros T H.
    split.
    - intros n x y; intros.
      exists n.
      tauto.
    - intros a H0 x y H1.
      destruct H1 as [n ?].
      specialize (H0 n x y).
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_while_fin, Bot_while_fin; simpl.
    sets_unfold; intros a.
    tauto.
Qed.

#[export] Instance Equiv_equiv_while_fin {A B: Type}:
  Equivalence (@equiv (A -> B -> Prop) _).
Proof.
  apply Sets_equiv_equiv.
Qed.



Lemma BinRel_concat_left_mono:
  forall (A B C: Type) (Y: A -> B -> Prop),
    mono (fun X: B -> C -> Prop => Y ∘ X).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_fin.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma BinRel_concat_omega_union_distr_l:
  forall
    {A B C}
    (R1: A -> B -> Prop)
    (R2: nat -> B -> C -> Prop),
  R1 ∘ (⋃ R2) == ⋃ (fun n => R1 ∘ R2 n).
Proof.
  intros.
  sets_unfold.
  intros a c. split; intros.
  - destruct H as [b [? [n ?] ] ].
    exists n, b. auto.
  - destruct H as [n [b [? ?] ] ].
    exists b. split.
    + auto.
    + exists n. auto.
Qed.


Lemma BinRel_concat_left_continuous:
  forall (A B C: Type) (Y: A -> B -> Prop),
    continuous (fun X: B -> C -> Prop => Y ∘ X).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin.
  intros.
  apply BinRel_concat_omega_union_distr_l.
Qed.

Lemma BinRel_concat_left_mono_and_continuous:
  forall
    (A B C: Type)
    (Y: A -> B -> Prop)
    (f: (B -> C -> Prop) -> (B -> C -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => Y ∘ f X) /\ continuous (fun X => Y ∘ f X).
Proof.
  intros.
  destruct H.
  pose proof BinRel_concat_left_mono _ _ C Y.
  pose proof BinRel_concat_left_continuous _ _ C Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

Lemma union_right2_mono:
  forall (A B: Type) (Y: A -> B -> Prop),
    mono (fun X => X ∪ Y).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_fin.
  sets_unfold.
  intros R R' H st1 st2.
  specialize (H st1 st2).
  tauto.
Qed.

Lemma union_right2_continuous:
  forall (A B: Type) (Y: A -> B -> Prop),
    continuous (fun X => X ∪ Y).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin.
  sets_unfold.
  intros l H st1 st2.
  split; intros.
  + destruct H0 as [ [ n ? ] | ?].
    - exists n; tauto.
    - exists O; tauto.
  + destruct H0 as [n [? | ? ] ].
    - left.
      exists n; tauto.
    - tauto.
Qed.

Lemma union_right2_mono_and_continuous:
  forall
    (A B: Type)
    (Y: A -> B -> Prop)
    (f: (A -> B -> Prop) -> (A -> B -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => f X ∪ Y) /\ continuous (fun X => f X ∪ Y).
Proof.
  intros.
  destruct H.
  pose proof union_right2_mono _ _ Y.
  pose proof union_right2_continuous _ _ Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.


#[export] Instance R_func {A B C : Type} : Order (A -> B -> C -> Prop) :=
  Sets.included.

#[export] Instance Equiv_func {A B C : Type} : Equiv (A -> B -> C -> Prop) :=
  Sets.equiv.

#[export] Instance PO_func {A B C : Type} : PartialOrder_Setoid (A -> B -> C -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_func, Equiv_func; simpl.
    sets_unfold; intros a b H x y z.
    specialize (H x y z).
    tauto.
  + unfold Transitive.
    unfold equiv, order_rel, R_func, Equiv_func; simpl.
    sets_unfold; intros a b c H H0 x y z.
    specialize (H x y z).
    specialize (H0 x y z).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_func, Equiv_func; simpl.
    sets_unfold; intros a b H H0 x y z.
    specialize (H x y z).
    specialize (H0 x y z).
    tauto.
Qed.

#[export] Instance oLub_func {A B C : Type} : OmegaLub (A -> B -> C -> Prop) :=
  Sets.indexed_union.

#[export] Instance Bot_func {A B C : Type} : Bot (A -> B -> C -> Prop) :=
  ∅: A -> B -> C -> Prop.

#[export] Instance oCPO_func {A B C : Type} : OmegaCompletePartialOrder_Setoid (A -> B -> C -> Prop).
Proof.
  split.
  + apply PO_func.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_func, oLub_func; simpl.
    sets_unfold; intros T H.
    split.
    - intros n x y z; intros.
      exists n.
      tauto.
    - intros a H0 x y z H1.
      destruct H1 as [n ?].
      specialize (H0 n x y z).
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_func, Bot_func; simpl.
    sets_unfold; intros a.
    tauto.
Qed.

#[export] Instance Equivalence_func {A B C: Type} : Equivalence (@equiv (A -> B -> C -> Prop) _).
Proof.
  split.
  - unfold Reflexive, equiv, Equiv_func.
    intros. reflexivity.
  - unfold Symmetric, equiv, Equiv_func.
    intros. symmetry. auto.
  - unfold Transitive, equiv, Equiv_func.
    intros. transitivity (y); auto.
Qed.


#[export] Instance R_whileret {A B C D : Type} : Order (A -> B -> C -> D -> Prop) :=
  Sets.included.

#[export] Instance Equiv_whileret {A B C D: Type} : Equiv (A -> B -> C -> D -> Prop) :=
  Sets.equiv.

#[export] Instance PO_whileret {A B C D : Type} : PartialOrder_Setoid (A -> B -> C -> D -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_whileret, Equiv_whileret; simpl.
    sets_unfold; intros a b H x y z u.
    specialize (H x y z u).
    tauto.
  + unfold Transitive.
    unfold equiv, order_rel, R_whileret, Equiv_whileret; simpl.
    sets_unfold; intros a b c H H0 x y z u.
    specialize (H x y z u).
    specialize (H0 x y z u).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_whileret, Equiv_whileret; simpl.
    sets_unfold; intros a b H H0 x y z u.
    specialize (H x y z u).
    specialize (H0 x y z u).
    tauto.
Qed.

#[export] Instance oLub_whileret {A B C D: Type} : OmegaLub (A -> B -> C ->  D -> Prop) :=
  Sets.indexed_union.

#[export] Instance Bot_whileret {A B C D : Type} : Bot (A -> B -> C -> D -> Prop) :=
  ∅: A -> B -> C -> D -> Prop.

#[export] Instance oCPO_whileret {A B C D : Type} : OmegaCompletePartialOrder_Setoid (A -> B -> C -> D -> Prop).
Proof.
  split.
  + apply PO_whileret.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_whileret, oLub_whileret; simpl.
    sets_unfold; intros T H.
    split.
    - intros n x y z u; intros.
      exists n.
      tauto.
    - intros a H0 x y z u H1.
      destruct H1 as [n ?].
      specialize (H0 n x y z u).
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_whileret, Bot_whileret; simpl.
    sets_unfold; intros a.
    tauto.
Qed.

#[export] Instance Equivalence_whileret {A B C D: Type} : Equivalence (@equiv (A -> B -> C -> D -> Prop) _).
Proof.
  split.
  - unfold Reflexive, equiv, Equiv_whileret.
    intros. reflexivity.
  - unfold Symmetric, equiv, Equiv_whileret.
    intros. symmetry. auto.
  - unfold Transitive, equiv, Equiv_whileret.
    intros. transitivity (y); auto.
Qed.