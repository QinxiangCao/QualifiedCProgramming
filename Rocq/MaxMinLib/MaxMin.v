
Require Import SetsClass.SetsClass.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.

Import ListNotations.
Import SetsNotation.

Local Open Scope sets.

(* ============================================= *)
(*          全序关系类型类定义                    *)
(* ============================================= *)

Class TotalOrder {T : Type} (le: T -> T -> Prop) := {
  le_refl : forall x, le x x;
  le_trans : forall x y z, le x y -> le y z -> le x z;
  le_antisym : forall x y, le x y -> le y x -> x = y;
  le_total : forall x y, {le x y} + {le y x};
}. 

Section TotalOrder.
Context {T: Type}
        (le: T -> T -> Prop)
        {total_order_le: TotalOrder le}.

Lemma le_total_cases :
  forall x y, le x y \/ le y x.
Proof. intros. destruct (le_total x y); [left | right]; auto. Qed.

Definition le_max (x y: T): T :=
    if le_total x y then y else x.

Definition le_min (x y: T): T :=
    if le_total x y then x else y.

Lemma max_r : 
  forall x y, 
    le x y -> le_max x y = y. 
Proof. intros. unfold le_max. destruct (le_total x y); [auto | apply le_antisym; auto]. Qed. 

Lemma max_l : 
  forall x y, 
    le y x -> le_max x y = x. 
Proof. intros. unfold le_max. destruct (le_total x y); [apply le_antisym; auto| auto]. Qed. 


Lemma max_comm : 
  forall x y, le_max x y = le_max y x.
Proof. 
  intros. unfold le_max. 
  destruct (le_total x y);
  destruct (le_total y x); 
  auto; eapply le_antisym; eauto. 
Qed.

Lemma max_assoc : 
  forall x y z, le_max x (le_max y z) = le_max (le_max x y) z.
Proof. 
  intros. unfold le_max. 
  destruct (le_total x y);
  destruct (le_total y z).
  - destruct (le_total x z); auto. 
    apply le_antisym; auto. 
    eapply le_trans; eauto. 
  - destruct (le_total x y); auto.  
    apply le_antisym; auto. 
  - reflexivity. 
  - destruct (le_total x y); destruct (le_total x z); auto;
    try (apply le_antisym; auto);
    try (eapply le_trans; eauto). 
Qed.

Lemma min_r : 
  forall x y, 
    le x y -> le_min x y = x. 
Proof. intros. unfold le_min. destruct (le_total x y); [auto | apply le_antisym; auto]. Qed. 

Lemma min_l : 
  forall x y, 
    le y x -> le_min x y = y. 
Proof. intros. unfold le_min. destruct (le_total x y); [apply le_antisym; auto| auto]. Qed.


(* Definition ge (x y : T) : Prop := le y x.   


Lemma ge_refl : forall x, ge x x. 
Proof. intros. unfold ge. apply le_refl. Qed.

Lemma ge_trans : forall x y z, ge x y -> ge y z -> ge x z.
Proof. intros. unfold ge. eapply le_trans; eauto. Qed.

Lemma ge_antisym : forall x y, ge x y -> ge y x -> x = y.
Proof. intros. unfold ge. apply le_antisym; auto. Qed. 

Lemma ge_total : forall x y, {ge x y} + {ge y x}.
Proof. intros. unfold ge. destruct (le_total y x); auto. Qed.

#[export] Instance ge_total_order: TotalOrder ge := {
  le_refl := ge_refl;
  le_trans := ge_trans;
  le_antisym := ge_antisym;
  le_total := ge_total
}. *)

Notation "x ≤ y" := (le x y) (at level 70, no associativity).
Notation "x ≥ y" := (le y x) (at level 70, no associativity).



Definition max_object_of_subset
             {A: Type}
             (X: A -> Prop)
             (f: A -> T)
             (a: A): Prop :=
  a ∈ X /\ forall b, b ∈ X -> f b ≤ f a.

Definition max_value_of_subset
             {A: Type}
             (X: A -> Prop)
             (f: A -> T)
             (n: T): Prop :=
  (exists a, max_object_of_subset X f a /\ f a = n). 

Definition max_value_of_subset_with_default
             {A: Type}
             (X: A -> Prop)
             (f: A -> T)
             (default: T)
             (n: T): Prop :=
  (max_value_of_subset X f n /\ default ≤ n) \/
  ((forall a, a ∈ X -> f a ≤ default) /\ default = n).

Notation "a 'is-the-max-of' e 'in-which' x 'satisfies' P" :=
  (max_value_of_subset (fun x => P) (fun x => e) a)
  (at level 1, no associativity).

Notation "a 'is-the-max-of' e 'in-which' ' pat 'satisfies' P" :=
  (max_value_of_subset (fun xx => match xx with pat => P end) (fun xx => match xx with pat => e end) a)
  (at level 1, pat pattern, no associativity).

Notation "a 'is-the-max-of' e 'in-which' x 'satisfies' P 'with-default' default" :=
  (max_value_of_subset_with_default (fun x => P) (fun x => e) default a)
  (at level 1, no associativity).

Notation "a 'is-the-max-of' e 'in-which' ' pat 'satisfies' P 'with-default' default" :=
  (max_value_of_subset_with_default (fun xx => match xx with pat => P end) (fun xx => match xx with pat => e end) default a)
  (at level 1, pat pattern, no associativity).

Lemma max_object_sound {A: Type}:
  forall (f: A -> T) (P: A -> Prop) (a: A),
    max_object_of_subset P f a ->
    (forall b: A, b ∈ P -> f b ≤ f a).
Proof. intros f P a [? ?]. tauto. Qed.

Lemma max_object_legal {A: Type}:
  forall (f: A -> T) (P: A -> Prop) (a: A),
    max_object_of_subset P f a ->
    a ∈ P.
Proof. intros f P a [? ?]. tauto. Qed.

Lemma max_default_ge_default {A: Type}:
  forall n (f: A -> T) (P: A -> Prop) default,
    max_value_of_subset_with_default P f default n ->
    default ≤ n.
Proof. intros. destruct H as [[]|[]]; subst; [auto|apply le_refl]. Qed.

#[export] Instance max_object_of_subset_congr {A: Type}:
  Proper
    (Sets.equiv ==> eq ==> eq ==> iff)
    (@max_object_of_subset A).
Proof.
  unfold Proper, respectful.
  intros.
  unfold max_object_of_subset.
  subst.
  rewrite H.
  apply Morphisms_Prop.and_iff_morphism; [reflexivity |].
  apply Morphisms_Prop.all_iff_morphism; intros ?.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance max_value_of_subset_congr {A: Type}:
  Proper
    (Sets.equiv ==> eq ==> eq ==> iff)
    (@max_value_of_subset A).
Proof.
  unfold Proper, respectful.
  intros.
  unfold max_value_of_subset.
  apply Morphisms_Prop.ex_iff_morphism; intros ?.
  rewrite H.
  subst.
  reflexivity.
Qed.

#[export] Instance max_value_of_subset_with_default_congr {A: Type}:
  Proper
    (Sets.equiv ==> eq ==> eq ==> eq ==> iff)
    (@max_value_of_subset_with_default A).
Proof.
  unfold Proper, respectful.
  intros.
  unfold max_value_of_subset_with_default.
  subst.
  rewrite H.
  apply Morphisms_Prop.or_iff_morphism; [reflexivity |].
  apply Morphisms_Prop.and_iff_morphism; [| reflexivity].
  apply Morphisms_Prop.all_iff_morphism; intros ?.
  rewrite H.
  reflexivity.
Qed.

Theorem max_unique {A: Type}:
  forall (f: A -> T) (P: A -> Prop) n m,
    max_value_of_subset P f n ->
    max_value_of_subset P f m ->
    n = m.
Proof.
  intros f P n m Hn Hm.
  destruct Hn as [a [Hobj_a Hfa_eq]].
  destruct Hm as [b [Hobj_b Hfb_eq]].
  subst n m.
  destruct Hobj_a as [Ha_in_P Ha_max].
  destruct Hobj_b as [Hb_in_P Hb_max].
  specialize (Ha_max b Hb_in_P).  (* f b ≤ f a *)
  specialize (Hb_max a Ha_in_P).  (* f a ≤ f b *)
  apply le_antisym; auto.
Qed.

Theorem max_default_unique {A: Type}:
  forall (f: A -> T) (P: A -> Prop) default n m,
    max_value_of_subset_with_default P f default n ->
    max_value_of_subset_with_default P f default m ->
    n = m.
Proof.
  intros f P default n m Hn Hm.
  destruct Hn as [[Hmax_n Hn_ge] | [Hall_n Hn_eq]];
  destruct Hm as [[Hmax_m Hm_ge] | [Hall_m Hm_eq]]; subst.
  + pose proof max_unique _ _ _ _ Hmax_n Hmax_m; auto.
  + destruct Hmax_n as [a [[? ?] ?]].
    pose proof Hall_m _ H; subst. 
    apply le_antisym; auto.
  + destruct Hmax_m as [a [[? ?] ?]].
    pose proof Hall_n _ H; subst. 
    apply le_antisym; auto.
  + reflexivity.
Qed.

Theorem max_le {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n1 n2,
    max_value_of_subset P1 f1 n1 ->
    max_value_of_subset P2 f2 n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f1 a1 ≤ f2 a2) ->
    n1 ≤ n2.
Proof.
  intros f1 f2 P1 P2 n1 n2 Hmax1 Hmax2 Hrel.
  destruct Hmax1 as [a1 [[Ha1_in Ha1_max] Ha1_eq]].
  destruct Hmax2 as [a2 [[Ha2_in Ha2_max] Ha2_eq]].
  subst n1 n2.
  specialize (Hrel a1 Ha1_in).
  destruct Hrel as [a2' [Ha2'_in Hle]].
  specialize (Ha2_max a2' Ha2'_in).
  eapply le_trans; eauto.
Qed.

Theorem max_default_le {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n1 n2,
    max_value_of_subset_with_default P1 f1 default n1 ->
    max_value_of_subset_with_default P2 f2 default n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f1 a1 ≤ f2 a2) ->
    n1 ≤ n2.
Proof.
  intros f1 f2 P1 P2 default n1 n2 Hmax1 Hmax2 Hrel.
  destruct Hmax1 as [[Hmax_n1 Hn1_ge] | [Hall_n1 Hn1_eq]];
  destruct Hmax2 as [[Hmax_n2 Hn2_ge] | [Hall_n2 Hn2_eq]]; subst.
  + apply (max_le f1 f2 P1 P2); auto.
  + destruct Hmax_n1 as [a1 [[Ha1_in _] Hfa1_eq]].
    subst.
    specialize (Hrel a1 Ha1_in) as [a2 [Ha2_in Hle]].
    specialize (Hall_n2 a2 Ha2_in).
    eapply le_trans; eauto.
  + auto.
  + apply le_refl.
Qed.

Theorem max_eq {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n1 n2,
    max_value_of_subset P1 f1 n1 ->
    max_value_of_subset P2 f2 n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f1 a1 ≤ f2 a2) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f2 a2 ≤ f1 a1) ->
    n1 = n2.
Proof.
  intros f1 f2 P1 P2 n1 n2 Hmax1 Hmax2 Hrel12 Hrel21.
  assert (Hle1: n1 ≤ n2).
  { apply (max_le f1 f2 P1 P2); auto. }
  assert (Hle2: n2 ≤ n1).
  { apply (max_le f2 f1 P2 P1); auto. }
  apply le_antisym; auto.
Qed.

Theorem max_default_eq {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n1 n2,
    max_value_of_subset_with_default P1 f1 default n1 ->
    max_value_of_subset_with_default P2 f2 default n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f1 a1 ≤ f2 a2) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f2 a2 ≤ f1 a1) ->
    n1 = n2.
Proof.
  intros f1 f2 P1 P2 default n1 n2 Hmax1 Hmax2 Hrel12 Hrel21.
  assert (Hle1: n1 ≤ n2).
  { apply (max_default_le f1 f2 P1 P2 default); auto. }
  assert (Hle2: n2 ≤ n1).
  { apply (max_default_le f2 f1 P2 P1 default); auto. }
  apply le_antisym; auto.
Qed.

Theorem max_eq_forward' {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n,
    max_value_of_subset P1 f1 n ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f1 a1 ≤ f2 a2) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f2 a2 ≤ f1 a1) ->
    max_value_of_subset P2 f2 n.
Proof.
  intros f1 f2 P1 P2 n Hmax1 Hrel12 Hrel21.
  destruct Hmax1 as [a [[Ha_in Ha_max] Hfa_eq]].
  subst n.
  specialize (Hrel12 a Ha_in) as [a2 [Ha2_in Hle]].
  exists a2.
  split.
  - unfold max_object_of_subset.
    split.
    + exact Ha2_in.
    + intros b Hb_in.
      specialize (Hrel21 b Hb_in) as [a1 [Ha1_in Hle2]].
      specialize (Ha_max a1 Ha1_in).
      do 2 (eapply le_trans; eauto).
  - specialize (Hrel21 a2 Ha2_in) as [a1' [Ha1'_in Hle2]].
    specialize (Ha_max a1' Ha1'_in).
    apply le_antisym; auto. 
    eapply le_trans; eauto.
Qed.

Theorem max_eq_forward {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n,
    max_value_of_subset P1 f1 n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ f1 a1 ≤ f2 a2) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ f2 a2 ≤ f1 a1) ->
    max_value_of_subset P2 f2 n.
Proof. exact max_eq_forward'. Qed.

Theorem max_default_eq_forward' {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n,
    max_value_of_subset_with_default P1 f1 default n ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f1 a1 ≤ f2 a2) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f2 a2 ≤ f1 a1) ->
    max_value_of_subset_with_default P2 f2 default n.
Proof.
  intros f1 f2 P1 P2 default n Hmax1 Hrel12 Hrel21.
  destruct Hmax1 as [[Hmax_n1 Hn_ge] | [Hall_n1 Hn_eq]].
  - left.
    split.
    + apply (max_eq_forward' f1 f2 P1 P2); auto.
    + exact Hn_ge.
  - right.
    split; [| exact Hn_eq].
    intros a2 Ha2_in.
    specialize (Hrel21 a2 Ha2_in) as [a1 [Ha1_in Hle]].
    specialize (Hall_n1 a1 Ha1_in). 
    eapply le_trans; eauto.
Qed.

Theorem max_default_eq_forward {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n,
    max_value_of_subset_with_default P1 f1 default n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ f1 a1 ≤ f2 a2) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ f2 a2 ≤ f1 a1) ->
    max_value_of_subset_with_default P2 f2 default n.
Proof. exact max_default_eq_forward'. Qed.

Theorem max_mono_incr_bind' {A: Type}:
  forall (f: A -> T) (g: T -> T) (P: A -> Prop) n,
    max_value_of_subset P f n ->
    (forall n1 n2, n1 ≤ n2 -> g n1 ≤ g n2) ->
    max_value_of_subset P (fun a => g (f a)) (g n).
Proof.
  intros f g P n Hmax Hg_mono.
  destruct Hmax as [a [[Ha_in Ha_max] Hfa_eq]].
  subst n.
  exists a.
  split.
  - unfold max_object_of_subset.
    split.
    + exact Ha_in.
    + intros b Hb_in.
      specialize (Ha_max b Hb_in).
      apply Hg_mono; auto.
  - reflexivity.
Qed.

Theorem max_mono_incr_bind {A: Type}:
  forall (h: T -> T) (f g: A -> T) (P: A -> Prop) n m,
    max_value_of_subset P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, n1 ≤ n2 -> h n1 ≤ h n2) ->
    m = h n ->
    max_value_of_subset P g m.
Proof.
  intros h f g P n m Hmax Hg_def Hh_mono Hm_eq.
  subst m.
  pose proof max_mono_incr_bind' f h P n Hmax Hh_mono. 
  destruct H as [? []]. 
  exists x; split.
  - destruct H. 
    split; auto. 
    intros. 
    do 2 rewrite Hg_def. 
    eapply le_trans; eauto. 
  - rewrite Hg_def. auto.
Qed.

Theorem max_object_union_left {A: Type}:
  forall a (f: A -> T) (P Q: A -> Prop) n,
    max_object_of_subset P f a ->
    (forall b, b ∈ Q -> f b ≤ n) ->
    n ≤ f a ->
    max_object_of_subset (P ∪ Q) f a.
Proof.
  intros.
  unfold max_object_of_subset.
  Sets_unfold.
  split.
  + pose proof max_object_legal _ _ _ H.
    left; tauto.
  + intros.
    destruct H2.
    - pose proof max_object_sound _ _ _ H _ H2.
      auto.
    - eapply le_trans; eauto.
Qed.

Theorem max_object_union1 {A: Type}:
  forall a b (f: A -> T) (P Q: A -> Prop),
    max_object_of_subset P f a ->
    max_object_of_subset Q f b ->
    f b ≤ f a ->
    max_object_of_subset (P ∪ Q) f a.
Proof.
  intros.
  pose proof max_object_sound _ _ _ H0.
  pose proof max_object_union_left _ _ _ _ _ H H2 H1.
  tauto.
Qed.

Theorem max_object_union_right {A: Type}:
  forall a (f: A -> T) (P Q: A -> Prop) n,
    (forall b, b ∈ P -> f b ≤ n) ->
    max_object_of_subset Q f a ->
    n ≤ f a ->
    max_object_of_subset (P ∪ Q) f a.
Proof.
  intros.
  unfold max_object_of_subset.
  Sets_unfold.
  split.
  + pose proof max_object_legal _ _ _ H0.
    right; tauto.
  + intros.
    destruct H2.
    - pose proof H _ H2.
      eapply le_trans; eauto.
    - pose proof max_object_sound _ _ _ H0 _ H2.
      auto.
Qed.

Theorem max_object_union2 {A: Type}:
  forall a b (f: A -> T) (P Q: A -> Prop),
    max_object_of_subset P f a ->
    max_object_of_subset Q f b ->
    f a ≤ f b ->
    max_object_of_subset (P ∪ Q) f b.
Proof.
  intros.
  pose proof max_object_sound _ _ _ H.
  pose proof max_object_union_right _ _ _ _ _ H2 H0 H1.
  tauto.
Qed.

Theorem max_object_union {A: Type}:
  forall a b (f: A -> T) (P Q: A -> Prop),
    max_object_of_subset P f a ->
    max_object_of_subset Q f b ->
    max_object_of_subset (P ∪ Q) f a \/
    max_object_of_subset (P ∪ Q) f b.
Proof.
  intros.
  pose proof le_total (f a) (f b).
  destruct H1; [right | left].
  + pose proof max_object_union2 a b _ _ _ H H0 ltac:(auto).
    tauto.
  + pose proof max_object_union1 a b _ _ _ H H0 ltac:(auto).
    tauto.
Qed.

Theorem max_union' {A: Type}:
  forall n m (f: A -> T) (P Q: A -> Prop),
    max_value_of_subset P f n ->
    max_value_of_subset Q f m ->
    max_value_of_subset (P ∪ Q) f (le_max n m).
Proof.
  intros. 
  destruct H as [a [? ?] ], H0 as [b [? ?] ].
  subst n m.
  pose proof le_total (f a) (f b).
  destruct H1.
  + pose proof max_object_union2 a b _ _ _ H H0 ltac:(auto).
    rewrite (max_r _ _ l).
    exists b.
    tauto.
  + pose proof max_object_union1 a b _ _ _ H H0 ltac:(auto).
    rewrite (max_l _ _ l).
    exists a.
    tauto.
Qed.

Theorem max_union {A: Type}:
  forall n m (f: A -> T) (P Q R: A -> Prop),
    max_value_of_subset P f n ->
    max_value_of_subset Q f m ->
    (forall a, P a \/ Q a <-> R a) ->
    max_value_of_subset R f (le_max n m).
Proof.
  intros.
  assert (P ∪ Q == R). {
    sets_unfold.
    apply H1.
  }
  rewrite <- H2.
  apply max_union'; tauto.
Qed.

Theorem max_default_union' {A: Type}:
  forall n m (f: A -> T) (P Q: A -> Prop) default,
    max_value_of_subset_with_default P f default n ->
    max_value_of_subset_with_default Q f default m ->
    max_value_of_subset_with_default (P ∪ Q) f default (le_max n m).
Proof.
  intros.
  destruct H as [ [? ?] | ? ], H0 as [ [? ?] | ?].
  + pose proof max_union' _ _ _ _ _ H H0.
    left.
    split; [tauto | auto]. 
    destruct (le_total n m); 
    [rewrite (max_r _ _ l) | rewrite (max_l _ _ l)]; auto.
  + rewrite (max_l n m ltac:(destruct H0; subst; auto)).
    destruct H0 as [? _].
    destruct H as [a [? ?] ].
    pose proof max_object_union_left _ _ _ _ _ H H0 
    ltac:(subst; eapply le_trans; try apply le_refl; eauto).
    left; split; [| auto].
    exists a.
    tauto.
  + rewrite (max_r n m ltac:(destruct H; subst; auto)).
    destruct H as [? _].
    destruct H0 as [a [? ?] ].
    pose proof max_object_union_right _ _ _ _ _ H H0 
    ltac:(subst; eapply le_trans; try apply le_refl; eauto).
    left; split; [| auto].
    exists a.
    tauto.
  + right.
    split; [| destruct H, H0; subst; rewrite max_r; try apply le_refl; auto ].
    destruct H as [? _], H0 as [? _].
    intros.
    Sets_unfold in H1.
    destruct H1.
    - pose proof H _ H1.
      tauto.
    - pose proof H0 _ H1.
      tauto.
Qed.

Theorem max_default_union {A: Type}:
  forall n m (f: A -> T) (P Q R: A -> Prop) default,
    max_value_of_subset_with_default P f default n ->
    max_value_of_subset_with_default Q f default m ->
    (forall a, P a \/ Q a <-> R a) ->
    max_value_of_subset_with_default R f default (le_max n m).
Proof.
  intros.
  assert (P ∪ Q == R). {
    sets_unfold.
    apply H1.
  }
  rewrite <- H2.
  apply max_default_union'; tauto.
Qed.

Theorem max_object_1 {A: Type}:
  forall a (f: A -> T),
    max_object_of_subset (Sets.singleton a) f a.
Proof.
  intros.
  unfold max_object_of_subset.
  sets_unfold.
  split; [reflexivity |].
  intros; subst.
  apply le_refl.
Qed.

Theorem max_empty {A: Type}:
  forall (f: A -> T),
    max_value_of_subset ∅ f == ∅.
Proof.
  intros f. 
  split; [intros H|intros; tauto].
  destruct H as [n [[Ha_in _] _]].
  tauto.
Qed.

Theorem max_1' {A: Type}:
  forall a (f: A -> T),
    max_value_of_subset (Sets.singleton a) f (f a).
Proof.
  intros.
  unfold max_value_of_subset.
  exists a.
  pose proof max_object_1 a f.
  tauto.
Qed.

Theorem max_1 {A: Type}:
  forall a (P: A -> Prop) (f: A -> T),
    (forall a0, P a0 <-> a = a0) ->
    max_value_of_subset P f (f a).
Proof.
  intros.
  assert (P == Sets.singleton a). {
    sets_unfold.
    tauto.
  }
  rewrite H0.
  apply max_1'.
Qed.

Theorem max_singleton {A: Type}:
  forall a (f: A -> T),
    max_value_of_subset (Sets.singleton a) f == [(f a)].
Proof.
  intros. 
  split; intros. 
  - destruct H as [? [[]]]. 
    sets_unfold in H; subst. 
    reflexivity. 
  - sets_unfold in H; rewrite <- H. 
    apply max_1'.
Qed.

Theorem max_default_1 {A: Type}:
  forall a (f: A -> T) default,
    max_value_of_subset_with_default (Sets.singleton a) f default (le_max (f a) default).
Proof.
  intros.
  unfold max_value_of_subset_with_default.
  destruct (le_total (f a) default).
  + right.
    split; [| auto].
    sets_unfold.
    intros; subst; auto. 
    rewrite max_r; auto.
  + left.
    split; [| auto].
    rewrite max_l by auto.
    apply max_1'. 
    rewrite max_l; auto.
Qed.

Theorem max_union_1_right' {A: Type}:
  forall n a (f: A -> T) (P: A -> Prop),
    max_value_of_subset P f n ->
    max_value_of_subset (P ∪ Sets.singleton a) f (le_max n (f a)).
Proof.
  intros.
  apply max_union'.
  + tauto.
  + apply max_1'.
Qed.

Theorem max_union_1_right {A: Type}:
  forall n m a (f: A -> T) (P Q: A -> Prop),
    max_value_of_subset P f n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    max_value_of_subset Q f (le_max n (f a)).
Proof.
  intros.
  subst.
  assert (Q == P ∪ Sets.singleton a). {
    sets_unfold.
    tauto.
  }
  rewrite H0.
  apply max_union_1_right'.
  tauto.
Qed.

Theorem max_default_union_1_right' {A: Type}:
  forall n a (f: A -> T) (P: A -> Prop) default,
    max_value_of_subset_with_default P f default n ->
    max_value_of_subset_with_default (P ∪ Sets.singleton a) f default (le_max n (f a)).
Proof.
  intros.
  pose proof max_default_ge_default _ _ _ _ H.
  replace (le_max n (f a)) with (le_max n (le_max (f a) default)).
  apply max_default_union'.
  + tauto.
  + apply max_default_1.
  + destruct (le_total (f a) default). 
    - rewrite (max_r _ _ l). 
      rewrite (max_l _ _ H0). 
      rewrite (max_l _ _ ltac:(eapply le_trans; eauto)). 
      reflexivity. 
    - rewrite (max_l _ _ l). 
      reflexivity. 
Qed.

Theorem max_default_union_1_right {A: Type}:
  forall n m a (f: A -> T) (P Q: A -> Prop) default,
    max_value_of_subset_with_default P f default n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    max_value_of_subset_with_default Q f default (le_max n m).
Proof.
  intros.
  subst.
  assert (Q == P ∪ Sets.singleton a). {
    sets_unfold.
    tauto.
  }
  rewrite H0.
  apply max_default_union_1_right'.
  tauto.
Qed.

Theorem max_default_default_inv {A: Type}:
  forall n (f: A -> T) (P: A -> Prop) default,
    max_value_of_subset_with_default P f default n ->
    P == ∅ ->
    n = default.
Proof.
  intros.
  destruct H as [ [ [a ?] _] | ?]; [ | auto].
  destruct H.
  destruct H.
  sets_unfold in H0.
  pose proof H0 a; tauto.
  destruct H; auto.
Qed.

Theorem max_default_default' {A: Type}:
  forall (f: A -> T) (P: A -> Prop) default,
    P == ∅ ->
    max_value_of_subset_with_default P f default default.
Proof.
  intros.
  right.
  split; [ | reflexivity].
  intros.
  sets_unfold in H.
  pose proof H a.
  tauto.
Qed.

Theorem max_default_default {A: Type}:
  forall (f: A -> T) (P: A -> Prop) default,
    (forall a, ~ P a) ->
    max_value_of_subset_with_default P f default default.
Proof.
  intros.
  apply max_default_default'.
  sets_unfold.
  intros a; pose proof H a; tauto.
Qed.

Definition min_object_of_subset
             {A: Type}
             (X: A -> Prop)
             (f: A -> T)
             (a: A): Prop :=
  a ∈ X /\ forall b, b ∈ X -> f a ≤ f b.

Definition min_value_of_subset
             {A: Type}
             (X: A -> Prop)
             (f: A -> T)
             (n: T): Prop :=
  (exists a, min_object_of_subset X f a /\ f a = n). 

Definition min_value_of_subset_with_default
             {A: Type}
             (X: A -> Prop)
             (f: A -> T)
             (default: T)
             (n: T): Prop :=
  (min_value_of_subset X f n /\ n ≤ default) \/
  ((forall a, a ∈ X -> default ≤ f a) /\ n = default).

Notation "a 'is-the-min-of' e 'in-which' x 'satisfies' P" :=
  (min_value_of_subset (fun x => P) (fun x => e) a)
  (at level 1, no associativity).

Notation "a 'is-the-min-of' e 'in-which' ' pat 'satisfies' P" :=
  (min_value_of_subset (fun xx => match xx with pat => P end) (fun xx => match xx with pat => e end) a)
  (at level 1, pat pattern, no associativity).

Notation "a 'is-the-min-of' e 'in-which' x 'satisfies' P 'with-default' default" :=
  (min_value_of_subset_with_default (fun x => P) (fun x => e) default a)
  (at level 1, no associativity).

Notation "a 'is-the-min-of' e 'in-which' ' pat 'satisfies' P 'with-default' default" :=
  (min_value_of_subset_with_default (fun xx => match xx with pat => P end) (fun xx => match xx with pat => e end) default a)
  (at level 1, pat pattern, no associativity).

Lemma min_object_sound {A: Type}:
  forall (f: A -> T) (P: A -> Prop) (a: A),
    min_object_of_subset P f a ->
    (forall b: A, b ∈ P -> f a ≤ f b).
Proof. intros f P a [? ?]. tauto. Qed.

Lemma min_object_legal {A: Type}:
  forall (f: A -> T) (P: A -> Prop) (a: A),
    min_object_of_subset P f a ->
    a ∈ P.
Proof. intros f P a [? ?]. tauto. Qed.

Lemma min_default_le_default {A: Type}:
  forall n (f: A -> T) (P: A -> Prop) default,
    min_value_of_subset_with_default P f default n ->
    n ≤ default.
Proof. intros. destruct H as [[? ?]|[? ?]]; [auto | subst; apply le_refl]. Qed.  

#[export] Instance min_object_of_subset_congr {A: Type}:
  Proper
    (Sets.equiv ==> eq ==> eq ==> iff)
    (@min_object_of_subset A).
Proof.
  unfold Proper, respectful.
  intros.
  unfold min_object_of_subset.
  subst.
  rewrite H.
  apply Morphisms_Prop.and_iff_morphism; [reflexivity |].
  apply Morphisms_Prop.all_iff_morphism; intros ?.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance min_value_of_subset_congr {A: Type}:
  Proper
    (Sets.equiv ==> eq ==> eq ==> iff)
    (@min_value_of_subset A).
Proof.
  unfold Proper, respectful.
  intros.
  unfold min_value_of_subset.
  apply Morphisms_Prop.ex_iff_morphism; intros ?.
  rewrite H.
  subst.
  reflexivity.
Qed. 

#[export] Instance min_value_of_subset_with_default_congr {A: Type}:
  Proper
    (Sets.equiv ==> eq ==> eq ==> eq ==> iff)
    (@min_value_of_subset_with_default A).
Proof.
  unfold Proper, respectful.
  intros.
  unfold min_value_of_subset_with_default.
  subst.
  rewrite H.
  apply Morphisms_Prop.or_iff_morphism; [reflexivity |].
  apply Morphisms_Prop.and_iff_morphism; [| reflexivity].
  apply Morphisms_Prop.all_iff_morphism; intros ?.
  rewrite H.
  reflexivity.
Qed.

Theorem min_unique {A: Type}:
  forall (f: A -> T) (P: A -> Prop) n m,
    min_value_of_subset P f n ->
    min_value_of_subset P f m ->
    n = m.
Proof.
  intros f P n m Hn Hm.
  destruct Hn as [a [Hobj_a Hfa_eq]].
  destruct Hm as [b [Hobj_b Hfb_eq]].
  subst n m.
  destruct Hobj_a as [Ha_in_P Ha_min].
  destruct Hobj_b as [Hb_in_P Hb_min].
  specialize (Ha_min b Hb_in_P).  (* f a ≤ f b *)
  specialize (Hb_min a Ha_in_P).  (* f b ≤ f a *)
  apply le_antisym; auto.
Qed.

Theorem min_default_unique {A: Type}:
  forall (f: A -> T) (P: A -> Prop) default n m,
    min_value_of_subset_with_default P f default n ->
    min_value_of_subset_with_default P f default m ->
    n = m.
Proof.
  intros f P default n m Hn Hm.
  destruct Hn as [[Hmin_n Hn_le] | [Hall_n Hn_eq]];
  destruct Hm as [[Hmin_m Hm_le] | [Hall_m Hm_eq]]; subst.
  + pose proof min_unique _ _ _ _ Hmin_n Hmin_m.
    auto.
  + destruct Hmin_n as [a [[? ?] ?]].
    pose proof Hall_m _ H; subst. 
    apply le_antisym; auto.
  + destruct Hmin_m as [a [[? ?] ?]].
    pose proof Hall_n _ H; subst. 
    apply le_antisym; auto.
  + reflexivity.
Qed.

Theorem min_le {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n1 n2,
    min_value_of_subset P1 f1 n1 ->
    min_value_of_subset P2 f2 n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f2 a2 ≤ f1 a1) ->
    n2 ≤ n1.
Proof.
  intros f1 f2 P1 P2 n1 n2 Hmin1 Hmin2 Hrel.
  destruct Hmin1 as [a1 [[Ha1_in Ha1_min] Ha1_eq]].
  destruct Hmin2 as [a2 [[Ha2_in Ha2_min] Ha2_eq]].
  subst n1 n2.
  specialize (Hrel a1 Ha1_in).
  destruct Hrel as [a2' [Ha2'_in Hle]].
  specialize (Ha2_min a2' Ha2'_in).
  eapply le_trans; eauto.
Qed.

Theorem min_default_le {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n1 n2,
    min_value_of_subset_with_default P1 f1 default n1 ->
    min_value_of_subset_with_default P2 f2 default n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f2 a2 ≤ f1 a1) ->
    n2 ≤ n1.
Proof.
  intros f1 f2 P1 P2 default n1 n2 Hmin1 Hmin2 Hrel.
  destruct Hmin1 as [[Hmin_n1 Hn1_le] | [Hall_n1 Hn1_eq]];
  destruct Hmin2 as [[Hmin_n2 Hn2_le] | [Hall_n2 Hn2_eq]]; subst.
  + apply (min_le f1 f2 P1 P2); auto.
  + destruct Hmin_n1 as [a1 [[Ha1_in _] Hfa1_eq]].
    subst.
    specialize (Hrel a1 Ha1_in) as [a2 [Ha2_in Hle]].
    specialize (Hall_n2 a2 Ha2_in).
    eapply le_trans; eauto.
  + auto.
  + apply le_refl.
Qed.

Theorem min_eq {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n1 n2,
    min_value_of_subset P1 f1 n1 ->
    min_value_of_subset P2 f2 n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f2 a2 ≤ f1 a1) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f1 a1 ≤ f2 a2) ->
    n1 = n2.
Proof.
  intros f1 f2 P1 P2 n1 n2 Hmin1 Hmin2 Hrel12 Hrel21.
  assert (Hle1: n2 ≤ n1).
  { apply (min_le f1 f2 P1 P2); auto. }
  assert (Hle2: n1 ≤ n2).
  { apply (min_le f2 f1 P2 P1); auto. }
  apply le_antisym; auto.
Qed.

Theorem min_default_eq {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n1 n2,
    min_value_of_subset_with_default P1 f1 default n1 ->
    min_value_of_subset_with_default P2 f2 default n2 ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f2 a2 ≤ f1 a1) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f1 a1 ≤ f2 a2) ->
    n1 = n2.
Proof.
  intros f1 f2 P1 P2 default n1 n2 Hmin1 Hmin2 Hrel12 Hrel21.
  assert (Hle1: n2 ≤ n1).
  { apply (min_default_le f1 f2 P1 P2 default); auto. }
  assert (Hle2: n1 ≤ n2).
  { apply (min_default_le f2 f1 P2 P1 default); auto. }
  apply le_antisym; auto.
Qed.

Theorem min_eq_forward' {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n,
    min_value_of_subset P1 f1 n ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f2 a2 ≤ f1 a1) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f1 a1 ≤ f2 a2) ->
    min_value_of_subset P2 f2 n.
Proof.
  intros f1 f2 P1 P2 n Hmin1 Hrel12 Hrel21.
  destruct Hmin1 as [a [[Ha_in Ha_min] Hfa_eq]].
  subst n.
  specialize (Hrel12 a Ha_in) as [a2 [Ha2_in Hle]].
  exists a2.
  split.
  - unfold min_object_of_subset.
    split.
    + exact Ha2_in.
    + intros b Hb_in.
      specialize (Hrel21 b Hb_in) as [a1 [Ha1_in Hle2]].
      specialize (Ha_min a1 Ha1_in).
      eapply le_trans; eauto.
      eapply le_trans; eauto.
  - specialize (Hrel21 a2 Ha2_in) as [a1' [Ha1'_in Hle2]].
    specialize (Ha_min a1' Ha1'_in).
    apply le_antisym; auto.
    eapply le_trans; eauto.
Qed.

Theorem min_eq_forward {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) n,
    min_value_of_subset P1 f1 n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ f2 a2 ≤ f1 a1) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ f1 a1 ≤ f2 a2) ->
    min_value_of_subset P2 f2 n.
Proof. exact min_eq_forward'. Qed.

Theorem min_default_eq_forward' {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n,
    min_value_of_subset_with_default P1 f1 default n ->
    (forall a1, a1 ∈ P1 -> exists a2, a2 ∈ P2 /\ f2 a2 ≤ f1 a1) ->
    (forall a2, a2 ∈ P2 -> exists a1, a1 ∈ P1 /\ f1 a1 ≤ f2 a2) ->
    min_value_of_subset_with_default P2 f2 default n.
Proof.
  intros f1 f2 P1 P2 default n Hmin1 Hrel12 Hrel21.
  destruct Hmin1 as [[Hmin_n1 Hn_le] | [Hall_n1 Hn_eq]].
  - left.
    split.
    + apply (min_eq_forward' f1 f2 P1 P2); auto.
    + exact Hn_le.
  - right.
    split; [| exact Hn_eq].
    intros a2 Ha2_in.
    specialize (Hrel21 a2 Ha2_in) as [a1 [Ha1_in Hle]].
    specialize (Hall_n1 a1 Ha1_in).
    eapply le_trans; eauto.
Qed.

Theorem min_default_eq_forward {A: Type}:
  forall (f1 f2: A -> T) (P1 P2: A -> Prop) default n,
    min_value_of_subset_with_default P1 f1 default n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ f2 a2 ≤ f1 a1) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ f1 a1 ≤ f2 a2) ->
    min_value_of_subset_with_default P2 f2 default n.
Proof. exact min_default_eq_forward'. Qed.

Theorem min_mono_incr_bind' {A: Type}:
  forall (f: A -> T) (g: T -> T) (P: A -> Prop) n,
    min_value_of_subset P f n ->
    (forall n1 n2, n1 ≤ n2 -> g n1 ≤ g n2) ->
    min_value_of_subset P (fun a => g (f a)) (g n).
Proof.
  intros f g P n Hmin Hg_mono.
  destruct Hmin as [a [[Ha_in Ha_min] Hfa_eq]].
  subst n.
  exists a.
  split.
  - unfold min_object_of_subset.
    split.
    + exact Ha_in.
    + intros b Hb_in.
      specialize (Ha_min b Hb_in).
      apply Hg_mono; auto.
  - reflexivity.
Qed.

Theorem min_mono_incr_bind {A: Type}:
  forall (h: T -> T) (f g: A -> T) (P: A -> Prop) n m,
    min_value_of_subset P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, n1 ≤ n2 -> h n1 ≤ h n2) ->
    m = h n ->
    min_value_of_subset P g m.
Proof.
  intros h f g P n m Hmin Hg_def Hh_mono Hm_eq.
  subst m.
  pose proof min_mono_incr_bind' f h P n Hmin Hh_mono.
  destruct H as [? []].
  exists x; split.
  - destruct H.
    split; auto.
    intros.
    do 2 rewrite Hg_def.
    apply H1; auto.
  - rewrite Hg_def. auto.
Qed.

Theorem min_object_union_left {A: Type}:
  forall a (f: A -> T) (P Q: A -> Prop) n,
    min_object_of_subset P f a ->
    (forall b, b ∈ Q -> n ≤ f b) ->
    f a ≤ n ->
    min_object_of_subset (P ∪ Q) f a.
Proof.
  intros.
  unfold min_object_of_subset.
  Sets_unfold.
  split.
  + pose proof min_object_legal _ _ _ H.
    left; tauto.
  + intros.
    destruct H2.
    - pose proof min_object_sound _ _ _ H _ H2.
      eapply le_trans; eauto.
      apply le_refl.
    - pose proof H0 _ H2.
      eapply le_trans; eauto.
Qed.

Theorem min_object_union1 {A: Type}:
  forall a b (f: A -> T) (P Q: A -> Prop),
    min_object_of_subset P f a ->
    min_object_of_subset Q f b ->
    f a ≤ f b ->
    min_object_of_subset (P ∪ Q) f a.
Proof.
  intros.
  pose proof min_object_sound _ _ _ H0.
  pose proof min_object_union_left _ _ _ _ _ H H2 H1.
  tauto.
Qed.

Theorem min_object_union_right {A: Type}:
  forall a (f: A -> T) (P Q: A -> Prop) n,
    (forall b, b ∈ P -> n ≤ f b) ->
    min_object_of_subset Q f a ->
    f a ≤ n ->
    min_object_of_subset (P ∪ Q) f a.
Proof.
  intros.
  unfold min_object_of_subset.
  Sets_unfold.
  split.
  + pose proof min_object_legal _ _ _ H0.
    right; tauto.
  + intros.
    destruct H2.
    - pose proof H _ H2.
      eapply le_trans; eauto.
    - pose proof min_object_sound _ _ _ H0 _ H2.
      eapply le_trans; eauto.
      apply le_refl.
Qed.

Theorem min_object_union2 {A: Type}:
  forall a b (f: A -> T) (P Q: A -> Prop),
    min_object_of_subset P f a ->
    min_object_of_subset Q f b ->
    f b ≤ f a ->
    min_object_of_subset (P ∪ Q) f b.
Proof.
  intros.
  pose proof min_object_sound _ _ _ H.
  pose proof min_object_union_right _ _ _ _ _ H2 H0 H1.
  tauto.
Qed.

Theorem min_object_union {A: Type}:
  forall a b (f: A -> T) (P Q: A -> Prop),
    min_object_of_subset P f a ->
    min_object_of_subset Q f b ->
    min_object_of_subset (P ∪ Q) f a \/
    min_object_of_subset (P ∪ Q) f b.
Proof.
  intros.
  pose proof le_total_cases (f a) (f b).
  destruct H1; [left | right].
  + pose proof min_object_union1 a b _ _ _ H H0 ltac:(auto).
    tauto.
  + pose proof min_object_union2 a b _ _ _ H H0 ltac:(auto).
    tauto.
Qed.

Theorem min_union' {A: Type}:
  forall n m (f: A -> T) (P Q: A -> Prop),
    min_value_of_subset P f n ->
    min_value_of_subset Q f m ->
    min_value_of_subset (P ∪ Q) f (le_min n m).
Proof.
  intros.
  destruct H as [a [? ?] ], H0 as [b [? ?] ].
  subst n m.
  pose proof le_total (f a) (f b).
  destruct H1.
  + pose proof min_object_union1 a b _ _ _ H H0 ltac:(auto).
    rewrite (min_r _ _ l).
    exists a.
    tauto.
  + pose proof min_object_union2 a b _ _ _ H H0 ltac:(auto).
    rewrite (min_l _ _ l).
    exists b.
    tauto.
Qed.

Theorem min_union {A: Type}:
  forall n m (f: A -> T) (P Q R: A -> Prop),
    min_value_of_subset P f n ->
    min_value_of_subset Q f m ->
    (forall a, P a \/ Q a <-> R a) ->
    min_value_of_subset R f (le_min n m).
Proof.
  intros.
  assert (P ∪ Q == R). {
    sets_unfold.
    apply H1.
  }
  rewrite <- H2.
  apply min_union'; tauto.
Qed.

Theorem min_default_union' {A: Type}:
  forall n m (f: A -> T) (P Q: A -> Prop) default,
    min_value_of_subset_with_default P f default n ->
    min_value_of_subset_with_default Q f default m ->
    min_value_of_subset_with_default (P ∪ Q) f default (le_min n m). 
Proof.
  intros.
  destruct H as [ [? ?] | ? ], H0 as [ [? ?] | ?].
  + pose proof min_union' _ _ _ _ _ H H0.
    left.
    split; [tauto | auto]. 
    destruct (le_total n m); 
    [rewrite (min_r _ _ l) | rewrite (min_l _ _ l)]; auto.
  + rewrite (min_r n m ltac:(destruct H0; subst; auto)).
    destruct H0 as [? _].
    destruct H as [a [? ?] ].
    pose proof min_object_union_left _ _ _ _ _ H H0 
    ltac:(subst; eapply le_trans; try apply le_refl; eauto).
    left; split; [| auto].
    exists a.
    tauto.
  + rewrite (min_l n m ltac:(destruct H; subst; auto)).
    destruct H as [? _].
    destruct H0 as [a [? ?] ].
    pose proof min_object_union_right _ _ _ _ _ H H0 
    ltac:(subst; eapply le_trans; try apply le_refl; eauto).
    left; split; [| auto].
    exists a.
    tauto.
  + right.
    split; [| destruct H, H0; subst; rewrite min_l; try apply le_refl; auto ].
    destruct H as [? _], H0 as [? _].
    intros.
    Sets_unfold in H1.
    destruct H1.
    - pose proof H _ H1.
      tauto.
    - pose proof H0 _ H1.
      tauto.
Qed.

Theorem min_default_union {A: Type}:
  forall n m (f: A -> T) (P Q R: A -> Prop) default,
    min_value_of_subset_with_default P f default n ->
    min_value_of_subset_with_default Q f default m ->
    (forall a, P a \/ Q a <-> R a) ->
    min_value_of_subset_with_default R f default (le_min n m).
Proof.
  intros.
  assert (P ∪ Q == R). {
    sets_unfold.
    apply H1.
  }
  rewrite <- H2.
  apply min_default_union'; tauto.
Qed.

Theorem min_object_1 {A: Type}:
  forall a (f: A -> T),
    min_object_of_subset (Sets.singleton a) f a.
Proof.
  intros.
  unfold min_object_of_subset.
  sets_unfold.
  split; [reflexivity |].
  intros; subst.
  apply le_refl.
Qed.

Theorem min_empty {A: Type}:
  forall (f: A -> T),
    min_value_of_subset ∅ f == ∅.
Proof.
  intros f. 
  split; [intros H|intros; tauto].
  destruct H as [n [[Ha_in _] _]].
  tauto.
Qed. 


Theorem min_1' {A: Type}:
  forall a (f: A -> T),
    min_value_of_subset (Sets.singleton a) f (f a).
Proof.
  intros.
  unfold min_value_of_subset.
  exists a.
  pose proof min_object_1 a f.
  tauto.
Qed.

Theorem min_1 {A: Type}:
  forall a (P: A -> Prop) (f: A -> T),
    (forall a0, P a0 <-> a = a0) ->
    min_value_of_subset P f (f a).
Proof.
  intros.
  assert (P == Sets.singleton a). {
    sets_unfold.
    tauto.
  }
  rewrite H0.
  apply min_1'.
Qed.

Theorem min_singleton {A: Type}:
  forall a (f: A -> T),
    min_value_of_subset (Sets.singleton a) f == [(f a)].
Proof.
  intros. 
  split; intros. 
  - destruct H as [? [[]]]. 
    sets_unfold in H; subst. 
    reflexivity. 
  - sets_unfold in H; rewrite <- H. 
    apply min_1'.
Qed.

Theorem min_default_1 {A: Type}:
  forall a (f: A -> T) default,
    min_value_of_subset_with_default (Sets.singleton a) f default (le_min (f a) default).
Proof.
  intros.
  unfold min_value_of_subset_with_default.
  destruct (le_total (f a) default).
  + left.
    rewrite min_r; auto.
    split; [apply min_1' | auto].
  + right.
    rewrite min_l; auto.
    split; [| auto].
    sets_unfold.
    intros.
    subst.
    auto.
Qed.

Theorem min_union_1_right' {A: Type}:
  forall n a (f: A -> T) (P: A -> Prop),
    min_value_of_subset P f n ->
    min_value_of_subset (P ∪ Sets.singleton a) f (le_min n (f a)).
Proof.
  intros.
  apply min_union'.
  + tauto.
  + apply min_1'.
Qed.

Theorem min_union_1_right {A: Type}:
  forall n m a (f: A -> T) (P Q: A -> Prop),
    min_value_of_subset P f n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    min_value_of_subset Q f (le_min n (f a)).
Proof.
  intros.
  subst.
  assert (Q == P ∪ Sets.singleton a). {
    sets_unfold.
    tauto.
  }
  rewrite H0.
  apply min_union_1_right'.
  tauto.
Qed.

Theorem min_default_union_1_right' {A: Type}:
  forall n a (f: A -> T) (P: A -> Prop) default,
    min_value_of_subset_with_default P f default n ->
    min_value_of_subset_with_default (P ∪ Sets.singleton a) f default (le_min n (f a)).
Proof.
  intros.
  pose proof min_default_le_default _ _ _ _ H as H_le.
  assert (H_eq: le_min n (f a) = le_min n (le_min (f a) default)).
  {
    destruct (le_total (f a) default).
    - rewrite (min_r _ _ l).
      reflexivity.    
    - rewrite (min_l _ _ l).
      rewrite (min_r _ _ H_le); auto.
      rewrite (min_r n (f a)); auto.
      eapply le_trans; eauto.
  }
  rewrite H_eq.
  apply min_default_union'.
  + auto.
  + apply min_default_1.
Qed.

Theorem min_default_union_1_right {A: Type}:
  forall n m a (f: A -> T) (P Q: A -> Prop) default,
    min_value_of_subset_with_default P f default n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    min_value_of_subset_with_default Q f default (le_min n m).
Proof.
  intros.
  subst.
  assert (Q == P ∪ Sets.singleton a). {
    sets_unfold.
    tauto.
  }
  rewrite H0.
  apply min_default_union_1_right'.
  tauto.
Qed.

Theorem min_default_default_inv {A: Type}:
  forall n (f: A -> T) (P: A -> Prop) default,
    min_value_of_subset_with_default P f default n ->
    P == ∅ ->
    n = default.
Proof.
  intros.
  destruct H as [ [ [a ?] _] | ?]; [ | auto].
  destruct H.
  destruct H.
  sets_unfold in H0.
  pose proof H0 a; tauto.
  destruct H; auto.
Qed.

Theorem min_default_default' {A: Type}:
  forall (f: A -> T) (P: A -> Prop) default,
    P == ∅ ->
    min_value_of_subset_with_default P f default default.
Proof.
  intros.
  right.
  split; [ | reflexivity].
  intros.
  rewrite H in H0.
  sets_unfold in H0.
  tauto.
Qed.

Theorem min_default_default {A: Type}:
  forall (f: A -> T) (P: A -> Prop) default,
    (forall a, ~ P a) ->
    min_value_of_subset_with_default P f default default.
Proof.
  intros.
  apply min_default_default'.
  sets_unfold.
  intros a0.
  split; [intro H1; apply (H a0 H1) | tauto].
Qed.

Theorem max_mono_decr_bind' {A: Type}:
  forall (f: A -> T) (g: T -> T) (P: A -> Prop) n,
    max_value_of_subset P f n ->
    (forall n1 n2, n1 ≤ n2 -> g n2 ≤ g n1) ->
    min_value_of_subset P (fun a => g (f a)) (g n).
Proof.
  intros f g P n Hmax Hg_decr.
  destruct Hmax as [a [[Ha_in Ha_max] Hfa_eq]].
  subst n.
  exists a.
  split.
  - unfold min_object_of_subset.
    split.
    + exact Ha_in.
    + intros b Hb_in.
      specialize (Ha_max b Hb_in). 
      pose proof (Hg_decr _ _ Ha_max).
      auto.
  - reflexivity.
Qed.

Theorem max_mono_decr_bind {A: Type}:
  forall (h: T -> T) (f g: A -> T) (P: A -> Prop) n m,
    max_value_of_subset P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, n1 ≤ n2 -> h n2 ≤ h n1) ->
    m = h n ->
    min_value_of_subset P g m.
Proof.
  intros h f g P n m Hmax Hg_def Hh_decr Hm_eq.
  subst m.
  pose proof (max_mono_decr_bind' f h P n Hmax Hh_decr).
  destruct H as [? [[]]].
  exists x; split; [split|]; auto. 
  - intros. 
    apply H0 in H2. 
    rewrite! Hg_def. 
    auto. 
  - rewrite Hg_def. auto.
Qed.

Theorem min_mono_decr_bind' {A: Type}:
  forall (f: A -> T) (g: T -> T) (P: A -> Prop) n,
    min_value_of_subset P f n ->
    (forall n1 n2, n1 ≤ n2 -> g n2 ≤ g n1) ->
    max_value_of_subset P (fun a => g (f a)) (g n).
Proof.
  intros f g P n Hmin Hg_decr.
  destruct Hmin as [a [[Ha_in Ha_min] Hfa_eq]].
  subst n.
  exists a.
  split.
  - unfold max_object_of_subset.
    split.
    + exact Ha_in.
    + intros b Hb_in.
      specialize (Ha_min b Hb_in).
      apply Hg_decr; auto.
  - reflexivity.
Qed.

Theorem min_mono_decr_bind {A: Type}:
  forall (h: T -> T) (f g: A -> T) (P: A -> Prop) n m,
    min_value_of_subset P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, n1 ≤ n2 -> h n2 ≤ h n1) ->
    m = h n ->
    max_value_of_subset P g m.
Proof.
  intros h f g P n m Hmin Hg_def Hh_decr Hm_eq.
  subst m.
  pose proof (min_mono_decr_bind' f h P n Hmin Hh_decr).
  destruct H as [? [[]]].
  exists x; split; [split|]; auto. 
  - intros. 
    apply H0 in H2. 
    rewrite! Hg_def. 
    auto. 
  - rewrite Hg_def. auto.
Qed.

Lemma min_exists_union_l {A: Type}:
  forall n m (f: A -> T) (P Q: A -> Prop), 
    (exists a, P a /\ f a = n) -> 
    min_value_of_subset (P ∪ Q) f m -> 
    n ≥ m.
Proof. 
  intros. 
  destruct H as [? []]. 
  destruct H0 as [? [[]]]. 
  subst. 
  apply H2. 
  left; auto. 
Qed.

Lemma min_exists_union_r {A: Type}:
  forall n m (f: A -> T) (P Q: A -> Prop), 
    (exists a, Q a /\ f a = n) -> 
    min_value_of_subset (P ∪ Q) f m -> 
    n ≥ m.
Proof. 
  intros. 
  destruct H as [? []]. 
  destruct H0 as [? [[]]]. 
  subst. 
  apply H2. 
  right; auto. 
Qed.

End TotalOrder.

Notation "'the-max-of' e 'in-which' x 'satisfies' P" :=
  (max_value_of_subset (fun x => P) (fun x => e))
  (at level 2, no associativity).

Notation "'the-max-of' e 'in-which' ' pat 'satisfies' P" :=
  (max_value_of_subset (fun xx => match xx with pat => P end) (fun xx => match xx with pat => e end))
  (at level 2, pat pattern, no associativity).

Notation "'the-min-of' e 'in-which' x 'satisfies' P" :=
  (min_value_of_subset (fun x => P) (fun x => e))
  (at level 2, no associativity).

Notation "'the-min-of' e 'in-which' ' pat 'satisfies' P" :=
  (min_value_of_subset (fun xx => match xx with pat => P end) (fun xx => match xx with pat => e end))
  (at level 2, pat pattern, no associativity).




