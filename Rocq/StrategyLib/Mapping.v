From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.

Definition total_mapping (A : Type) := Z -> A.
Definition total_mapping_update {A : Type} (m : total_mapping A) (k : Z) (v : A) : total_mapping A :=
  fun k' => if Z.eq_dec k k' then v else m k'.

Lemma total_mapping_update_eq : forall A (m : total_mapping A) k v,
  (total_mapping_update m k v) k = v.
  intros.
  unfold total_mapping_update.
  destruct (Z.eq_dec k k).
  - reflexivity.
  - contradiction.
Qed.

Lemma total_mapping_update_neq : forall A (m : total_mapping A) k k' v,
  k <> k' -> (total_mapping_update m k v) k' = m k'.
  intros.
  unfold total_mapping_update.
  destruct (Z.eq_dec k k').
  - contradiction.
  - reflexivity.
Qed.

Lemma total_mapping_update_shadow : forall A (m : total_mapping A) k v v',
  total_mapping_update (total_mapping_update m k v) k v' = total_mapping_update m k v'.
  intros.
  apply functional_extensionality; intros.
  unfold total_mapping_update.
  destruct (Z.eq_dec k x); reflexivity.
Qed.

Lemma total_mapping_update_permute : forall A (m : total_mapping A) k k' v v',
  k <> k' -> total_mapping_update (total_mapping_update m k v) k' v' = total_mapping_update (total_mapping_update m k' v') k v.
  intros.
  apply functional_extensionality; intros.
  unfold total_mapping_update.
  destruct (Z.eq_dec k x); destruct (Z.eq_dec k' x); subst; [ contradiction | | | ]; reflexivity.
Qed.

Lemma total_mapping_update_same : forall A (m : total_mapping A) k,
  total_mapping_update m k (m k) = m.
  intros; apply functional_extensionality; intros.
  unfold total_mapping_update; simpl.
  destruct (Z.eq_dec k x); subst; reflexivity.
Qed.

Definition partial_mapping (A : Type) := Z -> option A.
Definition partial_mapping_update {A : Type} (m : partial_mapping A) (k : Z) (v : A) : partial_mapping A :=
  fun k' => if Z.eq_dec k k' then Some v else m k'.

Lemma partial_mapping_update_eq : forall A (m : partial_mapping A) k v,
  (partial_mapping_update m k v) k = Some v.
  intros.
  unfold partial_mapping_update.
  destruct (Z.eq_dec k k).
  - reflexivity.
  - contradiction.
Qed.

Lemma partial_mapping_update_neq : forall A (m : partial_mapping A) k k' v,
  k <> k' -> (partial_mapping_update m k v) k' = m k'.
  intros.
  unfold partial_mapping_update.
  destruct (Z.eq_dec k k').
  - contradiction.
  - reflexivity.
Qed.

Lemma partial_mapping_update_shadow : forall A (m : partial_mapping A) k v v',
  partial_mapping_update (partial_mapping_update m k v) k v' = partial_mapping_update m k v'.
  intros.
  apply functional_extensionality; intros.
  unfold partial_mapping_update.
  destruct (Z.eq_dec k x); reflexivity.
Qed.

Lemma partial_mapping_update_permute : forall A (m : partial_mapping A) k k' v v',
  k <> k' -> partial_mapping_update (partial_mapping_update m k v) k' v' = partial_mapping_update (partial_mapping_update m k' v') k v.
  intros.
  apply functional_extensionality; intros.
  unfold partial_mapping_update.
  destruct (Z.eq_dec k x); destruct (Z.eq_dec k' x); subst; [ contradiction | | | ]; reflexivity.
Qed.