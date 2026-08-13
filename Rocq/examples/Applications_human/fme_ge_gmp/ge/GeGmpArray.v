Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic IntLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import GeGmpMatrix GeGmpMod.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import GmpNumber GmpMul.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string.
Local Open Scope sac.

(* The QCP memory model used by this suite is 32-bit: [int] and pointers are
   both four bytes, so mini-gmp's two-int/one-pointer [__mpz_struct] occupies
   twelve bytes.  Alias sizes are otherwise opaque to Rocq; this is the one
   human-supplied ABI layout fact for the GE/GMP array representation, in the
   same style as the handwritten [PointArray] model. *)
Axiom sizeof_mpz_struct :
  sizeof_front_end_type (FET_alias "__mpz_struct") = 12.

Definition mpz_sizeof : Z := sizeof("__mpz_struct").

Lemma mpz_sizeof_eq_12 : mpz_sizeof = 12.
Proof.
  unfold mpz_sizeof.
  apply sizeof_mpz_struct.
Qed.

Lemma mpz_offset_nonnull:
  forall x i,
    0 <= x ->
    x <> NULL ->
    0 <= i ->
    x + i * mpz_sizeof <> NULL.
Proof.
  intros x i Hx Hx_nonnull Hi.
  rewrite mpz_sizeof_eq_12.
  unfold NULL in *.
  lia.
Qed.

Definition mpz_store (x: addr) (lo: Z) (z: Z): Assertion :=
  store_Z (x + lo * mpz_sizeof) z.

Module MpzArray.
  Definition full (x: addr) (n: Z) (l: list Z): Assertion :=
    store_array mpz_store x n l.

  Definition missing_i (x: addr) (i lo hi: Z) (l: list Z): Assertion :=
    store_array_missing_i_rec mpz_store x i lo hi l.

  Lemma full_length: forall x n (l: list Z),
    full x n l |-- “ Z.of_nat (List.length l) = n ”.
  Proof.
    intros.
    unfold full.
    apply store_array_length.
  Qed.

  Lemma full_Zlength: forall x n (l: list Z),
    full x n l |-- “ Zlength l = n ”.
  Proof.
    intros.
    rewrite Zlength_correct.
    apply full_length.
  Qed.

  Lemma missing_i_merge_to_full: forall x n m a (l: list Z),
    0 <= n < m ->
    mpz_store x n a ** missing_i x n 0 m l |-- full x m (replace_Znth n a l).
  Proof.
    intros.
    unfold full, missing_i.
    apply store_array_missing_i_merge_to_array.
    exact H.
  Qed.

  Lemma full_split_to_missing_i: forall x n m (l: list Z) a,
    0 <= n < m ->
    full x m l |-- mpz_store x n (Znth n l a) ** missing_i x n 0 m l.
  Proof.
    intros.
    unfold full, missing_i.
    apply store_array_split_to_missing_i.
    exact H.
  Qed.
End MpzArray.

Definition mpz_array (x: addr) (n: Z) (l: list Z): Assertion :=
  MpzArray.full x n l.

Definition mpz_missing_i
  (x: addr) (i lo hi: Z) (l: list Z): Assertion :=
  MpzArray.missing_i x i lo hi l.

Lemma mpz_array_Zlength:
  forall x n l,
    mpz_array x n l |-- “ Zlength l = n ”.
Proof.
  intros.
  unfold mpz_array.
  apply MpzArray.full_Zlength.
Qed.

Lemma mpz_array_split:
  forall x idx n l default,
    0 <= idx < n ->
    mpz_array x n l
    |-- mpz_store x idx (Znth idx l default) **
        mpz_missing_i x idx 0 n l.
Proof.
  intros.
  unfold mpz_array, mpz_missing_i.
  apply MpzArray.full_split_to_missing_i.
  exact H.
Qed.

Lemma mpz_array_merge:
  forall x idx n v l,
    0 <= idx < n ->
    mpz_store x idx v **
    mpz_missing_i x idx 0 n l
    |-- mpz_array x n (replace_Znth idx v l).
Proof.
  intros.
  unfold mpz_array, mpz_missing_i.
  apply MpzArray.missing_i_merge_to_full.
  exact H.
Qed.
