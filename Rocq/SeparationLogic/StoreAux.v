Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Set Warnings "-warn-library-file-stdlib-vector".
Require Coq.Vectors.Vector.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap ListLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion.
From compcert.lib Require Import Coqlib Integers.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Set Asymmetric Patterns.

Module Type StoreLibSig (Arch : CArchSig) (Endian : CEndianSig) (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules).

Import CRules.
Import DePredSig.
Local Open Scope sac.  

Theorem store_byte_eqm:
  forall p v v',
    Byte.eqm v v' ->
    store_byte p v |-- store_byte p v'.
Proof.
  unfold store_byte; intros.
  apply mstore_eqm; auto.
Qed.

Lemma eqm_iff_mod_eq x y : Byte.eqm x y <-> x mod 256 = y mod 256.
Proof.
  split; intros.
  - apply Byte.eqm_mod_eq. exact H.
  - unfold Byte.eqm. apply Zbits.eqmod_trans with (x mod 256).
    + apply Zbits.eqmod_mod.
    + apply Zbits.eqmod_trans with (y mod 256).
      * apply Zbits.eqmod_refl2. auto.
        * apply Zbits.eqmod_sym. apply Zbits.eqmod_mod.
Qed.

Lemma byte_eqm_unsigned_last_8 x :
  Byte.eqm x (unsigned_last_nbits x 8).
Proof.
  apply eqm_iff_mod_eq.
  change 256 with (2 ^ 8).
  apply unsigned_Lastnbits_mod_correct.
  lia.
Qed.

Lemma byte_eqm_signed_last_8 x :
  Byte.eqm x (signed_last_nbits x 8).
Proof.
  apply eqm_iff_mod_eq.
  change 256 with (2 ^ 8).
  apply signed_Lastnbits_mod_correct.
  lia.
Qed.

Section generic_n_bytes.

Import Vector.VectorNotations.
Close Scope vector_scope.

Notation byte := Z (only parsing).

Fixpoint store_n_bytes (x : addr) n : Vector.t byte n -> CRules.expr :=
  match n with
    | O => fun _ => CRules.emp
    | S n' => fun v =>
        CRules.sepcon (CRules.mstore x (Vector.hd v)) (store_n_bytes (x + 1) n' (Vector.tl v))
  end.

Definition store_n_bytes_Z (x : addr) n (v : Z) : CRules.expr :=
  CRules.exp (fun bytes : Vector.t byte n =>
    CRules.andp
      (CRules.coq_prop (merge_n_bytes n bytes v))
      (store_n_bytes x n bytes)
  ).

Fixpoint store_n_bytes_noninit (x : addr) n (v : Vector.t byte n) : CRules.expr :=
  match v with 
    | Vector.nil => CRules.emp
    | Vector.cons b n v' =>
        CRules.sepcon (CRules.mstore_noninit x) (store_n_bytes_noninit (x + 1) n v')
  end.

(* Lemma byte_repr_mod_eq x :
    Byte.repr (x mod 256) = Byte.repr x.
Proof.
  apply Byte.eqm_samerepr.
  unfold Byte.eqm.
  apply Zbits.eqmod_sym.
  apply Zbits.eqmod_mod.
  lia.
Qed. *)

Lemma store_byte_equiv_store_n_bytes_Z a v :
    (store_byte a v) --||-- (store_n_bytes_Z a 1 v).
Proof.
  unfold store_byte, store_n_bytes_Z.
  split.
  - Exists [v]%vector.
    cbn.
    assert (Hmerge : merge_n_bytes 1 [v]%vector v).
    { apply merge_byte_equiv_merge_n_bytes. apply Byte.eqm_refl. }
    entailer!.
  - Intros bytes.
    revert H.
    apply (Vector.caseS' bytes). clear bytes. intros z1.
    refine (Vector.case0 _ _).
    intros H.
    cbn.
    entailer!.
    apply mstore_eqm.
    apply merge_byte_equiv_merge_n_bytes in H.
    exact H.
Qed.

Lemma store_2byte_equiv_store_n_bytes_Z a v :
    (store_2byte a v) --||-- (store_n_bytes_Z a 2 v).
Proof.
  unfold store_2byte, store_n_bytes_Z.
  cbn.
  split.
  - Intros z1 z2.
    Exists [z1; z2]%vector.
    apply merge_short_equiv_merge_n_bytes in H.
    entailer!.
  - Intros bytes.
    revert H.
    apply (Vector.caseS' bytes). clear bytes. intros z1 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z2.
    refine (Vector.case0 _ _).
    intros H.
    rewrite <- merge_short_equiv_merge_n_bytes in H.
    cbn.
    Exists z1 z2.
    entailer!.
Qed.

Lemma store_4byte_equiv_store_n_bytes_Z a v :
    (store_4byte a v) --||-- (store_n_bytes_Z a 4 v).
Proof.
  cbn.
  split.
  - Intros z1 z2 z3 z4.
    Exists [z1; z2; z3; z4]%vector.
    apply merge_int_equiv_merge_n_bytes in H.
    cbn.
    repeat (rewrite <- Z.add_assoc; cbn).
    entailer!.
  - Intros bytes.
    revert H.
    apply (Vector.caseS' bytes). clear bytes. intros z1 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z2 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z3 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z4.
    refine (Vector.case0 _ _).
    intros H.
    rewrite <- merge_int_equiv_merge_n_bytes in H.
    cbn.
    repeat (rewrite <- Z.add_assoc; cbn).
    Exists z1 z2 z3 z4.
    entailer!.
Qed.

Lemma store_8byte_equiv_store_n_bytes_Z a v :
    (store_8byte a v) --||-- (store_n_bytes_Z a 8 v).
Proof.
  cbn.
  split.
  - Intros z1 z2 z3 z4. Intros z5 z6 z7 z8.
    Exists [z1; z2; z3; z4; z5; z6; z7; z8]%vector.
    apply merge_int64_equiv_merge_n_bytes in H.
    cbn.
    repeat (rewrite <- Z.add_assoc; cbn).
    entailer!.
  - Intros bytes.
    revert H.
    apply (Vector.caseS' bytes). clear bytes. intros z1 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z2 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z3 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z4 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z5 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z6 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z7 bytes.
    apply (Vector.caseS' bytes). clear bytes. intros z8.
    refine (Vector.case0 _ _).
    intros H.
    rewrite <- merge_int64_equiv_merge_n_bytes in H.
    cbn.
    repeat (rewrite <- Z.add_assoc; cbn).
    Exists (z1) (z2) (z3) (z4).
    Exists (z5) (z6) (z7) (z8).
    entailer!.
Qed.

End generic_n_bytes.



Lemma store_int_store_char: forall p v,
  store_int p v --||--
  EX v1 v2 v3 v4: Z,
    “ merge_int v1 v2 v3 v4 v ”&&
    “ Int.min_signed <= v <= Int.max_signed ”&&
    “ aligned_4 p ”&&
    store_char p v1 **
    store_char (p + 1) v2 **
    store_char (p + 2) v3 **
    store_char (p + 3) v4.
Proof.
  intros.
  split.
  + unfold store_int, store_4byte.
    Intros z1 z2 z3 z4.
    Exists (Byte.signed (Byte.repr z1))
           (Byte.signed (Byte.repr z2))
           (Byte.signed (Byte.repr z3))
           (Byte.signed (Byte.repr z4)).
    unfold store_char.
    pose proof Byte.signed_range (Byte.repr z1).
    pose proof Byte.signed_range (Byte.repr z2).
    pose proof Byte.signed_range (Byte.repr z3).
    pose proof Byte.signed_range (Byte.repr z4).
    entailer!.
    - apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply store_byte_eqm, Byte.eqm_signed_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_int in H. apply H.
    - eapply merge_int_eqm; try apply Byte.eqm_signed_repr; exact H0.
  + Intros v1 v2 v3 v4.
    unfold store_int, store_char.
    unfold store_4byte.
    Intros.
    Exists v1 v2 v3 v4.
    entailer!.
    unfold isvalidptr_int.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Lemma undef_store_uint_undef_store_char : forall p,
  undef_store_uint p --||-- “ aligned_4 p ” && undef_store_char p ** undef_store_char (p + 1) ** undef_store_char (p + 2) ** undef_store_char (p + 3).
Proof.
  intros.
  unfold undef_store_uint, undef_store_char. 
  unfold isvalidptr_int. unfold isvalidptr_char.
  split ; Intros ; entailer!.
Qed.

Lemma undef_store_int_undef_store_char : forall p,
  undef_store_int p --||-- “ aligned_4 p ” && undef_store_char p ** undef_store_char (p + 1) ** undef_store_char (p + 2) ** undef_store_char (p + 3).
Proof.
  intros.
  unfold undef_store_int, undef_store_char. 
  unfold isvalidptr_int. unfold isvalidptr_char.
  split ; Intros ; entailer!.
Qed.

Lemma store_uint_store_char: forall p v,
  store_uint p v --||--
  EX v1 v2 v3 v4: Z,
    “ merge_int v1 v2 v3 v4 v ”&&
    “ 0 <= v <= Int.max_unsigned ”&&
    “ aligned_4 p ”&&
    store_char p v1 **
    store_char (p + 1) v2 **
    store_char (p + 2) v3 **
    store_char (p + 3) v4.
Proof.
  intros.
  split.
  + unfold store_uint, store_4byte.
    Intros z1 z2 z3 z4.
    Exists (Byte.signed (Byte.repr z1))
           (Byte.signed (Byte.repr z2))
           (Byte.signed (Byte.repr z3))
           (Byte.signed (Byte.repr z4)).
    unfold store_char.
    pose proof Byte.signed_range (Byte.repr z1).
    pose proof Byte.signed_range (Byte.repr z2).
    pose proof Byte.signed_range (Byte.repr z3).
    pose proof Byte.signed_range (Byte.repr z4).
    entailer!.
    - apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply store_byte_eqm, Byte.eqm_signed_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - apply H.
    - eapply merge_int_eqm; try apply Byte.eqm_signed_repr; exact H0.
  + Intros v1 v2 v3 v4.
    unfold store_uint, store_char.
    unfold store_4byte.
    Intros.
    Exists v1 v2 v3 v4.
    entailer!.
    unfold isvalidptr_int.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Lemma store_int64_store_char: forall p v,
  store_int64 p v --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v ”&&
    “ Int64.min_signed <= v <= Int64.max_signed ”&&
    “ aligned_4 p ”&&
    store_char p v1 **
    store_char (p + 1) v2 **
    store_char (p + 2) v3 **
    store_char (p + 3) v4 **
    store_char (p + 4) v5 **
    store_char (p + 5) v6 **
    store_char (p + 6) v7 **
    store_char (p + 7) v8.
Proof.
  intros.
  split.
  + unfold store_int64, store_8byte.
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    Exists (Byte.signed (Byte.repr z1)).
    Exists (Byte.signed (Byte.repr z2)).
    Exists (Byte.signed (Byte.repr z3)).
    Exists (Byte.signed (Byte.repr z4)).
    Exists (Byte.signed (Byte.repr z5)).
    Exists (Byte.signed (Byte.repr z6)).
    Exists (Byte.signed (Byte.repr z7)).
    Exists (Byte.signed (Byte.repr z8)).
    unfold store_char.
    pose proof Byte.signed_range (Byte.repr z1).
    pose proof Byte.signed_range (Byte.repr z2).
    pose proof Byte.signed_range (Byte.repr z3).
    pose proof Byte.signed_range (Byte.repr z4).
    pose proof Byte.signed_range (Byte.repr z5).
    pose proof Byte.signed_range (Byte.repr z6).
    pose proof Byte.signed_range (Byte.repr z7).
    pose proof Byte.signed_range (Byte.repr z8).
    entailer!.
    - repeat (apply derivable1_sepcon_mono;
              [apply store_byte_eqm, Byte.eqm_signed_repr |]).
      apply store_byte_eqm, Byte.eqm_signed_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_int64 in H. apply H.
    - eapply merge_int64_eqm; try apply Byte.eqm_signed_repr; exact H0.
  + Intros v1 v2 v3 v4.
    Intros v5 v6 v7 v8.
    unfold store_int64, store_char.
    unfold store_8byte.
    Intros.
    Exists v1 v2 v3 v4.
    Exists v5 v6 v7 v8.
    entailer!.
    unfold isvalidptr_int64.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Lemma store_uint64_store_uchar: forall p v,
  store_uint64 p v --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v ”&&
    “ 0 <= v <= Int64.max_unsigned ”&&
    “ aligned_4 p ”&&
    store_uchar p v1 **
    store_uchar (p + 1) v2 **
    store_uchar (p + 2) v3 **
    store_uchar (p + 3) v4 **
    store_uchar (p + 4) v5 **
    store_uchar (p + 5) v6 **
    store_uchar (p + 6) v7 **
    store_uchar (p + 7) v8.
Proof.
  intros.
  split.
  + unfold store_uint64, store_8byte.
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    Exists (Byte.unsigned (Byte.repr z1)).
    Exists (Byte.unsigned (Byte.repr z2)).
    Exists (Byte.unsigned (Byte.repr z3)).
    Exists (Byte.unsigned (Byte.repr z4)).
    Exists (Byte.unsigned (Byte.repr z5)).
    Exists (Byte.unsigned (Byte.repr z6)).
    Exists (Byte.unsigned (Byte.repr z7)).
    Exists (Byte.unsigned (Byte.repr z8)).
    unfold store_uchar.
    pose proof Byte.unsigned_range_2 (Byte.repr z1).
    pose proof Byte.unsigned_range_2 (Byte.repr z2).
    pose proof Byte.unsigned_range_2 (Byte.repr z3).
    pose proof Byte.unsigned_range_2 (Byte.repr z4).
    pose proof Byte.unsigned_range_2 (Byte.repr z5).
    pose proof Byte.unsigned_range_2 (Byte.repr z6).
    pose proof Byte.unsigned_range_2 (Byte.repr z7).
    pose proof Byte.unsigned_range_2 (Byte.repr z8).
    entailer!.
    - repeat (apply derivable1_sepcon_mono;
              [apply store_byte_eqm, Byte.eqm_unsigned_repr |]).
      apply store_byte_eqm, Byte.eqm_unsigned_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_int64 in H. apply H.
    - eapply merge_int64_eqm; try apply Byte.eqm_unsigned_repr; exact H0.
  + Intros v1 v2 v3 v4.
    Intros v5 v6 v7 v8.
    unfold store_uint64, store_uchar.
    unfold store_8byte.
    Intros.
    Exists v1 v2 v3 v4.
    Exists v5 v6 v7 v8.
    entailer!.
    unfold isvalidptr_int64.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Lemma store_int64_store_uchar: forall p v,
  store_int64 p v --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v ”&&
    “ Int64.min_signed <= v <= Int64.max_signed ”&&
    “ aligned_4 p ”&&
    store_uchar p v1 **
    store_uchar (p + 1) v2 **
    store_uchar (p + 2) v3 **
    store_uchar (p + 3) v4 **
    store_uchar (p + 4) v5 **
    store_uchar (p + 5) v6 **
    store_uchar (p + 6) v7 **
    store_uchar (p + 7) v8.
Proof.
  intros.
  split.
  + unfold store_int64, store_8byte.
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    Exists (Byte.unsigned (Byte.repr z1)).
    Exists (Byte.unsigned (Byte.repr z2)).
    Exists (Byte.unsigned (Byte.repr z3)).
    Exists (Byte.unsigned (Byte.repr z4)).
    Exists (Byte.unsigned (Byte.repr z5)).
    Exists (Byte.unsigned (Byte.repr z6)).
    Exists (Byte.unsigned (Byte.repr z7)).
    Exists (Byte.unsigned (Byte.repr z8)).
    unfold store_uchar.
    pose proof Byte.unsigned_range_2 (Byte.repr z1).
    pose proof Byte.unsigned_range_2 (Byte.repr z2).
    pose proof Byte.unsigned_range_2 (Byte.repr z3).
    pose proof Byte.unsigned_range_2 (Byte.repr z4).
    pose proof Byte.unsigned_range_2 (Byte.repr z5).
    pose proof Byte.unsigned_range_2 (Byte.repr z6).
    pose proof Byte.unsigned_range_2 (Byte.repr z7).
    pose proof Byte.unsigned_range_2 (Byte.repr z8).
    entailer!.
    - repeat (apply derivable1_sepcon_mono;
              [apply store_byte_eqm, Byte.eqm_unsigned_repr |]).
      apply store_byte_eqm, Byte.eqm_unsigned_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_int64 in H. apply H.
    - eapply merge_int64_eqm; try apply Byte.eqm_unsigned_repr; exact H0.
  + Intros v1 v2 v3 v4.
    Intros v5 v6 v7 v8.
    unfold store_int64, store_uchar.
    unfold store_8byte.
    Intros.
    Exists v1 v2 v3 v4.
    Exists v5 v6 v7 v8.
    entailer!.
    unfold isvalidptr_int64.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Lemma store_uint64_store_char: forall p v,
  store_uint64 p v --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v ”&&
    “ 0 <= v <= Int64.max_unsigned ”&&
    “ aligned_4 p ”&&
    store_char p v1 **
    store_char (p + 1) v2 **
    store_char (p + 2) v3 **
    store_char (p + 3) v4 **
    store_char (p + 4) v5 **
    store_char (p + 5) v6 **
    store_char (p + 6) v7 **
    store_char (p + 7) v8.
Proof.
  intros.
  split.
  + unfold store_uint64, store_8byte.
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    Exists (Byte.signed (Byte.repr z1)).
    Exists (Byte.signed (Byte.repr z2)).
    Exists (Byte.signed (Byte.repr z3)).
    Exists (Byte.signed (Byte.repr z4)).
    Exists (Byte.signed (Byte.repr z5)).
    Exists (Byte.signed (Byte.repr z6)).
    Exists (Byte.signed (Byte.repr z7)).
    Exists (Byte.signed (Byte.repr z8)).
    unfold store_char.
    pose proof Byte.signed_range (Byte.repr z1).
    pose proof Byte.signed_range (Byte.repr z2).
    pose proof Byte.signed_range (Byte.repr z3).
    pose proof Byte.signed_range (Byte.repr z4).
    pose proof Byte.signed_range (Byte.repr z5).
    pose proof Byte.signed_range (Byte.repr z6).
    pose proof Byte.signed_range (Byte.repr z7).
    pose proof Byte.signed_range (Byte.repr z8).
    entailer!.
    - repeat (apply derivable1_sepcon_mono;
              [apply store_byte_eqm, Byte.eqm_signed_repr |]).
      apply store_byte_eqm, Byte.eqm_signed_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int64 in H.
      lia.
    - unfold isvalidptr_int64 in H. apply H.
    - eapply merge_int64_eqm; try apply Byte.eqm_signed_repr; exact H0.
  + Intros v1 v2 v3 v4.
    Intros v5 v6 v7 v8.
    unfold store_uint64, store_char.
    unfold store_8byte.
    Intros.
    Exists v1 v2 v3 v4.
    Exists v5 v6 v7 v8.
    entailer!.
    unfold isvalidptr_int64.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Definition merge_int64_by_ints (w1 w2 v : Z) : Prop :=
  exists b1 b2 b3 b4 b5 b6 b7 b8,
    merge_int b1 b2 b3 b4 w1 /\
    merge_int b5 b6 b7 b8 w2 /\
    merge_int64 b1 b2 b3 b4 b5 b6 b7 b8 v.

Definition signed_int_of_bytes b1 b2 b3 b4 : Z :=
  signed_last_nbits (n_bytes_to_Z 4 (vec4 b1 b2 b3 b4)) 32.

Definition unsigned_int_of_bytes b1 b2 b3 b4 : Z :=
  unsigned_last_nbits (n_bytes_to_Z 4 (vec4 b1 b2 b3 b4)) 32.

Lemma merge_int_signed_of_bytes :
  forall b1 b2 b3 b4,
    merge_int b1 b2 b3 b4 (signed_int_of_bytes b1 b2 b3 b4).
Proof.
  intros.
  unfold signed_int_of_bytes.
  eapply merge_int_value_eqm.
  - apply signed_Lastnbits_mod_correct. lia.
  - rewrite merge_int_equiv_merge_n_bytes.
    apply merge_n_bytes_self.
Qed.

Lemma merge_int_unsigned_of_bytes :
  forall b1 b2 b3 b4,
    merge_int b1 b2 b3 b4 (unsigned_int_of_bytes b1 b2 b3 b4).
Proof.
  intros.
  unfold unsigned_int_of_bytes.
  eapply merge_int_value_eqm.
  - apply unsigned_Lastnbits_mod_correct. lia.
  - rewrite merge_int_equiv_merge_n_bytes.
    apply merge_n_bytes_self.
Qed.

Lemma signed_int_of_bytes_range :
  forall b1 b2 b3 b4,
    Int.min_signed <= signed_int_of_bytes b1 b2 b3 b4 <= Int.max_signed.
Proof.
  intros.
  unfold signed_int_of_bytes.
  pose proof (signed_Lastnbits_range (n_bytes_to_Z 4 (vec4 b1 b2 b3 b4)) 32).
  replace Int.min_signed with (- 2 ^ 31) by reflexivity.
  replace Int.max_signed with (2 ^ 31 - 1) by reflexivity.
  lia.
Qed.

Lemma unsigned_int_of_bytes_range :
  forall b1 b2 b3 b4,
    0 <= unsigned_int_of_bytes b1 b2 b3 b4 <= Int.max_unsigned.
Proof.
  intros.
  unfold unsigned_int_of_bytes.
  pose proof (unsigned_Lastnbits_range (n_bytes_to_Z 4 (vec4 b1 b2 b3 b4)) 32).
  replace Int.max_unsigned with (2 ^ 32 - 1) by reflexivity.
  lia.
Qed.

Lemma store_int64_store_int: forall p v,
  store_int64 p v |--
  EX v1 : Z, EX v2 : Z,
    “ merge_int64_by_ints v1 v2 v /\
      Int64.min_signed <= v <= Int64.max_signed /\
      aligned_4 p ” &&
    store_int p v1 ** store_int (p + 4) v2.
Proof.
  intros.
  unfold store_int64, store_int.
  unfold store_8byte, store_4byte.
  Intros z1 z2 z3 z4.
  Intros z5 z6 z7 z8.
  pose (v1 := signed_int_of_bytes z1 z2 z3 z4).
  pose (v2 := signed_int_of_bytes z5 z6 z7 z8).
  Exists v1. Exists v2.
  Exists z1 z2 z3 z4.
  Exists z5 z6 z7 z8.
  entailer!.
  - replace (p + 4 + 1) with (p + 5) by ring.
    replace (p + 4 + 2) with (p + 6) by ring.
    replace (p + 4 + 3) with (p + 7) by ring.
    entailer!.
  - subst v2. apply merge_int_signed_of_bytes.
  - subst v1. apply merge_int_signed_of_bytes.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmax Hvmin]].
    unfold isvalidptr_int.
    repeat split; try lia.
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Halign.
    reflexivity.
  - subst v2. pose proof signed_int_of_bytes_range z5 z6 z7 z8. lia.
  - subst v2. pose proof signed_int_of_bytes_range z5 z6 z7 z8. lia.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmax Hvmin]].
    unfold isvalidptr_int.
    repeat split; try lia.
    exact Halign.
  - subst v1. pose proof signed_int_of_bytes_range z1 z2 z3 z4. lia.
  - subst v1. pose proof signed_int_of_bytes_range z1 z2 z3 z4. lia.
  - unfold merge_int64_by_ints.
    do 8 eexists.
    repeat split.
    + subst v1. apply merge_int_signed_of_bytes.
    + subst v2. apply merge_int_signed_of_bytes.
    + exact H0.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmax Hvmin]].
    exact Halign.
Qed.

Lemma store_uint64_store_uint: forall p v,
  store_uint64 p v |--
  EX v1 : Z, EX v2 : Z,
    “ merge_int64_by_ints v1 v2 v /\
      0 <= v <= Int64.max_unsigned /\
      aligned_4 p ” &&
    store_uint p v1 ** store_uint (p + 4) v2.
Proof.
  intros.
  unfold store_uint64, store_uint.
  unfold store_8byte, store_4byte.
  Intros z1 z2 z3 z4.
  Intros z5 z6 z7 z8.
  pose (v1 := unsigned_int_of_bytes z1 z2 z3 z4).
  pose (v2 := unsigned_int_of_bytes z5 z6 z7 z8).
  Exists v1. Exists v2.
  Exists z1 z2 z3 z4.
  Exists z5 z6 z7 z8.
  entailer!.
  - replace (p + 4 + 1) with (p + 5) by ring.
    replace (p + 4 + 2) with (p + 6) by ring.
    replace (p + 4 + 3) with (p + 7) by ring.
    entailer!.
  - subst v2. apply merge_int_unsigned_of_bytes.
  - subst v1. apply merge_int_unsigned_of_bytes.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmin Hvmax]].
    unfold isvalidptr_int.
    repeat split; try lia.
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Halign.
    reflexivity.
  - subst v2. pose proof unsigned_int_of_bytes_range z5 z6 z7 z8. lia.
  - subst v2. pose proof unsigned_int_of_bytes_range z5 z6 z7 z8. lia.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmin Hvmax]].
    unfold isvalidptr_int.
    repeat split; try lia.
    exact Halign.
  - subst v1. pose proof unsigned_int_of_bytes_range z1 z2 z3 z4. lia.
  - subst v1. pose proof unsigned_int_of_bytes_range z1 z2 z3 z4. lia.
  - unfold merge_int64_by_ints.
    do 8 eexists.
    repeat split.
    + subst v1. apply merge_int_unsigned_of_bytes.
    + subst v2. apply merge_int_unsigned_of_bytes.
    + exact H0.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmin Hvmax]].
    exact Halign.
Qed.

Lemma store_int64_store_uint: forall p v,
  store_int64 p v |--
  EX v1 : Z, EX v2 : Z,
    “ merge_int64_by_ints v1 v2 v /\
      Int64.min_signed <= v <= Int64.max_signed /\
      aligned_4 p ” &&
    store_uint p v1 ** store_uint (p + 4) v2.
Proof.
  intros.
  unfold store_int64, store_uint.
  unfold store_8byte, store_4byte.
  Intros z1 z2 z3 z4.
  Intros z5 z6 z7 z8.
  pose (v1 := unsigned_int_of_bytes z1 z2 z3 z4).
  pose (v2 := unsigned_int_of_bytes z5 z6 z7 z8).
  Exists v1. Exists v2.
  Exists z1 z2 z3 z4.
  Exists z5 z6 z7 z8.
  entailer!.
  - replace (p + 4 + 1) with (p + 5) by ring.
    replace (p + 4 + 2) with (p + 6) by ring.
    replace (p + 4 + 3) with (p + 7) by ring.
    entailer!.
  - subst v2. apply merge_int_unsigned_of_bytes.
  - subst v1. apply merge_int_unsigned_of_bytes.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmax Hvmin]].
    unfold isvalidptr_int.
    repeat split; try lia.
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Halign.
    reflexivity.
  - subst v2. pose proof unsigned_int_of_bytes_range z5 z6 z7 z8. lia.
  - subst v2. pose proof unsigned_int_of_bytes_range z5 z6 z7 z8. lia.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmax Hvmin]].
    unfold isvalidptr_int.
    repeat split; try lia.
    exact Halign.
  - subst v1. pose proof unsigned_int_of_bytes_range z1 z2 z3 z4. lia.
  - subst v1. pose proof unsigned_int_of_bytes_range z1 z2 z3 z4. lia.
  - unfold merge_int64_by_ints.
    do 8 eexists.
    repeat split.
    + subst v1. apply merge_int_unsigned_of_bytes.
    + subst v2. apply merge_int_unsigned_of_bytes.
    + exact H0.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmax Hvmin]].
    exact Halign.
Qed.

Lemma store_uint64_store_int: forall p v,
  store_uint64 p v |--
  EX v1 : Z, EX v2 : Z,
    “ merge_int64_by_ints v1 v2 v /\
      0 <= v <= Int64.max_unsigned /\
      aligned_4 p ” &&
    store_int p v1 ** store_int (p + 4) v2.
Proof.
  intros.
  unfold store_uint64, store_int.
  unfold store_8byte, store_4byte.
  Intros z1 z2 z3 z4.
  Intros z5 z6 z7 z8.
  pose (v1 := signed_int_of_bytes z1 z2 z3 z4).
  pose (v2 := signed_int_of_bytes z5 z6 z7 z8).
  Exists v1. Exists v2.
  Exists z1 z2 z3 z4.
  Exists z5 z6 z7 z8.
  entailer!.
  - replace (p + 4 + 1) with (p + 5) by ring.
    replace (p + 4 + 2) with (p + 6) by ring.
    replace (p + 4 + 3) with (p + 7) by ring.
    entailer!.
  - subst v2. apply merge_int_signed_of_bytes.
  - subst v1. apply merge_int_signed_of_bytes.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmin Hvmax]].
    unfold isvalidptr_int.
    repeat split; try lia.
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Halign.
    reflexivity.
  - subst v2. pose proof signed_int_of_bytes_range z5 z6 z7 z8. lia.
  - subst v2. pose proof signed_int_of_bytes_range z5 z6 z7 z8. lia.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmin Hvmax]].
    unfold isvalidptr_int.
    repeat split; try lia.
    exact Halign.
  - subst v1. pose proof signed_int_of_bytes_range z1 z2 z3 z4. lia.
  - subst v1. pose proof signed_int_of_bytes_range z1 z2 z3 z4. lia.
  - unfold merge_int64_by_ints.
    do 8 eexists.
    repeat split.
    + subst v1. apply merge_int_signed_of_bytes.
    + subst v2. apply merge_int_signed_of_bytes.
    + exact H0.
  - destruct H as [[Hp0 [Hp7 Halign]] [Hvmin Hvmax]].
    exact Halign.
Qed.

Lemma store_byte_store_byte_noinit: forall p v,
  store_byte p v |-- store_byte_noninit p.
Proof.
  unfold store_byte, store_byte_noninit.
  intros.
  unfold derivable1.
  apply mstore_mstore_noninit.
Qed.

Lemma store_2byte_store_2byte_noinit: forall p v,
  store_2byte p v |-- store_2byte_noninit p.
Proof.
  unfold store_2byte, store_2byte_noninit.
  intros.
  Intros z1 z2.
  apply derivable1_sepcon_mono; apply store_byte_store_byte_noinit.
Qed.

Lemma store_4byte_store_4byte_noinit: forall p v,
  store_4byte p v |-- store_4byte_noninit p.
Proof.
  unfold store_4byte, store_4byte_noninit.
  intros.
  Intros z1 z2 z3 z4.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono; apply store_byte_store_byte_noinit.
Qed.

Lemma store_8byte_store_8byte_noinit: forall p v,
  store_8byte p v |-- store_8byte_noninit p.
Proof.
  unfold store_8byte, store_8byte_noninit.
  intros.
  Intros z1 z2 z3 z4.
  Intros z5 z6 z7 z8.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono; apply store_byte_store_byte_noinit.
Qed.

Lemma store_bytes_store_bytes_noninit:
  forall n p (bytes : Vector.t Z n),
    store_bytes p n bytes |-- store_bytes_noninit p n.
Proof.
  induction n; intros; cbn.
  - entailer!.
  - apply derivable1_sepcon_mono.
    + apply store_byte_store_byte_noinit.
    + apply IHn.
Qed.

Lemma store_16byte_store_16byte_noinit: forall p v,
  store_16byte p v |-- store_16byte_noninit p.
Proof.
  unfold store_16byte, store_16byte_noninit.
  intros.
  Intros bytes.
  apply store_bytes_store_bytes_noninit.
Qed.

Lemma store_ptr_undef_store_ptr: forall p v,
  store_ptr p v |-- undef_store_ptr p.
Proof.
  unfold store_ptr, undef_store_ptr.
  intros.
  destruct Arch.ptr_size_32_or_64 as [Hsize | Hsize];
    unfold ptr_size; rewrite Hsize; entailer!.
  - apply store_4byte_store_4byte_noinit.
  - apply store_8byte_store_8byte_noinit.
Qed.

Lemma store_int_range : forall x v,
  (x # Int |-> v) |-- “ Int.min_signed <= v <= Int.max_signed ”.
Proof.
  intros.
  unfold store_int.
  entailer!.
Qed.

Lemma store_int_undef_store_int: forall x v, 
  (x # Int |->v) |-- (x # Int |->_).
Proof.
  intros.
  unfold store_int, undef_store_int.
  entailer!.
  apply store_4byte_store_4byte_noinit.
Qed.

Lemma store_char_range : forall x v,
  (x # Char |-> v) |-- “ Byte.min_signed <= v <= Byte.max_signed ”.
Proof.
  intros.
  unfold store_char.
  entailer!.
Qed.

Lemma store_char_undef_store_char: forall x v, 
  (x # Char |->v) |-- (x # Char |->_).
Proof.
  intros.
  unfold store_char, undef_store_char.
  entailer!.
  apply store_byte_store_byte_noinit.
Qed.

Lemma store_short_range : forall x v,
  (x # Short |-> v) |-- “ -32768 <= v <= 32767 ”.
Proof. 
  intros.
  unfold store_short.
  entailer!.
Qed.

Lemma store_short_undef_store_short: forall x v, 
  (x # Short |->v) |-- (x # Short |->_).
Proof.
  intros.
  unfold store_short, undef_store_short.
  entailer!.
  apply store_2byte_store_2byte_noinit.
Qed.

Lemma store_int64_range : forall x v,
  (x # Int64 |-> v) |-- “ Int64.min_signed <= v <= Int64.max_signed ”.
Proof.
  intros.
  unfold store_int64.
  entailer!.
Qed.

Lemma store_int64_undef_store_int64: forall x v, 
  (x # Int64 |->v) |-- (x # Int64 |->_).
Proof.
  intros.
  unfold store_int64, undef_store_int64.
  entailer!.
  apply store_8byte_store_8byte_noinit.
Qed.

Lemma store_uint_range : forall x v,
  (x # UInt |-> v) |-- “ 0 <= v <= Int.max_unsigned ”.
Proof.
  intros.
  unfold store_uint.
  entailer!.
Qed.  

Lemma store_uint_undef_store_uint: forall x v, 
  (x # UInt |->v) |-- (x # UInt |->_).
Proof.
  intros.
  unfold store_uint, undef_store_uint.
  entailer!.
  apply store_4byte_store_4byte_noinit.
Qed.

Lemma store_uchar_range : forall x v,
  (x # UChar |-> v) |-- “ 0 <= v <= Byte.max_unsigned ”.
Proof.
  intros.
  unfold store_uchar.
  entailer!.
Qed.

Lemma store_uchar_undef_store_uchar: forall x v, 
  (x # UChar |->v) |-- (x # UChar |->_).
Proof.
  intros.
  unfold store_uchar, undef_store_uchar.
  entailer!.
  apply store_byte_store_byte_noinit.
Qed.

Lemma store_ushort_range : forall x v,
  (x # UShort |-> v) |-- “ 0 <= v <= 65535 ”.
Proof.
  intros.
  unfold store_ushort.
  entailer!.
Qed.

Lemma store_bool_undef_store_bool: forall x v,
  (x # Bool |-> v) |-- (x # Bool |->_).
Proof.
  intros.
  unfold store_bool, undef_store_bool.
  entailer!.
  apply store_byte_store_byte_noinit.
Qed.

Lemma valid_store_bool: forall x v,
  (x # Bool |-> v) |-- “ 0 <= v <= 1 ”.
Proof.
  intros.
  unfold store_bool.
  entailer!.
Qed.

Lemma store_ushort_undef_store_ushort: forall x v, 
  (x # UShort |->v) |-- (x # UShort |->_).
Proof.
  intros.
  unfold store_ushort, undef_store_ushort.
  entailer!.
  apply store_2byte_store_2byte_noinit.
Qed.

Lemma store_uint64_range : forall x v,
  (x # UInt64 |-> v) |-- “ 0 <= v <= Int64.max_unsigned ”.
Proof.
  intros.
  unfold store_uint64.
  entailer!.
Qed.  

Lemma store_uint64_undef_store_uint64: forall x v, 
  (x # UInt64 |->v) |-- (x # UInt64 |->_).
Proof.
  intros.
  unfold store_uint64, undef_store_uint64.
  entailer!.
  apply store_8byte_store_8byte_noinit.
Qed.

Lemma store_int128_range : forall x v,
  (x # Int128 |-> v) |-- CRules.coq_prop (Int128.min_signed <= v <= Int128.max_signed).
Proof.
  intros.
  unfold store_int128.
  entailer!.
Qed.

Lemma store_int128_undef_store_int128: forall x v,
  (x # Int128 |-> v) |-- (x # Int128 |->_).
Proof.
  intros.
  unfold store_int128, undef_store_int128.
  entailer!.
  apply store_16byte_store_16byte_noinit.
Qed.

Lemma store_uint128_range : forall x v,
  (x # UInt128 |-> v) |-- CRules.coq_prop (0 <= v <= Int128.max_unsigned).
Proof.
  intros.
  unfold store_uint128.
  entailer!.
Qed.

Lemma store_uint128_undef_store_uint128: forall x v,
  (x # UInt128 |-> v) |-- (x # UInt128 |->_).
Proof.
  intros.
  unfold store_uint128, undef_store_uint128.
  entailer!.
  apply store_16byte_store_16byte_noinit.
Qed.

Lemma store_float_undef_store_float:
  forall x v,
    x # Float |-> v |-- x # Float |->_.
Proof.
  intros.
  unfold store_float, undef_store_float.
  destruct (bits_of_float_value v).
  - apply derivable1_andp_mono.
    + apply coq_prop_imply. tauto.
    + apply store_4byte_store_4byte_noinit.
  - apply coq_prop_False_left. tauto.
Qed.

Lemma store_double_undef_store_double:
  forall x v,
    x # Double |-> v |-- x # Double |->_.
Proof.
  intros.
  unfold store_double, undef_store_double.
  destruct (bits_of_double_value v).
  - apply derivable1_andp_mono.
    + apply coq_prop_imply. tauto.
    + apply store_8byte_store_8byte_noinit.
  - apply coq_prop_False_left. tauto.
Qed.

Lemma store_long_double_undef_store_long_double:
  forall x v,
    x # LongDouble |-> v |-- x # LongDouble |->_.
Proof.
  intros.
  unfold store_long_double, undef_store_long_double.
  destruct (bits_of_long_double_value v).
  - apply derivable1_andp_mono.
    + apply coq_prop_imply. tauto.
    + apply store_16byte_store_16byte_noinit.
  - apply coq_prop_False_left. tauto.
Qed.

Lemma store_finite_float_undef_store_finite_float:
  forall x v,
    x # FiniteFloat |-> v |-- x # FiniteFloat |->_.
Proof.
  intros.
  unfold store_finite_float, undef_store_finite_float.
  apply coq_prop_andp_left. intros _.
  apply store_float_undef_store_float.
Qed.

Lemma store_finite_double_undef_store_finite_double:
  forall x v,
    x # FiniteDouble |-> v |-- x # FiniteDouble |->_.
Proof.
  intros.
  unfold store_finite_double, undef_store_finite_double.
  apply coq_prop_andp_left. intros _.
  apply store_double_undef_store_double.
Qed.

Lemma store_finite_long_double_undef_store_finite_long_double:
  forall x v,
    x # FiniteLongDouble |-> v |-- x # FiniteLongDouble |->_.
Proof.
  intros.
  unfold store_finite_long_double, undef_store_finite_long_double.
  apply coq_prop_andp_left. intros _.
  apply store_long_double_undef_store_long_double.
Qed.

Lemma valid_store_float:
  forall x v,
    x # Float |-> v |-- “ isvalidptr_float x ”.
Proof.
  intros.
  unfold store_float.
  destruct (bits_of_float_value v); entailer!.
Qed.

Lemma valid_store_double:
  forall x v,
    x # Double |-> v |-- “ isvalidptr_double x ”.
Proof.
  intros.
  unfold store_double.
  destruct (bits_of_double_value v); entailer!.
Qed.

Lemma valid_store_long_double:
  forall x v,
    x # LongDouble |-> v |-- “ isvalidptr_long_double x ”.
Proof.
  intros.
  unfold store_long_double.
  destruct (bits_of_long_double_value v); entailer!.
Qed.

Lemma valid_store_finite_float:
  forall x v,
    x # FiniteFloat |-> v |--
    “ fp32_isFinite v /\ isvalidptr_float x ”.
Proof.
  intros.
  unfold store_finite_float.
  apply coq_prop_andp_left. intros Hfinite.
  eapply derivable1_trans.
  - apply valid_store_float.
  - apply coq_prop_imply. intros Hvalid.
    split; auto.
Qed.

Lemma valid_store_finite_double:
  forall x v,
    x # FiniteDouble |-> v |--
    “ fp64_isFinite v /\ isvalidptr_double x ”.
Proof.
  intros.
  unfold store_finite_double.
  apply coq_prop_andp_left. intros Hfinite.
  eapply derivable1_trans.
  - apply valid_store_double.
  - apply coq_prop_imply. intros Hvalid.
    split; auto.
Qed.

Lemma valid_store_finite_long_double:
  forall x v,
    x # FiniteLongDouble |-> v |--
    “ fp128_isFinite v /\ isvalidptr_long_double x ”.
Proof.
  intros.
  unfold store_finite_long_double.
  apply coq_prop_andp_left. intros Hfinite.
  eapply derivable1_trans.
  - apply valid_store_long_double.
  - apply coq_prop_imply. intros Hvalid.
    split; auto.
Qed.

Lemma poly_store_poly_undef_store: forall x ty v,
  poly_store ty x v |-- poly_undef_store ty x.
Proof.
  intros.
  destruct ty; simpl.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + apply store_bool_undef_store_bool.
  + apply store_int_undef_store_int.
  + apply store_char_undef_store_char.
  + apply store_int64_undef_store_int64.
  + apply store_short_undef_store_short.
  + apply store_uint_undef_store_uint.
  + apply store_uchar_undef_store_uchar.
  + apply store_uint64_undef_store_uint64.
  + apply store_int128_undef_store_int128.
  + apply store_uint128_undef_store_uint128.
  + apply store_ushort_undef_store_ushort.
  + apply store_float_undef_store_float.
  + apply store_double_undef_store_double.
  + apply store_long_double_undef_store_long_double.
  + apply store_ptr_undef_store_ptr.
Qed.

Lemma typed_poly_store_poly_undef_store:
  forall x ty (v : front_end_type_value ty),
    typed_poly_store ty x v |-- poly_undef_store ty x.
Proof.
  intros.
  destruct ty; simpl.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + apply store_bool_undef_store_bool.
  + apply store_int_undef_store_int.
  + apply store_char_undef_store_char.
  + apply store_int64_undef_store_int64.
  + apply store_short_undef_store_short.
  + apply store_uint_undef_store_uint.
  + apply store_uchar_undef_store_uchar.
  + apply store_uint64_undef_store_uint64.
  + apply store_int128_undef_store_int128.
  + apply store_uint128_undef_store_uint128.
  + apply store_ushort_undef_store_ushort.
  + apply store_float_undef_store_float.
  + apply store_double_undef_store_double.
  + apply store_long_double_undef_store_long_double.
  + apply store_ptr_undef_store_ptr.
Qed.

Lemma dup_mstore: forall x v1 v2,
  mstore x v1 ** mstore x v2 |-- “ False ”.
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_mstore_noninit x).
  apply derivable1_sepcon_mono;
  unfold derivable1;
  apply (mstore_mstore_noninit).
Qed.

Lemma dup_store_byte_noninit: forall x, 
  store_byte_noninit x ** store_byte_noninit x |-- “ False ”.
Proof.
  intros.
  unfold store_byte_noninit.
  apply dup_mstore_noninit.
Qed.

Lemma dup_store_byte: forall x v1 v2,
  store_byte x v1 ** store_byte x v2 |-- “ False ”.
Proof.
  intros.
  unfold store_byte.
  apply dup_mstore.
Qed.

Lemma dup_store_2bytes_noninit: forall x,
  store_2byte_noninit x ** store_2byte_noninit x |-- “ False ”.
Proof.
  intros.
  unfold store_2byte_noninit.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ (“ False ”** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  eapply derivable1_trans. apply derivable1_sepcon_comm.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ (“ False ”** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  apply dup_store_byte_noninit.
Qed.

Lemma dup_store_2bytes: forall x v1 v2,
  store_2byte x v1 ** store_2byte x v2 |-- “ False ”.
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_store_2bytes_noninit x).
  apply derivable1_sepcon_mono;
  apply store_2byte_store_2byte_noinit.
Qed.

Lemma dup_store_4bytes_noninit: forall x,
  store_4byte_noninit x ** store_4byte_noninit x |-- “ False ”.
Proof.
  intros.
  unfold store_4byte_noninit.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ (“ False ”** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  eapply derivable1_trans. apply derivable1_sepcon_comm.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ (“ False ”** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  apply dup_store_byte_noninit.
Qed.

Lemma dup_store_4bytes: forall x v1 v2,
  store_4byte x v1 ** store_4byte x v2 |-- “ False ”.
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_store_4bytes_noninit x).
  apply derivable1_sepcon_mono;
  apply store_4byte_store_4byte_noinit.
Qed.

Lemma dup_store_8bytes_noninit: forall x,
  store_8byte_noninit x ** store_8byte_noninit x |-- “ False ”.
Proof.
  intros.
  unfold store_8byte_noninit.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ (“ False ”** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  eapply derivable1_trans. apply derivable1_sepcon_comm.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ (“ False ”** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  apply dup_store_byte_noninit.
Qed.

Lemma dup_store_8bytes: forall x v1 v2,
  store_8byte x v1 ** store_8byte x v2 |-- “ False ”.
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_store_8bytes_noninit x).
  apply derivable1_sepcon_mono;
  apply store_8byte_store_8byte_noinit.
Qed.

Lemma dup_undef_store_int: forall x,
  (x # Int |->_) ** (x # Int |->_) |-- “ False ”.
Proof.
  intros.
  unfold undef_store_int.
  eapply derivable1_trans.
  2: apply (dup_store_4bytes_noninit x).
  apply derivable1_sepcon_mono; entailer!.
Qed.

Lemma dup_store_int: forall x v1 v2,
  (x # Int |-> v1) ** (x # Int |-> v2) |-- “ False ”.
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_undef_store_int x).
  apply derivable1_sepcon_mono; apply store_int_undef_store_int.
Qed.

Lemma dup_undef_store_ptr: forall x,
  (x # Ptr |->_) ** (x # Ptr |->_) |-- “ False ”.
Proof.
  intros.
  unfold undef_store_ptr.
  destruct Arch.ptr_size_32_or_64 as [Hsize | Hsize];
    unfold ptr_size; rewrite Hsize.
  - eapply derivable1_trans.
    2: apply (dup_store_4bytes_noninit x).
    apply derivable1_sepcon_mono; entailer!.
  - eapply derivable1_trans.
    2: apply (dup_store_8bytes_noninit x).
    apply derivable1_sepcon_mono; entailer!.
Qed.

Lemma dup_store_ptr: forall x v1 v2,
  (x # Ptr |-> v1) ** (x # Ptr |-> v2) |-- “ False ”.
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_undef_store_ptr x).
  apply derivable1_sepcon_mono; apply store_ptr_undef_store_ptr.
Qed.

Lemma store_byte_cast : forall x v , store_byte x v |-- store_byte x (signed_last_nbits v 8).
Proof.
  intros. 
  apply store_byte_eqm.
  apply UByte_cast_correct.
Qed.

Lemma store_byte_cast' : forall x v , store_byte x v |-- store_byte x (unsigned_last_nbits v 8).
Proof.
  intros. 
  apply store_byte_eqm.
  apply Byte_cast_correct.
Qed.

Lemma store_char_cast : forall x v , x # Char |-> v |-- x # UChar |-> unsigned_last_nbits v 8.
Proof.
  intros.
  unfold store_char, store_uchar.
  entailer!.
  - sep_apply store_byte_cast'. entailer!.
  - pose proof (unsigned_Lastnbits_range v 8). lia.
  - pose proof (unsigned_Lastnbits_range v 8).  
    replace Byte.max_unsigned with (2 ^ 8 - 1) by reflexivity.
    lia.
Qed.

Lemma store_uchar_cast : forall x v , x # UChar |-> v |-- x # Char |-> signed_last_nbits v 8.
Proof.
  intros.
  unfold store_char, store_uchar.
  entailer!.
  - sep_apply store_byte_cast. entailer!.
  - pose proof (signed_Lastnbits_range v 8).
    replace Byte.max_signed with (2 ^ 7 - 1) by reflexivity. lia.  
  - pose proof (signed_Lastnbits_range v 8). 
    replace Byte.min_signed with (- 2 ^ 7) by reflexivity. lia.
Qed.

Lemma store_short_cast : forall x v , x # Short |-> v |-- x # UShort |-> unsigned_last_nbits v 16.
Proof.
  intros.
  unfold store_short, store_ushort.
  entailer!.
  - unfold store_2byte.
    Intros z1 z2.
    sep_apply (store_byte_cast' x).
    sep_apply (store_byte_cast' (x + 1)).
    entailer!.
    Exists (unsigned_last_nbits z1 8).
    Exists (unsigned_last_nbits z2 8).
    entailer!.
    eapply merge_short_value_eqm.
    + apply unsigned_Lastnbits_mod_correct. lia.
    + eapply merge_short_eqm; try apply byte_eqm_unsigned_last_8; exact H0.
  - pose proof (unsigned_Lastnbits_range v 16). lia.
  - pose proof (unsigned_Lastnbits_range v 16). 
    lia.
Qed.

Lemma store_ushort_cast : forall x v , x # UShort |-> v |-- x # Short |-> signed_last_nbits v 16.
Proof.
  intros.
  unfold store_short, store_ushort.
  entailer!.
  - unfold store_2byte.
    Intros z1 z2.
    sep_apply (store_byte_cast x).
    sep_apply (store_byte_cast (x + 1)).
    entailer!.
    Exists (signed_last_nbits z1 8).
    Exists (signed_last_nbits z2 8).
    entailer!.
    eapply merge_short_value_eqm.
    + apply signed_Lastnbits_mod_correct. lia.
    + eapply merge_short_eqm; try apply byte_eqm_signed_last_8; exact H0.
  - pose proof (signed_Lastnbits_range v 16). lia.
  - pose proof (signed_Lastnbits_range v 16). lia. 
Qed. 

Lemma store_int_cast : forall x v , x # Int |-> v |-- x # UInt |-> unsigned_last_nbits v 32.
Proof.
  intros.
  unfold store_int, store_uint.
  entailer!.
  - unfold store_4byte. 
    Intros z1 z2 z3 z4.
    sep_apply (store_byte_cast' x).
    sep_apply (store_byte_cast' (x + 1)).
    sep_apply (store_byte_cast' (x + 2)).
    sep_apply (store_byte_cast' (x + 3)).
    Exists (unsigned_last_nbits z1 8).
    Exists (unsigned_last_nbits z2 8).
    Exists (unsigned_last_nbits z3 8).
    Exists (unsigned_last_nbits z4 8).
    entailer!.
    eapply merge_int_value_eqm.
    + apply unsigned_Lastnbits_mod_correct. lia.
    + eapply merge_int_eqm; try apply byte_eqm_unsigned_last_8; exact H0.
  - pose proof (unsigned_Lastnbits_range v 32). lia.  
  - pose proof (unsigned_Lastnbits_range v 32). 
    replace Int.max_unsigned with (2 ^ 32 - 1) by reflexivity. lia.
Qed.

Lemma store_uint_cast : forall x v , x # UInt |-> v |-- x # Int |-> signed_last_nbits v 32.
Proof.
  intros.
  unfold store_int, store_uint.
  entailer!.
  - unfold store_4byte. 
    Intros z1 z2 z3 z4.
    sep_apply (store_byte_cast x).
    sep_apply (store_byte_cast (x + 1)).
    sep_apply (store_byte_cast (x + 2)).
    sep_apply (store_byte_cast (x + 3)).
    Exists (signed_last_nbits z1 8).
    Exists (signed_last_nbits z2 8).
    Exists (signed_last_nbits z3 8).
    Exists (signed_last_nbits z4 8).
    entailer!.
    eapply merge_int_value_eqm.
    + apply signed_Lastnbits_mod_correct. lia.
    + eapply merge_int_eqm; try apply byte_eqm_signed_last_8; exact H0.
  - pose proof (signed_Lastnbits_range v 32).
    replace Int.max_signed with (2 ^ 31 - 1) by reflexivity. lia.  
  - pose proof (signed_Lastnbits_range v 32). 
    replace Int.min_signed with (- 2 ^ 31) by reflexivity. lia.
Qed.

Lemma store_int64_cast : forall x v , x # Int64 |-> v |-- x # UInt64 |-> unsigned_last_nbits v 64.
Proof.
  intros.
  unfold store_int64, store_uint64.
  entailer!.
  - unfold store_8byte. 
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    sep_apply (store_byte_cast' x).
    sep_apply (store_byte_cast' (x + 1)).
    sep_apply (store_byte_cast' (x + 2)).
    sep_apply (store_byte_cast' (x + 3)).
    sep_apply (store_byte_cast' (x + 4)).
    sep_apply (store_byte_cast' (x + 5)).
    sep_apply (store_byte_cast' (x + 6)).
    sep_apply (store_byte_cast' (x + 7)).
    Exists (unsigned_last_nbits z1 8).
    Exists (unsigned_last_nbits z2 8).
    Exists (unsigned_last_nbits z3 8).
    Exists (unsigned_last_nbits z4 8).
    Exists (unsigned_last_nbits z5 8).
    Exists (unsigned_last_nbits z6 8).
    Exists (unsigned_last_nbits z7 8).
    Exists (unsigned_last_nbits z8 8).
    entailer!.
    eapply merge_int64_value_eqm.
    + apply unsigned_Lastnbits_mod_correct. lia.
    + eapply merge_int64_eqm; try apply byte_eqm_unsigned_last_8; exact H0.
  - pose proof (unsigned_Lastnbits_range v 64). lia.
  - pose proof (unsigned_Lastnbits_range v 64).
    replace Int64.max_unsigned with (2 ^ 64 - 1) by reflexivity. lia. 
Qed.

Lemma store_uint64_cast : forall x v , x # UInt64 |-> v |-- x # Int64 |-> signed_last_nbits v 64.
Proof.
  intros.
  unfold store_int64, store_uint64.
  entailer!.
  - unfold store_8byte. 
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    sep_apply (store_byte_cast x).
    sep_apply (store_byte_cast (x + 1)).
    sep_apply (store_byte_cast (x + 2)).
    sep_apply (store_byte_cast (x + 3)).
    sep_apply (store_byte_cast (x + 4)).
    sep_apply (store_byte_cast (x + 5)).
    sep_apply (store_byte_cast (x + 6)).
    sep_apply (store_byte_cast (x + 7)).
    Exists (signed_last_nbits z1 8).
    Exists (signed_last_nbits z2 8).
    Exists (signed_last_nbits z3 8).
    Exists (signed_last_nbits z4 8).
    Exists (signed_last_nbits z5 8).
    Exists (signed_last_nbits z6 8).
    Exists (signed_last_nbits z7 8).
    Exists (signed_last_nbits z8 8).
    entailer!.
    eapply merge_int64_value_eqm.
    + apply signed_Lastnbits_mod_correct. lia.
    + eapply merge_int64_eqm; try apply byte_eqm_signed_last_8; exact H0.
  - pose proof (signed_Lastnbits_range v 64).
    replace Int64.max_signed with (2 ^ 63 - 1) by reflexivity. lia. 
  - pose proof (signed_Lastnbits_range v 64).
    replace Int64.min_signed with (- 2 ^ 63) by reflexivity. lia.
Qed.

Lemma valid_store_char : forall x v, x # Char |-> v |-- “ Byte.min_signed <= v <= Byte.max_signed /\ isvalidptr_char x ”.
Proof.
  intros.
  unfold store_char.
  entailer!.
Qed.

Lemma valid_store_uchar : forall x v, x # UChar |-> v |-- “ 0 <= v <= Byte.max_unsigned /\ isvalidptr_char x ”.
Proof.
  intros.
  unfold store_uchar.
  entailer!.
Qed.

Lemma valid_undef_store_char : forall x, x # Char |->_ |-- “ isvalidptr_char x ”.
Proof.
  intros.
  unfold undef_store_char.
  entailer!.
Qed.

Lemma valid_undef_store_uchar : forall x, x # UChar |->_ |-- “ isvalidptr_char x ”.
Proof.
  intros.
  unfold undef_store_uchar.
  entailer!.
Qed.

Lemma valid_store_short : forall x v, x # Short |-> v |-- “ -32768 <= v <= 32767 /\ isvalidptr_short x ”.
Proof.
  intros.
  unfold store_short.
  entailer!.
Qed.

Lemma valid_store_ushort : forall x v, x # UShort |-> v |-- “ 0 <= v <= 65535 /\ isvalidptr_short x ”.
Proof.
  intros.
  unfold store_ushort.
  entailer!.
Qed.

Lemma valid_undef_store_short : forall x, x # Short |->_ |-- “ isvalidptr_short x ”.
Proof.
  intros.
  unfold undef_store_short.
  entailer!.
Qed.

Lemma valid_undef_store_ushort : forall x, x # UShort |->_ |-- “ isvalidptr_short x ”.
Proof.
  intros.
  unfold undef_store_ushort.
  entailer!.
Qed.

Lemma valid_store_int : forall x v, x # Int |-> v |-- “ Int.min_signed <= v <= Int.max_signed /\ isvalidptr_int x ”.
Proof.
  intros.
  unfold store_int.
  entailer!.
Qed.

Lemma valid_store_uint : forall x v, x # UInt |-> v |-- “ 0 <= v <= Int.max_unsigned /\ isvalidptr_int x ”.
Proof.
  intros.
  unfold store_uint.
  entailer!.
Qed.

Lemma valid_undef_store_int : forall x, x # Int |->_ |-- “ isvalidptr_int x ”.
Proof.
  intros.
  unfold undef_store_int.
  entailer!.
Qed.

Lemma valid_undef_store_uint : forall x, x # UInt |->_ |-- “ isvalidptr_int x ”.
Proof.
  intros.
  unfold undef_store_uint.
  entailer!.
Qed.

Lemma valid_store_int64 : forall x v, x # Int64 |-> v |-- “ Int64.min_signed <= v <= Int64.max_signed /\ isvalidptr_int64 x ”.
Proof.
  intros.
  unfold store_int64.
  entailer!.
Qed.

Lemma valid_store_uint64 : forall x v, x # UInt64 |-> v |-- “ 0 <= v <= Int64.max_unsigned /\ isvalidptr_int64 x ”.
Proof.
  intros.
  unfold store_uint64.
  entailer!.
Qed.


Lemma valid_store_int128 :
  forall x v,
    x # Int128 |-> v |--
    CRules.coq_prop (Int128.min_signed <= v <= Int128.max_signed /\ isvalidptr_int128 x).
Proof.
  intros.
  unfold store_int128.
  entailer!.
Qed.

Lemma valid_store_uint128 :
  forall x v,
    x # UInt128 |-> v |--
    CRules.coq_prop (0 <= v <= Int128.max_unsigned /\ isvalidptr_int128 x).
Proof.
  intros.
  unfold store_uint128.
  entailer!.
Qed.

Lemma valid_undef_store_int64 : forall x, x # Int64 |->_ |-- “ isvalidptr_int64 x ”.
Proof.
  intros.
  unfold undef_store_int64.
  entailer!.
Qed.

Lemma valid_undef_store_uint64 : forall x, x # UInt64 |->_ |-- “ isvalidptr_int64 x ”.
Proof.
  intros.
  unfold undef_store_uint64.
  entailer!.
Qed.


Lemma valid_undef_store_int128 :
  forall x, x # Int128 |->_ |-- CRules.coq_prop (isvalidptr_int128 x).
Proof.
  intros.
  unfold undef_store_int128.
  entailer!.
Qed.

Lemma valid_undef_store_uint128 :
  forall x, x # UInt128 |->_ |-- CRules.coq_prop (isvalidptr_int128 x).
Proof.
  intros.
  unfold undef_store_uint128.
  entailer!.
Qed.

Lemma valid_store_ptr : forall x v, x # Ptr |-> v |-- “ isvalidptr x /\ valid_ptr_value v ”.
Proof.
  intros.
  unfold store_ptr.
  entailer!.
Qed.

Lemma valid_undef_store_ptr : forall x, x # Ptr |->_ |-- “ isvalidptr x ”.
Proof.
  intros.
  unfold undef_store_ptr.
  entailer!.
Qed.

Lemma undef_store_char_align : forall x, x # Char |->_ |-- store_align_n 1.
Proof.
  intros.
  unfold undef_store_char, store_align_n. simpl.
  Intros. Exists [x].
  simpl.
  entailer!.
  unfold isvalidptr_char in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma store_char_align : forall x v, x # Char |-> v |-- store_align_n 1.
Proof.
  intros.
  sep_apply store_char_undef_store_char.
  sep_apply undef_store_char_align.
  entailer!.
Qed.

Lemma store_byte_align1 : forall x, isvalidptr_char x -> store_byte_noninit x |-- store_align_n 1.
Proof.
  intros.
  unfold store_align_n.
  Exists [x].
  simpl.
  entailer!.
  unfold isvalidptr_char in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma undef_store_uchar_align : forall x, x # UChar |->_ |-- store_align_n 1.
Proof.
  intros.
  unfold undef_store_uchar, store_align_n. simpl.
  Intros. Exists [x].
  simpl.
  entailer!.
  unfold isvalidptr_char in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma store_uchar_align : forall x v, x # UChar |-> v |-- store_align_n 1.
Proof.
  intros.
  sep_apply store_uchar_undef_store_uchar.
  sep_apply undef_store_uchar_align.
  entailer!.
Qed.

Lemma undef_store_bool_align : forall x, x # Bool |->_ |-- store_align_n 1.
Proof.
  intros.
  change (x # UChar |->_ |-- store_align_n 1).
  apply undef_store_uchar_align.
Qed.

Lemma store_bool_align : forall x v, x # Bool |-> v |-- store_align_n 1.
Proof.
  intros.
  sep_apply store_bool_undef_store_bool.
  sep_apply undef_store_bool_align.
  entailer!.
Qed.

Lemma undef_store_int_align4 :
  forall x, x # Int |->_ |-- store_align4_n 1.
Proof.
  intros.
  unfold undef_store_int, store_align4_n. simpl.
  Intros. Exists [x]. 
  simpl. 
  entailer!.
  unfold isvalidptr_int , aligned_4 in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma store_int_align4 : forall x v, x # Int |-> v |-- store_align4_n 1.
Proof.
  intros.
  sep_apply store_int_undef_store_int.
  sep_apply undef_store_int_align4.
  entailer!.
Qed.

Lemma undef_store_uint_align4 :
  forall x, x # UInt |->_ |-- store_align4_n 1.
Proof.
  intros.
  unfold undef_store_uint, store_align4_n. simpl.
  Intros. Exists [x]. 
  simpl. 
  entailer!.
  unfold isvalidptr_int , aligned_4 in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma store_uint_align4 : forall x v, x # UInt |-> v |-- store_align4_n 1.
Proof.
  intros.
  sep_apply store_uint_undef_store_uint.
  sep_apply undef_store_uint_align4.
  entailer!.
Qed.

Lemma undef_store_int64_align4 : forall x, x # Int64 |->_ |-- store_align4_n 2.
Proof.
  intros.
  unfold undef_store_int64, store_align4_n. simpl.
  Intros. Exists (x :: [x + 4]). 
  simpl.
  entailer!.
  - unfold store_8byte_noninit.
    unfold store_4byte_noninit. 
    replace (x + 4 + 1) with (x + 5) by lia.
    replace (x + 4 + 2) with (x + 6) by lia.
    replace (x + 4 + 3) with (x + 7) by lia.
    entailer!.
  - unfold isvalidptr_int64 in H. unfold isvalidptr_int. 
    unfold aligned_4 in *. 
    repeat split ; try lia. 
    rewrite <- Zplus_mod_idemp_l.
    destruct H as [Hlo [Hhi Halign]].
    rewrite Halign. reflexivity.
  - unfold isvalidptr_int64 in H. unfold isvalidptr_int. 
    unfold aligned_4 in *. 
    repeat split ; try lia.
  - unfold isvalidptr_int64, aligned_4 in H. 
    repeat constructor ; try lia. 
Qed.

Lemma store_int64_align4 : forall x v, x # Int64 |-> v |-- store_align4_n 2.
Proof.
  intros.
  sep_apply store_int64_undef_store_int64.
  sep_apply undef_store_int64_align4.
  entailer!.
Qed.

Lemma undef_store_uint64_align4 : forall x, x # UInt64 |->_ |-- store_align4_n 2.
Proof.
  intros.
  unfold undef_store_uint64, store_align4_n. simpl.
  Intros. Exists (x :: [x + 4]). 
  simpl.
  entailer!.
  - unfold store_8byte_noninit.
    unfold store_4byte_noninit. 
    replace (x + 4 + 1) with (x + 5) by lia.
    replace (x + 4 + 2) with (x + 6) by lia.
    replace (x + 4 + 3) with (x + 7) by lia.
    entailer!.
  - unfold isvalidptr_int64 in H. unfold isvalidptr_int. 
    unfold aligned_4 in *. 
    repeat split ; try lia. 
    rewrite <- Zplus_mod_idemp_l.
    destruct H as [Hlo [Hhi Halign]].
    rewrite Halign. reflexivity.
  - unfold isvalidptr_int64 in H. unfold isvalidptr_int. 
    unfold aligned_4 in *. 
    repeat split ; try lia.
  - unfold isvalidptr_int64, aligned_4 in H. 
    repeat constructor ; try lia. 
Qed.

Lemma store_uint64_align4 : forall x v, x # UInt64 |-> v |-- store_align4_n 2.
Proof.
  intros.
  sep_apply store_uint64_undef_store_uint64.
  sep_apply undef_store_uint64_align4.
  entailer!.
Qed.

Lemma aligned_8_aligned_4 :
  forall x, aligned_8 x -> aligned_4 x.
Proof.
  unfold aligned_8, aligned_4.
  intros x H.
  apply Z.mod_divide in H; try lia.
  destruct H as [k Hk].
  subst x.
  replace (k * 8) with ((2 * k) * 4) by ring.
  apply Z_mod_mult.
Qed.

Lemma store_float_aligned4 :
  forall x v,
    x # Float |-> v |-- “ aligned_4 x ”.
Proof.
  intros.
  unfold store_float.
  destruct (bits_of_float_value v); entailer!.
  unfold isvalidptr_float in H. tauto.
Qed.

Lemma store_double_aligned8 :
  forall x v,
    x # Double |-> v |-- “ aligned_8 x ”.
Proof.
  intros.
  unfold store_double.
  destruct (bits_of_double_value v); entailer!.
  unfold isvalidptr_double in H. tauto.
Qed.

Lemma store_finite_float_aligned4 :
  forall x v,
    x # FiniteFloat |-> v |-- “ aligned_4 x ”.
Proof.
  intros.
  unfold store_finite_float.
  apply coq_prop_andp_left. intros _.
  apply store_float_aligned4.
Qed.

Lemma store_finite_double_aligned8 :
  forall x v,
    x # FiniteDouble |-> v |-- “ aligned_8 x ”.
Proof.
  intros.
  unfold store_finite_double.
  apply coq_prop_andp_left. intros _.
  apply store_double_aligned8.
Qed.

Lemma store_long_double_aligned8 :
  forall x v,
    x # LongDouble |-> v |-- CRules.coq_prop (aligned_8 x).
Proof.
  intros.
  unfold store_long_double.
  destruct (bits_of_long_double_value v); entailer!.
  unfold isvalidptr_long_double in H. tauto.
Qed.

Lemma store_finite_long_double_aligned8 :
  forall x v,
    x # FiniteLongDouble |-> v |-- CRules.coq_prop (aligned_8 x).
Proof.
  intros.
  unfold store_finite_long_double.
  apply coq_prop_andp_left. intros _.
  apply store_long_double_aligned8.
Qed.

Lemma undef_store_float_align4 :
  forall x, x # Float |->_ |-- store_align4_n 1.
Proof.
  intros.
  unfold undef_store_float, store_align4_n. simpl.
  Intros. Exists [x].
  simpl.
  entailer!.
  unfold isvalidptr_float, aligned_4 in H.
  constructor; auto; try lia.
  constructor.
Qed.

Lemma store_float_align4 :
  forall x v,
    x # Float |-> v |-- store_align4_n 1.
Proof.
  intros.
  sep_apply store_float_undef_store_float.
  sep_apply undef_store_float_align4.
  entailer!.
Qed.

Lemma undef_store_double_align4 :
  forall x, x # Double |->_ |-- store_align4_n 2.
Proof.
  intros.
  unfold undef_store_double, store_align4_n. simpl.
  Intros. Exists (x :: [x + 4]).
  simpl.
  entailer!.
  - unfold store_8byte_noninit, store_4byte_noninit.
    replace (x + 4 + 1) with (x + 5) by lia.
    replace (x + 4 + 2) with (x + 6) by lia.
    replace (x + 4 + 3) with (x + 7) by lia.
    entailer!.
		  - unfold isvalidptr_double in H. unfold isvalidptr_int.
		    repeat split; try lia.
		    destruct H as [? [ ? H8]].
		    pose proof (aligned_8_aligned_4 x H8) as H4.
		    unfold aligned_4 in *.
		    rewrite <- Zplus_mod_idemp_l.
		    rewrite H4. reflexivity.
	  - unfold isvalidptr_double in H. unfold isvalidptr_int.
	    repeat split; try lia.
	    destruct H as [? [ ? H8]].
	    pose proof (aligned_8_aligned_4 x H8) as H4.
	    exact H4.
  - unfold isvalidptr_double, aligned_8 in H.
    repeat constructor; try lia.
Qed.

Lemma store_double_align4 :
  forall x v,
    x # Double |-> v |-- store_align4_n 2.
Proof.
  intros.
  sep_apply store_double_undef_store_double.
  sep_apply undef_store_double_align4.
  entailer!.
Qed.

Lemma undef_store_ptr_align4 : forall x : addr, ptr_size = 4%nat -> undef_store_ptr x |-- store_align4_n 1.
Proof.
  intros x Hsize.
  unfold undef_store_ptr, store_align4_n. simpl.
  rewrite Hsize.
  Intros.
  assert (Hvalid_int: isvalidptr_int x).
  {
    unfold isvalidptr, isvalidptr_int, aligned_4 in *.
    destruct H as [? [ ? ? ]].
    unfold ptr_size in Hsize.
    unfold ptr_size_Z, Arch.ptr_size_Z in *; rewrite Hsize in *; simpl in *.
    repeat split; try lia.
    apply Arch.ptr_aligned_aligned_4; auto.
  }
  assert (Hinterval: interval_list 3 0 addr_max_unsigned [x]).
  {
    constructor; try constructor.
    - unfold isvalidptr_int in Hvalid_int. lia.
    - unfold isvalidptr_int in Hvalid_int. lia.
  }
  Exists [x].
  simpl.
  entailer!.
Qed.

Lemma store_ptr_align4 : forall (x : addr) v, ptr_size = 4%nat -> x # Ptr |-> v |-- store_align4_n 1.
Proof.
  intros x v Hsize.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply (undef_store_ptr_align4 x Hsize).
  entailer!.
Qed.

Lemma store_byte_valid : forall x y, store_byte_noninit x ** store_byte_noninit y |-- “ x < y \/ y < x ”.
Proof.
  intros.
  unfold store_byte_noninit.
  destruct (Z_lt_ge_dec (x + 1) y).
  - entailer!.
  - destruct (Z_lt_ge_dec (y + 1) x).
    + entailer!.
    + assert (x = y - 1 \/ x = y \/ x = y + 1) by lia.
      destruct H as [ ? | [ ? | ? ]] ; subst.
      * entailer!.
      * prop_apply (dup_store_byte_noninit y). Intros. lia.
      * entailer!.
Qed.

Lemma store_4byte_valid : forall x y, store_4byte_noninit x ** store_4byte_noninit y |-- “ x + 3 < y \/ y + 3 < x ”.
Proof.
  intros.
  unfold store_4byte_noninit.
  destruct (Z_lt_ge_dec (x + 3) y).
  - entailer!. 
  - destruct (Z_lt_ge_dec (y + 3) x).
    + entailer!.
    + assert (x = y - 3 \/ x = y - 2 \/ x = y - 1 \/ x = y \/ x = y + 1 \/ x = y + 2 \/ x = y + 3) by lia.
      destruct H as [? | [ ? | [? | [ ? | [? | [ ? | ? ]]]]]] ; subst.
      * replace (y - 3 + 3) with y by lia. 
        prop_apply (dup_store_byte_noninit y). Intros. lia.
      * replace (y - 2 + 2) with y by lia. 
        prop_apply (dup_store_byte_noninit y). Intros. lia. 
      * replace (y - 1 + 1) with y by lia. 
        prop_apply (dup_store_byte_noninit y). Intros. lia.
      * prop_apply (dup_store_byte_noninit y). Intros. lia.
      * prop_apply (dup_store_byte_noninit (y + 1)). Intros. lia.
      * prop_apply (dup_store_byte_noninit (y + 2)). Intros. lia.
      * prop_apply (dup_store_byte_noninit (y + 3)). Intros. lia. 
Qed.

Lemma store_align4_valid : forall x l, store_align4_list l ** store_4byte_noninit x |-- “ Forall (fun x' => x + 3 < x' \/ x' + 3 < x) l ”.
Proof.
  intros.
  induction l; simpl in *.
  - entailer!.
  - Intros.
    prop_apply (store_4byte_valid a x). Intros.
    prop_apply IHl. Intros.
    entailer!.
    constructor ; auto.
    destruct H0; auto.
Qed.

Lemma store_align4_merge : forall n m, store_align4_n n ** store_align4_n m |-- store_align4_n (n + m).
Proof.
  intros.
  unfold store_align4_n. Intros l1 l2. 
  Exists (l1 ++ l2). destruct H , H0. 
  generalize dependent l2. generalize dependent n. revert m.
  induction H1 ; simpl in * ; intros ; auto.
  - entailer!. cbv in H. lia.  
  - rewrite Zlength_cons in *.
    specialize (IHinterval_list m (n - 1) (ltac:(lia)) l2 H4 H5).
    Intros.
    sep_apply IHinterval_list. Intros.
    destruct H7.
    prop_apply (store_align4_valid x (l ++ l2)). Intros.
    entailer!.
    constructor ; auto.
Qed. 

Lemma store_align4_n_valid : forall n, store_align4_n n |-- “ n <= addr_max_unsigned / 4 + 1 ”.
Proof.
  intros.
  unfold store_align4_n.
  Intros l.
  destruct H.
  rewrite <- H.
  entailer!.
  pose proof interval_list_range l 3 0 addr_max_unsigned
    (ltac:(lia))
    (ltac:(unfold addr_max_unsigned; pose proof Arch.addr_max_unsigned_ge_7; lia))
    H0 as Hrange.
  simpl in Hrange.
  assert (Hdiv: (4 * n) / 4 <= (addr_max_unsigned + 4) / 4).
  {
    apply Z.div_le_mono; lia.
  }
  replace (4 * n) with (n * 4) in Hdiv by ring.
  rewrite Z_div_mult_full in Hdiv by lia.
  replace (addr_max_unsigned + 4) with (1 * 4 + addr_max_unsigned) in Hdiv by ring.
  rewrite Z.div_add_l in Hdiv by lia.
  lia.
Qed.

Lemma store_align_valid : forall x l, store_align_list l ** store_byte_noninit x |-- “ Forall (fun x' => x + 0 < x' \/ x' + 0 < x) l ”.
Proof.
  intros.
  induction l; simpl in *.
  - entailer!.
  - Intros.
    prop_apply (store_byte_valid a x). Intros.
    prop_apply IHl. Intros.
    entailer!.
    constructor ; auto.
    destruct H0; lia.
Qed.

Lemma store_align_merge : forall n m, store_align_n n ** store_align_n m |-- store_align_n (n + m).
Proof.
  intros.
  unfold store_align_n. Intros l1 l2.
  Exists (l1 ++ l2). destruct H , H0.
  generalize dependent l2. generalize dependent n. revert m.
  induction H1 ; simpl in * ; intros ; auto.
  - entailer!. cbv in H. lia.
  - rewrite Zlength_cons in *.
    specialize (IHinterval_list m (n - 1) (ltac:(lia)) l2 H4 H5).
    Intros.
    sep_apply IHinterval_list. Intros.
    destruct H7.
    prop_apply (store_align_valid x (l ++ l2)). Intros.
    entailer!.
    constructor ; auto.
Qed.

Lemma undef_store_short_align : forall x, x # Short |->_ |-- store_align_n 2.
Proof.
  intros.
  unfold undef_store_short, store_2byte_noninit.
  Intros.
  sep_apply (store_byte_align1 x ltac:(
    unfold isvalidptr_short, isvalidptr_char in H;
    destruct H as [ ? [ ? ? ]];
    split; lia)).
  sep_apply (store_byte_align1 (x + 1) ltac:(
    unfold isvalidptr_short, isvalidptr_char in H;
    destruct H as [? [ ? ? ]];
    split; lia)).
  sep_apply (store_align_merge 1 1).
  replace (1 + 1) with 2 by lia.
  entailer!.
Qed.

Lemma store_short_align : forall x v, x # Short |-> v |-- store_align_n 2.
Proof.
  intros.
  sep_apply store_short_undef_store_short.
  sep_apply undef_store_short_align.
  entailer!.
Qed.

Lemma undef_store_ushort_align : forall x, x # UShort |->_ |-- store_align_n 2.
Proof.
  intros.
  unfold undef_store_ushort, store_2byte_noninit.
  Intros.
  sep_apply (store_byte_align1 x ltac:(
    unfold isvalidptr_short, isvalidptr_char in H;
    destruct H as [ ? [ ? ? ]];
    split; lia)).
  sep_apply (store_byte_align1 (x + 1) ltac:(
    unfold isvalidptr_short, isvalidptr_char in H;
    destruct H as [? [ ? ? ]];
    split; lia)).
  sep_apply (store_align_merge 1 1).
  replace (1 + 1) with 2 by lia.
  entailer!.
Qed.

Lemma store_ushort_align : forall x v, x # UShort |-> v |-- store_align_n 2.
Proof.
  intros.
  sep_apply store_ushort_undef_store_ushort.
  sep_apply undef_store_ushort_align.
  entailer!.
Qed.

Lemma store_bytes_noninit_align : forall n x,
  0 <= x ->
  x + Z.of_nat n - 1 <= addr_max_unsigned ->
  store_bytes_noninit x n |-- store_align_n (Z.of_nat n).
Proof.
  induction n; intros x Hlo Hhi; simpl.
  - unfold store_align_n.
    Exists nil.
    simpl.
    entailer!.
    constructor.
  - sep_apply (store_byte_align1 x ltac:(unfold isvalidptr_char; split; lia)).
    sep_apply (IHn (x + 1) ltac:(lia) ltac:(
      replace (x + 1 + Z.of_nat n - 1) with (x + Z.of_nat (S n) - 1) by lia;
      lia)).
    sep_apply (store_align_merge 1 (Z.of_nat n)).
    replace (1 + Z.of_nat n) with (Z.of_nat (S n)) by lia.
    entailer!.
Qed.

Lemma store_align_n_valid : forall n, store_align_n n |-- “ n <= addr_max_unsigned / 1 + 1 ”.
Proof.
  intros.
  unfold store_align_n.
  Intros l.
  destruct H.
  rewrite <- H.
  entailer!.
  pose proof interval_list_range l 0 0 addr_max_unsigned (ltac:(lia)) (ltac:(unfold addr_max_unsigned; pose proof Arch.addr_max_unsigned_ge_7; lia)) H0.
  simpl in *.
  rewrite Z.div_1_r.
  lia.
Qed.

Lemma store_align4_to_store_align : forall n, store_align4_n n |-- store_align_n (4 * n).
Proof.
  intros.
  unfold store_align4_n, store_align_n.
  Intros l.
  generalize dependent n.
  induction l ; intros.
  - Exists nil. rewrite Zlength_nil in *. entailer!.
    constructor.
  - simpl store_align4_list. Intros.
    sep_apply (IHl (n - 1)).
    Intros l0.
    + unfold store_4byte_noninit.
      prop_apply (store_align_valid a l0). Intros.
      prop_apply (store_align_valid (a + 1) l0). Intros.
      prop_apply (store_align_valid (a + 2) l0). Intros.
      prop_apply (store_align_valid (a + 3) l0). Intros.
      Exists ((a :: (a + 1) :: (a + 2) :: (a + 3) :: l0)).
      simpl store_align_list. unfold isvalidptr_char.
      unfold isvalidptr_int in H0. entailer!.
      repeat rewrite Zlength_cons. lia.
      destruct H2.
      repeat constructor ; auto ; try lia.
    + rewrite Zlength_cons in H.
      split ; try lia.
      destruct H. inversion H1.
      auto.
Qed.

Lemma store_float_align :
  forall x v,
    x # Float |-> v |-- store_align_n 4.
Proof.
  intros.
  eapply derivable1_trans.
  - apply store_float_align4.
  - replace 4 with (4 * 1) by lia.
    apply store_align4_to_store_align.
Qed.

Lemma store_double_align :
  forall x v,
    x # Double |-> v |-- store_align_n 8.
Proof.
  intros.
  eapply derivable1_trans.
  - apply store_double_align4.
  - replace 8 with (4 * 2) by lia.
    apply store_align4_to_store_align.
Qed.

Lemma undef_store_long_double_align :
  forall x,
    x # LongDouble |->_ |-- store_align_n 16.
Proof.
  intros.
  unfold undef_store_long_double, store_16byte_noninit.
  apply coq_prop_andp_left. intros Hvalid.
  apply store_bytes_noninit_align; unfold isvalidptr_long_double in Hvalid; lia.
Qed.

Lemma store_long_double_align :
  forall x v,
    x # LongDouble |-> v |-- store_align_n 16.
Proof.
  intros.
  sep_apply store_long_double_undef_store_long_double.
  sep_apply undef_store_long_double_align.
  entailer!.
Qed.

Lemma undef_store_int128_align :
  forall x,
    x # Int128 |->_ |-- store_align_n 16.
Proof.
  intros.
  unfold undef_store_int128, store_16byte_noninit.
  apply coq_prop_andp_left. intros Hvalid.
  apply store_bytes_noninit_align; unfold isvalidptr_int128 in Hvalid; lia.
Qed.

Lemma store_int128_align :
  forall x v,
    x # Int128 |-> v |-- store_align_n 16.
Proof.
  intros.
  sep_apply store_int128_undef_store_int128.
  sep_apply undef_store_int128_align.
  entailer!.
Qed.

Lemma undef_store_uint128_align :
  forall x,
    x # UInt128 |->_ |-- store_align_n 16.
Proof.
  intros.
  unfold undef_store_uint128, store_16byte_noninit.
  apply coq_prop_andp_left. intros Hvalid.
  apply store_bytes_noninit_align; unfold isvalidptr_int128 in Hvalid; lia.
Qed.

Lemma store_uint128_align :
  forall x v,
    x # UInt128 |-> v |-- store_align_n 16.
Proof.
  intros.
  sep_apply store_uint128_undef_store_uint128.
  sep_apply undef_store_uint128_align.
  entailer!.
Qed.

Lemma store_finite_float_align :
  forall x v,
    x # FiniteFloat |-> v |-- store_align_n 4.
Proof.
  intros.
  unfold store_finite_float.
  apply coq_prop_andp_left. intros _.
  apply store_float_align.
Qed.

Lemma store_finite_double_align :
  forall x v,
    x # FiniteDouble |-> v |-- store_align_n 8.
Proof.
  intros.
  unfold store_finite_double.
  apply coq_prop_andp_left. intros _.
  apply store_double_align.
Qed.

Lemma store_finite_long_double_align :
  forall x v,
    x # FiniteLongDouble |-> v |-- store_align_n 16.
Proof.
  intros.
  unfold store_finite_long_double.
  apply coq_prop_andp_left. intros _.
  apply store_long_double_align.
Qed.

Lemma undef_store_ptr_undef_store_uint64 :
  forall x, ptr_size = 8%nat -> x # Ptr |->_ |-- x # UInt64 |->_.
Proof.
  intros x Hsize.
  unfold undef_store_ptr, undef_store_uint64.
  rewrite Hsize.
  entailer!.
  unfold isvalidptr, isvalidptr_int64, aligned_4 in *.
  destruct H as [ ? [ ? ? ]].
  unfold ptr_size in Hsize.
  unfold ptr_size_Z, Arch.ptr_size_Z in *; rewrite Hsize in *; simpl in *.
  repeat split; try lia.
  apply Arch.ptr_aligned_aligned_4; auto.
Qed.

Lemma undef_store_ptr_undef_store_int64 :
  forall x, ptr_size = 8%nat -> x # Ptr |->_ |-- x # Int64 |->_.
Proof.
  intros x Hsize.
  unfold undef_store_ptr, undef_store_int64.
  rewrite Hsize.
  entailer!.
  unfold isvalidptr, isvalidptr_int64, aligned_4 in *.
  destruct H as [? [ ? ? ]].
  unfold ptr_size in Hsize.
  unfold ptr_size_Z, Arch.ptr_size_Z in *; rewrite Hsize in *; simpl in *.
  repeat split; try lia.
  apply Arch.ptr_aligned_aligned_4; auto.
Qed.

Lemma undef_store_ptr_align :
  forall x, x # Ptr |->_ |-- store_align_n ptr_size_Z.
Proof.
  intros x.
  destruct Arch.ptr_size_32_or_64 as [Hsize | Hsize].
  - eapply derivable1_trans.
    + apply undef_store_ptr_align4. unfold ptr_size. exact Hsize.
    + unfold ptr_size_Z, ptr_size, Arch.ptr_size_Z. rewrite Hsize. simpl.
      replace 4 with (4 * 1) by lia.
      apply store_align4_to_store_align.
  - eapply derivable1_trans.
    + eapply derivable1_trans.
      * apply undef_store_ptr_undef_store_uint64. unfold ptr_size. exact Hsize.
      * apply undef_store_uint64_align4.
    + unfold ptr_size_Z, ptr_size, Arch.ptr_size_Z. rewrite Hsize. simpl.
      replace 8 with (4 * 2) by lia.
      apply store_align4_to_store_align.
Qed.

Lemma store_ptr_align :
  forall x v, x # Ptr |-> v |-- store_align_n ptr_size_Z.
Proof.
  intros.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply undef_store_ptr_align.
  entailer!.
Qed.

Lemma store_ptr_store_uint : forall x v,
  ptr_size = 4%nat ->
  addr_max_unsigned = Int.max_unsigned ->
  x # Ptr |-> v |-- x # UInt |-> v.
Proof.
  intros x v Hsize Haddr.
  unfold store_ptr, store_uint.
  rewrite Hsize.
  Intros.
  destruct H as [[HpLo [HpHi HpAlign]] [HvLo HvHi]].
  assert (Hvalid_int: isvalidptr_int x).
  {
    unfold isvalidptr, isvalidptr_int, aligned_4 in *.
    unfold ptr_size in Hsize.
    unfold ptr_size_Z, Arch.ptr_size_Z in *; rewrite Hsize in *; simpl in *.
    refine (conj _ (conj _ _)); [lia | lia | exact (Arch.ptr_aligned_aligned_4 x HpAlign)].
  }
  assert (Huint_range: 0 <= v /\ v <= Int.max_unsigned).
  {
    unfold addr_max_unsigned in Haddr.
    unfold addr_max_unsigned in HvHi.
    rewrite Haddr in HvHi.
    lia.
  }
  entailer!.
Qed.

Lemma store_ptr_store_uint64 : forall x v,
  ptr_size = 8%nat ->
  addr_max_unsigned = Int64.max_unsigned ->
  x # Ptr |-> v |-- x # UInt64 |-> v.
Proof.
  intros x v Hsize Haddr.
  unfold store_ptr, store_uint64.
  rewrite Hsize.
  Intros.
  destruct H as [[HpLo [HpHi HpAlign]] [HvLo HvHi]].
  assert (Hvalid_int64: isvalidptr_int64 x).
  {
    unfold isvalidptr, isvalidptr_int64, aligned_4 in *.
    unfold ptr_size in Hsize.
    unfold ptr_size_Z, Arch.ptr_size_Z in *; rewrite Hsize in *; simpl in *.
    refine (conj _ (conj _ _)); [lia | lia | exact (Arch.ptr_aligned_aligned_4 x HpAlign)].
  }
  assert (Huint64_range: 0 <= v /\ v <= Int64.max_unsigned).
  {
    unfold addr_max_unsigned in Haddr.
    unfold addr_max_unsigned in HvHi.
    rewrite Haddr in HvHi.
    lia.
  }
  entailer!.
Qed.

End StoreLibSig.
