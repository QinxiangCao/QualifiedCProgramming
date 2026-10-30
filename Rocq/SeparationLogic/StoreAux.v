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

Module Type StoreLibSig (ArchImpl : CArchSig) (Endian : CEndianSig) (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig ArchImpl Endian CRules).

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

Import Vector.VectorNotations.
Close Scope vector_scope.

Lemma store_bytes_eqm : forall n x (bytes bytes' : Vector.t Z n),
  bytes_eqm bytes bytes' -> store_bytes x bytes |-- store_bytes x bytes'.
Proof.
  induction n as [|n IH]; intros x bytes bytes' Heqm.
  - apply derivable1_refl.
  - revert Heqm.
    apply (Vector.caseS' bytes). clear bytes. intros z bytes.
    apply (Vector.caseS' bytes'). clear bytes'. intros z' bytes' Heqm.
    simpl in *.
    destruct Heqm as [Hhead Htail].
    sep_apply (store_byte_eqm x z z' Hhead).
    sep_apply (IH (x + 1) bytes bytes' Htail).
    entailer!.
Qed.

Lemma store_bytes_append : forall n m x
    (left : Vector.t Z n) (right : Vector.t Z m),
  store_bytes x (Vector.append left right) --||--
  store_bytes x left ** store_bytes (x + Z.of_nat n) right.
Proof.
  intros n m x left right.
  revert m x right.
  induction left as [|z n left IH]; intros m x right.
  - simpl.
    rewrite Z.add_0_r.
    normalize.
    reflexivity.
  - simpl.
    rewrite (IH m (x + 1) right).
    replace (x + Z.pos (Pos.of_succ_nat n)) with (x + 1 + Z.of_nat n) by lia.
    rewrite logic_equiv_sepcon_assoc.
    reflexivity.
Qed.

Lemma store_bytes_Z_split : forall n m x v,
  store_bytes_Z x (n + m) v --||--
  EX left : Vector.t Z n, EX right : Vector.t Z m,
    “ merge_n_bytes (Vector.append left right) v ” &&
    (store_bytes x left ** store_bytes (x + Z.of_nat n) right).
Proof.
  intros n m x v.
  unfold store_bytes_Z.
  split.
  - Intros bytes.
    destruct (Vector.splitat n bytes) as [left right] eqn:Hsplit.
    pose proof (VectorSpec.append_splitat left right bytes Hsplit) as Happend.
    subst bytes.
    Exists left right.
    sep_apply (proj1 (store_bytes_append n m x left right)).
    entailer!.
  - Intros left right.
    Exists (Vector.append left right).
    sep_apply (proj2 (store_bytes_append n m x left right)).
    entailer!.
Qed.

Fixpoint byte_vector_ex (n : nat) :
    (Vector.t Z n -> CRules.expr) -> CRules.expr :=
  match n with
  | O => fun F => F []%vector
  | S n' => fun F => CRules.exp (fun z : Z =>
      byte_vector_ex n' (fun tail => F (z :: tail)%vector))
  end.

Lemma byte_vector_ex_equiv : forall n (F : Vector.t Z n -> CRules.expr),
  (EX bytes : Vector.t Z n, F bytes) --||-- byte_vector_ex n F.
Proof.
  induction n as [|n IH]; intros F; cbn [byte_vector_ex].
  - split.
    + Intros bytes.
      refine (Vector.case0 (fun b => F b |-- F []%vector) _ bytes).
      apply derivable1_refl.
    + Exists []%vector. apply derivable1_refl.
  - split.
    + Intros bytes.
      apply (Vector.caseS' bytes). intros z tail.
      Exists z.
      rewrite <- (IH (fun tail => F (z :: tail)%vector)).
      Exists tail. apply derivable1_refl.
    + Intros z.
      rewrite <- (IH (fun tail => F (z :: tail)%vector)).
      Intros tail.
      Exists (z :: tail)%vector. apply derivable1_refl.
Qed.

Lemma store_bytes_Z_curried : forall n x v,
  store_bytes_Z x n v --||--
  byte_vector_ex n (fun bytes =>
    “ merge_n_bytes bytes v ” && store_bytes x bytes).
Proof.
  intros n x v. unfold store_bytes_Z. apply byte_vector_ex_equiv.
Qed.

Lemma store_byte_undef_store_byte: forall p v,
  store_byte p v |-- undef_store_byte p.
Proof.
  unfold store_byte, undef_store_byte.
  intros p v m Hstore.
  eapply mstore_mstore_noninit; exact Hstore.
Qed.

Lemma store_bytes_undef_store_bytes :
  forall a len (bytes : Vector.t Z len),
    store_bytes a bytes |-- undef_store_bytes a len.
Proof.
  intros a len.
  revert a.
  induction len as [|len IH]; intros a bytes.
  - apply derivable1_refl.
  - simpl.
    sep_apply (store_byte_undef_store_byte a (Vector.hd bytes)).
    sep_apply (IH (a + 1) (Vector.tl bytes)).
    entailer!.
Qed.

Lemma store_bytes_Z_undef_store_bytes :
  forall a len v,
    store_bytes_Z a len v |-- undef_store_bytes a len.
Proof.
  intros a len v. unfold store_bytes_Z.
  Intros bytes.
  sep_apply (store_bytes_undef_store_bytes a len bytes).
  entailer!.
Qed.

Lemma store_byte_equiv_store_bytes_Z a v :
    (store_byte a v) --||-- (store_bytes_Z a 1 v).
Proof.
  unfold store_byte, store_bytes_Z.
  split.
  - Exists [v]%vector.
    cbn.
    assert (Hmerge : merge_n_bytes [v]%vector v).
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

Lemma store_int_expand : forall n align x v,
  store_integer n align x v --||--
  “ (0 <= x /\ x + Z.of_nat n - 1 <= addr_max_unsigned /\ aligned align x) /\
    v <= 2 ^ (8 * Z.of_nat n - 1) - 1 /\
    v >= - 2 ^ (8 * Z.of_nat n - 1) ” && store_bytes_Z x n v.
Proof.
  unfold store_integer, logic_equiv, derivable1, andp, coq_prop,
    valid_object, Arch.valid_object, Arch.valid_addr_range,
    aligned, addr_max_unsigned, valid_signed_value.
  intros n align x v.
  pose proof (Nat2Z.is_nonneg n).
  split; intros m [Hvalid Hbytes]; split;
    [intuition lia | exact Hbytes | intuition lia | exact Hbytes].
Qed.

Lemma store_uint_expand : forall n align x v,
  store_uinteger n align x v --||--
  “ (0 <= x /\ x + Z.of_nat n - 1 <= addr_max_unsigned /\ aligned align x) /\
    v >= 0 /\ v <= 2 ^ (8 * Z.of_nat n) - 1 ” && store_bytes_Z x n v.
Proof.
  unfold store_uinteger, logic_equiv, derivable1, andp, coq_prop,
    valid_object, Arch.valid_object, Arch.valid_addr_range,
    aligned, addr_max_unsigned, valid_unsigned_value.
  intros n align x v.
  pose proof (Nat2Z.is_nonneg n).
  split; intros m [Hvalid Hbytes]; split;
    [intuition lia | exact Hbytes | intuition lia | exact Hbytes].
Qed.

Lemma undef_store_int_expand : forall n align x,
  undef_store_integer n align x --||--
  “ 0 <= x /\ x + Z.of_nat n - 1 <= addr_max_unsigned /\ aligned align x ” &&
  undef_store_bytes x n.
Proof.
  unfold undef_store_integer, logic_equiv, derivable1, andp, coq_prop,
    valid_object, Arch.valid_object, Arch.valid_addr_range,
    aligned, addr_max_unsigned.
  intros n align x. pose proof (Nat2Z.is_nonneg n).
  split; intros m [Hvalid Hbytes]; split;
    [intuition lia | exact Hbytes | intuition lia | exact Hbytes].
Qed.

Lemma store_bytes_Z_2_unfold a v :
  store_bytes_Z a 2 v --||--
  CRules.exp (fun z1 =>
  CRules.exp (fun z2 =>
    CRules.andp
    (CRules.coq_prop (merge_n_bytes [z1; z2]%vector v))
    (CRules.sepcon (store_byte a z1) (store_byte (a+1) z2))
  )).
Proof.
  rewrite store_bytes_Z_curried.
  cbn [byte_vector_ex store_bytes Vector.hd Vector.tl].
  split; Intros z1 z2; Exists z1 z2; entailer!.
Qed.

Lemma store_bytes_Z_4_unfold a v :
  store_bytes_Z a 4 v --||--
  CRules.exp (fun z1 =>
  CRules.exp (fun z2 =>
  CRules.exp (fun z3 =>
  CRules.exp (fun z4 =>
    CRules.andp
    (CRules.coq_prop (merge_n_bytes [z1; z2; z3; z4]%vector v))
    (CRules.sepcon (store_byte a z1)
      (CRules.sepcon (store_byte (a+1) z2)
        (CRules.sepcon (store_byte (a+2) z3) (store_byte (a+3) z4))
    )
  ))))).
Proof.
  rewrite store_bytes_Z_curried.
  cbn [byte_vector_ex store_bytes].
  split; Intros z1 z2 z3 z4; Exists z1 z2 z3 z4;
    repeat (rewrite <- Z.add_assoc; cbn); entailer!.
Qed.

Lemma store_bytes_Z_8_unfold a v :
  store_bytes_Z a 8 v --||--
  CRules.exp (fun z1 =>
  CRules.exp (fun z2 =>
  CRules.exp (fun z3 =>
  CRules.exp (fun z4 =>
  CRules.exp (fun z5 =>
  CRules.exp (fun z6 =>
  CRules.exp (fun z7 =>
  CRules.exp (fun z8 =>
    CRules.andp
    (CRules.coq_prop (merge_n_bytes [z1; z2; z3; z4; z5; z6; z7; z8]%vector v))
    (CRules.sepcon (store_byte a z1)
      (CRules.sepcon (store_byte (a+1) z2)
        (CRules.sepcon (store_byte (a+2) z3)
          (CRules.sepcon (store_byte (a+3) z4)
            (CRules.sepcon (store_byte (a+4) z5)
              (CRules.sepcon (store_byte (a+5) z6)
                (CRules.sepcon (store_byte (a+6) z7) (store_byte (a+7) z8)
                )
              )
            )
          )
        )
      )
    )
  )))))))).
Proof.
  rewrite store_bytes_Z_curried.
  cbn [byte_vector_ex store_bytes].
  split; Intros z1 z2 z3 z4; Intros z5 z6 z7 z8;
    Exists z1 z2 z3 z4; Exists z5 z6 z7 z8;
    repeat (rewrite <- Z.add_assoc; cbn); entailer!.
Qed.

(* Integer storage is parameterized by byte count and alignment. *)
Lemma store_bytes_Z_value_eqm : forall x n v v',
  v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) ->
  store_bytes_Z x n v |-- store_bytes_Z x n v'.
Proof.
  intros x n v v' Hmod. unfold store_bytes_Z.
  Intros bytes. Exists bytes. entailer!.
  eapply merge_n_bytes_value_eqm; eauto.
Qed.

(* The signed and unsigned predicates differ only in their value condition.
   Keep the resource and object arguments in one proof for both variants. *)
Lemma store_number_change : forall (P Q : Z -> Prop) n align x v v',
  (P v -> Q v') ->
  v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) ->
  (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v) |--
  (“ valid_object x (Z.of_nat n) align /\ Q v' ” && store_bytes_Z x n v').
Proof.
  intros P Q n align x v v' Hrange Hmod.
  apply derivable1_andp_mono.
  - apply coq_prop_imply. intros [Hobject Hv].
    split; [exact Hobject | now apply Hrange].
  - apply store_bytes_Z_value_eqm. exact Hmod.
Qed.

Lemma store_number_valid_object : forall (P : Z -> Prop) n align x v,
  (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v) |--
  “ valid_object x (Z.of_nat n) align ”.
Proof.
  intros. entailer!.
Qed.

Lemma store_number_value_range : forall (P : Z -> Prop) n align x v,
  (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v) |--
  “ P v ”.
Proof.
  intros. entailer!.
Qed.

Lemma store_number_forget : forall (P : Z -> Prop) n align x v,
  (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v) |--
  undef_store_integer n align x.
Proof.
  intros P n align x v. unfold undef_store_integer.
  apply derivable1_andp_mono.
  - apply coq_prop_imply. intros [Hobject _]. exact Hobject.
  - apply store_bytes_Z_undef_store_bytes.
Qed.

Lemma store_int_to_uint : forall n align x v,
  (0 < n)%nat ->
  store_integer n align x v |--
  store_uinteger n align x (unsigned_last_nbits v (8 * Z.of_nat n)).
Proof.
  intros n align x v Hn.
  unfold store_integer, store_uinteger.
  eapply store_number_change.
  - intros _. unfold valid_unsigned_value.
    apply unsigned_Lastnbits_range. lia.
  - apply unsigned_Lastnbits_mod_correct. lia.
Qed.

Lemma store_uint_to_int : forall n align x v,
  (0 < n)%nat ->
  store_uinteger n align x v |--
  store_integer n align x (signed_last_nbits v (8 * Z.of_nat n)).
Proof.
  intros n align x v Hn.
  unfold store_integer, store_uinteger.
  eapply store_number_change.
  - intros _. unfold valid_signed_value.
    apply signed_Lastnbits_range. lia.
  - apply signed_Lastnbits_mod_correct. lia.
Qed.

Lemma store_int_valid_object : forall n align x v,
  store_integer n align x v |-- “ valid_object x (Z.of_nat n) align ”.
Proof.
  intros. unfold store_integer. apply store_number_valid_object.
Qed.

Lemma store_uint_valid_object : forall n align x v,
  store_uinteger n align x v |-- “ valid_object x (Z.of_nat n) align ”.
Proof.
  intros. unfold store_uinteger. apply store_number_valid_object.
Qed.

Lemma undef_store_int_valid_object : forall n align x,
  undef_store_integer n align x |-- “ valid_object x (Z.of_nat n) align ”.
Proof.
  intros. unfold undef_store_integer. entailer!.
Qed.

Lemma store_int_value_range : forall n align x v,
  store_integer n align x v |-- “ valid_signed_value n v ”.
Proof.
  intros. unfold store_integer. apply store_number_value_range.
Qed.

Lemma store_uint_value_range : forall n align x v,
  store_uinteger n align x v |-- “ valid_unsigned_value n v ”.
Proof.
  intros. unfold store_uinteger. apply store_number_value_range.
Qed.

Lemma store_int_forget : forall n align x v,
  store_integer n align x v |-- undef_store_integer n align x.
Proof.
  intros. unfold store_integer. apply store_number_forget.
Qed.

Lemma store_uint_forget : forall n align x v,
  store_uinteger n align x v |-- undef_store_integer n align x.
Proof.
  intros. unfold store_uinteger. apply store_number_forget.
Qed.

Fixpoint store_bytes_as (B : addr -> Z -> CRules.expr) (x : addr) (n : nat) :
    Vector.t Z n -> CRules.expr :=
  match n with
  | O => fun _ => emp
  | S n' => fun bytes => B x (Vector.hd bytes) **
      store_bytes_as B (x + 1) n' (Vector.tl bytes)
  end.

Arguments store_bytes_as B x {n} _.

Lemma valid_object_byte_parts : forall n align x,
  valid_object x (Z.of_nat (S n)) align ->
  valid_object x 1 1 /\ valid_object (x + 1) (Z.of_nat n) 1.
Proof.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range,
    aligned, Arch.aligned.
  intros n align x [[Hx [Hlen Hlast]] Halign].
  repeat split; try lia; apply Z.mod_1_r.
Qed.

Lemma store_bytes_as_forward : forall n x (bytes : Vector.t Z n) align
    (B : addr -> Z -> CRules.expr) (normalize : Z -> Z),
  valid_object x (Z.of_nat n) align ->
  (forall y z, valid_object y 1 1 ->
    store_byte y z |-- B y (normalize z)) ->
  store_bytes x bytes |--
    store_bytes_as B x (Vector.map normalize bytes).
Proof.
  induction n as [|n IH]; intros x bytes align B normalize Hobject Hbyte.
  - apply derivable1_refl.
  - revert Hobject.
    apply (Vector.caseS' bytes). intros z tail Hobject.
    destruct (valid_object_byte_parts n align x Hobject) as [Hhead Htail].
    cbn.
    sep_apply (Hbyte x z Hhead).
    sep_apply (IH (x + 1) tail 1 B normalize Htail Hbyte).
    entailer!.
Qed.

Lemma store_bytes_as_backward : forall (B : addr -> Z -> CRules.expr) n x
    (bytes : Vector.t Z n),
  (forall y z, B y z |-- store_byte y z) ->
  store_bytes_as B x bytes |-- store_bytes x bytes.
Proof.
  intros B n. induction n as [|n IH]; intros x bytes Hbyte.
  - apply derivable1_refl.
  - apply (Vector.caseS' bytes). intros z tail.
    cbn [store_bytes_as store_bytes].
    sep_apply (Hbyte x z).
    sep_apply (IH (x + 1) tail Hbyte).
    entailer!.
Qed.

Lemma bytes_eqm_map : forall n (bytes : Vector.t Z n) (normalize : Z -> Z),
  (forall z, Byte.eqm z (normalize z)) ->
  bytes_eqm bytes (Vector.map normalize bytes).
Proof.
  induction n as [|n IH]; intros bytes normalize Hnormalize.
  - exact I.
  - apply (Vector.caseS' bytes). intros z tail.
    cbn [bytes_eqm byte_vector_eqm Vector.map].
    split; [apply Hnormalize | apply IH, Hnormalize].
Qed.

Lemma store_bytes_as_bounds : forall (B : addr -> Z -> CRules.expr) n x
    (bytes : Vector.t Z n),
  (0 < n)%nat ->
  (forall y z, B y z |-- “ valid_object y 1 1 ”) ->
  store_bytes_as B x bytes |--
    “ 0 <= x /\ x + Z.of_nat n - 1 <= addr_max_unsigned ”.
Proof.
  intros B n. induction n as [|n IH]; intros x bytes Hn Hbyte; [lia|].
  revert Hn Hbyte.
  apply (Vector.caseS' bytes). intros z tail Hn Hbyte.
  cbn [store_bytes_as].
  destruct n as [|n'].
  - sep_apply (Hbyte x z).
    unfold valid_object, Arch.valid_object, Arch.valid_addr_range.
    entailer!; lia.
  - sep_apply (Hbyte x z).
    sep_apply (IH (x + 1) tail ltac:(lia) Hbyte).
    unfold valid_object, Arch.valid_object, Arch.valid_addr_range.
    entailer!; lia.
Qed.

Lemma store_number_as_bytes : forall n align
    (P : Z -> Prop) (B : addr -> Z -> CRules.expr)
    (R : addr -> Z -> Prop) (normalize : Z -> Z),
  (0 < n)%nat ->
  (forall y z, valid_object y 1 1 ->
    store_byte y z |-- B y (normalize z)) ->
  (forall y z, B y z |-- store_byte y z) ->
  (forall y z, B y z |-- “ valid_object y 1 1 ”) ->
  (forall z, Byte.eqm z (normalize z)) ->
  (forall x v, valid_object x (Z.of_nat n) align /\ P v -> R x v) ->
  (forall x v, R x v -> P v /\ aligned align x) ->
  forall x v,
    (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v)
    --||--
    EX bytes : Vector.t Z n,
      “ merge_n_bytes bytes v /\ R x v ” && store_bytes_as B x bytes.
Proof.
  intros n align P B R normalize Hn Hforward Hbackward Hbounds
    Hnormalize HR Hrecover x v.
  split.
  - unfold store_bytes_Z. Intros bytes.
    Exists (Vector.map normalize bytes).
    entailer!.
    + sep_apply (store_bytes_as_forward n x bytes align B normalize
        (proj1 H0) Hforward). entailer!.
    + eapply merge_n_bytes_eqm; [|exact H].
      apply bytes_eqm_map. exact Hnormalize.
  - apply _derivable1_andp_intros.
    + Intros bytes.
      sep_apply (store_bytes_as_bounds B n x bytes Hn Hbounds).
      destruct H as [_ HRpure].
      destruct (Hrecover x v HRpure) as [HP Halign].
      apply coq_prop_imply.
      intros [Hx Hlast].
      unfold valid_object, Arch.valid_object, Arch.valid_addr_range.
      repeat split; try lia; assumption.
    + Intros bytes.
      unfold store_bytes_Z.
      Exists bytes.
      sep_apply (store_bytes_as_backward B n x bytes Hbackward).
      entailer!.
Qed.

Lemma signed_byte_store_equiv : forall x z,
  (“ valid_object x 1 1 /\ valid_signed_value 1 z ” && store_byte x z)
    --||-- (x # Char |-> z).
Proof.
  intros x z. unfold store_char, store_integer.
  rewrite store_byte_equiv_store_bytes_Z.
  reflexivity.
Qed.

Lemma unsigned_byte_store_equiv : forall x z,
  (“ valid_object x 1 1 /\ valid_unsigned_value 1 z ” && store_byte x z)
    --||-- (x # UChar |-> z).
Proof.
  intros x z. unfold store_uchar, store_uinteger.
  rewrite store_byte_equiv_store_bytes_Z.
  reflexivity.
Qed.

Lemma signed_byte_normalize : forall z,
  valid_signed_value 1 (Byte.signed (Byte.repr z)) /\
  Byte.eqm z (Byte.signed (Byte.repr z)).
Proof.
  intro z. split; [|apply Byte.eqm_signed_repr].
  unfold valid_signed_value.
  pose proof (Byte.signed_range (Byte.repr z)).
  change Byte.min_signed with (-128) in *.
  change Byte.max_signed with 127 in *.
  change (2 ^ (8 * Z.of_nat 1 - 1)) with 128.
  lia.
Qed.

Lemma unsigned_byte_normalize : forall z,
  valid_unsigned_value 1 (Byte.unsigned (Byte.repr z)) /\
  Byte.eqm z (Byte.unsigned (Byte.repr z)).
Proof.
  intro z. split; [|apply Byte.eqm_unsigned_repr].
  unfold valid_unsigned_value.
  pose proof (Byte.unsigned_range (Byte.repr z)).
  change Byte.modulus with 256 in *.
  change (2 ^ (8 * Z.of_nat 1)) with 256.
  lia.
Qed.

Lemma store_number_as_poly_bytes : forall n align
    (P Q : Z -> Prop) (B : addr -> Z -> CRules.expr)
    (normalize : Z -> Z),
  (0 < n)%nat ->
  (forall z, Q (normalize z) /\ Byte.eqm z (normalize z)) ->
  (forall y z,
    (“ valid_object y 1 1 /\ Q z ” && store_byte y z) --||-- B y z) ->
  forall x v,
    (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v)
      --||--
    EX bytes : Vector.t Z n,
      “ merge_n_bytes bytes v /\ P v /\ aligned align x ” &&
      store_bytes_as B x bytes.
Proof.
  intros n align P Q B normalize Hn Hnormalize Hbyte x v.
  eapply store_number_as_bytes with
    (P := P) (B := B)
    (R := fun y w => P w /\ aligned align y)
    (normalize := normalize).
  - exact Hn.
  - intros y z Hobject.
    rewrite <- (Hbyte y (normalize z)).
    destruct (Hnormalize z) as [Hvalue Heqm].
    entailer!. apply store_byte_eqm. exact Heqm.
  - intros y z. rewrite <- (Hbyte y z). entailer!.
  - intros y z. rewrite <- (Hbyte y z). entailer!.
  - intro z. exact (proj2 (Hnormalize z)).
  - intros y w [Hobject HP]. split; [exact HP |].
    unfold valid_object, Arch.valid_object in Hobject. tauto.
  - intros y w [HP Halign]. split; assumption.
Qed.

Lemma store_number_as_char_bytes : forall n align (P : Z -> Prop) x v,
  (0 < n)%nat ->
  (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v)
    --||--
  EX bytes : Vector.t Z n,
    “ merge_n_bytes bytes v /\ P v /\ aligned align x ” &&
    store_bytes_as store_char x bytes.
Proof.
  intros n align P x v Hn.
  eapply store_number_as_poly_bytes with
    (Q := valid_signed_value 1)
    (normalize := fun z => Byte.signed (Byte.repr z));
    eauto using signed_byte_normalize, signed_byte_store_equiv.
Qed.

Lemma store_number_as_uchar_bytes : forall n align (P : Z -> Prop) x v,
  (0 < n)%nat ->
  (“ valid_object x (Z.of_nat n) align /\ P v ” && store_bytes_Z x n v)
    --||--
  EX bytes : Vector.t Z n,
    “ merge_n_bytes bytes v /\ P v /\ aligned align x ” &&
    store_bytes_as store_uchar x bytes.
Proof.
  intros n align P x v Hn.
  eapply store_number_as_poly_bytes with
    (Q := valid_unsigned_value 1)
    (normalize := fun z => Byte.unsigned (Byte.repr z));
    eauto using unsigned_byte_normalize, unsigned_byte_store_equiv.
Qed.

Lemma store_int_store_char: forall p v,
  (p # Int |-> v) --||--
  EX v1 v2 v3 v4: Z,
    “ merge_n_bytes [v1; v2; v3; v4]%vector v ”&&
    “ Int.min_signed <= v <= Int.max_signed ”&&
    “ aligned_4 p ”&&
    (p # Char |-> v1) **
    ((p + 1) # Char |-> v2) **
    ((p + 2) # Char |-> v3) **
    ((p + 3) # Char |-> v4).
Proof.
  intros p v.
  change (store_integer 4 4 p v) with ((p # Int |-> v)).
  rewrite (store_number_as_char_bytes 4 4 (valid_signed_value 4) p v ltac:(lia)).
  rewrite byte_vector_ex_equiv.
  cbn [byte_vector_ex store_bytes_as].
  cbn [Vector.hd Vector.tl].
  rewrite ?sepcon_emp_equiv.
  replace (p + 1 + 1) with (p + 2) by lia.
  replace (p + 1 + 1 + 1) with (p + 3) by lia.
  change Int.min_signed with (-2147483648).
  change Int.max_signed with 2147483647.
  unfold valid_signed_value, aligned_4, aligned, Arch.aligned.
  change (2 ^ (8 * Z.of_nat 4 - 1)) with 2147483648.
  split; Intros z1 z2 z3 z4; Exists z1 z2 z3 z4;
    cbv [Vector.hd Vector.tl];
    replace (p + 2 + 1) with (p + 3) by lia;
    entailer!.
Qed.

Lemma undef_store_uint_undef_store_char : forall p,
  (p # UInt |->_) --||-- “ aligned_4 p ” && (p # Char |->_) ** ((p + 1) # Char |->_) ** ((p + 2) # Char |->_) ** ((p + 3) # Char |->_).
Proof.
  intros.
  try unfold poly_undef_store; simpl_nonptr_sizeof;
    change (Z.to_nat 4) with (4%nat) in *;
    rewrite ?(undef_store_int_expand (4%nat) 4);
    change (Z.of_nat (4%nat)) with 4 in *;
    repeat rewrite <- Z.add_sub_assoc in *;
    change (4 - 1) with 3 in *;
    cbn [undef_store_bytes]; rewrite ?sepcon_emp_equiv;
    repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry];
    unfold aligned, Arch.aligned; rewrite ?Z.mod_1_r. try unfold poly_undef_store; simpl_nonptr_sizeof;
    change (Z.to_nat 1) with (1%nat) in *;
    rewrite ?(undef_store_int_expand (1%nat) 1);
    change (Z.of_nat (1%nat)) with 1 in *;
    repeat rewrite <- Z.add_sub_assoc in *;
    change (1 - 1) with 0 in *;
    cbn [undef_store_bytes]; rewrite ?sepcon_emp_equiv;
    repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry];
    unfold aligned, Arch.aligned; rewrite ?Z.mod_1_r.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned; fold addr_max_unsigned in *; simpl_nonptr_sizeof. unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned; fold addr_max_unsigned in *; simpl_nonptr_sizeof.
  split ; Intros ; entailer!.
Qed.

Lemma undef_store_int_undef_store_char : forall p,
  (p # Int |->_) --||-- “ aligned_4 p ” && (p # Char |->_) ** ((p + 1) # Char |->_) ** ((p + 2) # Char |->_) ** ((p + 3) # Char |->_).
Proof.
  apply undef_store_uint_undef_store_char.
Qed.

Lemma store_uint_store_char: forall p v,
  (p # UInt |-> v) --||--
  EX v1 v2 v3 v4: Z,
    “ merge_n_bytes [v1; v2; v3; v4]%vector v ”&&
    “ 0 <= v <= Int.max_unsigned ”&&
    “ aligned_4 p ”&&
    (p # Char |-> v1) **
    ((p + 1) # Char |-> v2) **
    ((p + 2) # Char |-> v3) **
    ((p + 3) # Char |-> v4).
Proof.
  intros p v.
  change (store_uinteger 4 4 p v) with ((p # UInt |-> v)).
  rewrite (store_number_as_char_bytes 4 4 (valid_unsigned_value 4) p v ltac:(lia)).
  rewrite byte_vector_ex_equiv.
  cbn [byte_vector_ex store_bytes_as].
  rewrite ?sepcon_emp_equiv.
  change Int.max_unsigned with 4294967295.
  unfold valid_unsigned_value, aligned_4, aligned, Arch.aligned.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  split; Intros z1 z2 z3 z4;
    Exists z1 z2 z3 z4;
    cbv [Vector.hd Vector.tl];
    repeat match goal with
    | |- context [p + ?k + 1] =>
        replace (p + k + 1) with (p + (k + 1)) by lia
    end;
    cbn [Z.add]; entailer!.
Qed.

Lemma store_int64_store_char: forall p v,
  (p # Int64 |-> v) --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_n_bytes [v1; v2; v3; v4; v5; v6; v7; v8]%vector v ”&&
    “ Int64.min_signed <= v <= Int64.max_signed ”&&
    “ aligned_4 p ”&&
    (p # Char |-> v1) **
    ((p + 1) # Char |-> v2) **
    ((p + 2) # Char |-> v3) **
    ((p + 3) # Char |-> v4) **
    ((p + 4) # Char |-> v5) **
    ((p + 5) # Char |-> v6) **
    ((p + 6) # Char |-> v7) **
    ((p + 7) # Char |-> v8).
Proof.
  intros p v.
  change (store_integer 8 4 p v) with ((p # Int64 |-> v)).
  rewrite (store_number_as_char_bytes 8 4 (valid_signed_value 8) p v ltac:(lia)).
  rewrite byte_vector_ex_equiv.
  cbn [byte_vector_ex store_bytes_as].
  rewrite ?sepcon_emp_equiv.
  change Int64.min_signed with (-9223372036854775808).
  change Int64.max_signed with 9223372036854775807.
  unfold valid_signed_value, aligned_4, aligned, Arch.aligned.
  change (2 ^ (8 * Z.of_nat 8 - 1)) with 9223372036854775808.
  split; Intros z1 z2 z3 z4 z5 z6 z7 z8;
    Exists z1 z2 z3 z4 z5 z6 z7 z8;
    cbv [Vector.hd Vector.tl];
    repeat match goal with
    | |- context [p + ?k + 1] =>
        replace (p + k + 1) with (p + (k + 1)) by lia
    end;
    cbn [Z.add]; entailer!.
Qed.

Lemma store_uint64_store_uchar: forall p v,
  (p # UInt64 |-> v) --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_n_bytes [v1; v2; v3; v4; v5; v6; v7; v8]%vector v ”&&
    “ 0 <= v <= Int64.max_unsigned ”&&
    “ aligned_4 p ”&&
    (p # UChar |-> v1) **
    ((p + 1) # UChar |-> v2) **
    ((p + 2) # UChar |-> v3) **
    ((p + 3) # UChar |-> v4) **
    ((p + 4) # UChar |-> v5) **
    ((p + 5) # UChar |-> v6) **
    ((p + 6) # UChar |-> v7) **
    ((p + 7) # UChar |-> v8).
Proof.
  intros p v.
  change (store_uinteger 8 4 p v) with ((p # UInt64 |-> v)).
  rewrite (store_number_as_uchar_bytes 8 4 (valid_unsigned_value 8) p v ltac:(lia)).
  rewrite byte_vector_ex_equiv.
  cbn [byte_vector_ex store_bytes_as].
  rewrite ?sepcon_emp_equiv.
  change Int64.max_unsigned with 18446744073709551615.
  unfold valid_unsigned_value, aligned_4, aligned, Arch.aligned.
  change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616.
  split; Intros z1 z2 z3 z4 z5 z6 z7 z8;
    Exists z1 z2 z3 z4 z5 z6 z7 z8;
    cbv [Vector.hd Vector.tl];
    repeat match goal with
    | |- context [p + ?k + 1] =>
        replace (p + k + 1) with (p + (k + 1)) by lia
    end;
    cbn [Z.add]; entailer!.
Qed.

Lemma store_int64_store_uchar: forall p v,
  (p # Int64 |-> v) --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_n_bytes [v1; v2; v3; v4; v5; v6; v7; v8]%vector v ”&&
    “ Int64.min_signed <= v <= Int64.max_signed ”&&
    “ aligned_4 p ”&&
    (p # UChar |-> v1) **
    ((p + 1) # UChar |-> v2) **
    ((p + 2) # UChar |-> v3) **
    ((p + 3) # UChar |-> v4) **
    ((p + 4) # UChar |-> v5) **
    ((p + 5) # UChar |-> v6) **
    ((p + 6) # UChar |-> v7) **
    ((p + 7) # UChar |-> v8).
Proof.
  intros p v.
  change (store_integer 8 4 p v) with ((p # Int64 |-> v)).
  rewrite (store_number_as_uchar_bytes 8 4 (valid_signed_value 8) p v ltac:(lia)).
  rewrite byte_vector_ex_equiv.
  cbn [byte_vector_ex store_bytes_as].
  rewrite ?sepcon_emp_equiv.
  change Int64.min_signed with (-9223372036854775808).
  change Int64.max_signed with 9223372036854775807.
  unfold valid_signed_value, aligned_4, aligned, Arch.aligned.
  change (2 ^ (8 * Z.of_nat 8 - 1)) with 9223372036854775808.
  split; Intros z1 z2 z3 z4 z5 z6 z7 z8;
    Exists z1 z2 z3 z4 z5 z6 z7 z8;
    cbv [Vector.hd Vector.tl];
    repeat match goal with
    | |- context [p + ?k + 1] =>
        replace (p + k + 1) with (p + (k + 1)) by lia
    end;
    cbn [Z.add]; entailer!.
Qed.

Lemma store_uint64_store_char: forall p v,
  (p # UInt64 |-> v) --||--
  EX v1 : Z, EX v2 : Z, EX v3 : Z, EX v4 : Z,
  EX v5 : Z, EX v6 : Z, EX v7 : Z, EX v8 : Z,
    “ merge_n_bytes [v1; v2; v3; v4; v5; v6; v7; v8]%vector v ”&&
    “ 0 <= v <= Int64.max_unsigned ”&&
    “ aligned_4 p ”&&
    (p # Char |-> v1) **
    ((p + 1) # Char |-> v2) **
    ((p + 2) # Char |-> v3) **
    ((p + 3) # Char |-> v4) **
    ((p + 4) # Char |-> v5) **
    ((p + 5) # Char |-> v6) **
    ((p + 6) # Char |-> v7) **
    ((p + 7) # Char |-> v8).
Proof.
  intros p v.
  change (store_uinteger 8 4 p v) with ((p # UInt64 |-> v)).
  rewrite (store_number_as_char_bytes 8 4 (valid_unsigned_value 8) p v ltac:(lia)).
  rewrite byte_vector_ex_equiv.
  cbn [byte_vector_ex store_bytes_as].
  rewrite ?sepcon_emp_equiv.
  change Int64.max_unsigned with 18446744073709551615.
  unfold valid_unsigned_value, aligned_4, aligned, Arch.aligned.
  change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616.
  split; Intros z1 z2 z3 z4 z5 z6 z7 z8;
    Exists z1 z2 z3 z4 z5 z6 z7 z8;
    cbv [Vector.hd Vector.tl];
    repeat match goal with
    | |- context [p + ?k + 1] =>
        replace (p + k + 1) with (p + (k + 1)) by lia
    end;
    cbn [Z.add]; entailer!.
Qed.

Definition merge_bytes_split (n m : nat) (w1 w2 v : Z) : Prop :=
  exists (left : Vector.t Z n) (right : Vector.t Z m),
    merge_n_bytes left w1 /\ merge_n_bytes right w2 /\
    merge_n_bytes (Vector.append left right) v.

Definition signed_value_of_bytes {n : nat} (bytes : Vector.t Z n) : Z :=
  signed_last_nbits (n_bytes_to_Z bytes) (8 * Z.of_nat n).

Definition unsigned_value_of_bytes {n : nat} (bytes : Vector.t Z n) : Z :=
  unsigned_last_nbits (n_bytes_to_Z bytes) (8 * Z.of_nat n).

Lemma merge_signed_value_of_bytes : forall n (bytes : Vector.t Z n),
  (0 < n)%nat -> merge_n_bytes bytes (signed_value_of_bytes bytes).
Proof.
  intros n bytes Hn. unfold signed_value_of_bytes.
  eapply merge_n_bytes_value_eqm.
  - apply signed_Lastnbits_mod_correct. lia.
  - apply merge_n_bytes_self.
Qed.

Lemma merge_unsigned_value_of_bytes : forall n (bytes : Vector.t Z n),
  (0 < n)%nat -> merge_n_bytes bytes (unsigned_value_of_bytes bytes).
Proof.
  intros n bytes Hn. unfold unsigned_value_of_bytes.
  eapply merge_n_bytes_value_eqm.
  - apply unsigned_Lastnbits_mod_correct. lia.
  - apply merge_n_bytes_self.
Qed.

Lemma signed_value_of_bytes_range : forall n (bytes : Vector.t Z n),
  (0 < n)%nat -> valid_signed_value n (signed_value_of_bytes bytes).
Proof.
  intros n bytes Hn. unfold valid_signed_value, signed_value_of_bytes.
  apply signed_Lastnbits_range. lia.
Qed.

Lemma unsigned_value_of_bytes_range : forall n (bytes : Vector.t Z n),
  (0 < n)%nat -> valid_unsigned_value n (unsigned_value_of_bytes bytes).
Proof.
  intros n bytes Hn. unfold valid_unsigned_value, unsigned_value_of_bytes.
  apply unsigned_Lastnbits_range. lia.
Qed.

Lemma signed_value_of_bytes_spec : forall n (bytes : Vector.t Z n),
  (0 < n)%nat ->
  valid_signed_value n (signed_value_of_bytes bytes) /\
  merge_n_bytes bytes (signed_value_of_bytes bytes).
Proof.
  intros n bytes Hn. split.
  - apply signed_value_of_bytes_range; exact Hn.
  - apply merge_signed_value_of_bytes; exact Hn.
Qed.

Lemma unsigned_value_of_bytes_spec : forall n (bytes : Vector.t Z n),
  (0 < n)%nat ->
  valid_unsigned_value n (unsigned_value_of_bytes bytes) /\
  merge_n_bytes bytes (unsigned_value_of_bytes bytes).
Proof.
  intros n bytes Hn. split.
  - apply unsigned_value_of_bytes_range; exact Hn.
  - apply merge_unsigned_value_of_bytes; exact Hn.
Qed.

Lemma store_number_split : forall n m align child_align
    (P Q1 Q2 : Z -> Prop) (R : addr -> Z -> Prop)
    (decode1 : Vector.t Z n -> Z) (decode2 : Vector.t Z m -> Z),
  (forall x, valid_object x (Z.of_nat (n + m)) align ->
    valid_object x (Z.of_nat n) child_align /\
    valid_object (x + Z.of_nat n) (Z.of_nat m) child_align) ->
  (forall x v, valid_object x (Z.of_nat (n + m)) align /\ P v -> R x v) ->
  (forall bytes, Q1 (decode1 bytes) /\ merge_n_bytes bytes (decode1 bytes)) ->
  (forall bytes, Q2 (decode2 bytes) /\ merge_n_bytes bytes (decode2 bytes)) ->
  forall x v,
    (“ valid_object x (Z.of_nat (n + m)) align /\ P v ” &&
      store_bytes_Z x (n + m) v) |--
    EX w1 : Z, EX w2 : Z,
      “ merge_bytes_split n m w1 w2 v /\ R x v ” &&
      ((“ valid_object x (Z.of_nat n) child_align /\ Q1 w1 ” &&
          store_bytes_Z x n w1) **
       (“ valid_object (x + Z.of_nat n) (Z.of_nat m) child_align /\ Q2 w2 ” &&
          store_bytes_Z (x + Z.of_nat n) m w2)).
Proof.
  intros n m align child_align P Q1 Q2 R decode1 decode2
    Hobject HR Hdecode1 Hdecode2 x v.
  rewrite (store_bytes_Z_split n m x v).
  Intros left right.
  Exists (decode1 left) (decode2 right).
  destruct H as [Hparent Hv].
  destruct (Hobject x Hparent) as [Hleft Hright].
  destruct (Hdecode1 left) as [Hvalue1 Hmerge1].
  destruct (Hdecode2 right) as [Hvalue2 Hmerge2].
  entailer!.
  - unfold store_bytes_Z. Exists left right. entailer!.
  - exists left, right. repeat split; assumption.
Qed.

Lemma valid_object_8_split_4 : forall x,
  valid_object x 8 4 -> valid_object x 4 4 /\ valid_object (x + 4) 4 4.
Proof.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range,
    aligned, Arch.aligned.
  intros x [[Hx [Hlen Hlast]] Halign].
  repeat split; try lia.
  rewrite Z.add_mod by lia. rewrite Halign. reflexivity.
Qed.

Lemma signed64_object_facts : forall x v,
  valid_object x 8 4 /\ valid_signed_value 8 v ->
  Int64.min_signed <= v <= Int64.max_signed /\ aligned_4 x.
Proof.
  intros x v [Hobject Hvalue].
  destruct Hobject as [_ Halign].
  unfold valid_signed_value in Hvalue.
  change (2 ^ (8 * Z.of_nat 8 - 1)) with 9223372036854775808 in Hvalue.
  change Int64.min_signed with (-9223372036854775808).
  change Int64.max_signed with 9223372036854775807.
  split; [lia | exact Halign].
Qed.

Lemma unsigned64_object_facts : forall x v,
  valid_object x 8 4 /\ valid_unsigned_value 8 v ->
  0 <= v <= Int64.max_unsigned /\ aligned_4 x.
Proof.
  intros x v [Hobject Hvalue].
  destruct Hobject as [_ Halign].
  unfold valid_unsigned_value in Hvalue.
  change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616 in Hvalue.
  change Int64.max_unsigned with 18446744073709551615.
  split; [lia | exact Halign].
Qed.

Lemma store_int64_store_int: forall p v,
  (p # Int64 |-> v) |--
  EX v1 : Z, EX v2 : Z,
    “ merge_bytes_split 4 4 v1 v2 v /\
      Int64.min_signed <= v <= Int64.max_signed /\
      aligned_4 p ” &&
    (p # Int |-> v1) ** ((p + 4) # Int |-> v2).
Proof.
  intros p v.
  eapply (store_number_split 4 4 4 4
    (valid_signed_value 8) (valid_signed_value 4) (valid_signed_value 4)
    (fun x w => Int64.min_signed <= w <= Int64.max_signed /\ aligned_4 x)
    (@signed_value_of_bytes 4) (@signed_value_of_bytes 4)).
  - apply valid_object_8_split_4.
  - apply signed64_object_facts.
  - intro bytes. apply signed_value_of_bytes_spec; lia.
  - intro bytes. apply signed_value_of_bytes_spec; lia.
Qed.

Lemma store_uint64_store_uint: forall p v,
  (p # UInt64 |-> v) |--
  EX v1 : Z, EX v2 : Z,
    “ merge_bytes_split 4 4 v1 v2 v /\
      0 <= v <= Int64.max_unsigned /\
      aligned_4 p ” &&
    (p # UInt |-> v1) ** ((p + 4) # UInt |-> v2).
Proof.
  intros p v.
  eapply (store_number_split 4 4 4 4
    (valid_unsigned_value 8) (valid_unsigned_value 4) (valid_unsigned_value 4)
    (fun x w => 0 <= w <= Int64.max_unsigned /\ aligned_4 x)
    (@unsigned_value_of_bytes 4) (@unsigned_value_of_bytes 4)).
  - apply valid_object_8_split_4.
  - apply unsigned64_object_facts.
  - intro bytes. apply unsigned_value_of_bytes_spec; lia.
  - intro bytes. apply unsigned_value_of_bytes_spec; lia.
Qed.

Lemma store_int64_store_uint: forall p v,
  (p # Int64 |-> v) |--
  EX v1 : Z, EX v2 : Z,
    “ merge_bytes_split 4 4 v1 v2 v /\
      Int64.min_signed <= v <= Int64.max_signed /\
      aligned_4 p ” &&
    (p # UInt |-> v1) ** ((p + 4) # UInt |-> v2).
Proof.
  intros p v.
  eapply (store_number_split 4 4 4 4
    (valid_signed_value 8) (valid_unsigned_value 4) (valid_unsigned_value 4)
    (fun x w => Int64.min_signed <= w <= Int64.max_signed /\ aligned_4 x)
    (@unsigned_value_of_bytes 4) (@unsigned_value_of_bytes 4)).
  - apply valid_object_8_split_4.
  - apply signed64_object_facts.
  - intro bytes. apply unsigned_value_of_bytes_spec; lia.
  - intro bytes. apply unsigned_value_of_bytes_spec; lia.
Qed.

Lemma store_uint64_store_int: forall p v,
  (p # UInt64 |-> v) |--
  EX v1 : Z, EX v2 : Z,
    “ merge_bytes_split 4 4 v1 v2 v /\
      0 <= v <= Int64.max_unsigned /\
      aligned_4 p ” &&
    (p # Int |-> v1) ** ((p + 4) # Int |-> v2).
Proof.
  intros p v.
  eapply (store_number_split 4 4 4 4
    (valid_unsigned_value 8) (valid_signed_value 4) (valid_signed_value 4)
    (fun x w => 0 <= w <= Int64.max_unsigned /\ aligned_4 x)
    (@signed_value_of_bytes 4) (@signed_value_of_bytes 4)).
  - apply valid_object_8_split_4.
  - apply unsigned64_object_facts.
  - intro bytes. apply signed_value_of_bytes_spec; lia.
  - intro bytes. apply signed_value_of_bytes_spec; lia.
Qed.

Lemma store_ptr_undef_store_ptr: forall p v,
  p # Ptr |-> v |-- p # Ptr |->_ .
Proof.
  intros p v.
  unfold poly_store, poly_undef_store, store_ptr, undef_store_ptr.
  Intros.
  sep_apply store_bytes_Z_undef_store_bytes.
  entailer!.
Qed.

Lemma store_int_range : forall x v,
  (x # Int |-> v) |-- “ Int.min_signed <= v <= Int.max_signed ”.
Proof.
  intros x v.
  change (store_integer 4 4 x v |-- “ -2147483648 <= v <= 2147483647 ”).
  prop_apply (store_int_value_range 4 4 x v).
  change (valid_signed_value 4 v) with (-2147483648 <= v < 2147483648) in *.
  entailer!.
Qed.

Lemma store_int_undef_store_int: forall x v, 
  (x # Int |->v) |-- (x # Int |->_).
Proof.
  intros.
  apply store_int_forget.
Qed.

Lemma store_char_range : forall x v,
  (x # Char |-> v) |-- “ Byte.min_signed <= v <= Byte.max_signed ”.
Proof.
  intros x v.
  change (store_integer 1 1 x v |-- “ -128 <= v <= 127 ”).
  prop_apply (store_int_value_range 1 1 x v).
  change (valid_signed_value 1 v) with (-128 <= v < 128) in *.
  entailer!.
Qed.

Lemma store_char_undef_store_char: forall x v, 
  (x # Char |->v) |-- (x # Char |->_).
Proof.
  intros.
  apply store_int_forget.
Qed.

Lemma store_short_range : forall x v,
  (x # Short |-> v) |-- “ -32768 <= v <= 32767 ”.
Proof.
  intros x v.
  change (store_integer 2 2 x v |-- “ -32768 <= v <= 32767 ”).
  prop_apply (store_int_value_range 2 2 x v).
  change (valid_signed_value 2 v) with (-32768 <= v < 32768) in *.
  entailer!.
Qed.

Lemma store_short_undef_store_short: forall x v, 
  (x # Short |->v) |-- (x # Short |->_).
Proof.
  intros.
  apply store_int_forget.
Qed.

Lemma store_int64_range : forall x v,
  (x # Int64 |-> v) |-- “ Int64.min_signed <= v <= Int64.max_signed ”.
Proof.
  intros x v.
  change (store_integer 8 4 x v |-- “ -9223372036854775808 <= v <= 9223372036854775807 ”).
  prop_apply (store_int_value_range 8 4 x v).
  change (valid_signed_value 8 v) with (-9223372036854775808 <= v < 9223372036854775808) in *.
  entailer!.
Qed.

Lemma store_int64_undef_store_int64: forall x v, 
  (x # Int64 |->v) |-- (x # Int64 |->_).
Proof.
  intros.
  apply store_int_forget.
Qed.

Lemma store_uint_range : forall x v,
  (x # UInt |-> v) |-- “ 0 <= v <= Int.max_unsigned ”.
Proof.
  intros x v.
  change (store_uinteger 4 4 x v |-- “ 0 <= v <= 4294967295 ”).
  prop_apply (store_uint_value_range 4 4 x v).
  change (valid_unsigned_value 4 v) with (0 <= v < 4294967296) in *.
  entailer!.
Qed.  

Lemma store_uint_undef_store_uint: forall x v, 
  (x # UInt |->v) |-- (x # UInt |->_).
Proof.
  intros.
  apply store_uint_forget.
Qed.

Lemma store_uchar_range : forall x v,
  (x # UChar |-> v) |-- “ 0 <= v <= Byte.max_unsigned ”.
Proof.
  intros x v.
  change (store_uinteger 1 1 x v |-- “ 0 <= v <= 255 ”).
  prop_apply (store_uint_value_range 1 1 x v).
  change (valid_unsigned_value 1 v) with (0 <= v < 256) in *.
  entailer!.
Qed.

Lemma store_uchar_undef_store_uchar: forall x v, 
  (x # UChar |->v) |-- (x # UChar |->_).
Proof.
  intros.
  apply store_uint_forget.
Qed.

Lemma store_ushort_range : forall x v,
  (x # UShort |-> v) |-- “ 0 <= v <= 65535 ”.
Proof.
  intros x v.
  change (store_uinteger 2 2 x v |-- “ 0 <= v <= 65535 ”).
  prop_apply (store_uint_value_range 2 2 x v).
  change (valid_unsigned_value 2 v) with (0 <= v < 65536) in *.
  entailer!.
Qed.

Lemma store_bool_undef_store_bool: forall x v,
  (x # Bool |-> v) |-- (x # Bool |->_).
Proof.
  intros.
  unfold poly_store, poly_undef_store, store_bool, undef_store_bool.
  entailer!.
  apply store_byte_undef_store_byte.
Qed.

Lemma valid_store_bool: forall x v,
  (x # Bool |-> v) |-- “ 0 <= v <= 1 ”.
Proof.
  intros.
  unfold poly_store, store_bool.
  entailer!.
Qed.

Lemma store_ushort_undef_store_ushort: forall x v, 
  (x # UShort |->v) |-- (x # UShort |->_).
Proof.
  intros.
  apply store_uint_forget.
Qed.

Lemma store_uint64_range : forall x v,
  (x # UInt64 |-> v) |-- “ 0 <= v <= Int64.max_unsigned ”.
Proof.
  intros x v.
  change (store_uinteger 8 4 x v |-- “ 0 <= v <= 18446744073709551615 ”).
  prop_apply (store_uint_value_range 8 4 x v).
  change (valid_unsigned_value 8 v) with (0 <= v < 18446744073709551616) in *.
  entailer!.
Qed.  

Lemma store_uint64_undef_store_uint64: forall x v, 
  (x # UInt64 |->v) |-- (x # UInt64 |->_).
Proof.
  intros.
  apply store_uint_forget.
Qed.

Lemma store_int128_range : forall x v,
  (x # Int128 |-> v) |-- CRules.coq_prop (Int128.min_signed <= v <= Int128.max_signed).
Proof.
  intros x v.
  change (store_integer 16 4 x v |-- “ -170141183460469231731687303715884105728 <= v <= 170141183460469231731687303715884105727 ”).
  prop_apply (store_int_value_range 16 4 x v).
  change (valid_signed_value 16 v) with (-170141183460469231731687303715884105728 <= v < 170141183460469231731687303715884105728) in *.
  entailer!.
Qed.

Lemma store_int128_undef_store_int128: forall x v,
  (x # Int128 |-> v) |-- (x # Int128 |->_).
Proof.
  intros.
  apply store_int_forget.
Qed.

Lemma store_uint128_range : forall x v,
  (x # UInt128 |-> v) |-- CRules.coq_prop (0 <= v <= Int128.max_unsigned).
Proof.
  intros x v.
  change (store_uinteger 16 4 x v |-- “ 0 <= v <= 340282366920938463463374607431768211455 ”).
  prop_apply (store_uint_value_range 16 4 x v).
  change (valid_unsigned_value 16 v) with (0 <= v < 340282366920938463463374607431768211456) in *.
  entailer!.
Qed.

Lemma store_uint128_undef_store_uint128: forall x v,
  (x # UInt128 |-> v) |-- (x # UInt128 |->_).
Proof.
  intros.
  apply store_uint_forget.
Qed.

Lemma store_float_undef_store_float:
  forall x v,
    x # Float |-> v |-- x # Float |->_.
Proof.
  intros.
  unfold poly_store, poly_undef_store, store_float, undef_store_float.
  destruct (bits_of_float_value v).
  - apply derivable1_andp_mono.
    + apply coq_prop_imply. tauto.
    + apply store_bytes_Z_undef_store_bytes.
  - apply coq_prop_False_left. tauto.
Qed.

Lemma store_double_undef_store_double:
  forall x v,
    x # Double |-> v |-- x # Double |->_.
Proof.
  intros.
  unfold poly_store, poly_undef_store, store_double, undef_store_double.
  destruct (bits_of_double_value v).
  - apply derivable1_andp_mono.
    + apply coq_prop_imply. tauto.
    + apply store_bytes_Z_undef_store_bytes.
  - apply coq_prop_False_left. tauto.
Qed.

Lemma store_long_double_undef_store_long_double:
  forall x v,
    x # LongDouble |-> v |-- x # LongDouble |->_.
Proof.
  intros.
  unfold poly_store, poly_undef_store, store_long_double, undef_store_long_double.
  destruct (bits_of_long_double_value v).
  - apply derivable1_andp_mono.
    + apply coq_prop_imply. tauto.
    + apply store_bytes_Z_undef_store_bytes.
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
    x # Float |-> v |-- “ (valid_object x (sizeof(FLOAT)) 4) ”.
Proof.
  intros.
  unfold poly_store, store_float.
  destruct (bits_of_float_value v); entailer!.
Qed.

Lemma valid_store_double:
  forall x v,
    x # Double |-> v |-- “ (valid_object x (sizeof(DOUBLE)) 8) ”.
Proof.
  intros.
  unfold poly_store, store_double.
  destruct (bits_of_double_value v); entailer!.
Qed.

Lemma valid_store_long_double:
  forall x v,
    x # LongDouble |-> v |-- “ (valid_object x (sizeof(LONGDOUBLE)) 8) ”.
Proof.
  intros.
  unfold poly_store, store_long_double.
  destruct (bits_of_long_double_value v); entailer!.
Qed.

Lemma valid_store_finite_float:
  forall x v,
    x # FiniteFloat |-> v |--
    “ fp32_isFinite v /\ (valid_object x (sizeof(FLOAT)) 4) ”.
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
    “ fp64_isFinite v /\ (valid_object x (sizeof(DOUBLE)) 8) ”.
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
    “ fp128_isFinite v /\ (valid_object x (sizeof(LONGDOUBLE)) 8) ”.
Proof.
  intros.
  unfold store_finite_long_double.
  apply coq_prop_andp_left. intros Hfinite.
  eapply derivable1_trans.
  - apply valid_store_long_double.
  - apply coq_prop_imply. intros Hvalid.
    split; auto.
Qed.

Lemma poly_store_poly_undef_store:
  forall x ty (v : front_end_type_value ty),
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

Lemma dup_undef_store_byte: forall x,
  undef_store_byte x ** undef_store_byte x |-- “ False ”.
Proof.
  intros.
  unfold undef_store_byte.
  apply dup_mstore_noninit.
Qed.

Lemma dup_undef_store_bytes : forall x n,
  (0 < n)%nat ->
  undef_store_bytes x n ** undef_store_bytes x n |-- “ False ”.
Proof.
  intros x [|n] Hpositive; [lia |].
  cbn [undef_store_bytes].
  sep_apply (dup_undef_store_byte x).
  entailer!.
Qed.

Lemma undef_store_int_exclusive : forall n align x,
  (0 < n)%nat ->
  undef_store_integer n align x ** undef_store_integer n align x |-- “ False ”.
Proof.
  intros n align x Hpositive.
  unfold undef_store_integer.
  Intros.
  sep_apply (dup_undef_store_bytes x n Hpositive).
  entailer!.
Qed.

Lemma dup_store_byte: forall x v1 v2,
  store_byte x v1 ** store_byte x v2 |-- “ False ”.
Proof.
  intros.
  unfold store_byte.
  apply dup_mstore.
Qed.

Lemma dup_undef_store_int: forall x,
  (x # Int |->_) ** (x # Int |->_) |-- “ False ”.
Proof.
  intros x. apply (undef_store_int_exclusive 4 4 x). lia.
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
  intros x.
  unfold poly_undef_store, undef_store_ptr.
  pose proof sizeof_ptr_pos as Hsize.
  pose proof (Z2Nat.id (sizeof(PTR)) ltac:(lia)) as Hsize_nat.
  assert (Hpositive : (0 < Z.to_nat (sizeof(PTR)))%nat) by lia.
  Intros.
  sep_apply (dup_undef_store_bytes x (Z.to_nat (sizeof(PTR))) Hpositive).
  entailer!.
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
  intros x v. apply (store_int_to_uint 1 1 x v). lia.
Qed.

Lemma store_uchar_cast : forall x v , x # UChar |-> v |-- x # Char |-> signed_last_nbits v 8.
Proof.
  intros x v. apply (store_uint_to_int 1 1 x v). lia.
Qed.

Lemma store_short_cast : forall x v , x # Short |-> v |-- x # UShort |-> unsigned_last_nbits v 16.
Proof.
  intros x v. apply (store_int_to_uint 2 2 x v). lia.
Qed.

Lemma store_ushort_cast : forall x v , x # UShort |-> v |-- x # Short |-> signed_last_nbits v 16.
Proof.
  intros x v. apply (store_uint_to_int 2 2 x v). lia.
Qed. 

Lemma store_int_cast : forall x v , x # Int |-> v |-- x # UInt |-> unsigned_last_nbits v 32.
Proof.
  intros x v. apply (store_int_to_uint 4 4 x v). lia.
Qed.

Lemma store_uint_cast : forall x v , x # UInt |-> v |-- x # Int |-> signed_last_nbits v 32.
Proof.
  intros x v. apply (store_uint_to_int 4 4 x v). lia.
Qed.

Lemma store_int64_cast : forall x v , x # Int64 |-> v |-- x # UInt64 |-> unsigned_last_nbits v 64.
Proof.
  intros x v. apply (store_int_to_uint 8 4 x v). lia.
Qed.

Lemma store_uint64_cast : forall x v , x # UInt64 |-> v |-- x # Int64 |-> signed_last_nbits v 64.
Proof.
  intros x v. apply (store_uint_to_int 8 4 x v). lia.
Qed.

Lemma valid_store_char : forall x v, x # Char |-> v |-- “ Byte.min_signed <= v <= Byte.max_signed /\ (valid_object x (sizeof(CHAR)) 1) ”.
Proof.
  intros x v.
  change (store_integer 1 1 x v |-- “ -128 <= v <= 127 /\ valid_object x 1 1 ”).
  prop_apply (store_int_valid_object 1 1 x v).
  Intros.
  prop_apply (store_int_value_range 1 1 x v).
  change (valid_signed_value 1 v) with (-128 <= v < 128) in *.
  entailer!.
Qed.

Lemma valid_store_uchar : forall x v, x # UChar |-> v |-- “ 0 <= v <= Byte.max_unsigned /\ (valid_object x (sizeof(CHAR)) 1) ”.
Proof.
  intros x v.
  change (store_uinteger 1 1 x v |-- “ 0 <= v <= 255 /\ valid_object x 1 1 ”).
  prop_apply (store_uint_valid_object 1 1 x v).
  Intros.
  prop_apply (store_uint_value_range 1 1 x v).
  change (valid_unsigned_value 1 v) with (0 <= v < 256) in *.
  entailer!.
Qed.

Lemma valid_undef_store_char : forall x, x # Char |->_ |-- “ (valid_object x (sizeof(CHAR)) 1) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_undef_store_uchar : forall x, x # UChar |->_ |-- “ (valid_object x (sizeof(CHAR)) 1) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_store_short : forall x v, x # Short |-> v |-- “ -32768 <= v <= 32767 /\ (valid_object x (sizeof(SHORT)) 2) ”.
Proof.
  intros x v.
  change (store_integer 2 2 x v |-- “ -32768 <= v <= 32767 /\ valid_object x 2 2 ”).
  prop_apply (store_int_valid_object 2 2 x v).
  Intros.
  prop_apply (store_int_value_range 2 2 x v).
  change (valid_signed_value 2 v) with (-32768 <= v < 32768) in *.
  entailer!.
Qed.

Lemma valid_store_ushort : forall x v, x # UShort |-> v |-- “ 0 <= v <= 65535 /\ (valid_object x (sizeof(SHORT)) 2) ”.
Proof.
  intros x v.
  change (store_uinteger 2 2 x v |-- “ 0 <= v <= 65535 /\ valid_object x 2 2 ”).
  prop_apply (store_uint_valid_object 2 2 x v).
  Intros.
  prop_apply (store_uint_value_range 2 2 x v).
  change (valid_unsigned_value 2 v) with (0 <= v < 65536) in *.
  entailer!.
Qed.

Lemma valid_undef_store_short : forall x, x # Short |->_ |-- “ (valid_object x (sizeof(SHORT)) 2) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_undef_store_ushort : forall x, x # UShort |->_ |-- “ (valid_object x (sizeof(SHORT)) 2) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_store_int : forall x v, x # Int |-> v |-- “ Int.min_signed <= v <= Int.max_signed /\ (valid_object x (sizeof(INT)) 4) ”.
Proof.
  intros x v.
  change (store_integer 4 4 x v |-- “ -2147483648 <= v <= 2147483647 /\ valid_object x 4 4 ”).
  prop_apply (store_int_valid_object 4 4 x v).
  Intros.
  prop_apply (store_int_value_range 4 4 x v).
  change (valid_signed_value 4 v) with (-2147483648 <= v < 2147483648) in *.
  entailer!.
Qed.

Lemma valid_store_uint : forall x v, x # UInt |-> v |-- “ 0 <= v <= Int.max_unsigned /\ (valid_object x (sizeof(INT)) 4) ”.
Proof.
  intros x v.
  change (store_uinteger 4 4 x v |-- “ 0 <= v <= 4294967295 /\ valid_object x 4 4 ”).
  prop_apply (store_uint_valid_object 4 4 x v).
  Intros.
  prop_apply (store_uint_value_range 4 4 x v).
  change (valid_unsigned_value 4 v) with (0 <= v < 4294967296) in *.
  entailer!.
Qed.

Lemma valid_undef_store_int : forall x, x # Int |->_ |-- “ (valid_object x (sizeof(INT)) 4) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_undef_store_uint : forall x, x # UInt |->_ |-- “ (valid_object x (sizeof(INT)) 4) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_store_int64 : forall x v, x # Int64 |-> v |-- “ Int64.min_signed <= v <= Int64.max_signed /\ (valid_object x (sizeof(INT64)) 4) ”.
Proof.
  intros x v.
  change (store_integer 8 4 x v |-- “ -9223372036854775808 <= v <= 9223372036854775807 /\ valid_object x 8 4 ”).
  prop_apply (store_int_valid_object 8 4 x v).
  Intros.
  prop_apply (store_int_value_range 8 4 x v).
  change (valid_signed_value 8 v) with (-9223372036854775808 <= v < 9223372036854775808) in *.
  entailer!.
Qed.

Lemma valid_store_uint64 : forall x v, x # UInt64 |-> v |-- “ 0 <= v <= Int64.max_unsigned /\ (valid_object x (sizeof(INT64)) 4) ”.
Proof.
  intros x v.
  change (store_uinteger 8 4 x v |-- “ 0 <= v <= 18446744073709551615 /\ valid_object x 8 4 ”).
  prop_apply (store_uint_valid_object 8 4 x v).
  Intros.
  prop_apply (store_uint_value_range 8 4 x v).
  change (valid_unsigned_value 8 v) with (0 <= v < 18446744073709551616) in *.
  entailer!.
Qed.


Lemma valid_store_int128 :
  forall x v,
    x # Int128 |-> v |--
    CRules.coq_prop (Int128.min_signed <= v <= Int128.max_signed /\ (valid_object x (sizeof(INT128)) 4)).
Proof.
  intros x v.
  change (store_integer 16 4 x v |-- “ -170141183460469231731687303715884105728 <= v <= 170141183460469231731687303715884105727 /\ valid_object x 16 4 ”).
  prop_apply (store_int_valid_object 16 4 x v).
  Intros.
  prop_apply (store_int_value_range 16 4 x v).
  change (valid_signed_value 16 v) with (-170141183460469231731687303715884105728 <= v < 170141183460469231731687303715884105728) in *.
  entailer!.
Qed.

Lemma valid_store_uint128 :
  forall x v,
    x # UInt128 |-> v |--
    CRules.coq_prop (0 <= v <= Int128.max_unsigned /\ (valid_object x (sizeof(INT128)) 4)).
Proof.
  intros x v.
  change (store_uinteger 16 4 x v |-- “ 0 <= v <= 340282366920938463463374607431768211455 /\ valid_object x 16 4 ”).
  prop_apply (store_uint_valid_object 16 4 x v).
  Intros.
  prop_apply (store_uint_value_range 16 4 x v).
  change (valid_unsigned_value 16 v) with (0 <= v < 340282366920938463463374607431768211456) in *.
  entailer!.
Qed.

Lemma valid_undef_store_int64 : forall x, x # Int64 |->_ |-- “ (valid_object x (sizeof(INT64)) 4) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_undef_store_uint64 : forall x, x # UInt64 |->_ |-- “ (valid_object x (sizeof(INT64)) 4) ”.
Proof.
  intros. apply undef_store_int_valid_object.
Qed.


Lemma valid_undef_store_int128 :
  forall x, x # Int128 |->_ |-- CRules.coq_prop ((valid_object x (sizeof(INT128)) 4)).
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_undef_store_uint128 :
  forall x, x # UInt128 |->_ |-- CRules.coq_prop ((valid_object x (sizeof(INT128)) 4)).
Proof.
  intros. apply undef_store_int_valid_object.
Qed.

Lemma valid_store_ptr : forall x v, x # Ptr |-> v |-- “ (valid_object x (sizeof(PTR)) Arch.ptr_align) /\ valid_ptr_value v ”.
Proof.
  intros.
  unfold poly_store, store_ptr.
  entailer!.
Qed.

Lemma valid_undef_store_ptr : forall x, x # Ptr |->_ |-- “ (valid_object x (sizeof(PTR)) Arch.ptr_align) ”.
Proof.
  intros.
  unfold poly_undef_store, undef_store_ptr.
  entailer!.
Qed.

Lemma undef_store_char_align : forall x, x # Char |->_ |-- store_align_n 1.
Proof.
  intros.
  unfold store_align_n. try unfold poly_undef_store; simpl_nonptr_sizeof;
    change (Z.to_nat 1) with (1%nat) in *;
    rewrite ?(undef_store_int_expand (1%nat) 1);
    change (Z.of_nat (1%nat)) with 1 in *;
    repeat rewrite <- Z.add_sub_assoc in *;
    change (1 - 1) with 0 in *;
    cbn [undef_store_bytes]; rewrite ?sepcon_emp_equiv;
    repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry];
    unfold aligned, Arch.aligned; rewrite ?Z.mod_1_r. simpl.
  Intros. Exists [x].
  simpl.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in *;
    fold addr_max_unsigned in *; simpl_nonptr_sizeof; rewrite ?Z.mod_1_r in *.
  entailer!.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in H; fold addr_max_unsigned in *; simpl_nonptr_sizeof.
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

Lemma store_byte_align1 : forall x, (valid_object x (sizeof(CHAR)) 1) -> undef_store_byte x |-- store_align_n 1.
Proof.
  intros.
  unfold store_align_n.
  Exists [x].
  simpl.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in *;
    fold addr_max_unsigned in *; simpl_nonptr_sizeof; rewrite ?Z.mod_1_r in *.
  entailer!.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in H; fold addr_max_unsigned in *; simpl_nonptr_sizeof.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma undef_store_uchar_align : forall x, x # UChar |->_ |-- store_align_n 1.
Proof.
  apply undef_store_char_align.
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
  intros x. unfold poly_undef_store, undef_store_bool. Intros.
  apply store_byte_align1. exact H.
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
  unfold store_align4_n. try unfold poly_undef_store; simpl_nonptr_sizeof;
    change (Z.to_nat 4) with (4%nat) in *;
    rewrite ?(undef_store_int_expand (4%nat) 4);
    change (Z.of_nat (4%nat)) with 4 in *;
    repeat rewrite <- Z.add_sub_assoc in *;
    change (4 - 1) with 3 in *;
    cbn [undef_store_bytes]; rewrite ?sepcon_emp_equiv;
    repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry];
    unfold aligned, Arch.aligned; rewrite ?Z.mod_1_r. simpl.
  Intros. Exists [x]. 
  simpl. 
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in *;
    fold addr_max_unsigned in *; simpl_nonptr_sizeof.
  rewrite ?sepcon_emp_equiv.
  repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry].
  entailer!.
  unfold aligned_4 in H. unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in H; fold addr_max_unsigned in *; simpl_nonptr_sizeof.
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
  intros x. apply undef_store_int_align4.
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
  unfold store_align4_n. try unfold poly_undef_store; simpl_nonptr_sizeof;
    change (Z.to_nat 8) with (8%nat) in *;
    rewrite ?(undef_store_int_expand (8%nat) 4);
    change (Z.of_nat (8%nat)) with 8 in *;
    repeat rewrite <- Z.add_sub_assoc in *;
    change (8 - 1) with 7 in *;
    cbn [undef_store_bytes]; rewrite ?sepcon_emp_equiv;
    repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry];
    unfold aligned, Arch.aligned; rewrite ?Z.mod_1_r. simpl.
  Intros. Exists (x :: [x + 4]). 
  simpl.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in *;
    fold addr_max_unsigned in *; simpl_nonptr_sizeof.
  rewrite ?sepcon_emp_equiv.
  repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry].
  entailer!.
  - rewrite <- Zplus_mod_idemp_l.
    destruct H as [Hlo [Hhi Halign]].
    rewrite Halign. reflexivity.
  - repeat constructor; intuition lia.
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
  intros x. apply undef_store_int64_align4.
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
  unfold poly_store, store_float.
  destruct (bits_of_float_value v); entailer!.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in H; fold addr_max_unsigned in *; simpl_nonptr_sizeof. tauto.
Qed.

Lemma store_double_aligned8 :
  forall x v,
    x # Double |-> v |-- “ aligned_8 x ”.
Proof.
  intros.
  unfold poly_store, store_double.
  destruct (bits_of_double_value v); entailer!.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in H; fold addr_max_unsigned in *; simpl_nonptr_sizeof. tauto.
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
  unfold poly_store, store_long_double.
  destruct (bits_of_long_double_value v); entailer!.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in H; fold addr_max_unsigned in *; simpl_nonptr_sizeof. tauto.
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
  intros x. apply undef_store_int_align4.
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
  intros x. eapply derivable1_trans.
  2: apply undef_store_int64_align4.
  unfold poly_undef_store, undef_store_double, undef_store_int64, undef_store_integer.
  Intros. entailer!.
  unfold valid_object, Arch.valid_object in *.
  destruct H as [Hrange Halign]. split; [exact Hrange|].
  apply aligned_8_aligned_4. exact Halign.
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

Lemma undef_store_ptr_align4 : forall x : addr, sizeof(PTR) = 4 -> (4 | ptr_align) -> x # Ptr |->_ |-- store_align4_n 1.
Proof.
  intros x Hsize Hdiv. eapply derivable1_trans.
  2: apply undef_store_int_align4.
  unfold poly_undef_store, undef_store_ptr, undef_store_int, undef_store_integer.
  rewrite Hsize. Intros. entailer!.
  unfold valid_object, Arch.valid_object in *.
  destruct H as [Hrange Halign]. split; [exact Hrange|].
  eapply Arch.aligned_weaken; [lia|apply Arch.ptr_align_pos|exact Hdiv|exact Halign].
Qed.

Lemma store_ptr_align4 : forall (x : addr) v, sizeof(PTR) = 4 -> (4 | ptr_align) -> x # Ptr |-> v |-- store_align4_n 1.
Proof.
  intros x v Hsize Hdiv.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply (undef_store_ptr_align4 x Hsize Hdiv).
  entailer!.
Qed.

Lemma store_byte_valid : forall x y, undef_store_byte x ** undef_store_byte y |-- “ x < y \/ y < x ”.
Proof.
  intros.
  unfold undef_store_byte.
  destruct (Z_lt_ge_dec (x + 1) y).
  - entailer!.
  - destruct (Z_lt_ge_dec (y + 1) x).
    + entailer!.
    + assert (x = y - 1 \/ x = y \/ x = y + 1) by lia.
      destruct H as [ ? | [ ? | ? ]] ; subst.
      * entailer!.
      * prop_apply (dup_undef_store_byte y). Intros. lia.
      * entailer!.
Qed.

Lemma store_4byte_valid : forall x y, undef_store_bytes x 4 ** undef_store_bytes y 4 |-- “ x + 3 < y \/ y + 3 < x ”.
Proof.
  intros.
  cbn [undef_store_bytes]; rewrite ?sepcon_emp_equiv;
    repeat rewrite <- Z.add_assoc; cbn [Z.add Pos.add Pos.add_carry].
  destruct (Z_lt_ge_dec (x + 3) y).
  - entailer!. 
  - destruct (Z_lt_ge_dec (y + 3) x).
    + entailer!.
    + assert (x = y - 3 \/ x = y - 2 \/ x = y - 1 \/ x = y \/ x = y + 1 \/ x = y + 2 \/ x = y + 3) by lia.
      destruct H as [? | [ ? | [? | [ ? | [? | [ ? | ? ]]]]]] ; subst.
      * replace (y - 3 + 3) with y by lia. 
        prop_apply (dup_undef_store_byte y). Intros. lia.
      * replace (y - 2 + 2) with y by lia. 
        prop_apply (dup_undef_store_byte y). Intros. lia.
      * replace (y - 1 + 1) with y by lia. 
        prop_apply (dup_undef_store_byte y). Intros. lia.
      * prop_apply (dup_undef_store_byte y). Intros. lia.
      * prop_apply (dup_undef_store_byte (y + 1)). Intros. lia.
      * prop_apply (dup_undef_store_byte (y + 2)). Intros. lia.
      * prop_apply (dup_undef_store_byte (y + 3)). Intros. lia.
Qed.

Lemma store_align4_valid : forall x l, store_align4_list l ** undef_store_bytes x 4 |-- “ Forall (fun x' => x + 3 < x' \/ x' + 3 < x) l ”.
Proof.
  intros.
  induction l; cbn [store_align4_list] in *.
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
  induction H1 ; cbn [List.app store_align4_list] in * ; intros ; auto.
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
    (ltac:(unfold addr_max_unsigned; pose proof Arch.addr_max_unsigned_nonneg; lia))
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

Lemma store_align_valid : forall x l, store_align_list l ** undef_store_byte x |-- “ Forall (fun x' => x + 0 < x' \/ x' + 0 < x) l ”.
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

Lemma undef_store_bytes_align : forall n x,
  0 <= x ->
  x + Z.of_nat n - 1 <= addr_max_unsigned ->
  undef_store_bytes x n |-- store_align_n (Z.of_nat n).
Proof.
  induction n; intros x Hlo Hhi; cbn [undef_store_bytes].
  - unfold store_align_n.
    Exists nil.
    simpl.
    entailer!.
    constructor.
  - sep_apply (store_byte_align1 x ltac:(unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned; fold addr_max_unsigned in *; simpl_nonptr_sizeof; rewrite ?Z.mod_1_r; repeat split; lia)).
    sep_apply (IHn (x + 1) ltac:(lia) ltac:(
      replace (x + 1 + Z.of_nat n - 1) with (x + Z.of_nat (S n) - 1) by lia;
      lia)).
    sep_apply (store_align_merge 1 (Z.of_nat n)).
    replace (1 + Z.of_nat n) with (Z.of_nat (S n)) by lia.
    entailer!.
Qed.

Lemma undef_store_int_footprint : forall n align x,
  undef_store_integer n align x |-- store_align_n (Z.of_nat n).
Proof.
  intros n align x.
  unfold undef_store_integer.
  Intros_p Hvalid.
  unfold valid_object, Arch.valid_object, Arch.valid_addr_range in Hvalid.
  destruct Hvalid as [[Hlo [_ Hhi]] _].
  apply undef_store_bytes_align; assumption.
Qed.

Lemma store_int_footprint : forall n align x v,
  store_integer n align x v |-- store_align_n (Z.of_nat n).
Proof.
  intros.
  eapply derivable1_trans.
  - apply store_int_forget.
  - apply undef_store_int_footprint.
Qed.

Lemma store_uint_footprint : forall n align x v,
  store_uinteger n align x v |-- store_align_n (Z.of_nat n).
Proof.
  intros.
  eapply derivable1_trans.
  - apply store_uint_forget.
  - apply undef_store_int_footprint.
Qed.


Lemma undef_store_short_align : forall x, x # Short |->_ |-- store_align_n 2.
Proof.
  intros x. apply undef_store_int_footprint.
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
  intros x. apply undef_store_int_footprint.
Qed.

Lemma store_ushort_align : forall x v, x # UShort |-> v |-- store_align_n 2.
Proof.
  intros.
  sep_apply store_ushort_undef_store_ushort.
  sep_apply undef_store_ushort_align.
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
  pose proof interval_list_range l 0 0 addr_max_unsigned (ltac:(lia)) (ltac:(unfold addr_max_unsigned; pose proof Arch.addr_max_unsigned_nonneg; lia)) H0.
  simpl in *.
  rewrite Z.div_1_r.
  lia.
Qed.

(* The owned byte resources determine their count, independently of any
   array element size or machine integer bound. *)
Lemma store_align_n_range : forall n,
  store_align_n n |-- “ 0 <= n <= addr_max_unsigned + 1 ”.
Proof.
  intros n.
  prop_apply (store_align_n_valid n).
  Intros_p Hupper.
  unfold store_align_n.
  Intros l.
  match goal with
  | Hcount : Zlength l = n /\ _ |- _ =>
      destruct Hcount as [Hlength _]
  end.
  dump_pre_spatial.
  pose proof (Zlength_nonneg l) as Hnonnegative.
  rewrite Z.div_1_r in Hupper.
  lia.
Qed.

Lemma store_align4_to_store_align : forall n, store_align4_n n |-- store_align_n (4 * n).
Proof.
  intros n. unfold store_align4_n. Intros l.
  destruct H as [Hcount Hinterval]. rewrite <- Hcount.
  clear n Hcount Hinterval. induction l as [|a l IH].
  - cbn [store_align4_list]. unfold store_align_n.
    Exists nil. entailer!. constructor.
  - cbn [store_align4_list]. Intros_p Hvalid.
    unfold valid_object, Arch.valid_object, Arch.valid_addr_range in Hvalid.
    destruct Hvalid as [[Hlo [_ Hhi]] _].
    sep_apply (undef_store_bytes_align 4 a Hlo Hhi).
    change (Z.of_nat (4%nat)) with 4.
    sep_apply IH.
    sep_apply (store_align_merge 4 (4 * Zlength l)).
    rewrite Zlength_cons.
    replace (4 * Z.succ (Zlength l)) with (4 + 4 * Zlength l) by lia.
    apply derivable1_refl.
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
  unfold poly_undef_store, undef_store_long_double.
  apply coq_prop_andp_left. intros Hvalid.
  apply undef_store_bytes_align; unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in Hvalid; fold addr_max_unsigned in *; simpl_nonptr_sizeof; lia.
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
  intros x. apply undef_store_int_footprint.
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
  intros x. apply undef_store_int_footprint.
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
  forall x, sizeof(PTR) = 8 -> (4 | ptr_align) -> x # Ptr |->_ |-- x # UInt64 |->_.
Proof.
  intros x Hsize Hdiv.
  unfold poly_undef_store, undef_store_ptr, undef_store_int64, undef_store_integer,
    derivable1, andp, coq_prop.
  rewrite Hsize. intros m [Hobject Hbytes]. split; [|exact Hbytes].
  unfold valid_object, Arch.valid_object in *.
  destruct Hobject as [Hrange Halign]. split; [exact Hrange|].
  eapply Arch.aligned_weaken; [lia|apply Arch.ptr_align_pos|exact Hdiv|exact Halign].
Qed.

Lemma undef_store_ptr_undef_store_int64 :
  forall x, sizeof(PTR) = 8 -> (4 | ptr_align) -> x # Ptr |->_ |-- x # Int64 |->_.
Proof.
  intros x Hsize Hdiv. apply undef_store_ptr_undef_store_uint64; assumption.
Qed.

Lemma undef_store_ptr_align :
  forall x, x # Ptr |->_ |-- store_align_n (sizeof(PTR)).
Proof.
  intros x.
  unfold poly_undef_store, undef_store_ptr.
  Intros_p Hvalid.
  pose proof sizeof_ptr_pos as Hsize.
  pose proof (Z2Nat.id (sizeof(PTR)) ltac:(lia)) as Hsize_nat.
  eapply derivable1_trans.
  - apply undef_store_bytes_align;
      unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned in Hvalid; fold addr_max_unsigned in *; simpl_nonptr_sizeof; lia.
  - rewrite Z2Nat.id by lia.
    apply derivable1_refl.
Qed.

Lemma store_ptr_align :
  forall x v, x # Ptr |-> v |-- store_align_n (sizeof(PTR)).
Proof.
  intros.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply undef_store_ptr_align.
  entailer!.
Qed.

Lemma store_ptr_store_uint : forall x v,
  sizeof(PTR) = 4 ->
  (4 | ptr_align) ->
  x # Ptr |-> v |-- x # UInt |-> v.
Proof.
  intros x v Hsize Hdiv.
  unfold poly_store, store_ptr, store_uinteger, derivable1, andp, coq_prop.
  rewrite Hsize. intros m [[Hobject Hvalue] Hbytes]. split.
  - split.
    + unfold valid_object, Arch.valid_object in *.
      destruct Hobject as [Hrange Halign]. split; [exact Hrange|].
      eapply Arch.aligned_weaken; [lia|apply Arch.ptr_align_pos|exact Hdiv|exact Halign].
    + unfold valid_unsigned_value. change (0 <= v < 4294967296).
      pose proof (Arch.valid_ptr_value_range v Hvalue) as Hrange.
      change (0 <= v < 2 ^ (8 * sizeof(PTR))) in Hrange.
      rewrite Hsize in Hrange. exact Hrange.
  - exact Hbytes.
Qed.

Lemma store_ptr_store_uint64 : forall x v,
  sizeof(PTR) = 8 ->
  (4 | ptr_align) ->
  x # Ptr |-> v |-- x # UInt64 |-> v.
Proof.
  intros x v Hsize Hdiv.
  unfold poly_store, store_ptr, store_uinteger, derivable1, andp, coq_prop.
  rewrite Hsize. intros m [[Hobject Hvalue] Hbytes]. split.
  - split.
    + unfold valid_object, Arch.valid_object in *.
      destruct Hobject as [Hrange Halign]. split; [exact Hrange|].
      eapply Arch.aligned_weaken; [lia|apply Arch.ptr_align_pos|exact Hdiv|exact Halign].
    + unfold valid_unsigned_value. change (0 <= v < 18446744073709551616).
      pose proof (Arch.valid_ptr_value_range v Hvalue) as Hrange.
      change (0 <= v < 2 ^ (8 * sizeof(PTR))) in Hrange.
      rewrite Hsize in Hrange. exact Hrange.
  - exact Hbytes.
Qed.

End StoreLibSig.
