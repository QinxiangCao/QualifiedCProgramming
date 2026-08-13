Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Set Warnings "-warn-library-file-stdlib-vector".
Require Coq.Vectors.Vector.
From compcert.lib Require Import Coqlib Integers.

Local Open Scope Z_scope.

Module Type CArchSig.
  Parameter ptr_size : nat.
  Parameter ptr_align : Z.
  Parameter addr_max_unsigned : Z.

  Definition ptr_size_Z : Z := Z.of_nat ptr_size.
  Definition ptr_width_Z : Z := 8 * ptr_size_Z.
  Definition aligned (align p : Z) : Prop :=
    p mod align = 0.

  Axiom ptr_size_pos : 0 < ptr_size_Z.
  Axiom ptr_size_32_or_64 : ptr_size = 4%nat \/ ptr_size = 8%nat.
  Axiom ptr_align_pos : 0 < ptr_align.
  Axiom ptr_aligned_aligned_4 :
    forall x, aligned ptr_align x -> x mod 4 = 0.
  Axiom addr_max_unsigned_ge_7 : 7 <= addr_max_unsigned.
  Axiom ptr_size_fits_addr : ptr_size_Z - 1 <= addr_max_unsigned.
  Axiom int_max_fits_addr : Int.max_unsigned <= addr_max_unsigned.

  Definition valid_addr_range (p len : Z) : Prop :=
    0 <= p /\ 0 <= len /\ p + len - 1 <= addr_max_unsigned.

  Definition valid_object (p len align : Z) : Prop :=
    valid_addr_range p len /\ aligned align p.

  Definition valid_ptr_value (v : Z) : Prop :=
    0 <= v /\ v <= addr_max_unsigned.
End CArchSig.

Module Arch32 <: CArchSig.
  Definition ptr_size : nat := 4%nat.
  Definition ptr_align : Z := 4.
  Definition addr_max_unsigned : Z := Int.max_unsigned.
  Definition ptr_size_Z : Z := Z.of_nat ptr_size.
  Definition ptr_width_Z : Z := 8 * ptr_size_Z.
  Definition aligned (align p : Z) : Prop :=
    p mod align = 0.

  Lemma ptr_size_pos : 0 < ptr_size_Z.
  Proof. compute; auto. Qed.

  Lemma ptr_size_32_or_64 : ptr_size = 4%nat \/ ptr_size = 8%nat.
  Proof. left; reflexivity. Qed.

  Lemma ptr_align_pos : 0 < ptr_align.
  Proof. compute; auto. Qed.

  Lemma ptr_aligned_aligned_4 :
    forall x, aligned ptr_align x -> x mod 4 = 0.
  Proof. cbv; auto. Qed.

  Lemma addr_max_unsigned_ge_7 : 7 <= addr_max_unsigned.
  Proof. unfold addr_max_unsigned. change Int.max_unsigned with 4294967295. lia. Qed.

  Lemma ptr_size_fits_addr : ptr_size_Z - 1 <= addr_max_unsigned.
  Proof. unfold ptr_size_Z, ptr_size, addr_max_unsigned. change Int.max_unsigned with 4294967295. lia. Qed.

  Lemma int_max_fits_addr : Int.max_unsigned <= addr_max_unsigned.
  Proof. unfold addr_max_unsigned. lia. Qed.

  Definition valid_addr_range (p len : Z) : Prop :=
    0 <= p /\ 0 <= len /\ p + len - 1 <= addr_max_unsigned.

  Definition valid_object (p len align : Z) : Prop :=
    valid_addr_range p len /\ aligned align p.

  Definition valid_ptr_value (v : Z) : Prop :=
    0 <= v /\ v <= addr_max_unsigned.
End Arch32.

Module Arch64 <: CArchSig.
  Definition ptr_size : nat := 8%nat.
  Definition ptr_align : Z := 8.
  Definition addr_max_unsigned : Z := Int64.max_unsigned.
  Definition ptr_size_Z : Z := Z.of_nat ptr_size.
  Definition ptr_width_Z : Z := 8 * ptr_size_Z.
  Definition aligned (align p : Z) : Prop :=
    p mod align = 0.

  Lemma ptr_size_pos : 0 < ptr_size_Z.
  Proof. compute; auto. Qed.

  Lemma ptr_size_32_or_64 : ptr_size = 4%nat \/ ptr_size = 8%nat.
  Proof. right; reflexivity. Qed.

  Lemma ptr_align_pos : 0 < ptr_align.
  Proof. compute; auto. Qed.

  Lemma ptr_aligned_aligned_4 :
    forall x, aligned ptr_align x -> x mod 4 = 0.
  Proof.
    unfold aligned, ptr_align.
    intros x H.
    apply Z.mod_divide in H; try lia.
    destruct H as [k Hk].
    subst x.
    replace (k * 8) with ((2 * k) * 4) by ring.
    apply Z_mod_mult.
  Qed.

  Lemma addr_max_unsigned_ge_7 : 7 <= addr_max_unsigned.
  Proof. unfold addr_max_unsigned. change Int64.max_unsigned with 18446744073709551615. lia. Qed.

  Lemma ptr_size_fits_addr : ptr_size_Z - 1 <= addr_max_unsigned.
  Proof. unfold ptr_size_Z, ptr_size, addr_max_unsigned. change Int64.max_unsigned with 18446744073709551615. lia. Qed.

  Lemma int_max_fits_addr : Int.max_unsigned <= addr_max_unsigned.
  Proof.
    unfold addr_max_unsigned.
    change Int.max_unsigned with 4294967295.
    change Int64.max_unsigned with 18446744073709551615.
    lia.
  Qed.

  Definition valid_addr_range (p len : Z) : Prop :=
    0 <= p /\ 0 <= len /\ p + len - 1 <= addr_max_unsigned.

  Definition valid_object (p len align : Z) : Prop :=
    valid_addr_range p len /\ aligned align p.

  Definition valid_ptr_value (v : Z) : Prop :=
    0 <= v /\ v <= addr_max_unsigned.
End Arch64.

Module Type CEndianSig.
  Import Vector.VectorNotations.
  Notation byte := Z (only parsing).

  Parameter bytes_eqm : forall n : nat, Vector.t byte n -> Vector.t byte n -> Prop.
  Parameter n_bytes_to_Z : forall n : nat, Vector.t byte n -> Z.
  Parameter Z_to_n_bytes : Z -> forall length : nat, Vector.t byte length.
  Parameter merge_n_bytes : forall n : nat, Vector.t byte n -> Z -> Prop.
  Parameter merge_short : Z -> Z -> Z -> Prop.
  Parameter merge_int : Z -> Z -> Z -> Z -> Z -> Prop.
  Parameter merge_int64 : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop.

  Axiom eqm_bytes_to_Z_eq :
    forall n (v1 v2 : Vector.t byte n),
      bytes_eqm n v1 v2 -> n_bytes_to_Z n v1 = n_bytes_to_Z n v2.
  Axiom Z_to_n_bytes_to_Z :
    forall length v,
      n_bytes_to_Z length (Z_to_n_bytes v length) =
      v mod (2 ^ (8 * Z.of_nat length)).
  Axiom merge_n_bytes_self :
    forall n (v : Vector.t byte n),
      merge_n_bytes n v (n_bytes_to_Z n v).
  Axiom merge_byte_equiv_merge_n_bytes :
    forall x y,
      Byte.eqm x y <-> merge_n_bytes 1 [x]%vector y.
  Axiom merge_short_equiv_merge_n_bytes :
    forall x1 x2 y,
      merge_short x1 x2 y <-> merge_n_bytes 2 [x1; x2]%vector y.
  Axiom merge_int_equiv_merge_n_bytes :
    forall x1 x2 x3 x4 y,
      merge_int x1 x2 x3 x4 y <-> merge_n_bytes 4 [x1; x2; x3; x4]%vector y.
  Axiom merge_int64_equiv_merge_n_bytes :
    forall x1 x2 x3 x4 x5 x6 x7 x8 y,
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 y <->
      merge_n_bytes 8 [x1; x2; x3; x4; x5; x6; x7; x8]%vector y.
  Axiom merge_short_eqm :
    forall x1 x2 y1 y2 v,
      Byte.eqm x1 y1 -> Byte.eqm x2 y2 ->
      merge_short x1 x2 v -> merge_short y1 y2 v.
  Axiom merge_int_eqm :
    forall x1 x2 x3 x4 y1 y2 y3 y4 v,
      Byte.eqm x1 y1 -> Byte.eqm x2 y2 -> Byte.eqm x3 y3 -> Byte.eqm x4 y4 ->
      merge_int x1 x2 x3 x4 v -> merge_int y1 y2 y3 y4 v.
  Axiom merge_int64_eqm :
    forall x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 y6 y7 y8 v,
      Byte.eqm x1 y1 -> Byte.eqm x2 y2 -> Byte.eqm x3 y3 -> Byte.eqm x4 y4 ->
      Byte.eqm x5 y5 -> Byte.eqm x6 y6 -> Byte.eqm x7 y7 -> Byte.eqm x8 y8 ->
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v ->
      merge_int64 y1 y2 y3 y4 y5 y6 y7 y8 v.
  Axiom merge_short_value_eqm :
    forall x1 x2 v v',
      v mod 2^16 = v' mod 2^16 ->
      merge_short x1 x2 v -> merge_short x1 x2 v'.
  Axiom merge_int_value_eqm :
    forall x1 x2 x3 x4 v v',
      v mod 2^32 = v' mod 2^32 ->
      merge_int x1 x2 x3 x4 v -> merge_int x1 x2 x3 x4 v'.
  Axiom merge_int64_value_eqm :
    forall x1 x2 x3 x4 x5 x6 x7 x8 v v',
      v mod 2^64 = v' mod 2^64 ->
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v ->
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v'.
End CEndianSig.

Module BigEndian <: CEndianSig.
  Import Vector.VectorNotations.
  Notation byte := Z (only parsing).

  Fixpoint bytes_eqm (n : nat) : forall (v1 v2 : Vector.t byte n), Prop :=
    match n with
    | O => fun _ _ => True
    | S n => fun v1 v2 =>
        Vector.caseS' v1 (fun _ => Prop) (fun hd1 tl1 =>
          Vector.caseS' v2 (fun _ => Prop) (fun hd2 tl2 =>
            Byte.eqm hd1 hd2 /\ bytes_eqm n tl1 tl2))
    end.

  Fixpoint n_bytes_to_Z n (v : Vector.t byte n) : Z :=
    match v with
    | Vector.nil _ => 0
    | Vector.cons _ b n v' =>
        (b mod 2^8) * 2 ^ (8 * Z.of_nat n) + n_bytes_to_Z n v'
    end.

  Fixpoint Z_to_n_bytes (v : Z) (length : nat) : Vector.t byte length :=
    match length with
    | O => Vector.nil _
    | S n =>
        (v / 2 ^ (8 * Z.of_nat n) mod 2^8 :: Z_to_n_bytes v n)%vector
    end.

  Lemma n_bytes_to_Z_cons b n v :
    n_bytes_to_Z (S n) (b :: v)%vector =
    (b mod 2^8) * 2 ^ (8 * Z.of_nat n) + n_bytes_to_Z n v.
  Proof. reflexivity. Qed.

  Lemma Z_to_n_bytes_succ v length :
    Z_to_n_bytes v (S length) =
    (v / 2 ^ (8 * Z.of_nat length) mod 2^8 :: Z_to_n_bytes v length)%vector.
  Proof. reflexivity. Qed.

  Definition merge_n_bytes n (v : Vector.t byte n) (x : Z) : Prop :=
    x mod (2 ^ (8 * Z.of_nat n)) = n_bytes_to_Z n v.

  Definition merge_short (x1 x2 y: Z): Prop :=
    y mod (2^16) =
    x1 mod (2^8) * (2^8) +
    x2 mod (2^8).

  Definition merge_int (x1 x2 x3 x4 y: Z): Prop :=
    y mod (2^32) =
    x1 mod (2^8) * (2^24) +
    x2 mod (2^8) * (2^16) +
    x3 mod (2^8) * (2^8) +
    x4 mod (2^8).

  Definition merge_int64 (x1 x2 x3 x4 x5 x6 x7 x8 y: Z): Prop :=
    y mod (2^64) =
    x1 mod (2^8) * (2^56) +
    x2 mod (2^8) * (2^48) +
    x3 mod (2^8) * (2^40) +
    x4 mod (2^8) * (2^32) +
    x5 mod (2^8) * (2^24) +
    x6 mod (2^8) * (2^16) +
    x7 mod (2^8) * (2^8) +
    x8 mod (2^8).

  Lemma eqm_bytes_to_Z_eq n v1 v2 :
    bytes_eqm n v1 v2 -> n_bytes_to_Z n v1 = n_bytes_to_Z n v2.
  Proof.
    induction n.
    - revert v1. refine (Vector.case0 _ _).
      revert v2. refine (Vector.case0 _ _).
      cbn. reflexivity.
    - apply (Vector.caseS' v1). clear v1. intros hd1 tl1.
      apply (Vector.caseS' v2). clear v2. intros hd2 tl2.
      simpl (bytes_eqm _ _). cbn. intros [Hhd H].
      assert (Hmod : hd1 mod 256 = hd2 mod 256).
      { change 256 with Byte.modulus. apply Byte.eqm_mod_eq. exact Hhd. }
      rewrite Hmod.
      rewrite (IHn tl1 tl2); auto.
  Qed.

  Lemma Z_to_n_bytes_to_Z length v :
    n_bytes_to_Z length (Z_to_n_bytes v length) =
    v mod (2 ^ (8 * Z.of_nat length)).
  Proof.
    revert v; induction length; intros v.
    - simpl. rewrite Z.mod_1_r. reflexivity.
    - rewrite Z_to_n_bytes_succ, n_bytes_to_Z_cons.
      rewrite Z.mod_mod. 2: lia.
      rewrite IHlength.
      replace (8 * (Z.of_nat (S length))) with (8 + 8 * Z.of_nat length) by lia.
      rewrite Z.pow_add_r. 2-3: lia.
      rewrite Zmod_recombine. 2-3: lia.
      reflexivity.
  Qed.

  Lemma n_bytes_to_Z_range n (v : Vector.t byte n) :
    0 <= n_bytes_to_Z n v < 2 ^ (8 * Z.of_nat n).
  Proof.
    induction v as [|b n v IH].
    - cbn. lia.
    - rewrite n_bytes_to_Z_cons.
      pose proof Z.mod_pos_bound b (2 ^ 8) ltac:(lia) as Hb.
      replace (2 ^ (8 * Z.of_nat (S n)))
        with (256 * 2 ^ (8 * Z.of_nat n)).
      2:{
        replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
        rewrite Z.pow_add_r by lia.
        change (2 ^ 8) with 256.
        ring.
      }
      change (Z.pow_pos 2 (Pos.of_succ_nat n)~0~0~0)
        with (2 ^ (8 * Z.of_nat n)).
      change (2 ^ 8) with 256 in *.
      assert (Hpow_pos : 0 < 2 ^ (8 * Z.of_nat n))
        by (apply Z.pow_pos_nonneg; lia).
      set (q := 2 ^ (8 * Z.of_nat n)) in *.
      destruct IH as [IHlo IHhi].
      destruct Hb as [Hblo Hbhi].
      split.
      + nia.
      + assert (Hb_le : b mod 256 <= 255) by lia.
        assert (Hmul : b mod 256 * q <= 255 * q) by nia.
        assert (IH_le : n_bytes_to_Z n v <= q - 1) by lia.
        replace (256 * q) with (255 * q + q) by ring.
        nia.
  Qed.

  Lemma merge_n_bytes_self n (v : Vector.t byte n) :
    merge_n_bytes n v (n_bytes_to_Z n v).
  Proof.
    unfold merge_n_bytes.
    rewrite Z.mod_small; [reflexivity | apply n_bytes_to_Z_range].
  Qed.

  Lemma merge_byte_equiv_merge_n_bytes x y :
    Byte.eqm x y <-> merge_n_bytes 1 [x]%vector y.
  Proof.
    unfold merge_n_bytes. cbn. rewrite Z.add_0_r, Z.mul_1_r.
    split; intros H.
    - assert (Hmod : x mod 256 = y mod 256).
      { change 256 with Byte.modulus. apply Byte.eqm_mod_eq. exact H. }
      rewrite Hmod. reflexivity.
    - unfold Byte.eqm. apply Zbits.eqmod_trans with (x mod 256).
      + apply Zbits.eqmod_mod.
      + apply Zbits.eqmod_trans with (y mod 256).
        * apply Zbits.eqmod_refl2. symmetry; auto.
        * apply Zbits.eqmod_sym. apply Zbits.eqmod_mod.
  Qed.

  Lemma merge_short_equiv_merge_n_bytes x1 x2 y :
    merge_short x1 x2 y <-> merge_n_bytes 2 [x1; x2]%vector y.
  Proof.
    unfold merge_short, merge_n_bytes. cbn.
    rewrite Z.add_0_r, Z.mul_1_r.
    reflexivity.
  Qed.

  Lemma merge_int_equiv_merge_n_bytes x1 x2 x3 x4 y :
    merge_int x1 x2 x3 x4 y <-> merge_n_bytes 4 [x1; x2; x3; x4]%vector y.
  Proof.
    unfold merge_int, merge_n_bytes. cbn.
    rewrite Z.add_0_r, Z.mul_1_r, !Z.add_assoc.
    reflexivity.
  Qed.

  Lemma merge_int64_equiv_merge_n_bytes x1 x2 x3 x4 x5 x6 x7 x8 y :
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 y <->
    merge_n_bytes 8 [x1; x2; x3; x4; x5; x6; x7; x8]%vector y.
  Proof.
    unfold merge_int64, merge_n_bytes. cbn.
    rewrite Z.add_0_r, Z.mul_1_r, !Z.add_assoc.
    reflexivity.
  Qed.

  Lemma merge_short_eqm x1 x2 y1 y2 v :
    Byte.eqm x1 y1 -> Byte.eqm x2 y2 ->
    merge_short x1 x2 v -> merge_short y1 y2 v.
  Proof.
    intros H1 H2 H.
    assert (Hmod1 : x1 mod 2^8 = y1 mod 2^8).
    { change (2^8) with Byte.modulus. apply Byte.eqm_mod_eq. exact H1. }
    assert (Hmod2 : x2 mod 2^8 = y2 mod 2^8).
    { change (2^8) with Byte.modulus. apply Byte.eqm_mod_eq. exact H2. }
    unfold merge_short in *.
    rewrite <- Hmod1, <- Hmod2.
    exact H.
  Qed.

  Lemma merge_int_eqm x1 x2 x3 x4 y1 y2 y3 y4 v :
    Byte.eqm x1 y1 -> Byte.eqm x2 y2 -> Byte.eqm x3 y3 -> Byte.eqm x4 y4 ->
    merge_int x1 x2 x3 x4 v -> merge_int y1 y2 y3 y4 v.
  Proof.
    intros H1 H2 H3 H4 H.
    assert (Hmod1 : x1 mod 2^8 = y1 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H1).
    assert (Hmod2 : x2 mod 2^8 = y2 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H2).
    assert (Hmod3 : x3 mod 2^8 = y3 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H3).
    assert (Hmod4 : x4 mod 2^8 = y4 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H4).
    unfold merge_int in *.
    rewrite <- Hmod1, <- Hmod2, <- Hmod3, <- Hmod4.
    exact H.
  Qed.

  Lemma merge_int64_eqm x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 y6 y7 y8 v :
    Byte.eqm x1 y1 -> Byte.eqm x2 y2 -> Byte.eqm x3 y3 -> Byte.eqm x4 y4 ->
    Byte.eqm x5 y5 -> Byte.eqm x6 y6 -> Byte.eqm x7 y7 -> Byte.eqm x8 y8 ->
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v ->
    merge_int64 y1 y2 y3 y4 y5 y6 y7 y8 v.
  Proof.
    intros H1 H2 H3 H4 H5 H6 H7 H8 H.
    assert (Hmod1 : x1 mod 2^8 = y1 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H1).
    assert (Hmod2 : x2 mod 2^8 = y2 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H2).
    assert (Hmod3 : x3 mod 2^8 = y3 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H3).
    assert (Hmod4 : x4 mod 2^8 = y4 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H4).
    assert (Hmod5 : x5 mod 2^8 = y5 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H5).
    assert (Hmod6 : x6 mod 2^8 = y6 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H6).
    assert (Hmod7 : x7 mod 2^8 = y7 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H7).
    assert (Hmod8 : x8 mod 2^8 = y8 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H8).
    unfold merge_int64 in *.
    rewrite <- Hmod1, <- Hmod2, <- Hmod3, <- Hmod4.
    rewrite <- Hmod5, <- Hmod6, <- Hmod7, <- Hmod8.
    exact H.
  Qed.

  Lemma merge_short_value_eqm x1 x2 v v' :
    v mod 2^16 = v' mod 2^16 ->
    merge_short x1 x2 v -> merge_short x1 x2 v'.
  Proof.
    unfold merge_short.
    intros Hmod H. rewrite <- Hmod. exact H.
  Qed.

  Lemma merge_int_value_eqm x1 x2 x3 x4 v v' :
    v mod 2^32 = v' mod 2^32 ->
    merge_int x1 x2 x3 x4 v -> merge_int x1 x2 x3 x4 v'.
  Proof.
    unfold merge_int.
    intros Hmod H. rewrite <- Hmod. exact H.
  Qed.

  Lemma merge_int64_value_eqm x1 x2 x3 x4 x5 x6 x7 x8 v v' :
    v mod 2^64 = v' mod 2^64 ->
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v ->
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v'.
  Proof.
    unfold merge_int64.
    intros Hmod H. rewrite <- Hmod. exact H.
  Qed.
End BigEndian.

Module LittleEndian <: CEndianSig.
  Import Vector.VectorNotations.
  Notation byte := Z (only parsing).

  Fixpoint bytes_eqm (n : nat) : forall (v1 v2 : Vector.t byte n), Prop :=
    match n with
    | O => fun _ _ => True
    | S n => fun v1 v2 =>
        Vector.caseS' v1 (fun _ => Prop) (fun hd1 tl1 =>
          Vector.caseS' v2 (fun _ => Prop) (fun hd2 tl2 =>
            Byte.eqm hd1 hd2 /\ bytes_eqm n tl1 tl2))
    end.

  Fixpoint n_bytes_to_Z n (v : Vector.t byte n) : Z :=
    match v with
    | Vector.nil _ => 0
    | Vector.cons _ b n v' =>
        (b mod 2^8) + 2^8 * n_bytes_to_Z n v'
    end.

  Fixpoint Z_to_n_bytes (v : Z) (length : nat) : Vector.t byte length :=
    match length with
    | O => Vector.nil _
    | S n => (v mod 2^8 :: Z_to_n_bytes (v / 2^8) n)%vector
    end.

  Definition merge_n_bytes n (v : Vector.t byte n) (x : Z) : Prop :=
    x mod (2 ^ (8 * Z.of_nat n)) = n_bytes_to_Z n v.

  Definition merge_short (x1 x2 y: Z): Prop :=
    y mod (2^16) =
    x1 mod (2^8) +
    x2 mod (2^8) * (2^8).

  Definition merge_int (x1 x2 x3 x4 y: Z): Prop :=
    y mod (2^32) =
    x1 mod (2^8) +
    x2 mod (2^8) * (2^8) +
    x3 mod (2^8) * (2^16) +
    x4 mod (2^8) * (2^24).

  Definition merge_int64 (x1 x2 x3 x4 x5 x6 x7 x8 y: Z): Prop :=
    y mod (2^64) =
    x1 mod (2^8) +
    x2 mod (2^8) * (2^8) +
    x3 mod (2^8) * (2^16) +
    x4 mod (2^8) * (2^24) +
    x5 mod (2^8) * (2^32) +
    x6 mod (2^8) * (2^40) +
    x7 mod (2^8) * (2^48) +
    x8 mod (2^8) * (2^56).

  Lemma n_bytes_to_Z_cons b n v :
    n_bytes_to_Z (S n) (b :: v)%vector =
    b mod 2^8 + 2^8 * n_bytes_to_Z n v.
  Proof. reflexivity. Qed.

  Lemma eqm_bytes_to_Z_eq n v1 v2 :
    bytes_eqm n v1 v2 -> n_bytes_to_Z n v1 = n_bytes_to_Z n v2.
  Proof.
    induction n.
    - revert v1. refine (Vector.case0 _ _).
      revert v2. refine (Vector.case0 _ _).
      cbn. reflexivity.
    - apply (Vector.caseS' v1). clear v1. intros hd1 tl1.
      apply (Vector.caseS' v2). clear v2. intros hd2 tl2.
      simpl (bytes_eqm _ _). cbn. intros [Hhd H].
      assert (Hmod : hd1 mod 256 = hd2 mod 256).
      { change 256 with Byte.modulus. apply Byte.eqm_mod_eq. exact Hhd. }
      rewrite Hmod.
      rewrite (IHn tl1 tl2); auto.
  Qed.

  Lemma Z_to_n_bytes_to_Z length v :
    n_bytes_to_Z length (Z_to_n_bytes v length) =
    v mod (2 ^ (8 * Z.of_nat length)).
  Proof.
    revert v; induction length; intros v.
    - simpl. rewrite Z.mod_1_r. reflexivity.
    - simpl.
      rewrite Z.mod_mod. 2: lia.
      rewrite IHlength.
      change (Z.pow_pos 2 8) with 256.
      change (match (v / 256) mod 2 ^ (8 * Z.of_nat length) with
              | 0 => 0
              | Z.pos y' => Z.pos y'~0~0~0~0~0~0~0~0
              | Z.neg y' => Z.neg y'~0~0~0~0~0~0~0~0
              end) with
        (256 * ((v / 256) mod 2 ^ (8 * Z.of_nat length))).
      set (a := 2 ^ (8 * Z.of_nat length)).
      assert (Hpow : Z.pow_pos 2 (Pos.of_succ_nat length)~0~0~0 = a * 256).
      {
        subst a.
        change (Z.pow_pos 2 (Pos.of_succ_nat length)~0~0~0) with
          (2 ^ (8 * Z.of_nat (S length))).
        replace (8 * Z.of_nat (S length)) with (8 * Z.of_nat length + 8) by lia.
        rewrite Z.pow_add_r. 2-3: lia.
        change (2 ^ 8) with 256.
        ring.
      }
      rewrite Hpow.
      rewrite (Zmod_recombine v a 256). 2: subst a; lia. 2: lia.
      ring.
  Qed.

  Lemma n_bytes_to_Z_range n (v : Vector.t byte n) :
    0 <= n_bytes_to_Z n v < 2 ^ (8 * Z.of_nat n).
  Proof.
    induction v as [|b n v IH].
    - cbn. lia.
    - rewrite n_bytes_to_Z_cons.
      pose proof Z.mod_pos_bound b (2 ^ 8) ltac:(lia) as Hb.
      replace (2 ^ (8 * Z.of_nat (S n)))
        with (256 * 2 ^ (8 * Z.of_nat n)).
      2:{
        replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
        rewrite Z.pow_add_r by lia.
        change (2 ^ 8) with 256.
        ring.
      }
      change (Z.pow_pos 2 (Pos.of_succ_nat n)~0~0~0)
        with (2 ^ (8 * Z.of_nat n)).
      change (2 ^ 8) with 256 in *.
      assert (Hpow_pos : 0 < 2 ^ (8 * Z.of_nat n))
        by (apply Z.pow_pos_nonneg; lia).
      set (q := 2 ^ (8 * Z.of_nat n)) in *.
      destruct IH as [IHlo IHhi].
      destruct Hb as [Hblo Hbhi].
      split.
      + nia.
      + assert (Hb_le : b mod 256 <= 255) by lia.
        assert (IH_le : n_bytes_to_Z n v <= q - 1) by lia.
        replace (256 * q) with (255 + 256 * (q - 1) + 1) by ring.
        nia.
  Qed.

  Lemma merge_n_bytes_self n (v : Vector.t byte n) :
    merge_n_bytes n v (n_bytes_to_Z n v).
  Proof.
    unfold merge_n_bytes.
    rewrite Z.mod_small; [reflexivity | apply n_bytes_to_Z_range].
  Qed.

  Lemma merge_byte_equiv_merge_n_bytes x y :
    Byte.eqm x y <-> merge_n_bytes 1 [x]%vector y.
  Proof.
    unfold merge_n_bytes. cbn. rewrite Z.add_0_r.
    split; intros H.
    - assert (Hmod : x mod 256 = y mod 256).
      { change 256 with Byte.modulus. apply Byte.eqm_mod_eq. exact H. }
      rewrite Hmod. reflexivity.
    - unfold Byte.eqm. apply Zbits.eqmod_trans with (x mod 256).
      + apply Zbits.eqmod_mod.
      + apply Zbits.eqmod_trans with (y mod 256).
        * apply Zbits.eqmod_refl2. symmetry; auto.
        * apply Zbits.eqmod_sym. apply Zbits.eqmod_mod.
  Qed.

  Lemma merge_short_equiv_merge_n_bytes x1 x2 y :
    merge_short x1 x2 y <-> merge_n_bytes 2 [x1; x2]%vector y.
  Proof.
    unfold merge_short, merge_n_bytes. cbn -[Z.mul Z.add Z.pow].
    replace (2 ^ (8 * 2)) with (2 ^ 16) by reflexivity.
    replace (x1 mod 2 ^ 8 + 2 ^ 8 * (x2 mod 2 ^ 8 + 2 ^ 8 * 0))
      with (x1 mod 2 ^ 8 + x2 mod 2 ^ 8 * 2 ^ 8) by ring.
    reflexivity.
  Qed.

  Lemma merge_int_equiv_merge_n_bytes x1 x2 x3 x4 y :
    merge_int x1 x2 x3 x4 y <-> merge_n_bytes 4 [x1; x2; x3; x4]%vector y.
  Proof.
    unfold merge_int, merge_n_bytes. cbn -[Z.mul Z.add Z.pow].
    replace (2 ^ (8 * 4)) with (2 ^ 32) by reflexivity.
    replace
      (x1 mod 2 ^ 8 +
       2 ^ 8 *
         (x2 mod 2 ^ 8 +
          2 ^ 8 * (x3 mod 2 ^ 8 + 2 ^ 8 * (x4 mod 2 ^ 8 + 2 ^ 8 * 0))))
      with
      (x1 mod 2 ^ 8 +
       x2 mod 2 ^ 8 * 2 ^ 8 +
       x3 mod 2 ^ 8 * 2 ^ 16 +
       x4 mod 2 ^ 8 * 2 ^ 24) by ring.
    reflexivity.
  Qed.

  Lemma merge_int64_equiv_merge_n_bytes x1 x2 x3 x4 x5 x6 x7 x8 y :
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 y <->
    merge_n_bytes 8 [x1; x2; x3; x4; x5; x6; x7; x8]%vector y.
  Proof.
    unfold merge_int64, merge_n_bytes. cbn -[Z.mul Z.add Z.pow].
    replace (2 ^ (8 * 8)) with (2 ^ 64) by reflexivity.
    replace
      (x1 mod 2 ^ 8 +
       2 ^ 8 *
         (x2 mod 2 ^ 8 +
          2 ^ 8 *
            (x3 mod 2 ^ 8 +
             2 ^ 8 *
               (x4 mod 2 ^ 8 +
                2 ^ 8 *
                  (x5 mod 2 ^ 8 +
                   2 ^ 8 *
                     (x6 mod 2 ^ 8 +
                      2 ^ 8 * (x7 mod 2 ^ 8 + 2 ^ 8 * (x8 mod 2 ^ 8 + 2 ^ 8 * 0))))))))
      with
      (x1 mod 2 ^ 8 +
       x2 mod 2 ^ 8 * 2 ^ 8 +
       x3 mod 2 ^ 8 * 2 ^ 16 +
       x4 mod 2 ^ 8 * 2 ^ 24 +
       x5 mod 2 ^ 8 * 2 ^ 32 +
       x6 mod 2 ^ 8 * 2 ^ 40 +
       x7 mod 2 ^ 8 * 2 ^ 48 +
       x8 mod 2 ^ 8 * 2 ^ 56) by ring.
    reflexivity.
  Qed.

  Lemma merge_short_eqm x1 x2 y1 y2 v :
    Byte.eqm x1 y1 -> Byte.eqm x2 y2 ->
    merge_short x1 x2 v -> merge_short y1 y2 v.
  Proof.
    intros H1 H2 H.
    assert (Hmod1 : x1 mod 2^8 = y1 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H1).
    assert (Hmod2 : x2 mod 2^8 = y2 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H2).
    unfold merge_short in *.
    rewrite <- Hmod1, <- Hmod2.
    exact H.
  Qed.

  Lemma merge_int_eqm x1 x2 x3 x4 y1 y2 y3 y4 v :
    Byte.eqm x1 y1 -> Byte.eqm x2 y2 -> Byte.eqm x3 y3 -> Byte.eqm x4 y4 ->
    merge_int x1 x2 x3 x4 v -> merge_int y1 y2 y3 y4 v.
  Proof.
    intros H1 H2 H3 H4 H.
    assert (Hmod1 : x1 mod 2^8 = y1 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H1).
    assert (Hmod2 : x2 mod 2^8 = y2 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H2).
    assert (Hmod3 : x3 mod 2^8 = y3 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H3).
    assert (Hmod4 : x4 mod 2^8 = y4 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H4).
    unfold merge_int in *.
    rewrite <- Hmod1, <- Hmod2, <- Hmod3, <- Hmod4.
    exact H.
  Qed.

  Lemma merge_int64_eqm x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 y6 y7 y8 v :
    Byte.eqm x1 y1 -> Byte.eqm x2 y2 -> Byte.eqm x3 y3 -> Byte.eqm x4 y4 ->
    Byte.eqm x5 y5 -> Byte.eqm x6 y6 -> Byte.eqm x7 y7 -> Byte.eqm x8 y8 ->
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v ->
    merge_int64 y1 y2 y3 y4 y5 y6 y7 y8 v.
  Proof.
    intros H1 H2 H3 H4 H5 H6 H7 H8 H.
    assert (Hmod1 : x1 mod 2^8 = y1 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H1).
    assert (Hmod2 : x2 mod 2^8 = y2 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H2).
    assert (Hmod3 : x3 mod 2^8 = y3 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H3).
    assert (Hmod4 : x4 mod 2^8 = y4 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H4).
    assert (Hmod5 : x5 mod 2^8 = y5 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H5).
    assert (Hmod6 : x6 mod 2^8 = y6 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H6).
    assert (Hmod7 : x7 mod 2^8 = y7 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H7).
    assert (Hmod8 : x8 mod 2^8 = y8 mod 2^8) by (change (2^8) with Byte.modulus; apply Byte.eqm_mod_eq; exact H8).
    unfold merge_int64 in *.
    rewrite <- Hmod1, <- Hmod2, <- Hmod3, <- Hmod4.
    rewrite <- Hmod5, <- Hmod6, <- Hmod7, <- Hmod8.
    exact H.
  Qed.

  Lemma merge_short_value_eqm x1 x2 v v' :
    v mod 2^16 = v' mod 2^16 ->
    merge_short x1 x2 v -> merge_short x1 x2 v'.
  Proof.
    unfold merge_short.
    intros Hmod H. rewrite <- Hmod. exact H.
  Qed.

  Lemma merge_int_value_eqm x1 x2 x3 x4 v v' :
    v mod 2^32 = v' mod 2^32 ->
    merge_int x1 x2 x3 x4 v -> merge_int x1 x2 x3 x4 v'.
  Proof.
    unfold merge_int.
    intros Hmod H. rewrite <- Hmod. exact H.
  Qed.

  Lemma merge_int64_value_eqm x1 x2 x3 x4 x5 x6 x7 x8 v v' :
    v mod 2^64 = v' mod 2^64 ->
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v ->
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v'.
  Proof.
    unfold merge_int64.
    intros Hmod H. rewrite <- Hmod. exact H.
  Qed.
End LittleEndian.
