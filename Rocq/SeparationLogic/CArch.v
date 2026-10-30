Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Set Warnings "-warn-library-file-stdlib-vector".
Require Coq.Vectors.Vector.
From compcert.lib Require Import Coqlib Integers.

Local Open Scope Z_scope.

(* The architecture implementation supplies layout constants and basic laws. *)
Module Type CArchSig.
  Parameter ptr_size : nat.
  Parameter ptr_align : Z.
  Parameter addr_max_unsigned : Z.
  Axiom ptr_size_pos : 0 < Z.of_nat ptr_size.
  Axiom ptr_align_power_two : exists k : nat, ptr_align = 2 ^ Z.of_nat k.
  (* These bounds belong to our flat unsigned-address model, not to ISO C. *)
  Axiom addr_max_unsigned_nonneg : 0 <= addr_max_unsigned.
  Axiom addr_max_unsigned_fits_ptr :
    addr_max_unsigned < 2 ^ (8 * Z.of_nat ptr_size).
End CArchSig.

(* Shared definitions and consequences of the architecture laws. *)
Module CArch (Impl : CArchSig).
  Include Impl.
  Definition ptr_size_Z : Z := Z.of_nat ptr_size.
  Definition ptr_width_Z : Z := 8 * ptr_size_Z.
  Definition aligned (align p : Z) : Prop := p mod align = 0.
  Definition valid_addr_range (p len : Z) : Prop :=
    0 <= p /\ 0 <= len /\ p + len - 1 <= addr_max_unsigned.
  Definition valid_object (p len align : Z) : Prop :=
    valid_addr_range p len /\ aligned align p.
  Definition valid_ptr_value (v : Z) : Prop :=
    0 <= v /\ v <= addr_max_unsigned.

  Lemma ptr_align_pos : 0 < ptr_align.
  Proof.
    destruct ptr_align_power_two as [k H]. rewrite H.
    apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma valid_ptr_value_range : forall v,
    valid_ptr_value v -> 0 <= v < 2 ^ ptr_width_Z.
  Proof.
    unfold valid_ptr_value, ptr_width_Z, ptr_size_Z.
    intros v [Hlo Hhi]. pose proof addr_max_unsigned_fits_ptr as Hbound. lia.
  Qed.

  Lemma aligned_weaken : forall a b p,
    0 < a -> 0 < b -> (a | b) -> aligned b p -> aligned a p.
  Proof.
    unfold aligned. intros a b p Ha Hb Hdiv Halign.
    apply Z.mod_divide; [lia|].
    apply Z.mod_divide in Halign; [|lia].
    eapply Z.divide_trans; eauto.
  Qed.
End CArch.

Module Arch32Impl <: CArchSig.
  Definition ptr_size : nat := 4%nat.
  Definition ptr_align : Z := 4.
  Definition addr_max_unsigned : Z := Int.max_unsigned.
  Lemma ptr_size_pos : 0 < Z.of_nat ptr_size.
  Proof. compute; auto. Qed.
  Lemma ptr_align_power_two : exists k : nat, ptr_align = 2 ^ Z.of_nat k.
  Proof. exists 2%nat. reflexivity. Qed.
  Lemma addr_max_unsigned_nonneg : 0 <= addr_max_unsigned.
  Proof. change (0 <= 4294967295). lia. Qed.
  Lemma addr_max_unsigned_fits_ptr :
    addr_max_unsigned < 2 ^ (8 * Z.of_nat ptr_size).
  Proof. change (4294967295 < 4294967296). lia. Qed.
End Arch32Impl.

Module Arch32 := CArch Arch32Impl.

Module Arch64Impl <: CArchSig.
  Definition ptr_size : nat := 8%nat.
  Definition ptr_align : Z := 8.
  Definition addr_max_unsigned : Z := Int64.max_unsigned.
  Lemma ptr_size_pos : 0 < Z.of_nat ptr_size.
  Proof. compute; auto. Qed.
  Lemma ptr_align_power_two : exists k : nat, ptr_align = 2 ^ Z.of_nat k.
  Proof. exists 3%nat. reflexivity. Qed.
  Lemma addr_max_unsigned_nonneg : 0 <= addr_max_unsigned.
  Proof. change (0 <= 18446744073709551615). lia. Qed.
  Lemma addr_max_unsigned_fits_ptr :
    addr_max_unsigned < 2 ^ (8 * Z.of_nat ptr_size).
  Proof. change (18446744073709551615 < 18446744073709551616). lia. Qed.
End Arch64Impl.

Module Arch64 := CArch Arch64Impl.

  Fixpoint byte_vector_eqm (n : nat) : forall (v1 v2 : Vector.t Z n), Prop :=
    match n with
    | O => fun _ _ => True
    | S n => fun v1 v2 =>
        Vector.caseS' v1 (fun _ => Prop) (fun hd1 tl1 =>
          Vector.caseS' v2 (fun _ => Prop) (fun hd2 tl2 =>
            Byte.eqm hd1 hd2 /\ byte_vector_eqm n tl1 tl2))
    end.


(* Implementations provide only encoding operations and their basic laws. *)
Module Type CEndianSig.
  Parameter n_bytes_to_Z : forall n : nat, Vector.t Z n -> Z.
  Parameter Z_to_n_bytes : Z -> forall length : nat, Vector.t Z length.
  Axiom eqm_bytes_to_Z_eq :
    forall n (v1 v2 : Vector.t Z n),
      byte_vector_eqm n v1 v2 -> n_bytes_to_Z n v1 = n_bytes_to_Z n v2.
  Axiom Z_to_n_bytes_to_Z :
    forall length v,
      n_bytes_to_Z length (Z_to_n_bytes v length) =
      v mod (2 ^ (8 * Z.of_nat length)).
  Axiom n_bytes_to_Z_single : forall x,
    n_bytes_to_Z 1 (Vector.cons Z x 0 (Vector.nil Z)) = x mod 2^8.
  Arguments n_bytes_to_Z {n} _.
End CEndianSig.

(* The public interface adds shared definitions and proved consequences. *)
Module CEndian (Impl : CEndianSig).
  Include Impl.
  Definition bytes_eqm := byte_vector_eqm.
  Definition merge_n_bytes n (bytes : Vector.t Z n) (v : Z) : Prop :=
    v mod (2 ^ (8 * Z.of_nat n)) = n_bytes_to_Z bytes.
  Arguments bytes_eqm {n} _ _.
  Arguments merge_n_bytes {n} _ _.

  Lemma merge_n_bytes_eqm : forall n (v1 v2 : Vector.t Z n) x,
    bytes_eqm v1 v2 -> merge_n_bytes v1 x -> merge_n_bytes v2 x.
  Proof.
    unfold merge_n_bytes, bytes_eqm.
    intros n v1 v2 x Heqm Hmerge.
    rewrite <- (eqm_bytes_to_Z_eq n v1 v2 Heqm). exact Hmerge.
  Qed.

  Lemma merge_n_bytes_value_eqm : forall n (bytes : Vector.t Z n) v v',
    v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) ->
    merge_n_bytes bytes v -> merge_n_bytes bytes v'.
  Proof.
    unfold merge_n_bytes.
    intros n bytes v v' Hmod Hmerge. rewrite <- Hmod. exact Hmerge.
  Qed.

  (* Finite byte classes let the round-trip law determine the decoder range. *)
  Local Fixpoint byte_vectors (n : nat) : list (Vector.t Z n) :=
    match n with
    | O => (Vector.nil Z :: nil)%list
    | S k => List.flat_map
        (fun b => List.map (Vector.cons Z (Z.of_nat b) k) (byte_vectors k))
        (List.seq 0 256)
    end.

  Local Lemma byte_vectors_cover n (bytes : Vector.t Z n) :
    exists canon, List.In canon (byte_vectors n) /\ byte_vector_eqm n bytes canon.
  Proof.
    induction bytes as [|b n bytes IH].
    - exists (Vector.nil Z). split; [left; reflexivity|exact I].
    - destruct IH as [canon [Hin Heqm]].
      exists (Vector.cons Z (b mod 256) n canon). split.
      + cbn [byte_vectors]. apply List.in_flat_map.
        exists (Z.to_nat (b mod 256)). split.
        * apply List.in_seq. pose proof (Z.mod_pos_bound b 256 ltac:(lia)). lia.
        * apply List.in_map_iff. exists canon. split; [|exact Hin].
          rewrite Z2Nat.id by (pose proof (Z.mod_pos_bound b 256 ltac:(lia)); lia).
          reflexivity.
      + cbn [byte_vector_eqm]. split; [|exact Heqm].
        unfold Byte.eqm. apply Zbits.eqmod_mod.
  Qed.

  Local Lemma byte_vectors_length n :
    List.length (byte_vectors n) = Z.to_nat (2 ^ (8 * Z.of_nat n)).
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - cbn [byte_vectors].
      rewrite List.flat_map_constant_length with (c := List.length (byte_vectors n)).
      2:{ intros b _. apply List.length_map. }
      rewrite List.length_seq, IH.
      replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 8) with 256.
      rewrite Z2Nat.inj_mul by (try apply Z.pow_nonneg; lia).
      reflexivity.
  Qed.

  Local Lemma residue_list_nodup n :
    List.NoDup (List.map Z.of_nat (List.seq 0 n)).
  Proof.
    assert (H : forall l : list nat, List.NoDup l -> List.NoDup (List.map Z.of_nat l)).
    {
      intros l H. induction H as [|x l Hnot Hdup IH]; cbn.
      - constructor.
      - constructor; [|exact IH]. intro Hin.
        apply List.in_map_iff in Hin. destruct Hin as [y [Heq Hin]].
        apply Nat2Z.inj in Heq. subst y. contradiction.
    }
    apply H. apply List.seq_NoDup.
  Qed.

  Lemma n_bytes_to_Z_range : forall n (bytes : Vector.t Z n),
    0 <= n_bytes_to_Z bytes < 2 ^ (8 * Z.of_nat n).
  Proof.
    intros n bytes.
    set (modulus := 2 ^ (8 * Z.of_nat n)).
    assert (Hpos : 0 < modulus) by (unfold modulus; apply Z.pow_pos_nonneg; lia).
    set (residues := List.map Z.of_nat (List.seq 0 (Z.to_nat modulus))).
    set (decoded := List.map (@n_bytes_to_Z n) (byte_vectors n)).
    assert (Hcover : List.incl residues decoded).
    {
      intros r Hr. unfold residues in Hr.
      apply List.in_map_iff in Hr. destruct Hr as [k [<- Hk]].
      apply List.in_seq in Hk.
      destruct (byte_vectors_cover n (Z_to_n_bytes (Z.of_nat k) n))
        as [canon [Hin Heqm]].
      unfold decoded. apply List.in_map_iff. exists canon. split; [|exact Hin].
      rewrite <- (eqm_bytes_to_Z_eq n _ _ Heqm), Z_to_n_bytes_to_Z.
      apply Z.mod_small. unfold modulus in *. lia.
    }
    assert (Hreverse : List.incl decoded residues).
    {
      apply List.NoDup_length_incl.
      - apply residue_list_nodup.
      - unfold decoded, residues. rewrite !List.length_map, List.length_seq,
          byte_vectors_length. unfold modulus. lia.
      - exact Hcover.
    }
    destruct (byte_vectors_cover n bytes) as [canon [Hin Heqm]].
    assert (Hin_decoded : List.In (n_bytes_to_Z bytes) decoded).
    {
      unfold decoded. apply List.in_map_iff. exists canon. split; [|exact Hin].
      symmetry. apply eqm_bytes_to_Z_eq. exact Heqm.
    }
    specialize (Hreverse _ Hin_decoded). unfold residues in Hreverse.
    apply List.in_map_iff in Hreverse. destruct Hreverse as [k [Heq Hk]].
    apply List.in_seq in Hk. rewrite <- Heq. unfold modulus in *. lia.
  Qed.

  Lemma merge_n_bytes_self : forall n (bytes : Vector.t Z n),
    merge_n_bytes bytes (n_bytes_to_Z bytes).
  Proof.
    unfold merge_n_bytes. intros n bytes.
    apply Z.mod_small. apply n_bytes_to_Z_range.
  Qed.

  Lemma merge_byte_equiv_merge_n_bytes : forall x y,
    Byte.eqm x y <-> merge_n_bytes (Vector.cons Z x 0 (Vector.nil Z)) y.
  Proof.
    intros x y. unfold merge_n_bytes. rewrite n_bytes_to_Z_single.
    change (Byte.eqm x y <-> y mod 256 = x mod 256).
    split; intros H.
    - symmetry. change 256 with Byte.modulus. apply Byte.eqm_mod_eq. exact H.
    - unfold Byte.eqm. apply Zbits.eqmod_trans with (x mod 256).
      + apply Zbits.eqmod_mod.
      + apply Zbits.eqmod_trans with (y mod 256).
        * apply Zbits.eqmod_refl2. symmetry; exact H.
        * apply Zbits.eqmod_sym. apply Zbits.eqmod_mod.
  Qed.
End CEndian.

Module BigEndianImpl <: CEndianSig.
  Import Vector.VectorNotations.
  Notation byte := Z (only parsing).

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

  Lemma eqm_bytes_to_Z_eq n v1 v2 :
    byte_vector_eqm n v1 v2 -> n_bytes_to_Z n v1 = n_bytes_to_Z n v2.
  Proof.
    induction n.
    - revert v1. refine (Vector.case0 _ _).
      revert v2. refine (Vector.case0 _ _).
      cbn. reflexivity.
    - apply (Vector.caseS' v1). clear v1. intros hd1 tl1.
      apply (Vector.caseS' v2). clear v2. intros hd2 tl2.
      simpl (byte_vector_eqm _ _). cbn. intros [Hhd H].
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


  Lemma n_bytes_to_Z_single x :
    n_bytes_to_Z 1 [x]%vector = x mod 2^8.
  Proof. cbn. ring. Qed.

  Arguments n_bytes_to_Z {n} _.
End BigEndianImpl.

Module BigEndian := CEndian BigEndianImpl.

Module LittleEndianImpl <: CEndianSig.
  Import Vector.VectorNotations.
  Notation byte := Z (only parsing).

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

  Lemma n_bytes_to_Z_cons b n v :
    n_bytes_to_Z (S n) (b :: v)%vector =
    b mod 2^8 + 2^8 * n_bytes_to_Z n v.
  Proof. reflexivity. Qed.

  Lemma eqm_bytes_to_Z_eq n v1 v2 :
    byte_vector_eqm n v1 v2 -> n_bytes_to_Z n v1 = n_bytes_to_Z n v2.
  Proof.
    induction n.
    - revert v1. refine (Vector.case0 _ _).
      revert v2. refine (Vector.case0 _ _).
      cbn. reflexivity.
    - apply (Vector.caseS' v1). clear v1. intros hd1 tl1.
      apply (Vector.caseS' v2). clear v2. intros hd2 tl2.
      simpl (byte_vector_eqm _ _). cbn. intros [Hhd H].
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


  Lemma n_bytes_to_Z_single x :
    n_bytes_to_Z 1 [x]%vector = x mod 2^8.
  Proof. cbn. ring. Qed.

  Arguments n_bytes_to_Z {n} _.
End LittleEndianImpl.

Module LittleEndian := CEndian LittleEndianImpl.
