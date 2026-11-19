From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.Verification Require Import VCPrelude.
Require Export SimpleC.EE.stdlib.glibc.memmove_model.
Import Snaive_C_Rules64.
Local Open Scope Z_scope.
Local Open Scope sac.

(** Internal representation only. Public contracts use ordinary byte arrays. *)
Definition mm_cells (base len : Z) (m : mm_memory) : list (option Z) :=
  map (fun k => m (base + Z.of_nat k)) (seq 0 (Z.to_nat len)).
Definition mm_lookup (m : mm_memory) (p : Z) := m p.
Definition mm_in (p b1 n1 b2 n2 : Z) :=
  b1 <= p < b1+n1 \/ b2 <= p < b2+n2.
Definition mm_separated (b1 n1 b2 n2 : Z) :=
  b1+n1 <= b2 \/ b2+n2 <= b1 \/ n1 = 0 \/ n2 = 0.
Definition mm_initialized (m : mm_memory) (p : Z) := exists v, m p = Some v.
Definition mm_access (m : mm_memory) (s d n b1 n1 b2 n2 : Z) :=
  forall i, 0 <= i < n ->
    mm_in (s+i) b1 n1 b2 n2 /\ mm_in (d+i) b1 n1 b2 n2 /\
    mm_initialized m (s+i).

Lemma mm_cells_length : forall b n m, 0 <= n -> Zlength (mm_cells b n m) = n.
Proof.
 intros; unfold mm_cells. rewrite Zlength_correct, map_length, seq_length, Z2Nat.id by lia.
 reflexivity.
Qed.

Lemma mm_cells_empty : forall b m, mm_cells b 0 m = nil.
Proof. reflexivity. Qed.

Lemma mm_cells_nth : forall b n m i, 0 <= i < n ->
 Znth i (mm_cells b n m) None = m (b+i).
Proof.
 intros; unfold mm_cells, Znth.
 rewrite (map_nth_len _ _ _ _ _ None O) by (rewrite seq_length; lia).
 rewrite seq_nth by lia. cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma mm_cells_write_inside : forall b n m p v, b <= p < b+n ->
 mm_cells b n (mm_write m p v) = replace_Znth (p-b) v (mm_cells b n m).
Proof.
 intros. apply (proj2 (list_eq_ext _ _ None)); split.
 - rewrite Zlength_replace_Znth, !mm_cells_length by lia. reflexivity.
 - intros i Hi. rewrite mm_cells_length in Hi by lia.
   rewrite mm_cells_nth by lia. unfold mm_write.
   destruct (Z.eq_dec (b+i) p).
   + replace i with (p-b) by lia. rewrite Znth_replace_Znth_Same by (rewrite mm_cells_length by lia; lia). reflexivity.
   + rewrite Znth_replace_Znth_Diff by (try rewrite mm_cells_length by lia; lia).
     symmetry; apply mm_cells_nth; lia.
Qed.

Lemma mm_cells_write_outside : forall b n m p v, 0 <= n ->
 (p < b \/ b+n <= p) -> mm_cells b n (mm_write m p v) = mm_cells b n m.
Proof.
 intros. apply (proj2 (list_eq_ext _ _ None)); split.
 - rewrite !mm_cells_length by lia. reflexivity.
 - intros i Hi. rewrite mm_cells_length in Hi by lia.
   rewrite !mm_cells_nth by lia. unfold mm_write.
   destruct (Z.eq_dec (b+i) p); [lia|reflexivity].
Qed.

Lemma mm_mixed_view : forall b n m p,
 UCharArray.mixed_seg p (b-p) (b+n-p) (mm_cells b n m) --||--
 UCharArray.mixed_full b n (mm_cells b n m).
Proof.
 intros. rewrite UCharArray.mixed_seg_0_shift.
 unfold StoreUCharAsElement.sizeA. rewrite sizeof_uchar.
 replace (p+(b-p)*1) with b by ring.
 replace (b+n-p-(b-p)) with n by ring.
 unfold UCharArray.mixed_seg, UCharArray.mixed_full, store_array. reflexivity.
Qed.

Lemma mm_extract_byte : forall b n m p v,
 b <= p < b+n -> m p = Some v ->
 UCharArray.mixed_full b n (mm_cells b n m) |--
 (p # UChar |-> v) **
 UCharArray.mixed_missing_i p 0 (b-p) (b+n-p) (mm_cells b n m).
Proof.
 intros b n m p v Hp Hv. rewrite <- (mm_mixed_view b n m p).
 sep_apply (UCharArray.mixed_seg_split_to_mixed_missing_i p (b-p) 0 (b+n-p) (mm_cells b n m) None); [|lia].
 replace (0-(b-p)) with (p-b) by ring.
 rewrite mm_cells_nth by lia. replace (b+(p-b)) with p by ring.
 rewrite Hv. cbn [UCharArray.mixedstoreA StoreUCharAsElement.storeA].
 rewrite Z.mul_0_l, Z.add_0_r. entailer!.
Qed.

Lemma mm_extract_writable : forall b n m p,
 b <= p < b+n ->
 UCharArray.mixed_full b n (mm_cells b n m) |--
 (p # UChar |->_) **
 UCharArray.mixed_missing_i p 0 (b-p) (b+n-p) (mm_cells b n m).
Proof.
 intros. rewrite <- (mm_mixed_view b n m p).
 sep_apply (UCharArray.mixed_seg_split_to_mixed_missing_i p (b-p) 0 (b+n-p) (mm_cells b n m) None); [|lia].
 sep_apply UCharArray.mixedstoreA_to_undefstoreA.
 cbn [StoreUCharAsElement.undefstoreA].
 rewrite Z.mul_0_l, Z.add_0_r. entailer!.
Qed.

Lemma mm_restore_written : forall b n m p v,
 b <= p < b+n ->
 (p # UChar |-> v) **
 UCharArray.mixed_missing_i p 0 (b-p) (b+n-p) (mm_cells b n m) |--
 UCharArray.mixed_full b n (mm_cells b n (mm_write m p (Some v))).
Proof.
 intros. rewrite mm_cells_write_inside by lia.
 rewrite <- (Z.add_0_r p) at 1.
 change (p+0) with (p+0*sizeof(UCHAR)).
 change ((p+0*sizeof(UCHAR)) # UChar |-> v)
   with (UCharArray.mixedstoreA p 0 (Some v)).
 sep_apply (UCharArray.mixed_missing_i_merge_to_mixed_seg p (b-p) 0 (b+n-p) (Some v) (mm_cells b n m)); [|lia].
 replace (0-(b-p)) with (p-b) by ring.
 rewrite <- mm_cells_write_inside by lia.
 rewrite mm_mixed_view. reflexivity.
Qed.

Lemma mm_write_same : forall m p v, m p = v -> mm_write m p v = m.
Proof.
 intros; apply functional_extensionality; intro a; unfold mm_write.
 destruct (Z.eq_dec a p); subst; auto.
Qed.

Lemma mm_restore_byte : forall b n m p v,
 b <= p < b+n -> m p = Some v ->
 (p # UChar |-> v) **
 UCharArray.mixed_missing_i p 0 (b-p) (b+n-p) (mm_cells b n m) |--
 UCharArray.mixed_full b n (mm_cells b n m).
Proof.
 intros. sep_apply (mm_restore_written b n m p v); [|lia].
 rewrite mm_write_same by assumption. reflexivity.
Qed.
