From SimpleC.Verification Require Import VCPrelude.
Require Export SimpleC.EE.stdlib.glibc.memmove_lib.
Import Snaive_C_Rules64.
Local Open Scope Z_scope.
Local Open Scope sac.

Definition mm_initial (s : Z) (xs : list Z) : mm_memory := fun a =>
 if andb (s <=? a) (a <? s + Zlength xs) then Some (Znth (a-s) xs 0) else None.

Lemma mm_initial_inside : forall s xs i, 0 <= i < Zlength xs ->
 mm_initial s xs (s+i) = Some (Znth i xs 0).
Proof.
 intros; unfold mm_initial.
 destruct (s <=? s+i) eqn:E; destruct (s+i <? s+Zlength xs) eqn:F; cbn;
 try (apply Z.leb_gt in E); try (apply Z.ltb_ge in F); try lia.
 f_equal; f_equal; lia.
Qed.

Lemma mm_initial_outside : forall s xs a, a<s \/ s+Zlength xs<=a ->
 mm_initial s xs a=None.
Proof.
 intros; unfold mm_initial.
 destruct (s<=?a) eqn:E; destruct (a<?s+Zlength xs) eqn:F; cbn; auto.
 apply Z.leb_le in E; apply Z.ltb_lt in F; lia.
Qed.

Lemma mm_cells_some : forall b n m xs, 0<=n -> Zlength xs=n ->
 (forall i,0<=i<n -> m(b+i)=Some(Znth i xs 0)) ->
 mm_cells b n m=map Some xs.
Proof.
 intros b n m xs Hn Hlen Hm. apply (proj2 (list_eq_ext _ _ None)); split.
 - rewrite mm_cells_length, Zlength_map by lia; lia.
 - intros i Hi. rewrite mm_cells_length in Hi by lia.
   rewrite mm_cells_nth, (Znth_map _ _ _ 0) by lia. apply Hm; lia.
Qed.

Lemma mm_cells_none : forall b n m, 0<=n ->
 (forall i,0<=i<n -> m(b+i)=None) ->
 mm_cells b n m=repeat None (Z.to_nat n).
Proof.
 intros b n m Hn Hm. apply (proj2 (list_eq_ext _ _ None)); split.
 - rewrite mm_cells_length, Zlength_correct, repeat_length, Z2Nat.id by lia; reflexivity.
 - intros i Hi. rewrite mm_cells_length in Hi by lia.
   rewrite mm_cells_nth by lia. rewrite Hm by lia.
   unfold Znth. rewrite nth_repeat. reflexivity.
Qed.

Lemma mm_cells_slice : forall b n m lo hi, 0<=lo<=hi -> hi<=n ->
 sublist lo hi (mm_cells b n m)=mm_cells (b+lo) (hi-lo) m.
Proof.
 intros. apply (proj2 (list_eq_ext _ _ None)); split.
 - rewrite Zlength_sublist by (rewrite mm_cells_length by lia; lia). rewrite !mm_cells_length by lia; reflexivity.
 - intros i Hi. rewrite Zlength_sublist in Hi by (rewrite mm_cells_length by lia; lia).
   rewrite Znth_sublist, !mm_cells_nth by lia. f_equal; lia.
Qed.

Lemma mm_heap_split : forall b n k m, 0<=k<=n ->
 UCharArray.mixed_full b n (mm_cells b n m) |--
 UCharArray.mixed_full b k (mm_cells b k m) **
 UCharArray.mixed_full (b+k) (n-k) (mm_cells (b+k) (n-k) m).
Proof.
 intros. sep_apply (UCharArray.mixed_full_split_to_mixed_full b k n (mm_cells b n m) H).
 rewrite !mm_cells_slice by lia. rewrite sizeof_uchar, Z.mul_1_r, Z.add_0_r, Z.sub_0_r.
 reflexivity.
Qed.

Lemma mm_heap_merge : forall b n k m, 0<=k<=n ->
 UCharArray.mixed_full b k (mm_cells b k m) **
 UCharArray.mixed_full (b+k) (n-k) (mm_cells (b+k) (n-k) m) |--
 UCharArray.mixed_full b n (mm_cells b n m).
Proof.
 intros. replace (b+k) with (b+k*sizeof(UCHAR)) at 1 by (rewrite sizeof_uchar; ring).
 sep_apply (UCharArray.mixed_full_merge_to_mixed_full b k n (mm_cells b k m) (mm_cells (b+k) (n-k) m) H).
 rewrite <- (mm_cells_slice b n m k n) by lia.
 replace (mm_cells b k m) with (sublist 0 k (mm_cells b n m))
   by (rewrite mm_cells_slice by lia; rewrite Z.add_0_r, Z.sub_0_r; reflexivity).
 rewrite <- sublist_split by (try rewrite mm_cells_length by lia; lia).
 rewrite sublist_self by (rewrite mm_cells_length by lia; lia). reflexivity.
Qed.

Lemma mm_heap_initial : forall s n xs, 0<=n -> Zlength xs=n ->
 UCharArray.full s n xs |-- UCharArray.mixed_full s n (mm_cells s n (mm_initial s xs)).
Proof.
 intros. rewrite (mm_cells_some s n _ xs) by (auto; intros; apply mm_initial_inside; lia).
 apply UCharArray.full_to_mixed_full.
Qed.

Lemma mm_heap_undef : forall s xs b n, 0<=n -> (b+n<=s \/ s+Zlength xs<=b) ->
 UCharArray.undef_full b n |-- UCharArray.mixed_full b n (mm_cells b n (mm_initial s xs)).
Proof.
 intros. rewrite mm_cells_none by (auto; intros; apply mm_initial_outside; lia).
 apply UCharArray.undef_full_to_mixed_full.
Qed.

Lemma mm_heap_values : forall b n m xs, 0<=n -> Zlength xs=n ->
 (forall i,0<=i<n -> m(b+i)=Some(Znth i xs 0)) ->
 UCharArray.mixed_full b n (mm_cells b n m) |-- UCharArray.full b n xs.
Proof. intros. rewrite (mm_cells_some b n m xs) by auto. apply UCharArray.mixed_full_to_full. Qed.

Lemma mm_snapshot_target : forall s d n xs, Zlength xs=n -> 0<=n ->
 UCharArray.mixed_full d n (mm_cells d n (mm_snapshot (mm_initial s xs) s d n)) |--
 UCharArray.full d n xs.
Proof.
 intros. apply mm_heap_values; auto. intros.
 rewrite mm_snapshot_inside by lia. replace (s+(d+i)-d) with (s+i) by ring.
 apply mm_initial_inside; lia.
Qed.

Lemma mm_snapshot_source_slice : forall s d n xs lo hi, Zlength xs=n ->
 0<=lo<=hi -> hi<=n -> (s+hi<=d \/ d+n<=s+lo) ->
 UCharArray.mixed_full (s+lo) (hi-lo) (mm_cells (s+lo) (hi-lo) (mm_snapshot (mm_initial s xs) s d n)) |--
 UCharArray.full (s+lo) (hi-lo) (sublist lo hi xs).
Proof.
 intros. apply mm_heap_values; try (rewrite Zlength_sublist by lia; lia); try lia.
 intros. rewrite mm_snapshot_outside by lia.
 replace (s+lo+i) with (s+(i+lo)) by ring.
 rewrite mm_initial_inside, Znth_sublist by lia. reflexivity.
Qed.

Lemma mm_undef_disjoint : forall s d n,
 UCharArray.undef_full s n ** UCharArray.undef_full d n |--
 “ mm_separated s n d n ”.
Proof.
 intros. destruct (Z_le_dec (s+n) d); [unfold mm_separated; entailer!|].
 destruct (Z_le_dec (d+n) s); [unfold mm_separated; entailer!|].
 destruct (Z.eq_dec n 0); [unfold mm_separated; entailer!|].

 assert (Hp : 0<=Z.max s d-s<n /\ 0<=Z.max s d-d<n) by (split; split; lia).
 sep_apply (UCharArray.undef_full_split_to_undef_missing_i s (Z.max s d-s) n ltac:(lia)).
 sep_apply (UCharArray.undef_full_split_to_undef_missing_i d (Z.max s d-d) n ltac:(lia)).
 cbn [StoreUCharAsElement.undefstoreA]. rewrite !sizeof_uchar, !Z.mul_1_r.
 replace (s+(Z.max s d-s)) with (Z.max s d) by ring.
 replace (d+(Z.max s d-d)) with (Z.max s d) by ring.
 unfold undef_store_uchar. sep_apply (undef_store_int_exclusive 1%nat 1 (Z.max s d) ltac:(lia)).
 entailer!.
Qed.

Lemma mm_full_disjoint : forall s d n xs,
 UCharArray.full s n xs ** UCharArray.undef_full d n |--
 “ mm_separated s n d n ” && (UCharArray.full s n xs ** UCharArray.undef_full d n).
Proof.
 intros. apply derivable1s_andp_intros; [|reflexivity].
 sep_apply UCharArray.full_to_undef_full. apply mm_undef_disjoint.
Qed.

Definition mm_forward_ok (s d n : Z) := d<=s \/ s+n<=d.
Lemma mm_direction_forward : forall s d n,
 0<=s -> s+n<=18446744073709551615 -> 0<=d -> d+n<=18446744073709551615 -> 0<=n ->
 unsigned_last_nbits (d-s) 64 >= n -> mm_forward_ok s d n.
Proof.
 intros. unfold mm_forward_ok. destruct (Z_le_dec d s); auto. right.
 rewrite unsigned_last_nbits_eq in H4 by (cbn; lia). lia.
Qed.
Lemma mm_direction_backward : forall s d n,
 0<=s -> s+n<=18446744073709551615 -> 0<=d -> d+n<=18446744073709551615 -> 0<=n ->
 unsigned_last_nbits (d-s) 64 < n -> s<=d.
Proof.
 intros. destruct (Z_le_dec s d); auto.
 unfold unsigned_last_nbits in H4. change (2^64) with 18446744073709551616 in H4.
 assert (E : (d-s) mod 18446744073709551616 = d-s+18446744073709551616).
 { symmetry. apply Z.mod_unique with (q:= -1); lia. }
 rewrite E in H4. lia.
Qed.
