From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Export SimpleC.EE.stdlib.glibc.strstr_lib.
Require Export SimpleC.EE.stdlib.glibc.two_way_dynamic_lib.
Local Open Scope sac.
Local Open Scope Z_scope.

Definition gs_piece base (b:list Z) lo hi :=
 UCharArray.seg base lo hi (sublist lo hi b).
Definition gs_tw_frame base len b ho hl no nl :=
 if ho <? no then
 gs_piece base b 0 ho ** gs_piece base b (ho+hl+1) no ** gs_piece base b (no+nl) len
 else
 gs_piece base b 0 no ** gs_piece base b (no+nl) ho ** gs_piece base b (ho+hl+1) len.

Lemma gs_piece_split : forall base b lo mid hi,
 0 <= lo <= mid -> mid <= hi ->
 gs_piece base b lo hi |-- gs_piece base b lo mid ** gs_piece base b mid hi.
Proof.
 intros. unfold gs_piece. sep_apply (UCharArray.seg_split_to_seg base lo mid hi (sublist lo hi b) ltac:(lia)).
 repeat rewrite Zsublist_Zsublist by lia.
 replace (0+lo) with lo by ring. replace (mid-lo+lo) with mid by ring.
 replace (hi-lo+lo) with hi by ring. entailer!.
Qed.

Lemma gs_piece_join : forall base b lo mid hi,
 0 <= lo <= mid -> mid <= hi <= Zlength b ->
 gs_piece base b lo mid ** gs_piece base b mid hi |-- gs_piece base b lo hi.
Proof.
 intros. unfold gs_piece. sep_apply (UCharArray.seg_merge_to_seg base lo mid hi); try lia.
 rewrite <- sublist_split by lia. entailer!.
Qed.

Lemma gs_piece_to_full : forall base b lo n,
 gs_piece base b lo (lo+n) |-- UCharArray.full (base+lo) n (sublist lo (lo+n) b).
Proof.
 intros. unfold gs_piece. sep_apply UCharArray.seg_to_full.
 rewrite sizeof_uchar. replace (base+lo*1) with (base+lo) by ring.
 replace (lo+n-lo) with n by ring. entailer!.
Qed.
Lemma gs_full_to_piece : forall base b lo n,
 UCharArray.full (base+lo) n (sublist lo (lo+n) b) |-- gs_piece base b lo (lo+n).
Proof.
 intros. unfold gs_piece. sep_apply UCharArray.full_to_seg.
 replace (base+lo) with (base+lo*sizeof(UCHAR)) by (rewrite sizeof_uchar; ring).
 rewrite <- UCharArray.seg_shift.
 replace (lo+0) with lo by ring. entailer!.
Qed.

Lemma gs_piece_terminator : forall base b off,
 0 <= off < Zlength b -> Znth off b 0 = 0 ->
 gs_piece base b off (off+1) |-- tw_terminator base off.
Proof.
 intros. unfold gs_piece. rewrite (sublist_single 0 off b) by lia. rewrite H0.
 unfold tw_terminator. rewrite UCharArray.seg_unfold, UCharArray.seg_empty.
 rewrite sizeof_uchar. replace (base+off*1) with (base+off) by ring. entailer!.
Qed.
Lemma gs_terminator_piece : forall base b off,
 0 <= off < Zlength b -> Znth off b 0 = 0 ->
 tw_terminator base off |-- gs_piece base b off (off+1).
Proof.
 intros. unfold gs_piece. rewrite (sublist_single 0 off b) by lia. rewrite H0.
 unfold tw_terminator. rewrite UCharArray.seg_unfold, UCharArray.seg_empty.
 rewrite sizeof_uchar. replace (base+off*1) with (base+off) by ring. entailer!.
Qed.

Lemma gs_tw_open : forall base len b ho hl no nl,
 gs_inputs b len ho hl no nl -> 256 < nl ->
 UCharArray.full base len b |--
 UCharArray.full (base+ho) hl (sublist ho (ho+hl) b) **
 UCharArray.full (base+no) nl (sublist no (no+nl) b) **
 tw_terminator (base+ho) hl ** gs_tw_frame base len b ho hl no nl.
Proof.
 intros base len b ho hl no nl (Len & LB & Ho & Hl & HE & No & Nl & NE & Bytes & [Hnz Hz] & Ns & Sep) Long.
 specialize (Sep Long).
 assert (E : sublist 0 len b = b) by (apply sublist_self; lia).
 eapply derivable1_trans; [apply UCharArray.full_to_seg|].
 rewrite <- E at 1.
 fold (gs_piece base b 0 len).
 unfold gs_tw_frame. destruct (ho <? no) eqn:Order.
 - apply Z.ltb_lt in Order.
   sep_apply (gs_piece_split base b 0 ho len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b ho (ho+hl) len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b (ho+hl) (ho+hl+1) len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b (ho+hl+1) no len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b no (no+nl) len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_to_full base b ho hl).
   sep_apply (gs_piece_to_full base b no nl).
   sep_apply (gs_piece_terminator base b (ho+hl) ltac:(lia) Hz).
   unfold tw_terminator. replace (base+(ho+hl)) with (base+ho+hl) by ring. entailer!.
 - apply Z.ltb_ge in Order.
   sep_apply (gs_piece_split base b 0 no len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b no (no+nl) len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b (no+nl) ho len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b ho (ho+hl) len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_split base b (ho+hl) (ho+hl+1) len ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_to_full base b ho hl).
   sep_apply (gs_piece_to_full base b no nl).
   sep_apply (gs_piece_terminator base b (ho+hl) ltac:(lia) Hz).
   unfold tw_terminator. replace (base+(ho+hl)) with (base+ho+hl) by ring. entailer!.
Qed.

Lemma gs_tw_close : forall base len b ho hl no nl,
 gs_inputs b len ho hl no nl -> 256 < nl ->
 UCharArray.full (base+ho) hl (sublist ho (ho+hl) b) **
 UCharArray.full (base+no) nl (sublist no (no+nl) b) **
 tw_terminator (base+ho) hl ** gs_tw_frame base len b ho hl no nl |--
 UCharArray.full base len b.
Proof.
 intros base len b ho hl no nl (Len & LB & Ho & Hl & HE & No & Nl & NE & Bytes & [Hnz Hz] & Ns & Sep) Long.
 specialize (Sep Long).
 sep_apply (gs_full_to_piece base b ho hl).
 sep_apply (gs_full_to_piece base b no nl).
 replace (tw_terminator (base+ho) hl) with (tw_terminator base (ho+hl))
 by (unfold tw_terminator; f_equal; ring).
 sep_apply (gs_terminator_piece base b (ho+hl) ltac:(lia) Hz).
 unfold gs_tw_frame. destruct (ho <? no) eqn:Order.
 - apply Z.ltb_lt in Order.
   eapply derivable1_trans with (y :=
    (gs_piece base b 0 ho ** gs_piece base b ho (ho+hl)) **
    gs_piece base b (ho+hl) (ho+hl+1) ** gs_piece base b (ho+hl+1) no **
    gs_piece base b no (no+nl) ** gs_piece base b (no+nl) len); [entailer!|].
   sep_apply (gs_piece_join base b 0 ho (ho+hl) ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 (ho+hl) (ho+hl+1) ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 (ho+hl+1) no ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 no (no+nl) ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 (no+nl) len ltac:(lia) ltac:(lia)).
   unfold gs_piece. rewrite sublist_self by lia. sep_apply UCharArray.seg_to_full.
   replace (base+0*sizeof(UCHAR)) with base by ring.
   replace (len-0) with len by ring. entailer!.
 - apply Z.ltb_ge in Order.
   eapply derivable1_trans with (y :=
    (gs_piece base b 0 no ** gs_piece base b no (no+nl)) **
    gs_piece base b (no+nl) ho ** gs_piece base b ho (ho+hl) **
    gs_piece base b (ho+hl) (ho+hl+1) ** gs_piece base b (ho+hl+1) len); [entailer!|].
   sep_apply (gs_piece_join base b 0 no (no+nl) ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 (no+nl) ho ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 ho (ho+hl) ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 (ho+hl) (ho+hl+1) ltac:(lia) ltac:(lia)).
   sep_apply (gs_piece_join base b 0 (ho+hl+1) len ltac:(lia) ltac:(lia)).
   unfold gs_piece. rewrite sublist_self by lia. sep_apply UCharArray.seg_to_full.
   replace (base+0*sizeof(UCHAR)) with base by ring.
   replace (len-0) with len by ring. entailer!.
Qed.

(* Same nonempty-slice bound argument used in musl's result bridge. *)
Lemma gs_nonempty_sublist_bounds : forall hay needle pos,
 needle <> (@nil Z) -> sublist pos (pos+Zlength needle) hay = needle ->
 0 <= pos /\ pos+Zlength needle <= Zlength hay.
Proof.
 intros hay needle pos NE Eq.
 assert (NL : 0 < Zlength needle).
 { rewrite Zlength_correct. destruct needle; simpl in *; [contradiction|lia]. }
 pose proof (f_equal (@List.length Z) Eq) as Len.
 unfold sublist in Len. rewrite length_skipn, length_firstn in Len.
 rewrite Zlength_correct in *.
 destruct (Nat.min_spec (Z.to_nat (pos+Z.of_nat (List.length needle))) (List.length hay))
 as [[B E]|[B E]]; rewrite E in Len; rewrite Zlength_correct; lia.
Qed.

Lemma gs_match_sublist : forall b len ho hl no nl pos,
 gs_inputs b len ho hl no nl -> 0 < nl ->
 (hp_match_at b ho hl no nl pos <->
 sublist pos (pos+nl) (sublist ho (ho+hl) b) = sublist no (no+nl) b).
Proof.
 intros b len ho hl no nl pos Input N.
 destruct Input as (L & LB & Ho & Hl & HE & No & Nl & NE & Rest).
 assert (HN : Zlength (sublist ho (ho+hl) b) = hl) by (rewrite Zlength_sublist by lia; lia).
 assert (NN : Zlength (sublist no (no+nl) b) = nl) by (rewrite Zlength_sublist by lia; lia).
 split.
 - intros (P & Fit & M).
   apply (proj2 (list_eq_ext _ _ 0)).
   rewrite Zlength_sublist by lia. rewrite ?HN,?NN. split; [lia|].
   intros i I. repeat rewrite Znth_sublist by lia.
   replace (i+pos+ho) with (ho+pos+i) by ring.
   replace (i+no) with (no+i) by ring. apply M; lia.
 - intro Eq.
   assert (Nonempty : sublist no (no+nl) b <> nil) by (intro E; rewrite E in NN; change (0 = nl) in NN; lia).
   pose proof (gs_nonempty_sublist_bounds (sublist ho (ho+hl) b)
     (sublist no (no+nl) b) pos Nonempty ltac:(rewrite NN; exact Eq)) as [P Fit].
   rewrite NN,HN in Fit. unfold hp_match_at. split; [lia|]. split; [lia|].
   intros i I. pose proof (f_equal (fun l => Znth i l 0) Eq) as E.
   cbn beta in E. repeat rewrite Znth_sublist in E by lia.
   replace (i+pos+ho) with (ho+pos+i) in E by ring.
   replace (i+no) with (no+i) in E by ring. exact E.
Qed.

Lemma gs_tw_result : forall b base len ho hl no nl r opt,
 gs_inputs b len ho hl no nl -> 0 < nl ->
 match_post (sublist ho (ho+hl) b) (sublist no (no+nl) b) opt ->
 uchar_ptr_option_repr (base+ho) r 1 = opt ->
 hp_result b base ho hl no nl r.
Proof.
 intros b base len ho hl no nl r opt Input N Post Repr.
 assert (HN : Zlength (sublist ho (ho+hl) b) = hl).
 { destruct Input as (L & LB & Ho & Hl & HE & Rest).
   rewrite Zlength_sublist by lia; lia. }
 assert (NN : Zlength (sublist no (no+nl) b) = nl).
 { destruct Input as (L & LB & Ho & Hl & HE & No & Nl & NE & Rest).
   rewrite Zlength_sublist by lia; lia. }
 rewrite <- Repr in Post. unfold uchar_ptr_option_repr in Post.
 destruct (Z.eq_dec r NULL) as [Zero|Nonzero].
 - subst r. left. split; [reflexivity|]. intros pos M.
   unfold match_post, no_occur in Post. rewrite ?HN,?NN in Post.
   apply (Post pos); [unfold hp_match_at in M; lia|].
   apply gs_match_sublist with (len:=len); auto.
 - rewrite Z.div_1_r in Post. unfold match_post, first_occur, no_occur in Post.
   rewrite ?HN,?NN in Post. destruct Post as [Before Match].
   right. exists (r-(base+ho)). split; [lia|]. split.
   + apply gs_match_sublist with (len:=len); auto.
   + intros pos P M. apply (Before pos P). apply gs_match_sublist with (len:=len); auto.
Qed.

Lemma gs_tw_nonzero : forall b len ho hl no nl,
 gs_inputs b len ho hl no nl -> tw_nonzero_bytes (sublist ho (ho+hl) b).
Proof.
 intros b len ho hl no nl (L & LB & Ho & Hl & HE & No & Nl & NE & Bytes & [Hnz Hz] & Rest).
 assert (SliceLength : Zlength (sublist ho (ho+hl) b) = hl)
 by (rewrite Zlength_sublist by lia; lia).
 unfold tw_nonzero_bytes. apply (proj2 (Forall_nth _ _)).
 intros n d B.
 assert (E : nth n (sublist ho (ho+hl) b) d = Znth (Z.of_nat n) (sublist ho (ho+hl) b) 0).
 { unfold Znth. rewrite Nat2Z.id. apply nth_indep; exact B. }
 rewrite E. rewrite Zlength_correct in SliceLength.
 rewrite Znth_sublist by lia. replace (Z.of_nat n+ho) with (ho+Z.of_nat n) by ring.
 apply Hnz; lia.
Qed.
