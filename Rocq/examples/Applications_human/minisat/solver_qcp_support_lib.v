From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_shared_semantics.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** ===== group: clause_is_lit ===== *)
Lemma clause_read_lit_value__clause_is_lit : forall c,
  0 <= c ->
  tagged_word c ->
  0 <= tag_lit c ->
  tag_lit c <= INT_MAX ->
  signed_last_nbits
    (Z.shiftr (unsigned_last_nbits c 32) 1) 32 = tag_lit c.
Proof.
  intros c Hnonneg Htag Hlo Hhi.
  unfold tagged_word, is_tag in Htag.
  apply Z.odd_spec in Htag.
  destruct Htag as [k ->].
  unfold tag_lit in *.
  assert (Hdiv : (2 * k + 1) / 2 = k).
  { apply Zdiv2_pack. lia. }
  rewrite Hdiv in Hlo, Hhi |- *.
  rewrite unsigned_last_nbits_eq.
  2: { replace (2 ^ 32) with 4294967296 by reflexivity. lia. }
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  rewrite Hdiv.
  apply signed_last_nbits_eq.
  - lia.
  - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity.
    lia.
Qed.

Lemma order_heap_one_hole_x_neq_cell__order_update :
  forall n origin x hole heap orderpos i,
  order_heap_one_hole n origin x hole heap orderpos ->
  0 <= i < Zlength heap -> i <> hole ->
  x <> Znth i heap (-1).
Proof.
  intros n origin x hole heap orderpos i H Hi Hne.
  destruct H as
    (Hoplen & Hlen & Hhole & Hx & Hnd & Hrng & Hperm & Hinv & Hout).
  assert (Hnd2 : NoDup (x :: list_without_Znth hole heap))
    by (apply (Permutation_NoDup Hperm); exact Hnd).
  inversion Hnd2 as [|? ? Hxnotin ?]; subst.
  intros Heq. apply Hxnotin. rewrite Heq.
  apply In_list_without_Znth; lia.
Qed.

Lemma double_array_missing2_refold :
  forall base i j n values,
  0 <= i < n -> 0 <= j < n -> i <> j ->
  ((base + i * sizeof(DOUBLE)) # Double |-> double_Znth i values) **
  ((base + j * sizeof(DOUBLE)) # Double |-> double_Znth j values) **
  double_array_missing2 base i j n values
  |-- DoubleArray.seg base 0 n values.
Proof.
  intros base i j n values Hi Hj Hij.
  unfold double_array_missing2.
  Intros_p Hlen.
  destruct (i <? j) eqn:Eij.
  - apply Z.ltb_lt in Eij.
    assert (E_i : sublist 0 (i + 1) values =
                  sublist 0 i values ++ double_Znth i values :: nil).
    { unfold double_Znth.
      rewrite (sublist_split 0 (i + 1) i values) by lia.
      rewrite (sublist_single msat_fp64_zero i values) by lia.
      reflexivity. }
    assert (E_j : sublist 0 (j + 1) values =
                  sublist 0 j values ++ double_Znth j values :: nil).
    { unfold double_Znth.
      rewrite (sublist_split 0 (j + 1) j values) by lia.
      rewrite (sublist_single msat_fp64_zero j values) by lia.
      reflexivity. }
    assert (E_mid : sublist 0 j values =
                    sublist 0 (i + 1) values ++ sublist (i + 1) j values).
    { rewrite (sublist_split 0 j (i + 1) values) by lia. reflexivity. }
    assert (E_all : values = sublist 0 (j + 1) values ++
                             sublist (j + 1) n values).
    { rewrite <- Hlen at 1.
      rewrite <- (sublist_self values (Zlength values)) at 1 by reflexivity.
      rewrite (sublist_split 0 (Zlength values) (j + 1) values) by lia.
      reflexivity. }
    sep_apply_l_atomic (DoubleArray.seg_single base i (double_Znth i values)).
    sep_apply_l_atomic (DoubleArray.seg_single base j (double_Znth j values)).
    sep_apply (DoubleArray.seg_merge_to_seg base 0 i (i + 1)
      (sublist 0 i values) (double_Znth i values :: nil)); try lia.
    rewrite <- E_i.
    sep_apply (DoubleArray.seg_merge_to_seg base 0 (i + 1) j
      (sublist 0 (i + 1) values) (sublist (i + 1) j values)); try lia.
    rewrite <- E_mid.
    sep_apply (DoubleArray.seg_merge_to_seg base 0 j (j + 1)
      (sublist 0 j values) (double_Znth j values :: nil)); try lia.
    rewrite <- E_j.
    sep_apply (DoubleArray.seg_merge_to_seg base 0 (j + 1) n
      (sublist 0 (j + 1) values) (sublist (j + 1) n values)); try lia.
    rewrite <- E_all. cancel.
  - apply Z.ltb_ge in Eij.
    assert (Hji : j < i) by lia.
    assert (E_j : sublist 0 (j + 1) values =
                  sublist 0 j values ++ double_Znth j values :: nil).
    { unfold double_Znth.
      rewrite (sublist_split 0 (j + 1) j values) by lia.
      rewrite (sublist_single msat_fp64_zero j values) by lia.
      reflexivity. }
    assert (E_i : sublist 0 (i + 1) values =
                  sublist 0 i values ++ double_Znth i values :: nil).
    { unfold double_Znth.
      rewrite (sublist_split 0 (i + 1) i values) by lia.
      rewrite (sublist_single msat_fp64_zero i values) by lia.
      reflexivity. }
    assert (E_mid : sublist 0 i values =
                    sublist 0 (j + 1) values ++ sublist (j + 1) i values).
    { rewrite (sublist_split 0 i (j + 1) values) by lia. reflexivity. }
    assert (E_all : values = sublist 0 (i + 1) values ++
                             sublist (i + 1) n values).
    { rewrite <- Hlen at 1.
      rewrite <- (sublist_self values (Zlength values)) at 1 by reflexivity.
      rewrite (sublist_split 0 (Zlength values) (i + 1) values) by lia.
      reflexivity. }
    sep_apply_l_atomic (DoubleArray.seg_single base j (double_Znth j values)).
    sep_apply_l_atomic (DoubleArray.seg_single base i (double_Znth i values)).
    sep_apply (DoubleArray.seg_merge_to_seg base 0 j (j + 1)
      (sublist 0 j values) (double_Znth j values :: nil)); try lia.
    rewrite <- E_j.
    sep_apply (DoubleArray.seg_merge_to_seg base 0 (j + 1) i
      (sublist 0 (j + 1) values) (sublist (j + 1) i values)); try lia.
    rewrite <- E_mid.
    sep_apply (DoubleArray.seg_merge_to_seg base 0 i (i + 1)
      (sublist 0 i values) (double_Znth i values :: nil)); try lia.
    rewrite <- E_i.
    sep_apply (DoubleArray.seg_merge_to_seg base 0 (i + 1) n
      (sublist 0 (i + 1) values) (sublist (i + 1) n values)); try lia.
    rewrite <- E_all. msat_entailer_with lia.
Qed.

Lemma order_heap_one_hole_saved_neq_cell__order_update :
  forall n origin x hole heap orderpos j,
  order_heap_one_hole n origin x hole heap orderpos ->
  0 <= j < Zlength heap -> j <> hole ->
  x <> Znth j heap (-1).
Proof.
  intros n origin x hole heap orderpos j Hhole Hj Hjh.
  destruct Hhole as
    (Hoplen & Hlen & Hhr & Hxr & Hnd & Hrange & Hperm & Hinv & Hout).
  assert (Hnd' : NoDup (x :: list_without_Znth hole heap)).
  { apply (Permutation_NoDup Hperm). exact Hnd. }
  inversion Hnd' as [|? ? Hnotin ?]; subst.
  intros E. apply Hnotin. rewrite E.
  apply (In_list_without_Znth (-1)); lia.
Qed.

Lemma order_update_loop_inv_step__order_update :
  forall n v origin x hole child heap orderpos,
  order_update_loop_inv n v origin x hole heap orderpos ->
  0 <= child < Zlength heap -> child <> hole ->
  order_update_loop_inv n v origin x child
    (replace_Znth hole (Znth child heap 0) heap)
    (replace_Znth (Znth child heap 0) hole orderpos).
Proof.
  intros n v origin x hole child heap orderpos
    (Hv & Hin & Hhole) Hchild Hne.
  unfold order_update_loop_inv.
  split; [exact Hv|]. split; [exact Hin|].
  rewrite (Znth_indep heap child 0 (-1)) by lia.
  apply order_heap_one_hole_step; assumption.
Qed.

Lemma order_update_close_post__order_update :
  forall n v before_heap before_pos x hole heap orderpos,
  order_update_pre n v before_heap before_pos ->
  order_update_loop_inv n v before_heap x hole heap orderpos ->
  order_update_post n v before_heap before_pos
    (replace_Znth hole x heap) (replace_Znth x hole orderpos).
Proof.
  intros n v before_heap before_pos x hole heap orderpos Hpre Hloop.
  destruct Hloop as (Hv & Hin & Hhole).
  unfold order_update_post.
  split; [exact Hpre|].
  split; [apply (order_heap_one_hole_close n before_heap x hole heap orderpos);
          exact Hhole|].
  split; [apply (order_heap_one_hole_perm n before_heap x hole heap orderpos);
          exact Hhole|].
  intros u Hu.
  destruct Hpre as (Hwf & Hv0 & Hpresent).
  unfold order_heap_wf in Hwf.
  pose proof (heap_wf_in_iff n
    {| mh_heap := before_heap; mh_orderpos := before_pos |} u Hwf Hu) as Hold.
  cbn [mh_heap mh_orderpos] in Hold.
  pose proof (order_heap_one_hole_close_missing
    n before_heap x hole heap orderpos u Hhole Hu) as Hnew.
  split.
  - intros Hmissing. apply Hnew. intros Huin.
    apply Hold in Huin. contradiction.
  - intros Hmissing.
    destruct (Z.eq_dec (Znth u before_pos (-1)) (-1)) as [E|E]; [exact E|].
    exfalso. apply Hnew in Hmissing. apply Hmissing. apply Hold. exact E.
Qed.

Lemma order_unassigned_post_after_update__order_unassigned :
  forall n v before_heap before_pos after_heap after_pos,
  order_unassigned_pre n v before_heap before_pos ->
  Znth v before_pos (-1) = -1 ->
  order_update_post n v (before_heap ++ v :: nil)
    (replace_Znth v (Zlength before_heap) before_pos) after_heap after_pos ->
  order_unassigned_post n v before_heap before_pos after_heap after_pos.
Proof.
  intros n v before_heap before_pos after_heap after_pos Hun Hmissing Hupd.
  destruct Hupd as (Hupre & Hwf & Hperm & Hsame).
  unfold order_unassigned_post.
  split; [exact Hwf|].
  left. split; [exact Hmissing|]. apply Permutation_sym. exact Hperm.
Qed.

Lemma order_unassigned_post_noop__order_unassigned :
  forall n v heap orderpos,
  order_unassigned_pre n v heap orderpos ->
  Znth v orderpos 0 <> -1 ->
  order_unassigned_post n v heap orderpos heap orderpos.
Proof.
  intros n v heap orderpos Hpre Hpresent0.
  destruct Hpre as (Hwf & Hv & Htwon).
  unfold order_unassigned_post.
  split; [exact Hwf|].
  right. split.
  - rewrite (Znth_indep orderpos v (-1) 0).
    + exact Hpresent0.
    + pose proof (heap_wf_orderpos_length n
        {| mh_heap := heap; mh_orderpos := orderpos |} Hwf) as E.
      cbn [mh_orderpos] in E. lia.
  - split; reflexivity.
Qed.

(** ===== group: order_select ===== *)
Lemma order_select_loop_inv_cell_range__order_select : forall
    n origin heap orderpos assigns trail qhead i,
  order_select_loop_inv n origin heap orderpos assigns trail qhead ->
  0 <= i < Zlength heap ->
  0 <= Znth i heap 0 < n.
Proof.
  intros n origin heap orderpos assigns trail qhead i Hinv Hi.
  unfold order_select_loop_inv, order_select_pre in Hinv.
  destruct Hinv as ((Hbound & Hwf & Hcov & Hassigned & Hlen & Hvals) & Hincl).
  unfold order_heap_wf in Hwf.
  pose proof
    (heap_wf_range n {| mh_heap := heap; mh_orderpos := orderpos |} Hwf)
    as Hrange.
  cbn [mh_heap mh_orderpos] in Hrange.
  rewrite Forall_forall in Hrange.
  apply Hrange. apply Znth_In. exact Hi.
Qed.

Lemma Znth_zero_past_end__order_select : forall (l : list Z) i,
  Zlength l <= i -> Znth i l 0 = 0.
Proof.
  intros l i Hi.
  unfold Znth.
  assert (Hnat : (List.length l <= Z.to_nat i)%nat).
  { rewrite Zlength_correct in Hi. lia. }
  rewrite nth_overflow by exact Hnat. reflexivity.
Qed.

Lemma order_select_sift_inv_init__order_select : forall
    n origin before orderpos assigns trail qhead size popped x,
  order_select_loop_inv n origin before orderpos assigns trail qhead ->
  Zlength before = size + 1 ->
  0 < size ->
  popped = Znth 0 before (-1) ->
  x = Znth size before (-1) ->
  order_select_sift_inv n popped x 0 origin before
    (sublist 0 size before) (replace_Znth popped (-1) orderpos)
    assigns trail qhead.
Proof.
  intros n origin before orderpos assigns trail qhead size popped x
    Hloop Hlength Hsize Hpopped Hx.
  unfold order_select_loop_inv, order_select_pre in Hloop.
  destruct Hloop as
    ((Hbound & Hwf & Hcovers & Hassigned & Hassigns & Hvalues) & Hincl).
  pose proof
    (heap_wf_orderpos_length n
      {| mh_heap := before; mh_orderpos := orderpos |} Hwf) as Hposlen.
  cbn [mh_orderpos] in Hposlen.
  assert (Hpopped_range : 0 <= popped < n).
  { unfold order_heap_wf in Hwf.
    pose proof
      (heap_wf_range n {| mh_heap := before; mh_orderpos := orderpos |} Hwf)
      as Hrange.
    cbn [mh_heap mh_orderpos] in Hrange.
    rewrite Forall_forall in Hrange.
    rewrite Hpopped.
    apply Hrange. apply Znth_In. lia. }
  unfold order_select_sift_inv.
  split; [exact Hbound|].
  split; [exact Hpopped_range|].
  split; [exact Hincl|].
  split; [exact Hassigns|].
  split; [exact Hvalues|].
  split; [exact Hassigned|].
  split.
  - eapply heap_covers_except_intro; [exact Hcovers|].
    intros u Hu Hmissing.
    cbn [mh_orderpos] in Hmissing |- *.
    destruct (Z.eq_dec u popped) as [->|Hne].
    + left. reflexivity.
    + right.
      assert (Hpopped_pos : 0 <= popped < Zlength orderpos) by lia.
      assert (Hu_pos : 0 <= u < Zlength orderpos) by lia.
      assert (Hpu : popped <> u) by lia.
      pose proof
        (Znth_replace_Znth_Diff (-1) orderpos popped u (-1)
          Hpopped_pos Hu_pos Hpu) as Hsame.
      rewrite Hsame in Hmissing.
      exact Hmissing.
  - apply order_heap_one_hole_init_select; assumption.
Qed.

Lemma order_select_sift_inv_step__order_select : forall
    n popped x hole origin before heap orderpos assigns trail qhead child,
  order_select_sift_inv n popped x hole origin before heap orderpos
    assigns trail qhead ->
  0 <= child < Zlength heap ->
  child <> hole ->
  order_select_sift_inv n popped x child origin before
    (replace_Znth hole (Znth child heap 0) heap)
    (replace_Znth (Znth child heap 0) hole orderpos)
    assigns trail qhead.
Proof.
  intros n popped x hole origin before heap orderpos assigns trail qhead child
    Hinv Hchild Hne.
  unfold order_select_sift_inv in Hinv |- *.
  destruct Hinv as
    (Hbound & Hpopped & Hincl & Hassigns & Hvalues & Hassigned & Hcovers & Hhole).
  pose proof Hhole as Hhole_facts.
  unfold order_heap_one_hole in Hhole_facts.
  destruct Hhole_facts as
    (Hposlen & Hheaplen & Hhole_range & Hxrange & Hnodup & Hrange &
     Hperm & Hinverse & Hout).
  pose proof
    (order_heap_one_hole_cell_range n (list_without_Znth 0 before)
      x hole heap orderpos child Hhole Hchild Hne) as Hmoved_range.
  rewrite <- (Znth_indep heap child 0 (-1)) in Hmoved_range by lia.
  assert (Hcovers' :
    heap_covers_except n
      {| mh_heap := replace_Znth hole (Znth child heap 0) heap;
         mh_orderpos := replace_Znth (Znth child heap 0) hole orderpos |}
      assigns trail qhead popped).
  { unfold heap_covers_except in Hcovers |- *.
    intros u Hu Hnot_popped Hmissing.
    cbn [mh_orderpos] in Hmissing |- *.
    destruct (Z.eq_dec u (Znth child heap 0)) as [->|Hnot_moved].
    - rewrite (Znth_replace_Znth_Same (-1) orderpos
        (Znth child heap 0) hole) in Hmissing by lia.
      lia.
    - apply Hcovers; [exact Hu|exact Hnot_popped|].
      rewrite (Znth_replace_Znth_Diff (-1) orderpos
        (Znth child heap 0) u hole) in Hmissing by lia.
      exact Hmissing. }
  split; [exact Hbound|].
  split; [exact Hpopped|].
  split; [exact Hincl|].
  split; [exact Hassigns|].
  split; [exact Hvalues|].
  split; [exact Hassigned|].
  split; [exact Hcovers'|].
  rewrite (Znth_indep heap child 0 (-1)) by lia.
  apply order_heap_one_hole_step; assumption.
Qed.

Lemma order_select_sift_inv_cell_range__order_select : forall
    n popped x hole origin before heap orderpos assigns trail qhead i,
  order_select_sift_inv n popped x hole origin before heap orderpos
    assigns trail qhead ->
  0 <= i < Zlength heap ->
  i <> hole ->
  0 <= Znth i heap 0 < n.
Proof.
  intros n popped x hole origin before heap orderpos assigns trail qhead i
    Hinv Hi Hne.
  unfold order_select_sift_inv in Hinv.
  destruct Hinv as
    (Hbound & Hpopped & Hincl & Hassigns & Hvalues & Hassigned & Hcovers & Hhole).
  pose proof
    (order_heap_one_hole_cell_range n (list_without_Znth 0 before) x hole
       heap orderpos i Hhole Hi Hne) as Hrange.
  rewrite (Znth_indep heap i 0 (-1)) by lia.
  exact Hrange.
Qed.

Lemma order_select_sift_inv_cells_neq__order_select : forall
    n popped x hole origin before heap orderpos assigns trail qhead i j,
  order_select_sift_inv n popped x hole origin before heap orderpos
    assigns trail qhead ->
  0 <= i < Zlength heap ->
  0 <= j < Zlength heap ->
  i <> hole ->
  j <> hole ->
  i <> j ->
  Znth i heap 0 <> Znth j heap 0.
Proof.
  intros n popped x hole origin before heap orderpos assigns trail qhead i j
    Hinv Hi Hj Hih Hjh Hij.
  unfold order_select_sift_inv in Hinv.
  destruct Hinv as
    (Hbound & Hpopped & Hincl & Hassigns & Hvalues & Hassigned & Hcovers & Hhole).
  unfold order_heap_one_hole in Hhole.
  destruct Hhole as
    (Hoplen & Hlen & Hhole_range & Hx & Hnodup & Hrange & Hperm & Hinverse & Hout).
  pose proof (Hinverse i Hi Hih) as Ei.
  pose proof (Hinverse j Hj Hjh) as Ej.
  assert (Hneq : Znth i heap (-1) <> Znth j heap (-1)).
  { intros E. rewrite E in Ei. lia. }
  rewrite (Znth_indep heap i 0 (-1)) by lia.
  rewrite (Znth_indep heap j 0 (-1)) by lia.
  exact Hneq.
Qed.

Lemma double_array_seg_split_to_missing2__order_select : forall
    base i j n values,
  0 <= i < n ->
  0 <= j < n ->
  i <> j ->
  DoubleArray.seg base 0 n values |--
    ((base + i * sizeof(DOUBLE)) # Double |-> double_Znth i values) **
    ((base + j * sizeof(DOUBLE)) # Double |-> double_Znth j values) **
    double_array_missing2 base i j n values.
Proof.
  intros base i j n values Hi Hj Hne.
  prop_apply_p (DoubleArray.seg_Zlength base 0 n values).
  Intros_p Hvalues.
  unfold double_array_missing2.
  destruct (i <? j) eqn:Hijb.
  - apply Z.ltb_lt in Hijb.
    sep_apply (DoubleArray.seg_split_to_seg base 0 i n values); try lia.
    replace (i - 0) with i by lia.
    replace (n - 0) with n by lia.
    assert (Hsi :
      sublist i n values =
      double_Znth i values :: sublist (i + 1) n values).
    { unfold double_Znth.
      rewrite (sublist_split i n (i + 1) values) by lia.
      rewrite (sublist_single msat_fp64_zero i values) by lia.
      reflexivity. }
    rewrite Hsi.
    sep_apply (proj1 (DoubleArray.seg_unfold base i n (sublist (i + 1) n values) (double_Znth i values))).
    sep_apply (DoubleArray.seg_split_to_seg base (i + 1) j n
      (sublist (i + 1) n values)); try lia.
    assert (Hmid :
      sublist 0 (j - (i + 1)) (sublist (i + 1) n values) =
      sublist (i + 1) j values).
    { apply list_eq_ext with (d := msat_fp64_zero). split.
      - rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia).
        rewrite Zlength_sublist by lia. lia.
      - intros k Hk.
        rewrite Zlength_sublist in Hk by
          (rewrite Zlength_sublist by lia; lia).
        rewrite !Znth_sublist by
          (try rewrite Zlength_sublist by lia; lia).
        f_equal. lia. }
    assert (Htail :
      sublist (j - (i + 1)) (n - (i + 1))
        (sublist (i + 1) n values) = sublist j n values).
    { apply list_eq_ext with (d := msat_fp64_zero). split.
      - rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia).
        rewrite Zlength_sublist by lia. lia.
      - intros k Hk.
        rewrite Zlength_sublist in Hk by
          (rewrite Zlength_sublist by lia; lia).
        rewrite !Znth_sublist by
          (try rewrite Zlength_sublist by lia; lia).
        f_equal. lia. }
    rewrite Hmid, Htail.
    assert (Hsj :
      sublist j n values =
      double_Znth j values :: sublist (j + 1) n values).
    { unfold double_Znth.
      rewrite (sublist_split j n (j + 1) values) by lia.
      rewrite (sublist_single msat_fp64_zero j values) by lia.
      reflexivity. }
    rewrite Hsj.
    sep_apply (proj1 (DoubleArray.seg_unfold base j n (sublist (j + 1) n values) (double_Znth j values))).
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - apply Z.ltb_ge in Hijb.
    assert (Hji : j < i) by lia.
    sep_apply (DoubleArray.seg_split_to_seg base 0 j n values); try lia.
    replace (j - 0) with j by lia.
    replace (n - 0) with n by lia.
    assert (Hsj :
      sublist j n values =
      double_Znth j values :: sublist (j + 1) n values).
    { unfold double_Znth.
      rewrite (sublist_split j n (j + 1) values) by lia.
      rewrite (sublist_single msat_fp64_zero j values) by lia.
      reflexivity. }
    rewrite Hsj.
    sep_apply (proj1 (DoubleArray.seg_unfold base j n (sublist (j + 1) n values) (double_Znth j values))).
    sep_apply (DoubleArray.seg_split_to_seg base (j + 1) i n
      (sublist (j + 1) n values)); try lia.
    assert (Hmid :
      sublist 0 (i - (j + 1)) (sublist (j + 1) n values) =
      sublist (j + 1) i values).
    { apply list_eq_ext with (d := msat_fp64_zero). split.
      - rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia).
        rewrite Zlength_sublist by lia. lia.
      - intros k Hk.
        rewrite Zlength_sublist in Hk by
          (rewrite Zlength_sublist by lia; lia).
        rewrite !Znth_sublist by
          (try rewrite Zlength_sublist by lia; lia).
        f_equal. lia. }
    assert (Htail :
      sublist (i - (j + 1)) (n - (j + 1))
        (sublist (j + 1) n values) = sublist i n values).
    { apply list_eq_ext with (d := msat_fp64_zero). split.
      - rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia).
        rewrite Zlength_sublist by lia. lia.
      - intros k Hk.
        rewrite Zlength_sublist in Hk by
          (rewrite Zlength_sublist by lia; lia).
        rewrite !Znth_sublist by
          (try rewrite Zlength_sublist by lia; lia).
        f_equal. lia. }
    rewrite Hmid, Htail.
    assert (Hsi :
      sublist i n values =
      double_Znth i values :: sublist (i + 1) n values).
    { unfold double_Znth.
      rewrite (sublist_split i n (i + 1) values) by lia.
      rewrite (sublist_single msat_fp64_zero i values) by lia.
      reflexivity. }
    rewrite Hsi.
    sep_apply (proj1 (DoubleArray.seg_unfold base i n (sublist (i + 1) n values) (double_Znth i values))).
    msat_entailer_with lia.
Qed.

Lemma firstn_incl__order_select : forall (A : Type) k (l : list A),
  incl (firstn k l) l.
Proof.
  intros A k. induction k as [|k IH]; intros [|a l]; simpl.
  - intros x H. contradiction.
  - intros x H. contradiction.
  - intros x H. contradiction.
  - intros x [->|H]; [left; reflexivity|right; apply IH; exact H].
Qed.

Lemma skipn_incl__order_select : forall (A : Type) k (l : list A),
  incl (skipn k l) l.
Proof.
  intros A k. induction k as [|k IH]; intros [|a l]; simpl.
  - apply incl_refl.
  - apply incl_refl.
  - apply incl_refl.
  - intros x H. right. apply IH. exact H.
Qed.

Lemma list_without_Znth_incl__order_select : forall i (l : list Z),
  incl (list_without_Znth i l) l.
Proof.
  intros i l x Hx. unfold list_without_Znth, sublist in Hx.
  apply in_app_or in Hx. destruct Hx as [Hx|Hx].
  - apply (skipn_incl__order_select Z _ _) in Hx.
    apply (firstn_incl__order_select Z _ _) in Hx. exact Hx.
  - apply (skipn_incl__order_select Z _ _) in Hx.
    apply (firstn_incl__order_select Z _ _) in Hx. exact Hx.
Qed.

Lemma order_select_sift_closed_wf_incl__order_select : forall
    n popped x hole origin before heap orderpos assigns trail qhead,
  order_select_sift_inv n popped x hole origin before heap orderpos
    assigns trail qhead ->
  order_heap_wf n (replace_Znth hole x heap)
    (replace_Znth x hole orderpos) /\
  incl (replace_Znth hole x heap) origin.
Proof.
  intros n popped x hole origin before heap orderpos assigns trail qhead Hinv.
  unfold order_select_sift_inv in Hinv.
  destruct Hinv as
    (Hbound & Hpopped & Hincl & Hassigns & Hvalues & Hassigned & Hcovers & Hhole).
  split.
  - exact (order_heap_one_hole_close n (list_without_Znth 0 before)
      x hole heap orderpos Hhole).
  - intros u Hu. apply Hincl.
    pose proof (order_heap_one_hole_perm n (list_without_Znth 0 before)
      x hole heap orderpos Hhole) as Hperm.
    assert (Hu_without : In u (list_without_Znth 0 before)).
    { eapply Permutation_in.
      - exact (Permutation_sym Hperm).
      - exact Hu. }
    exact (list_without_Znth_incl__order_select 0 before u Hu_without).
Qed.

Lemma order_select_sift_closed_covers_except__order_select : forall
    n popped x hole origin before heap orderpos assigns trail qhead,
  order_select_sift_inv n popped x hole origin before heap orderpos
    assigns trail qhead ->
  heap_covers_except n
    {| mh_heap := replace_Znth hole x heap;
       mh_orderpos := replace_Znth x hole orderpos |}
    assigns trail qhead popped.
Proof.
  intros n popped x hole origin before heap orderpos assigns trail qhead Hinv.
  unfold order_select_sift_inv in Hinv.
  destruct Hinv as
    (Hbound & Hpopped & Hincl & Hassigns & Hvalues & Hassigned & Hcovers & Hhole).
  pose proof Hhole as Hhole_facts.
  unfold order_heap_one_hole in Hhole_facts.
  destruct Hhole_facts as
    (Hposlen & Hheaplen & Hhole_range & Hxrange & Hnodup & Hrange &
     Hperm & Hinverse & Hout).
  unfold heap_covers_except in Hcovers |- *.
  intros v Hv Hvpopped Hmissing. cbn [mh_orderpos] in Hmissing |- *.
  destruct (Z.eq_dec v x) as [->|Hvx].
  - rewrite (Znth_replace_Znth_Same (-1) orderpos x hole) in Hmissing by lia.
    lia.
  - apply Hcovers; [exact Hv|exact Hvpopped|].
    rewrite (Znth_replace_Znth_Diff (-1) orderpos x v hole) in Hmissing by lia.
    exact Hmissing.
Qed.

Lemma order_select_sift_close_assigned__order_select : forall
    n popped x hole origin before heap orderpos assigns trail qhead,
  order_select_sift_inv n popped x hole origin before heap orderpos
    assigns trail qhead ->
  Znth popped assigns 0 <> 0 ->
  order_select_loop_inv n origin (replace_Znth hole x heap)
    (replace_Znth x hole orderpos) assigns trail qhead.
Proof.
  intros n popped x hole origin before heap orderpos assigns trail qhead
    Hinv Hpopped_assigned.
  pose proof (order_select_sift_closed_wf_incl__order_select
    n popped x hole origin before heap orderpos assigns trail qhead Hinv)
    as [Hwf Hincl].
  pose proof (order_select_sift_closed_covers_except__order_select
    n popped x hole origin before heap orderpos assigns trail qhead Hinv)
    as Hcovers_except.
  unfold order_select_sift_inv in Hinv.
  destruct Hinv as
    (Hbound & Hpopped & Hbefore & Hassigns & Hvalues & Hbelow & Hcovers & Hhole).
  unfold order_select_loop_inv, order_select_pre.
  split; [|exact Hincl].
  split; [exact Hbound|].
  split; [exact Hwf|].
  split.
  - intros v Hv Hmissing.
    destruct (Z.eq_dec v popped) as [->|Hne].
    + split; [exact Hpopped_assigned|].
      apply Hbelow; assumption.
    + apply Hcovers_except; assumption.
  - split; [exact Hbelow|].
    split; assumption.
Qed.

Lemma order_select_sift_close_unassigned_post__order_select : forall
    n popped x hole origin before heap orderpos assigns trail qhead,
  order_select_sift_inv n popped x hole origin before heap orderpos
    assigns trail qhead ->
  Znth popped assigns 0 = 0 ->
  order_select_post n popped origin (replace_Znth hole x heap)
    (replace_Znth x hole orderpos) assigns trail qhead.
Proof.
  intros n popped x hole origin before heap orderpos assigns trail qhead
    Hinv Hpopped_unassigned.
  pose proof (order_select_sift_closed_wf_incl__order_select
    n popped x hole origin before heap orderpos assigns trail qhead Hinv)
    as [Hwf Hincl].
  pose proof (order_select_sift_closed_covers_except__order_select
    n popped x hole origin before heap orderpos assigns trail qhead Hinv)
    as Hcovers.
  unfold order_select_sift_inv in Hinv.
  destruct Hinv as
    (Hbound & Hpopped & Hbefore & Hassigns & Hvalues & Hbelow & Holdcovers & Hhole).
  unfold order_select_post. split; [exact Hwf|].
  split; [exact Hincl|]. right.
  split; [exact Hpopped|].
  split; [exact Hpopped_unassigned|exact Hcovers].
Qed.

Lemma order_select_loop_pop_assigned_empty__order_select : forall
    n origin heap orderpos assigns trail qhead,
  order_select_loop_inv n origin heap orderpos assigns trail qhead ->
  Zlength heap = 1 ->
  Znth (Znth 0 heap (-1)) assigns 0 <> 0 ->
  order_select_loop_inv n origin []
    (replace_Znth (Znth 0 heap (-1)) (-1) orderpos)
    assigns trail qhead.
Proof.
  intros n origin heap orderpos assigns trail qhead Hloop Hlen Hassigned.
  unfold order_select_loop_inv, order_select_pre in Hloop.
  destruct Hloop as
    ((Hbound & Hwf & Hcovers & Hbelow & Hassigns & Hvalues) & Hincl).
  set (v := Znth 0 heap (-1)).
  assert (Hv : 0 <= v < n).
  { subst v. pose proof (heap_wf_range n
      {| mh_heap := heap; mh_orderpos := orderpos |} Hwf) as Hrange.
    rewrite Forall_forall in Hrange. apply Hrange.
    exact (Znth_In Z heap (-1) 0 ltac:(lia)). }
  assert (Hsingle : heap = [v]).
  { apply list_eq_ext with (d := -1). split.
    - simpl. exact Hlen.
    - intros i Hi. simpl in Hi. assert (i = 0) by lia. subst i.
      subst v. reflexivity. }
  assert (Hposlen : Zlength orderpos = n).
  { apply (heap_wf_orderpos_length n
      {| mh_heap := heap; mh_orderpos := orderpos |}). exact Hwf. }
  assert (Hwf' : heap_wf n
    {| mh_heap := [];
       mh_orderpos := replace_Znth v (-1) orderpos |}).
  { eapply heap_wf_pop with
      (h := {| mh_heap := heap; mh_orderpos := orderpos |}) (v := v).
    - exact Hwf.
    - exact Hv.
    - cbn [mh_heap]. rewrite Hsingle. apply Permutation_refl.
    - cbn [mh_orderpos]. rewrite Zlength_replace_Znth. exact Hposlen.
    - cbn [mh_orderpos]. apply Znth_replace_Znth_Same. lia.
    - intros u Hu Huv Hout. cbn [mh_heap mh_orderpos] in Hout |- *.
      rewrite (Znth_replace_Znth_Diff (-1) orderpos v u (-1)) by lia.
      apply (heap_wf_not_in n
        {| mh_heap := heap; mh_orderpos := orderpos |} u Hwf Hu).
      rewrite Hsingle. intros [E|[]]. lia.
    - cbn [mh_heap]. intros i Hi. cbn in Hi. lia. }
  assert (Hcovers' : heap_covers n
    {| mh_heap := []; mh_orderpos := replace_Znth v (-1) orderpos |}
    assigns trail qhead).
  { unfold heap_covers. intros u Hu Hmissing.
    cbn [mh_orderpos] in Hmissing |- *.
    destruct (Z.eq_dec u v) as [->|Huv].
    - split; [exact Hassigned|]. apply Hbelow; assumption.
    - apply Hcovers; [exact Hu|]. cbn [mh_orderpos].
      rewrite (Znth_replace_Znth_Diff (-1) orderpos v u (-1)) in Hmissing
        by lia.
      exact Hmissing. }
  unfold order_select_loop_inv, order_select_pre. split.
  - split; [exact Hbound|].
    split; [exact Hwf'|].
    split; [exact Hcovers'|].
    split; [exact Hbelow|].
    split; assumption.
  - intros u H. contradiction.
Qed.

Lemma order_select_loop_empty_post__order_select : forall
    n origin orderpos assigns trail qhead,
  order_select_loop_inv n origin [] orderpos assigns trail qhead ->
  order_select_post n (-1) origin [] orderpos assigns trail qhead.
Proof.
  intros n origin orderpos assigns trail qhead Hloop.
  unfold order_select_loop_inv, order_select_pre in Hloop.
  destruct Hloop as
    ((Hbound & Hwf & Hcovers & Hbelow & Hassigns & Hvalues) & Hincl).
  unfold order_select_post. split; [exact Hwf|].
  split; [exact Hincl|]. left.
  split; [reflexivity|]. split; [reflexivity|].
  apply (heap_covers_total n {| mh_heap := []; mh_orderpos := orderpos |}
    assigns trail qhead Hwf eq_refl Hcovers).
Qed.

Lemma order_select_sift_close_post__order_select :
  forall n next x hole before_heap sift_before heap orderpos assigns trail qhead,
  order_select_sift_inv n next x hole before_heap sift_before heap orderpos
    assigns trail qhead ->
  Znth next assigns 0 = 0 ->
  order_select_post n next before_heap
    (replace_Znth hole x heap) (replace_Znth x hole orderpos)
    assigns trail qhead.
Proof.
  intros n next x hole before_heap sift_before heap orderpos assigns trail qhead
    Hsift Hunassigned.
  unfold order_select_sift_inv in Hsift.
  destruct Hsift as
    (Htwon & Hnext & Hincl & Hassign_len & Hassign_vals & Hassigned &
     Hcovers & Hhole).
  pose proof (order_heap_one_hole_close n (list_without_Znth 0 sift_before)
    x hole heap orderpos Hhole) as Hwf.
  pose proof (order_heap_one_hole_perm n (list_without_Znth 0 sift_before)
    x hole heap orderpos Hhole) as Hperm.
  assert (Hsift_nonempty : 0 < Zlength sift_before).
  { pose proof Hhole as Hparts.
    destruct Hparts as (_ & Hheap_len & Hhole_range & _).
    destruct sift_before as [|a tl].
    - change (Zlength heap = 0) in Hheap_len. lia.
    - rewrite Zlength_cons. pose proof (Zlength_nonneg tl). lia. }
  assert (Hwithout_incl : incl (list_without_Znth 0 sift_before) sift_before).
  { intros u Hu.
    pose proof (list_without_Znth_perm (-1) 0 sift_before
      ltac:(lia)) as Hpopped.
    apply (Permutation_in _ (Permutation_sym Hpopped)).
    right. exact Hu. }
  unfold order_select_post.
  split; [exact Hwf|].
  split.
  - intros u Hu.
    apply Hincl, Hwithout_incl.
    apply (Permutation_in _ (Permutation_sym Hperm)). exact Hu.
  - right. split; [exact Hnext|].
    split; [exact Hunassigned|].
    unfold heap_covers_except in *; cbn in *.
    intros u Hu Hune Hmissing.
    change (Znth u (replace_Znth x hole orderpos) (-1) = -1) in Hmissing.
    apply Hcovers; [exact Hu|exact Hune|].
    pose proof Hhole as Hparts.
    destruct Hparts as (Hoplen & _ & Hhole_range & Hx & _).
    destruct (Z.eq_dec u x) as [->|Hux].
    + rewrite Znth_replace_Znth_Same in Hmissing by lia.
      lia.
    + rewrite Znth_replace_Znth_Diff in Hmissing by lia.
      exact Hmissing.
Qed.

Lemma order_select_singleton_post__order_select :
  forall n before_heap heap orderpos assigns trail qhead,
  order_select_loop_inv n before_heap heap orderpos assigns trail qhead ->
  Zlength heap = 1 ->
  Znth (Znth 0 heap 0) assigns 0 = 0 ->
  order_select_post n (Znth 0 heap 0) before_heap []
    (replace_Znth (Znth 0 heap 0) (-1) orderpos) assigns trail qhead.
Proof.
  intros n before_heap heap orderpos assigns trail qhead Hloop Hheap_len Hunassigned.
  destruct Hloop as (Hpre & Hincl).
  destruct Hpre as
    (Htwon & Hwf & Hcovers & Hassigned & Hassign_len & Hassign_vals).
  assert (Hheap : heap = [Znth 0 heap 0]).
  { destruct heap as [|a tl].
    - cbn in Hheap_len. lia.
    - destruct tl as [|b tl].
      + reflexivity.
      + rewrite !Zlength_cons in Hheap_len.
        pose proof (Zlength_nonneg tl). lia. }
  assert (Hnext : 0 <= Znth 0 heap 0 < n).
  { pose proof (heap_wf_range n {| mh_heap := heap; mh_orderpos := orderpos |}
      Hwf) as Hrange.
    rewrite Forall_forall in Hrange.
    apply Hrange. rewrite Hheap. left. reflexivity. }
  pose proof (heap_wf_orderpos_length n
    {| mh_heap := heap; mh_orderpos := orderpos |} Hwf) as Hoplen.
  cbn [mh_orderpos] in Hoplen.
  assert (Hwf_empty :
    heap_wf n {| mh_heap := []; mh_orderpos :=
      replace_Znth (Znth 0 heap 0) (-1) orderpos |}).
  { apply (heap_wf_pop n {| mh_heap := heap; mh_orderpos := orderpos |}
      {| mh_heap := []; mh_orderpos :=
        replace_Znth (Znth 0 heap 0) (-1) orderpos |}
      (Znth 0 heap 0)); cbn.
    - exact Hwf.
    - exact Hnext.
    - rewrite Hheap. apply Permutation_refl.
    - rewrite Zlength_replace_Znth.
      apply (heap_wf_orderpos_length n
        {| mh_heap := heap; mh_orderpos := orderpos |} Hwf).
    - apply (Znth_replace_Znth_Same (-1) orderpos
        (Znth 0 heap 0) (-1)). lia.
    - intros u Hu Hune _.
      change (Znth u (replace_Znth (Znth 0 heap 0) (-1) orderpos) (-1) = -1).
      rewrite (Znth_replace_Znth_Diff (-1) orderpos
        (Znth 0 heap 0) u (-1)) by lia.
      apply (heap_wf_not_in n {| mh_heap := heap; mh_orderpos := orderpos |}
        u Hwf Hu).
      rewrite Hheap. intros [E|[]]. apply Hune. symmetry. exact E.
    - intros i Hi. lia. }
  unfold order_select_post.
  split; [exact Hwf_empty|].
  split; [intros u []|].
  right. split; [exact Hnext|].
  split; [exact Hunassigned|].
  unfold heap_covers_except in *; cbn in *.
  intros u Hu Hune Hmissing.
  change (Znth u (replace_Znth (Znth 0 heap 0) (-1) orderpos) (-1) = -1)
    in Hmissing.
  apply Hcovers; [exact Hu|].
  rewrite (Znth_replace_Znth_Diff (-1) orderpos
    (Znth 0 heap 0) u (-1)) in Hmissing by lia.
  exact Hmissing.
Qed.

Lemma order_select_noop_post__order_select :
  forall n ret heap orderpos assigns trail qhead,
  order_select_pre n heap orderpos assigns trail qhead ->
  0 <= ret < n ->
  Znth ret assigns 0 = 0 ->
  order_select_post n ret heap heap orderpos assigns trail qhead.
Proof.
  intros n ret heap orderpos assigns trail qhead Hpre Hret Hunassigned.
  destruct Hpre as
    (Htwon & Hwf & Hcovers & Hassigned & Hassign_len & Hassign_vals).
  unfold order_select_post.
  split; [exact Hwf|].
  split; [apply incl_refl|].
  right. split; [exact Hret|].
  split; [exact Hunassigned|].
  apply heap_covers_except_weaken. exact Hcovers.
Qed.

(** ===== group: act_var_bump ===== *)
Lemma learnt_clause_remainder_from_split__act_var_bump :
  forall db c co pre post,
    db = pre ++ (c, co) :: post ->
    co_learnt co = true ->
    clause_db_rep post ** clause_db_rep pre
    |-- clause_db_pair_remainder db_nil db c msat_true (co_lits co).
Proof.
  intros db c co pre post Hdb Htag.
  unfold clause_db_pair_remainder.
  Right.
  Exists co pre post.
  msat_entailer_with int_auto.
Qed.

Lemma learnt_clause_focus_by_word__act_var_bump : forall db c,
  learnt_db db ->
  In c (db_words db) ->
  clause_db_rep db
  |-- EX clause_words : list Z, EX activity_now : fp32,
      “ learnt_db db /\ In c (db_words db) /\
        msat_fp32_nonnegative activity_now /\ 0 < c /\ c mod 2 = 0 ” &&
      (clause_hdr_addr c # Int |->
         clause_hdr_word msat_true (Zlength clause_words) **
       clause_act_addr c (Zlength clause_words) # Float |-> activity_now **
       IntArray.seg (clause_lits_addr c) 0
         (Zlength clause_words) clause_words **
       clause_db_pair_remainder db_nil db c msat_true clause_words).
Proof.
  intros db c Hlearnt Hinword.
  pose proof Hinword as Hinword_db.
  unfold db_words in Hinword.
  apply in_map_iff in Hinword.
  destruct Hinword as [[p co] [Hpc Hinentry]].
  cbn in Hpc. subst p.
  pose proof Hinentry as Hinentry0.
  pose proof Hlearnt as Hlearnt_db.
  unfold learnt_db in Hlearnt.
  rewrite Forall_forall in Hlearnt.
  specialize (Hlearnt (c, co) Hinentry).
  cbn in Hlearnt.
  apply in_split in Hinentry0.
  destruct Hinentry0 as [pre [post Hdb]].
  pose proof (clause_db_rep_app_elim pre ((c, co) :: post)) as Hsplit_db.
  rewrite <- Hdb in Hsplit_db.
  sep_apply Hsplit_db.
  rewrite clause_db_rep_cons.
  cbn [fst snd].
  rewrite Hlearnt.
  unfold MiniSatClause.rep at 1.
  Intros_p Hptr.
  unfold activity_state at 1.
  Intros activity_now.
  Exists (co_lits co) activity_now.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]).
  sep_apply
    (learnt_clause_remainder_from_split__act_var_bump
       db c co pre post Hdb Hlearnt).
  cbn.
  unfold msat_true.
  msat_entailer_with int_auto.
Qed.

(** ===== group: clause_new ===== *)
Lemma first_two_neg_distinct_ge2__clause_new : forall words,
  2 <= Zlength words ->
  NoDup (map lit_var_c words) ->
  lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0).
Proof.
  intros words Hlen Hnodup.
  destruct words as [|a words].
  { rewrite Zlength_nil in Hlen. lia. }
  destruct words as [|b rest].
  { rewrite Zlength_cons, Zlength_nil in Hlen. lia. }
  cbn [map Znth] in Hnodup |-*.
  intro Heq. apply (f_equal lit_var_c) in Heq.
  rewrite !lit_var_c_neg in Heq.
  rewrite Znth0_cons in Heq.
  rewrite Znth_cons in Heq by lia.
  replace (1 - 1) with 0 in Heq by lia.
  rewrite Znth0_cons in Heq.
  inversion Hnodup as [|x xs Hnotin Htail].
  apply Hnotin. simpl. left. symmetry. exact Heq.
Qed.

Lemma intarray_expose_first_two__clause_new : forall p l,
  2 <= Zlength l ->
  IntArray.seg p 0 (Zlength l) l |--
  p # Int |-> Znth 0 l 0 **
  (p + sizeof(INT)) # Int |-> Znth 1 l 0 **
  IntArray.seg p 2 (Zlength l) (sublist 2 (Zlength l) l).
Proof. msat_intarray_first_two a b rest. Qed.

Lemma msat_dot_field_addr_arrow :
  forall (L : lvalue_expr) (t : front_end_type) (f : string),
    eval_addr_expr (RE_addr_of (LE_dot_field L f)) =
    eval_addr_expr (RE_addr_of
      (LE_arrow_field (RE_const (eval_addr_expr (RE_addr_of L)) t) f)).
Proof.
  intros L t f. apply eval_addr_expr_congr.
  eapply rvalue_expr_equiv_trans.
  - apply addr_of_arrow_field.
  - apply RE_addr_of_congr. apply LE_arrow_field_congr.
    + apply rvalue_expr_equiv_sym. apply eval_addr.
    + reflexivity.
Qed.

Lemma stats_rep_from_solver_cells__clause_new :
  forall s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10,
  (&(s # "solver_t" ->ₛ "stats" .ₛ "starts") # UInt64 |-> x0 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "decisions") # UInt64 |-> x1 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "propagations") # UInt64 |-> x2 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "inspects") # UInt64 |-> x3 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "conflicts") # UInt64 |-> x4 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "clauses") # UInt64 |-> x5 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "clauses_literals") # UInt64 |-> x6 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "learnts") # UInt64 |-> x7 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "learnts_literals") # UInt64 |-> x8 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "max_literals") # UInt64 |-> x9 **
   &(s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") # UInt64 |-> x10)
  |-- stats_rep &(s # "solver_t" ->ₛ "stats")
        (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: nil).
Proof.
  intros s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
  unfold stats_rep, stats_starts, stats_decisions, stats_propagations,
    stats_inspects, stats_conflicts, stats_clauses, stats_clauses_literals,
    stats_learnts, stats_learnts_literals, stats_max_literals, stats_tot_literals.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  repeat (rewrite Znth0_cons || rewrite Znth_cons by lia).
  rewrite <- !msat_dot_field_addr_arrow.
  cancel.
Qed.

(** ===== group: clause_remove ===== *)
Lemma intarray_refold_first_two__clause_remove : forall p l,
  2 <= Zlength l ->
  p # Int |-> Znth 0 l 0 **
  (p + sizeof(INT)) # Int |-> Znth 1 l 0 **
  IntArray.seg p 2 (Zlength l) (sublist 2 (Zlength l) l)
  |-- IntArray.seg p 0 (Zlength l) l.
Proof. msat_intarray_first_two a b rest. Qed.

(** ===== group: assume ===== *)
Lemma replace_nth_zero_comm__assume :
  forall i j (xs : list Z),
    replace_nth j (replace_nth i xs 0) 0 =
    replace_nth i (replace_nth j xs 0) 0.
Proof.
  induction i; intros j xs; destruct xs as [|x xs]; destruct j;
    simpl; auto.
  f_equal. apply IHi.
Qed.

Lemma replace_Znth_zero_comm__assume :
  forall i j (xs : list Z),
    replace_Znth j 0 (replace_Znth i 0 xs) =
    replace_Znth i 0 (replace_Znth j 0 xs).
Proof.
  intros. unfold replace_Znth.
  apply replace_nth_zero_comm__assume.
Qed.

Lemma clear_vars_replace_zero__assume :
  forall ls a v,
    replace_Znth v 0 (clear_vars ls a) =
    clear_vars ls (replace_Znth v 0 a).
Proof.
  induction ls as [|x ls IH]; intros a v; simpl; [reflexivity|].
  rewrite IH, replace_Znth_zero_comm__assume. reflexivity.
Qed.

Lemma clear_vars_sublist_step__assume :
  forall (xs a : list Z) c hi,
    0 <= c < hi -> hi <= Zlength xs ->
    replace_Znth (lit_var_c (Znth c xs 0)) 0
      (clear_vars (sublist (c + 1) hi xs) a) =
    clear_vars (sublist c hi xs) a.
Proof.
  intros xs a c hi Hc Hhi.
  rewrite (sublist_split c hi (c + 1) xs) by lia.
  rewrite (sublist_single 0) by lia.
  simpl.
  apply clear_vars_replace_zero__assume.
Qed.

Lemma sublist_to_zdrop__assume :
  forall (xs : list Z) lo,
    sublist lo (Zlength xs) xs = zdrop lo xs.
Proof.
  intros xs lo. unfold sublist, zdrop.
  rewrite Zlength_correct, Nat2Z.id, firstn_all. reflexivity.
Qed.

Lemma sublist_zero_ztake__assume :
  forall (xs : list Z) hi,
    sublist 0 hi xs = ztake hi xs.
Proof. intros. reflexivity. Qed.

Lemma order_unassigned_post_members__assume :
  forall n v before_heap before_pos
         after_heap after_pos,
    order_unassigned_post n v before_heap before_pos after_heap after_pos ->
    heap_wf n (heap_of_lists before_heap before_pos) ->
    0 <= v < n ->
    incl before_heap after_heap /\ Znth v after_pos (-1) <> -1.
Proof.
  intros n v before_heap before_pos
    after_heap after_pos Hpost Hwf Hvrange.
  unfold order_unassigned_post in Hpost.
  destruct Hpost as (Hwfnew & Hcases).
  destruct Hcases as [[Hmissing Hperm] |
    [Hpresent [Hheap Hpos]]].
  - split.
    + intros x Hx.
      apply (Permutation_in x (Permutation_sym Hperm)).
      apply in_or_app. left. exact Hx.
    + apply (proj1 (heap_wf_in_iff n
        (heap_of_lists after_heap after_pos) v Hwfnew Hvrange)).
      apply (Permutation_in v (Permutation_sym Hperm)).
      apply in_or_app. right. simpl. auto.
  - subst after_heap after_pos.
    split; [apply incl_refl|exact Hpresent].
Qed.

Lemma solver_fp_rep_cancel_project__assume :
  forall s M level orderpos order root,
    solver_fp_rep s M |-- solver_fp_rep s
      (msolver_cancel_project M level orderpos order root).
Proof.
  intros.
  unfold solver_fp_rep, msolver_cancel_project, msolver_core_heap_update.
  simpl. cancel.
Qed.

(** ===== group: cancellation ===== *)

Lemma solver_shape_heap_project__canceluntil_cap :
  forall M orderpos order,
    solver_shape M ->
    Zlength orderpos = ms_size M ->
    solver_shape (msolver_heap_project M orderpos order).
Proof.
  intros M0 orderpos order Hshape Hlen.
  unfold solver_shape, msolver_heap_project, msolver_core_heap_update in *.
  simpl in *. tauto.
Qed.

Lemma solver_propagation_bound_le_qhead__canceluntil_cap :
  forall n F A_arr K M,
    solver_propagation_inv n F A_arr K M ->
    Znth 0 (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M).
Proof.
  intros n F A_arr K M Hinv.
  unfold solver_propagation_inv in Hinv.
  destruct K; destruct Hinv as [_ Hinv].
  - destruct Hinv as [Hweak Hprop _ _ _].
    unfold prop_level in Hprop.
    destruct (mt_lim (ms_core M)) as [|b rest] eqn:Hlim.
    + exact (proj1 (mtw_qhead_range (msw_trail_wf Hweak))).
    + inversion Hprop as [|b' rest' Hb Hrest]. simpl. exact Hb.
  - destruct Hinv as [Hweak Hprop _ _ _].
    unfold prop_level in Hprop.
    destruct (mt_lim (ms_core M)) as [|b rest] eqn:Hlim.
    + exact (proj1 (mtw_qhead_range (msa_trail_wf Hweak))).
    + inversion Hprop as [|b' rest' Hb Hrest]. simpl. exact Hb.
Qed.

Lemma solver_root_rebuild_strong__canceluntil_cap : forall n F M,
  solver_root_rebuild_ready n F M ->
  msolver_inv n F (@nil literal) (@nil literal) (msolver_set_root M 0).
Proof.
  intros n F M Hready.
  unfold solver_root_rebuild_ready in Hready.
  destruct Hready as [Hweak [Hlim [Hfront Hcovers]]].
  apply Zlength_nil_inv in Hlim.
  constructor.
  - exact Hweak.
  - unfold prop_level, msolver_set_root, msolver_core_heap_update. simpl.
    rewrite Hlim. constructor.
  - exact Hfront.
  - exact Hcovers.
  - unfold current_reasonless_earliest, msolver_set_root,
      msolver_core_heap_update. simpl. rewrite Hlim, Zlength_nil. simpl.
    intros d Hd. lia.
Qed.

Lemma clear_reason_fun_none_in__canceluntil_cap : forall ls r v,
  In v (map lit_var_c ls) -> clear_reason_fun ls r v = None.
Proof.
  induction ls as [|x ls IH]; intros r v Hin; simpl in *; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst v. destruct (List.in_dec Z.eq_dec (lit_var_c x)
      (map lit_var_c ls)) as [Hrest|Hrest].
    + apply IH. exact Hrest.
    + rewrite clear_reason_fun_notin by exact Hrest.
      apply sat_function_update_eq.
  - apply IH. exact Hin.
Qed.

Lemma stable_view_restrict__search :
  forall old new root,
    stable_view old -> restrict_above_level old new root ->
    0 <= root <= current_level old -> stable_view new.
Proof.
  intros old new root [Hground Hclosed] Hrestrict Hrootold.
  unfold restrict_above_level in Hrestrict.
  destruct Hrestrict as [Hcur [Hdb Hagree]].
  split.
  - unfold grounded_at in *. intros x b Hassign.
    pose proof (Hagree x) as Hxagree.
    destruct (level_of old x) as [d|] eqn:Hlev.
    + destruct (Z.leb d root) eqn:Hle.
      * apply Z.leb_le in Hle.
        destruct Hxagree as [Ha [Hl [Hr Hrank]]].
        destruct (Hground x b) as
          [d0 [rx [Holdlev [Holdrank Hreason]]]].
        { rewrite <- Ha. exact Hassign. }
        rewrite Hlev in Holdlev. inversion Holdlev; subst d0.
        exists d, rx. split; [ | split ].
        -- exact Hl.
        -- rewrite Hrank. exact Holdrank.
        -- destruct Hreason as [Hnone|[c [Hsome Hvalid]]].
           ++ left. rewrite Hr. exact Hnone.
           ++ right. exists c. split; [rewrite Hr; exact Hsome|].
              destruct Hvalid as
                [b0 [d0 [rx0 [Hax [Hlx [Hrx [Hin Hdeps]]]]]]].
              exists b0, d0, rx0.
              split; [exact (eq_trans Ha Hax)|].
              split; [congruence|].
              split; [exact (eq_trans Hrank Hrx)|].
              split; [exact Hin|].
              intros lit Hlmem Hvar.
              destruct (Hdeps lit Hlmem Hvar) as
                [Hfalse [dy [ry [Hly [Hry [Hyd Hrr]]]]]].
              specialize (Hagree (literal_var lit)).
              rewrite Hly in Hagree.
              assert (Hd0 : d0 = d) by congruence.
              assert (Hdy : dy <= root) by lia.
              assert (Hdyb : Z.leb dy root = true)
                by (apply Z.leb_le; exact Hdy).
              rewrite Hdyb in Hagree.
              destruct Hagree as [Hay [Hly' [Hreason' Hrank']]].
              split.
              ** destruct lit; unfold eval_partial_literal in *;
                   rewrite Hay; exact Hfalse.
              ** exists dy, ry. repeat split.
                 --- exact Hly'.
                 --- exact (eq_trans Hrank' Hry).
                 --- exact Hyd.
                 --- exact Hrr.
      * destruct Hxagree as [Hnone _]. rewrite Hnone in Hassign. discriminate.
    + destruct Hxagree as [Hnone _]. rewrite Hnone in Hassign. discriminate.
  - unfold closed_levels in *.
    destruct Hclosed as [Holdnonneg [Holdbound Holddec]].
    split; [rewrite Hcur; exact (proj1 Hrootold)|].
    split.
    + intros x b d Hassign Hlevel.
      specialize (Hagree x).
      destruct (level_of old x) as [d0|] eqn:Hlev.
      * destruct (Z.leb d0 root) eqn:Hle.
        -- apply Z.leb_le in Hle.
           destruct Hagree as [Ha [Hl [Hr Hrank]]].
           assert (Hassign_old : assignment old x = Some b).
           { rewrite <- Ha. exact Hassign. }
           rewrite Hl in Hlevel. inversion Hlevel; subst d.
           pose proof (Holdbound x b d0 Hassign_old Hlev) as Hbound.
           rewrite Hcur. lia.
        -- destruct Hagree as [Hnone _]. rewrite Hnone in Hassign. discriminate.
      * destruct Hagree as [Hnone _]. rewrite Hnone in Hassign. discriminate.
    + intros d Hd.
      assert (Hdold : 0 < d <= current_level old) by lia.
      destruct (Holddec d Hdold) as [x Hdecision].
      unfold decision_at in Hdecision.
      destruct Hdecision as [[b Hb] [Hlev Hnone]].
      destruct (level_of old x) as [d0|] eqn:Hlev0.
      * injection Hlev as Heq. subst d0.
        destruct (Z.leb d root) eqn:Hle.
        -- assert (HleZ : d <= root) by (apply Z.leb_le; exact Hle).
           specialize (Hagree x).
           rewrite Hlev0, Hle in Hagree.
           destruct Hagree as [Ha [Hl [Hr Hrank]]].
           exists x. unfold decision_at. split.
           ++ exists b. rewrite Ha. exact Hb.
           ++ split; [exact Hl|rewrite Hr; exact Hnone].
        -- apply Z.leb_gt in Hle. lia.
      * discriminate.
Qed.

Lemma stable_view_restrict_zero__canceluntil_cap : forall old new,
  stable_view old -> restrict_above_level old new 0 -> stable_view new.
Proof.
  intros old new Hstable Hrestrict.
  eapply stable_view_restrict__search with (root := 0);
    [exact Hstable | exact Hrestrict |].
  split; [lia | exact (proj1 (proj2 Hstable))].
Qed.

Lemma reasons_entailed_restrict :
  forall F old new root,
    reasons_entailed F old -> restrict_above_level old new root ->
    reasons_entailed F new.
Proof.
  intros F old new root Hold [_ [_ Hagree]] x c Hsome.
  specialize (Hagree x).
  destruct (level_of old x) as [d|] eqn:Hlev.
  - destruct (Z.leb d root) eqn:Hle.
    + destruct Hagree as [_ [_ [Hr _]]]. apply (Hold x c). rewrite <- Hr. exact Hsome.
    + destruct Hagree as [_ [_ [Hr _]]]. rewrite Hr in Hsome. discriminate.
  - destruct Hagree as [_ [_ [Hr _]]]. rewrite Hr in Hsome. discriminate.
Qed.

Lemma reasons_var_injective_restrict :
  forall old new root,
    reasons_var_injective old -> restrict_above_level old new root ->
    reasons_var_injective new.
Proof.
  intros old new root Hold [_ [_ Hagree]] x c Hsome.
  specialize (Hagree x).
  destruct (level_of old x) as [d|] eqn:Hlev.
  - destruct (Z.leb d root) eqn:Hle.
    + destruct Hagree as [_ [_ [Hr _]]]. apply (Hold x c). rewrite <- Hr. exact Hsome.
    + destruct Hagree as [_ [_ [Hr _]]]. rewrite Hr in Hsome. discriminate.
  - destruct Hagree as [_ [_ [Hr _]]]. rewrite Hr in Hsome. discriminate.
Qed.

Lemma reasons_match_cancel__canceluntil_cap :
  forall n t db words r level,
    mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
    Zlength words = n -> reasons_match n t db words r ->
    reasons_match n (mt_cancel t level) db
      (clear_vars (zdrop (Znth level (mt_lim t) 0) (mt_trail t)) words)
      (clear_reason_fun
        (zdrop (Znth level (mt_lim t) 0) (mt_trail t)) r).
Proof.
  intros n t db words r level Hwf Hlevel Hwords Hmatch v Hv.
  set (suffix := zdrop (Znth level (mt_lim t) 0) (mt_trail t)).
  assert (Hrange : forall x, In x suffix ->
    0 <= lit_var_c x < Zlength words).
  { intros x Hx. rewrite Hwords. apply lit_var_c_in_range.
    pose proof (mtw_trail_lits Hwf) as Hlits.
    rewrite Forall_forall in Hlits.
    apply Hlits. apply In_zdrop in Hx. exact Hx. }
  specialize (Hmatch v Hv).
  destruct (List.in_dec Z.eq_dec v (map lit_var_c suffix)) as [Hin|Hnot].
  - unfold reason_word_ok.
    rewrite (clear_vars_in suffix words v);
      [ | rewrite Hwords; exact Hv | exact Hrange | exact Hin ].
    rewrite clear_reason_fun_none_in__canceluntil_cap by exact Hin.
    reflexivity.
  - rewrite (clear_vars_notin suffix words v);
      [ | rewrite Hwords; exact Hv | exact Hrange | exact Hnot ].
    rewrite clear_reason_fun_notin by exact Hnot.
    assert (Hcell : Znth v (clear_vars suffix (mt_assigns t)) 0 =
      Znth v (mt_assigns t) 0).
    { apply clear_vars_notin.
      - rewrite (mtw_assigns_len Hwf). exact Hv.
      - intros x Hx. rewrite (mtw_assigns_len Hwf), <- Hwords.
        apply Hrange. exact Hx.
      - exact Hnot. }
    unfold suffix in Hcell.
    unfold reason_word_ok in *.
    cbn [mt_assigns mt_cancel]. rewrite Hcell.
    replace (trail_lit_of (mt_cancel t level) v) with (trail_lit_of t v).
    + exact Hmatch.
    + unfold trail_lit_of. rewrite mt_cancel_assigns.
      cbn [mt_assigns mt_cancel].
      rewrite Hcell. reflexivity.
Qed.

Lemma msolver_view_cancel_project__canceluntil_cap :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    msolver_view n
      (msolver_set_root
        (msolver_cancel_project M level orderpos order root) 0) =
    view_of n (mt_cancel (ms_core M) level) (ms_reason_of M)
      (msolver_clauses M).
Proof. unfold msolver_set_root. msat_view_cancel_project. Qed.

Lemma db_complete_cancel_project__canceluntil_cap :
  forall n F M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    db_complete F M ->
    db_complete F
      (msolver_set_root
        (msolver_cancel_project M level orderpos order root) 0).
Proof. msat_db_complete_cancel_project. Qed.

Lemma solver_shape_cancel_project__search :
  forall n M level orderpos order root,
    solver_shape M -> mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    heap_wf (ms_size M) (heap_of_lists order orderpos) ->
    0 <= root ->
    solver_shape
      (msolver_cancel_project M level orderpos order root).
Proof.
  intros n M level orderpos order root
    Hshape Htrail Hlevel Hheap Hroot_nonneg.
  pose proof (mtrail_wf_cancel n (ms_core M) level Htrail Hlevel)
    as Htrail'.
  pose proof (lim_lt_trail n (ms_core M) level Htrail Hlevel) as Hbound.
  pose proof (heap_wf_orderpos_length (ms_size M)
    (heap_of_lists order orderpos) Hheap) as Hopos.
  unfold solver_shape, msolver_cancel_project,
    msolver_core_heap_update, heap_of_lists in *.
  simpl in *.
  destruct Hshape as
    (Hs & Hcap0 & Htwice & Hass & Hlevels & Hreasons & Holdopos & Hact &
     Htags & Htrail_len & Hq & Hpending & Hflag & Hflag1 & Hqt & Hwm &
     Hbinary_lits & Hstats & Hroot & Hbinary & Heven).
  repeat split; try assumption; try lia.
  - rewrite Zlength_clear_vars. exact Hass.
  - rewrite Zlength_clear_vars. exact Hreasons.
  - rewrite Zlength_ztake by lia. reflexivity.
Qed.

Lemma solver_shape_cancel_project__canceluntil_cap :
  forall n M level orderpos order root,
    solver_shape M -> mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    heap_wf (ms_size M) (heap_of_lists order orderpos) ->
    solver_shape
      (msolver_set_root
        (msolver_cancel_project M level orderpos order root) 0).
Proof.
  intros n M level orderpos order root
    Hshape Htrail Hlevel Hheap.
  exact (solver_shape_cancel_project__search n M level orderpos order 0
    Hshape Htrail Hlevel Hheap (Z.le_refl 0)).
Qed.

Lemma reason_head_ok_cancel_project__canceluntil_cap :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    Zlength (ms_reason_words M) = n ->
    n = ms_size M ->
    reason_head_ok M ->
    reason_head_ok
      (msolver_set_root
        (msolver_cancel_project M level orderpos order root) 0).
Proof. unfold msolver_set_root. msat_reason_head_ok_cancel_project. Qed.

Lemma binary_reason_same_level_cancel_proj__canceluntil_cap :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    Zlength (ms_reason_words M) = n ->
    n = ms_size M ->
    binary_reason_same_level M ->
    binary_reason_same_level
      (msolver_set_root
        (msolver_cancel_project M level orderpos order root) 0).
Proof. unfold msolver_set_root. msat_binary_reason_cancel_project. Qed.

(** Cancel to level zero and reseed the heap in either propagation context.
    Root fields follow from the cancelled trail; persistent fields transport
    unchanged. Both cases conclude the weak invariant at root zero. *)
Lemma msolver_inv_ctx_cancel_zero__canceluntil_cap :
  forall n F A_arr K M orderpos order,
    msolver_inv_ctx n F A_arr K M ->
    0 < Zlength (mt_lim (ms_core M)) ->
    heap_wf (ms_size M) (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M))
      (Znth 0 (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    msolver_inv_weak n F (@nil literal) (@nil literal)
      (msolver_set_root
        (msolver_cancel_project M 0 orderpos order
          (ms_root_level M)) 0).
Proof.
  intros n F A_arr K M orderpos order Hinv Hlim Hheap Hincl Hre.
  assert (Hlevel : 0 <= 0 < Zlength (mt_lim (ms_core M))) by lia.
  destruct (msolver_inv_ctx_core_facts n F A_arr K M Hinv) as [Hsize [Htrail _]].
  pose proof (mtrail_wf_cancel n (ms_core M) 0 Htrail Hlevel) as Htrail'.
  pose proof (view_of_cancel n (ms_core M) (ms_reason_of M)
    (msolver_clauses M) 0 Htrail Hlevel) as Hrestrict.
  assert (Hwords : Zlength (ms_reason_words M) = n).
  { destruct K as [A_inst|A_proc]; cbn in Hinv;
      [pose proof (msw_shape Hinv) as Hshape
      |pose proof (msa_shape Hinv) as Hshape];
      unfold solver_shape in Hshape; rewrite Hsize; tauto. }
  destruct K as [A_inst|A_proc]; cbn in Hinv; destruct Hinv; constructor.
  (* Each changed record field has one predicate-directed proof. *)
  all: lazymatch goal with
       | |- solver_shape _ =>
           apply (solver_shape_cancel_project__canceluntil_cap
             n M 0 orderpos order (ms_root_level M));
             [assumption|exact Htrail|exact Hlevel|exact Hheap]
       | |- mtrail_wf _ _ => exact Htrail'
       | |- Zlength (mt_lim _) <= _ =>
           simpl; rewrite Zlength_ztake by lia; assumption
       | |- 0 <= _ <= Zlength (mt_lim _) =>
           simpl; rewrite Zlength_ztake by lia; lia
       | |- Forall _ (@nil literal) => constructor
       | |- decisions_upto _ _ = _ => unfold decisions_upto; simpl; reflexivity
       | |- (exists _, decisions_upto _ _ = _ /\ incl _ _) =>
           exists (@nil literal); split;
             [unfold decisions_upto; simpl; reflexivity|apply incl_refl]
       | |- incl _ _ => apply incl_refl
       | |- stable_view _ =>
           rewrite (msolver_view_cancel_project__canceluntil_cap
             n M 0 orderpos order (ms_root_level M) Htrail Hlevel);
           apply stable_view_restrict_zero__canceluntil_cap with
             (old := msolver_view n M); [assumption|exact Hrestrict]
       | |- reasons_entailed _ _ =>
           rewrite (msolver_view_cancel_project__canceluntil_cap
             n M 0 orderpos order (ms_root_level M) Htrail Hlevel);
           apply reasons_entailed_restrict with
             (old := msolver_view n M) (root := 0); [assumption|exact Hrestrict]
       | |- reasons_var_injective _ =>
           rewrite (msolver_view_cancel_project__canceluntil_cap
             n M 0 orderpos order (ms_root_level M) Htrail Hlevel);
           apply reasons_var_injective_restrict with
             (old := msolver_view n M) (root := 0); [assumption|exact Hrestrict]
       | |- trail_implied _ _ =>
           apply (trail_implied_cancel n F (ms_core M) 0);
             [exact Htrail|exact Hlevel|assumption]
       | |- db_complete _ _ =>
           apply (db_complete_cancel_project__canceluntil_cap
             n F M 0 orderpos order (ms_root_level M));
             [exact Htrail|exact Hlevel|assumption]
       | |- reasons_match _ _ _ _ _ =>
           simpl; apply reasons_match_cancel__canceluntil_cap;
             [exact Htrail|exact Hlevel|exact Hwords|assumption]
       | |- reason_head_ok _ =>
           apply (reason_head_ok_cancel_project__canceluntil_cap
             n M 0 orderpos order (ms_root_level M));
             [exact Htrail|exact Hlevel|exact Hwords|exact Hsize|assumption]
       | |- binary_reason_same_level _ =>
           apply (binary_reason_same_level_cancel_proj__canceluntil_cap
             n M 0 orderpos order (ms_root_level M));
             [exact Htrail|exact Hlevel|exact Hwords|exact Hsize|assumption]
       | |- heap_wf _ _ => simpl; rewrite Hsize; exact Hheap
       | _ => simpl; assumption
       end.
Qed.

Lemma minisat_processed_cancel_sub__canceluntil_cap :
  forall n t level l,
    mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
    Znth level (mt_lim t) 0 <= mt_qhead t ->
    minisat_processed n (mt_assigns (mt_cancel t level))
      (mt_trail (mt_cancel t level)) (mt_qhead (mt_cancel t level)) l ->
    minisat_processed n (mt_assigns t) (mt_trail t) (mt_qhead t) l.
Proof.
  intros n t level l Hwf Hlevel Hbound
    [packed [Hpacked [Hden [Htrue [i [Hi Hlit]]]]]].
  exists packed. split; [exact Hpacked|]. split; [exact Hden|].
  split.
  - pose proof (mtw_trail_true Hwf) as Htrailtrue.
    rewrite Forall_forall in Htrailtrue. apply Htrailtrue.
    rewrite mt_cancel_qhead in Hi. rewrite mt_cancel_trail in Hlit.
    pose proof (lim_lt_trail n t level Hwf Hlevel) as Hb.
    rewrite Znth_ztake in Hlit by lia.
    rewrite <- Hlit. apply Znth_In. lia.
  - exists i. split.
    + rewrite mt_cancel_qhead in Hi. lia.
    + rewrite mt_cancel_qhead in Hi. rewrite mt_cancel_trail in Hlit.
      rewrite Znth_ztake in Hlit by lia. exact Hlit.
Qed.

Lemma minisat_watch_frontier_cancel__canceluntil_cap :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    Znth level (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M) ->
    minisat_watch_frontier n (msolver_db M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) ->
    minisat_watch_frontier n
      (msolver_db
        (msolver_set_root
          (msolver_cancel_project M level orderpos order root) 0))
      (mt_assigns (ms_core
        (msolver_cancel_project M level orderpos order root)))
      (mt_trail (ms_core
        (msolver_cancel_project M level orderpos order root)))
      (mt_qhead (ms_core
        (msolver_cancel_project M level orderpos order root))).
Proof.
  intros n M level orderpos order root Hwf Hlevel Hbound Hfront.
  unfold minisat_watch_frontier in *.
  unfold msolver_set_root, msolver_cancel_project, msolver_core_heap_update,
    msolver_db in *; simpl in *.
  apply watch_frontier_shrink with
    (Pold := minisat_processed n (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M))).
  - exact Hfront.
  - intros l Hl. apply (minisat_processed_cancel_sub__canceluntil_cap
      n (ms_core M) level l Hwf Hlevel Hbound). exact Hl.
Qed.

Lemma heap_covers_cancel_project__canceluntil_cap :
  forall n M level orderpos order,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    Znth level (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M) ->
    heap_wf n (msolver_heap M) ->
    heap_wf n (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M))
      (Znth level (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    heap_covers n (heap_of_lists order orderpos)
      (mt_assigns (mt_cancel (ms_core M) level))
      (mt_trail (mt_cancel (ms_core M) level))
      (mt_qhead (mt_cancel (ms_core M) level)).
Proof.
  intros n M level orderpos order Hwf Hlevel Hbound
    Hheap_old Hheap_new Hincl Hcovers Hre.
  set (bound := Znth level (mt_lim (ms_core M)) 0).
  set (suffix := zdrop bound (mt_trail (ms_core M))).
  pose proof (lim_lt_trail n (ms_core M) level Hwf Hlevel) as Hboundrange.
  pose proof (mtw_qhead_range Hwf) as Hqrange.
  assert (Hsuffix_range : forall x, In x suffix -> 0 <= lit_var_c x < n).
  { intros x Hx. apply lit_var_c_in_range.
    pose proof (mtw_trail_lits Hwf) as Hlits.
    rewrite Forall_forall in Hlits. apply Hlits.
    unfold suffix in Hx. apply In_zdrop in Hx. exact Hx. }
  assert (Hsplit : bound + Zlength suffix = Zlength (mt_trail (ms_core M))).
  { assert (Hlen : Zlength
        (ztake bound (mt_trail (ms_core M)) ++
         zdrop bound (mt_trail (ms_core M))) =
        Zlength (mt_trail (ms_core M))).
    { rewrite ztake_zdrop. reflexivity. }
    rewrite Zlength_app, Zlength_ztake in Hlen by lia.
    unfold suffix. lia. }
  assert (Hdist : forall i j,
    0 <= i < Zlength (mt_trail (ms_core M)) ->
    0 <= j < Zlength (mt_trail (ms_core M)) ->
    lit_var_c (Znth i (mt_trail (ms_core M)) 0) =
      lit_var_c (Znth j (mt_trail (ms_core M)) 0) -> i = j).
  { intros i j Hi Hj Heq.
    change (trail_var (ms_core M) i = trail_var (ms_core M) j) in Heq.
    pose proof (trail_pos_of_index (ms_core M) i (mtw_trail_nodup Hwf) Hi)
      as Hpi.
    pose proof (trail_pos_of_index (ms_core M) j (mtw_trail_nodup Hwf) Hj)
      as Hpj.
    rewrite Heq, Hpj in Hpi. inversion Hpi.
    apply Z2Nat.inj; lia. }
  assert (Hcancel : forall v,
    0 <= v < n ->
    Znth v (mt_assigns (mt_cancel (ms_core M) level)) 0 = 0 ->
    Znth v (mt_assigns (ms_core M)) 0 <> 0 ->
    exists i, bound <= i < Zlength (mt_trail (ms_core M)) /\
      lit_var_c (Znth i (mt_trail (ms_core M)) 0) = v).
  { intros v Hv Hnew Hold.
    assert (Hin : In v (map lit_var_c suffix)).
    { destruct (List.in_dec Z.eq_dec v (map lit_var_c suffix)) as [Hin|Hnot];
        [exact Hin|exfalso].
      assert (Heq : Znth v (clear_vars suffix (mt_assigns (ms_core M))) 0 =
        Znth v (mt_assigns (ms_core M)) 0).
      { apply clear_vars_notin.
        - rewrite (mtw_assigns_len Hwf). exact Hv.
        - intros x Hx. rewrite (mtw_assigns_len Hwf).
          apply Hsuffix_range. exact Hx.
        - exact Hnot. }
      rewrite mt_cancel_assigns in Hnew. unfold suffix, bound in Heq.
      rewrite Heq in Hnew. contradiction. }
    apply in_map_iff in Hin. destruct Hin as [x [Hvx Hxin]].
    destruct (In_Znth_ex Z suffix 0 x Hxin) as [j [Hj Hjx]].
    exists (bound + j). split; [lia|].
    rewrite <- (Znth_zdrop bound (mt_trail (ms_core M)) j 0) by lia.
    unfold suffix in Hjx. rewrite Hjx. exact Hvx. }
  assert (Hraw : heap_covers n (heap_of_lists order orderpos)
    (mt_assigns (mt_cancel (ms_core M) level))
    (mt_trail (ms_core M)) bound).
  { eapply heap_covers_cancel with
      (h := msolver_heap M)
      (qhead := mt_qhead (ms_core M))
      (qtail := Zlength (mt_trail (ms_core M))).
    - exact Hcovers.
    - exact (conj (proj1 Hboundrange) Hbound).
    - exact (proj2 Hqrange).
    - exact Hdist.
    - exact Hcancel.
    - exact Hre.
    - intros v Hv Hmissing.
      eapply heap_wf_incl_missing_mono;
        [exact Hheap_old|exact Hheap_new| |exact Hv|exact Hmissing].
      exact Hincl. }
  unfold heap_covers in *.
  intros v Hv Hmissing. destruct (Hraw v Hv Hmissing) as [Hassigned [i [Hi Hvar]]].
  split; [exact Hassigned|]. exists i. split.
  - rewrite mt_cancel_qhead. exact Hi.
  - rewrite mt_cancel_trail, Znth_ztake by lia. exact Hvar.
Qed.

Lemma msolver_inv_weak_root_empty_core : forall n F M,
  n = ms_size M ->
  0 <= n ->
  solver_shape M ->
  cnf_wf n F ->
  mtrail_wf n (ms_core M) ->
  Zlength (mt_lim (ms_core M)) <= n ->
  stable_view (msolver_view n M) ->
  reasons_entailed F (msolver_view n M) ->
  reasons_var_injective (msolver_view n M) ->
  trail_implied F (ms_core M) ->
  db_wf n (msolver_db M) ->
  db_matches_cnf F M ->
  db_implied F M ->
  db_complete F M ->
  learnt_db (ms_learnt M) ->
  prob_db (ms_prob M) ->
  ~ In (ms_binary M) (map fst (msolver_db M)) ->
  reasons_match n (ms_core M) (msolver_db M) (ms_reason_words M)
    (ms_reason_of M) ->
  reason_head_ok M ->
  binary_reason_same_level M ->
  wmap_exact n (msolver_db M) (ms_wm M) ->
  solver_tags_clear M ->
  heap_wf n (msolver_heap M) ->
  msat_fp32_nonnegative (ms_cla_inc M) ->
  msolver_seed_ok M ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  msolver_inv_weak n F (@nil literal) (@nil literal)
    (msolver_set_root M 0).
Proof.
  intros n F M Hsize_c Hnrange_c Hshape_c HFwf_c Htrailwf_c Hlevelb_c
    Hstable_c Hrent_c Hrinj_c Htimpl_c Hdbwf_c Hdbm_c Hdbi_c Hdbc_c
    Hlearnt_c Hprob_c Hbinout_c Hrmem_c Hrhead_c Hrbin_c Hwmap_c Htags_c
    Hheap_c Hclainc_c Hseed_c Hlim.
  refine {|
    msw_size := _; msw_n_range := Hnrange_c; msw_shape := _;
    msw_F_wf := HFwf_c; msw_A_wf := _; msw_trail_wf := _;
    msw_level_bound := _; msw_root_range := _; msw_assumptions := _;
    msw_assump_incl := _; msw_assump_sat := _; msw_stable := _;
    msw_reasons_ent := _; msw_reasons_inj := _; msw_trail_impl := _;
    msw_db_wf := _; msw_db_matches := _; msw_db_implied := _;
    msw_db_complete := _; msw_learnt_db := _; msw_prob_db := _;
    msw_binary_out := _; msw_reasons_mem := _; msw_reason_head := _;
    msw_reason_bin := _; msw_wmap_exact := _; msw_tags_clear := _;
    msw_heap_wf := _; msw_cla_inc_nonnegative := _; msw_seed := _ |}.
  - simpl. exact Hsize_c.
  - pose proof Hshape_c as Hshape.
    unfold solver_shape, msolver_set_root, msolver_core_heap_update in *.
    simpl in *.
    destruct Hshape as
      (Hs & Hcap & Htwice & Hass & Hlevels & Hreasons & Hopos & Hact &
       Htags & Htrail & Hq & Hpending & Hflag & Hflag1 & Hqt & Hwm &
       Hbinary_lits & Hstats & Hroot & Hbinary & Heven).
    repeat split; try assumption; try lia.
  - constructor.
  - simpl. exact Htrailwf_c.
  - simpl. exact Hlevelb_c.
  - simpl. rewrite Hlim. lia.
  - unfold decisions_upto. simpl. reflexivity.
  - apply incl_refl.
  - constructor.
  - simpl. exact Hstable_c.
  - simpl. exact Hrent_c.
  - simpl. exact Hrinj_c.
  - simpl. exact Htimpl_c.
  - simpl. exact Hdbwf_c.
  - simpl. exact Hdbm_c.
  - simpl. exact Hdbi_c.
  - simpl. exact Hdbc_c.
  - simpl. exact Hlearnt_c.
  - simpl. exact Hprob_c.
  - simpl. exact Hbinout_c.
  - simpl. exact Hrmem_c.
  - simpl. exact Hrhead_c.
  - simpl. exact Hrbin_c.
  - simpl. exact Hwmap_c.
  - simpl. exact Htags_c.
  - simpl. exact Hheap_c.
  - simpl. exact Hclainc_c.
  - simpl. exact Hseed_c.
Qed.

Lemma msolver_inv_ctx_root_empty__canceluntil_cap :
  forall n F A_arr K M,
    msolver_inv_ctx n F A_arr K M ->
    Zlength (mt_lim (ms_core M)) = 0 ->
    msolver_inv_weak n F (@nil literal) (@nil literal)
      (msolver_set_root M 0).
Proof.
  intros n F A_arr K M H Hlim. destruct K as [A_inst|A_proc]; cbn in H;
    destruct H; apply msolver_inv_weak_root_empty_core; assumption.
Qed.

Lemma solver_propagation_root_ready_empty__canceluntil_cap :
  forall n F A_arr K M,
    solver_propagation_inv n F A_arr K M ->
    Zlength (mt_lim (ms_core M)) = 0 ->
    heap_covers (ms_size M) (msolver_heap M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) ->
    solver_root_rebuild_ready n F M.
Proof.
  intros n F A_arr K M Hinv Hlim Hcovers.
  pose proof (msolver_inv_ctx_of_propagation n F A_arr K M Hinv) as Hctx.
  destruct (msolver_inv_ctx_core_facts n F A_arr K M Hctx) as [Hsize _].
  destruct (propagation_inv_context_facts__analyze n F A_arr K M Hinv)
    as [_ [_ [Hfront _]]].
  assert (Hcovers_n : heap_covers n (msolver_heap M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M)))
    by (rewrite Hsize; exact Hcovers).
  split.
  - apply msolver_inv_ctx_root_empty__canceluntil_cap with
      (A_arr := A_arr) (K := K); assumption.
  - split; [exact Hlim|]. split.
    + simpl. exact Hfront.
    + exact Hcovers_n.
Qed.

Lemma solver_propagation_cancel_root_ready__canceluntil_cap :
  forall n F A_arr K M orderpos order,
    solver_propagation_inv n F A_arr K M ->
    0 < Zlength (mt_lim (ms_core M)) ->
    heap_wf (ms_size M) (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    heap_covers (ms_size M) (msolver_heap M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M)) (Znth 0 (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    solver_root_rebuild_ready n F
      (msolver_cancel_project M 0 orderpos order (ms_root_level M)).
Proof.
  intros n F A_arr K M orderpos order Hinv Hlim
    Hheap Hincl Hcovers Hre.
  pose proof (solver_propagation_bound_le_qhead__canceluntil_cap
    n F A_arr K M Hinv) as Hbound.
  pose proof (msolver_inv_ctx_of_propagation n F A_arr K M Hinv) as Hctx.
  destruct (msolver_inv_ctx_core_facts n F A_arr K M Hctx)
    as [Hsize [Htrail Hheap_old]].
  destruct (propagation_inv_context_facts__analyze n F A_arr K M Hinv)
    as [_ [_ [Hfront _]]].
  assert (Hlevel : 0 <= 0 < Zlength (mt_lim (ms_core M))) by lia.
  assert (Hheap_new : heap_wf n (heap_of_lists order orderpos))
    by (rewrite Hsize; exact Hheap).
  assert (Hcovers_n : heap_covers n (msolver_heap M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M)))
    by (rewrite Hsize; exact Hcovers).
  split.
  - apply msolver_inv_ctx_cancel_zero__canceluntil_cap with
      (A_arr := A_arr) (K := K); assumption.
  - split.
    + simpl. reflexivity.
    + split.
      * apply (minisat_watch_frontier_cancel__canceluntil_cap
          n M 0 orderpos order (ms_root_level M)); assumption.
      * simpl. apply (heap_covers_cancel_project__canceluntil_cap
          n M 0 orderpos order); assumption.
Qed.

(** ===== group: clause installation and recording ===== *)

(** A successful learned-clause installation already carries the current
    strong invariant.  The only additional record-side fact not stored in the
    transition is the drained-queue equality. *)
Lemma clause_new_success_record_allocated__prep_pub_cap_exit :
  forall n F A_arr A_inst entry words c current,
    2 <= Zlength words ->
    mt_qhead (ms_core entry) = ms_qtail entry ->
    clause_new_success_transition n F A_arr A_inst entry words c current ->
    record_allocated n F A_arr A_inst entry words c current.
Proof.
  intros n F A_arr A_inst entry words c current Hlen Hq Hsuccess.
  pose proof Hsuccess as Hsuccess0.
  destruct Hsuccess as [Hfresh [-> [Hinv [Hpending [Hseed Hcert]]]]].
  destruct Hfresh as [Hcpos [Heven [Hbinary Hnotin]]].
  assert (Hcne : c <> 0) by lia.
  unfold record_allocated.
  split.
  - right. split; [exact Hlen |]. split; [exact Hcne |]. exact Hsuccess0.
  - split; [exact Hcert |].
    split; [exact Hinv |].
    split; [cbn; exact Hq |].
    split; [exact Hpending |].
    split; [exact Hseed | reflexivity].
Qed.

(** ===== group: solver_record ===== *)
Lemma solver_shape_with_cla_inc_stats__record :
  forall M cla_inc stats,
    solver_shape M ->
    Zlength stats = 11 ->
    solver_shape (msolver_with_cla_inc_stats M cla_inc stats).
Proof.
  intros M cla_inc stats Hshape Hstats.
  unfold solver_shape, msolver_with_cla_inc_stats in *. cbn in *. tauto.
Qed.

Lemma msolver_inv_with_cla_inc_stats__record :
  forall n F A_arr A_inst M cla_inc stats,
    msolver_inv n F A_arr A_inst M ->
    msat_fp32_nonnegative cla_inc ->
    Zlength stats = 11 ->
    msolver_inv n F A_arr A_inst
      (msolver_with_cla_inc_stats M cla_inc stats).
Proof.
  intros n F A_arr A_inst M cla_inc stats Hinv Hcla Hstats.
  destruct Hinv as [Hweak Hprop Hfront Hheap Hreason].
  constructor; cbn.
  - destruct Hweak; constructor; cbn in *; try assumption.
    apply solver_shape_with_cla_inc_stats__record;
      assumption.
  - exact Hprop.
  - exact Hfront.
  - exact Hheap.
  - exact Hreason.
Qed.

Lemma record_stats_update_length__record :
  forall words stats,
    Zlength (record_stats_update words stats) = Zlength stats.
Proof.
  intros words stats.
  unfold record_stats_update, stats_set_learnts, stats_set_learnts_literals.
  rewrite !Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma record_stats_update_explicit__record :
  forall words stats,
    Zlength stats = 11 ->
    record_stats_update words stats =
      [stats_starts stats; stats_decisions stats; stats_propagations stats;
       stats_inspects stats; stats_conflicts stats; stats_clauses stats;
       stats_clauses_literals stats;
       MiniSatTarget.lo64 (stats_learnts stats + 1);
       MiniSatTarget.lo64 (stats_learnts_literals stats + Zlength words);
       stats_max_literals stats; stats_tot_literals stats].
Proof.
  intros words stats Hlen.
  rewrite Zlength_correct in Hlen.
  destruct stats as [|a0 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a1 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a2 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a3 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a4 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a5 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a6 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a7 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a8 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a9 stats]; [cbn in Hlen; lia|].
  destruct stats as [|a10 stats]; [cbn in Hlen; lia|].
  destruct stats as [|extra stats].
  - cbn [record_stats_update replace_Znth Znth]. reflexivity.
  - cbn in Hlen. lia.
Qed.

Lemma solver_record_finish_refold__record :
  forall s M lvl words cla_inc wl,
    Vecp.rep &(s # "solver_t" ->ₛ "learnts")
      (db_words (ms_learnt M)) **
    clause_db_rep (ms_learnt M) **
    &(s # "solver_t" ->ₛ "cla_inc") # Float |-> cla_inc **
    &(s # "solver_t" ->ₛ "stats" .ₛ "learnts") # UInt64
      |-> MiniSatTarget.lo64 (stats_learnts (ms_stats M) + 1) **
    &(s # "solver_t" ->ₛ "stats" .ₛ "learnts_literals") # UInt64
      |-> MiniSatTarget.lo64 (stats_learnts_literals (ms_stats M) + Zlength words) **
    solver_record_finish_frame_at s M lvl wl
    |-- solver_rep_levels_wl_at s
      (msolver_with_cla_inc_stats M cla_inc
        (record_stats_update words (ms_stats M))) wl lvl.
Proof.
  intros s M lvl words cla_inc wl.
  unfold solver_record_finish_frame_at.
  Intros act asg opos rsn trl tgs.
  assert (Hstats : Zlength (ms_stats M) = 11).
  { unfold solver_shape in H. tauto. }
  pose proof
    (record_stats_update_explicit__record
       words (ms_stats M) Hstats) as Hupdate.
  assert (Hshape' :
    solver_shape
      (msolver_with_cla_inc_stats M cla_inc
        (record_stats_update words (ms_stats M)))).
  { apply solver_shape_with_cla_inc_stats__record.
    - exact H.
    - rewrite Hupdate. reflexivity. }
  rewrite Hupdate in Hshape'.
  unfold solver_rep_levels_wl_at.
  Exists act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_fp_rep,
    solver_vecs_rep, solver_ptrs_rep, solver_var_arrays_rep,
    solver_trail_array_rep, stats_record_frame, stats_rep.
  rewrite Hupdate.
  unfold stats_starts, stats_decisions, stats_propagations,
    stats_inspects, stats_conflicts, stats_clauses, stats_clauses_literals,
    stats_learnts, stats_learnts_literals, stats_max_literals, stats_tot_literals.
  unfold msolver_with_cla_inc_stats.
  unfold solver_levels_slice_at.
  cbn [Znth ms_size ms_cap ms_qtail ms_capacity_pending_qhead
    ms_capacity_root_propagation_pending ms_core ms_root_level
    ms_reason_words ms_reason_of ms_prob ms_learnt ms_binary ms_binary_lits ms_wm ms_activity
    ms_orderpos ms_order ms_model
    ms_tags ms_tagged ms_stack ms_var_inc
    ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress
    ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats].
  repeat (rewrite Znth0_cons || rewrite Znth_cons by lia).
  unfold db_words.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  all: try exact Hshape'.
  csimpl.
  msat_entailer_with lia.
Qed.

Lemma clause_new_success_installs_word__record :
  forall n F A_arr A_inst entry words c current,
    clause_new_success_transition n F A_arr A_inst
      entry words c current ->
    In c (db_words (ms_learnt current)).
Proof.
  intros n F A_arr A_inst entry words c current Htrans.
  destruct Htrans as
    [Hfresh [Hcurrent [Hinv [Hpending [Hseed Hcert]]]]].
  subst current.
  unfold msolver_install_learnt_clause, db_words.
  cbn [msolver_propagation_overlay msolver_propagation_update ].
  change (In c
    (map fst
      (ms_learnt entry ++
       [(c, {| co_lits := words; co_learnt := true |})]))).
  rewrite map_app.
  apply in_or_app. right. simpl. auto.
Qed.

Lemma record_allocated_enqueue_input__record :
  forall n F A_arr A_inst entry words c current,
    record_allocated n F A_arr A_inst entry words c current ->
    enqueue_input (ms_size current) (Znth 0 words 0)
      (ms_qtail current) (mt_assigns (ms_core current))
      (mt_levels (ms_core current)) (ms_reason_words current)
      (mt_trail (ms_core current)).
Proof.
  intros n F A_arr A_inst entry words c current Halloc.
  destruct Halloc as
    [Hkind [Hcert [Hinv [Hqhead [Hpending [Hseed Hmodel]]]]]].
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as
    [Hwordslen [Hwordswf [Hwordsnd [Hentailed [Hfresh [Hfalse Hroot]]]]]].
  pose proof (msi_weak Hinv) as Hweak.
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_trail_wf Hweak) as Htrailwf.
  assert (Hheadwf : lit_wf_c n (Znth 0 words 0)).
  { apply (Forall_Znth_elim _ _ _ 0 0 Hwordswf). lia. }
  assert (Hv : 0 <= lit_var_c (Znth 0 words 0) < n).
  { apply lit_var_c_in_range. exact Hheadwf. }
  assert (Hnotin : ~ In (lit_var_c (Znth 0 words 0))
                           (map lit_var_c (mt_trail (ms_core current)))).
  { intro Hin.
    pose proof
      (proj2 (mtw_assigned_iff Htrailwf
        (lit_var_c (Znth 0 words 0)) Hv) Hin) as Hassigned.
    contradiction. }
  assert (Hnd : NoDup
    (lit_var_c (Znth 0 words 0) ::
      map lit_var_c (mt_trail (ms_core current)))).
  { constructor; [exact Hnotin|exact (mtw_trail_nodup Htrailwf)]. }
  assert (Hall : forall x,
    In x (lit_var_c (Znth 0 words 0) ::
      map lit_var_c (mt_trail (ms_core current))) -> 0 <= x < n).
  { intros x Hmem. destruct Hmem as [Hx|Hin].
    - subst x. exact Hv.
    - apply in_map_iff in Hin. destruct Hin as [l [<- Hin]].
    apply lit_var_c_in_range.
    pose proof (mtw_trail_lits Htrailwf) as Htlits.
    rewrite Forall_forall in Htlits.
    apply Htlits. exact Hin. }
  pose proof
    (NoDup_Z_bounded_length
      (lit_var_c (Znth 0 words 0) ::
       map lit_var_c (mt_trail (ms_core current)))
      n (msw_n_range Hweak) Hnd Hall) as Hroom.
  assert (Hqroom : ms_qtail current < n).
  { rewrite <- Zlength_correct in Hroom.
    rewrite Zlength_cons, Zlength_map_Z in Hroom.
    unfold solver_shape in Hshape. lia. }
  assert (Hcells : Forall (fun x => -1 <= x <= 1)
      (mt_assigns (ms_core current))).
  { eapply Forall_impl; [|exact (mtw_cells Htrailwf)].
    intros x Hx. unfold lbool_cell in Hx. lia. }
  assert (Hheadwf_current : lit_wf_c (ms_size current) (Znth 0 words 0)).
  { unfold lit_wf_c in *. pose proof (msw_size Hweak). lia. }
  assert (Hqbound : ms_qtail current <= ms_size current).
  { pose proof (mtw_trail_bound Htrailwf) as Htrailbound.
    pose proof (msw_size Hweak) as Hsize.
    unfold solver_shape in Hshape. lia. }
  assert (Hfreshroom :
    Znth (lit_var_c (Znth 0 words 0))
      (mt_assigns (ms_core current)) 0 = 0 ->
    ms_qtail current < ms_size current).
  { intros _. pose proof (msw_size Hweak) as Hsize. lia. }
  unfold enqueue_input.
  unfold solver_shape in Hshape.
  repeat split; try assumption; try lia.
  all: unfold lit_wf_c in Hheadwf_current; try lia.
Qed.

Lemma enqueue_post_record_refold_wl :
  forall s assigns_ptr levels_ptr l c n cap qtail
         assigns levels reasons trail lim M reason_opt wl,
    n = ms_size M -> cap = ms_cap M -> qtail = ms_qtail M ->
    assigns = mt_assigns (ms_core M) ->
    levels = mt_levels (ms_core M) ->
    reasons = ms_reason_words M ->
    trail = mt_trail (ms_core M) ->
    lim = mt_lim (ms_core M) ->
    solver_shape (msolver_enqueue_fresh M l c reason_opt) ->
    Znth (lit_var_c l) assigns 0 = 0 ->
    enqueue_post_at s assigns_ptr levels_ptr l c n cap qtail 1
      assigns levels reasons trail lim **
    solver_enqueue_frame_wl s M wl
    |-- solver_rep_levels_wl_at s
          (msolver_enqueue_fresh M l c reason_opt)
          wl levels_ptr.
Proof.
  intros s assigns_ptr levels_ptr l c n cap qtail
         assigns levels reasons trail lim M reason_opt wl
         Hn Hcap Hqtail Hassigns Hlevels Hreasons Htrail Hlim
         Hshape Hfresh.
  msat_enqueue_refold_transition n cap qtail assigns levels reasons trail lim
    l Hfresh rsn trl Htransition qtail' assigns' levels' reasons' trail'.
    unfold solver_enqueue_frame_wl, solver_enqueue_frame_with_scalars_wl, solver_enqueue_cells_at.
    Intros act opos tgs.
    unfold solver_rep_levels_wl_at.
    Exists act assigns_ptr opos rsn trl tgs.
    msat_enqueue_refold_close Hshape.
Qed.

(* Reason grounding depends on the assignment update, not on the current-level policy. *)
Lemma grounded_at_assigns_one :
  forall old new x b d reason,
    grounded_at old -> assigns_one old new x b d reason ->
    (reason = None \/ exists c, reason = Some c /\ reason_valid new x c) ->
    grounded_at new.
Proof.
  intros old new x b d reason Hground Hstep Hnewreason.
  destruct Hstep as
    [Hxnone [Hxassign [Hxlevel [Hxreason [[rx [Hxrank Hdeps]] [Hother Hdb]]]]]].
  intros y bv Hyassign.
  destruct (Z.eqb y x) eqn:Hyx.
  + apply Z.eqb_eq in Hyx. subst y.
    exists d, rx. split; [exact Hxlevel|].
    split; [exact Hxrank|].
    rewrite Hxreason. exact Hnewreason.
  + apply Z.eqb_neq in Hyx.
    destruct (Hother y Hyx) as [Hay [Hly [Hry Hky]]].
    rewrite Hay in Hyassign.
    destruct (Hground y bv Hyassign) as
      [dy [ry [Hylevel [Hyrank [Hyreason | [c [Hyreason Hyvalid]]]]]]].
    * exists dy, ry. split; [rewrite Hly; exact Hylevel|].
      split; [rewrite Hky; exact Hyrank|].
      left. rewrite Hry. exact Hyreason.
    * exists dy, ry. split; [rewrite Hly; exact Hylevel|].
      split; [rewrite Hky; exact Hyrank|].
      right. exists c. split; [rewrite Hry; exact Hyreason|].
      destruct Hyvalid as
        [yb [yd [yr [Hya [Hyl [Hyk [Hsat Htail]]]]]]].
      exists yb, yd, yr.
      split; [rewrite Hay; exact Hya|].
      split; [rewrite Hly; exact Hyl|].
      split; [rewrite Hky; exact Hyk|].
      split; [exact Hsat|].
      intros k Hk Hneq.
      destruct (Htail k Hk Hneq) as
        [Heval [dl [rl [Hll [Hlr [Hdl Hrl]]]]]].
      assert (Hlx : literal_var k <> x).
      { intro Heq. subst x.
        destruct (eval_partial_literal_assigned
          (assignment old) k false Heval) as [bx Hbx].
        rewrite Hxnone in Hbx. discriminate. }
      destruct (Hother (literal_var k) Hlx) as [Hal [Hll' [Hrl' Hkl']]].
      split.
      -- unfold eval_partial_literal in *.
         rewrite Hal. exact Heval.
      -- exists dl, rl. repeat split.
         ++ rewrite Hll'. exact Hll.
         ++ rewrite Hkl'. exact Hlr.
         ++ exact Hdl.
         ++ exact Hrl.
Qed.

Lemma stable_view_assigns_one__record :
  forall old new x b d reason,
    stable_view old ->
    assigns_one old new x b d reason ->
    current_level new = current_level old ->
    (0 <= d <= current_level old) ->
    (reason = None \/
      exists c, reason = Some c /\ reason_valid new x c) ->
    stable_view new.
Proof.
  intros old new x b d reason [Hground Hclosed] Hstep Hcur Hd Hnewreason.
  split.
  - eapply grounded_at_assigns_one; eassumption.
  - destruct Hstep as
    [Hxnone [Hxassign [Hxlevel [Hxreason [[rx [Hxrank Hdeps]] [Hother Hdb]]]]]].
    destruct Hclosed as [Hcur0 [Hlevels Hdecisions]].
    split; [rewrite Hcur; exact Hcur0|]. split.
    + intros y bv dy Hyassign Hylevel.
      destruct (Z.eqb y x) eqn:Hyx.
      * apply Z.eqb_eq in Hyx. subst y.
        rewrite Hxlevel in Hylevel. inversion Hylevel. subst dy.
        rewrite Hcur. exact Hd.
      * apply Z.eqb_neq in Hyx.
        destruct (Hother y Hyx) as [Hay [Hly _]].
        rewrite Hay in Hyassign. rewrite Hly in Hylevel.
        rewrite Hcur. eapply Hlevels; eassumption.
    + intros dy Hdy. rewrite Hcur in Hdy.
      destruct (Hdecisions dy Hdy) as [y [[bv Hyassign] [Hylevel Hyreason]]].
      assert (Hyx : y <> x).
      { intro Heq. subst y. rewrite Hxnone in Hyassign. discriminate. }
      destruct (Hother y Hyx) as [Hay [Hly [Hry _]]].
      exists y. split.
      * exists bv. rewrite Hay. exact Hyassign.
      * split; [rewrite Hly; exact Hylevel|rewrite Hry; exact Hyreason].
Qed.

Lemma reasons_entailed_assigns_one__record :
  forall F old new x b d reason,
    assigns_one old new x b d reason ->
    reasons_entailed F old ->
    (reason = None \/ exists c, reason = Some c /\ entails_clause F c) ->
    reasons_entailed F new.
Proof.
  intros F old new x b d reason Hstep Hold Hnew y c Hy.
  destruct Hstep as
    [_ [_ [_ [Hxreason [_ [Hother _]]]]]].
  destruct (Z.eqb y x) eqn:Hyx.
  - apply Z.eqb_eq in Hyx. subst y. rewrite Hxreason in Hy.
    destruct Hnew as [->|[c' [-> Hent]]]; [discriminate|].
    inversion Hy. subst c. exact Hent.
  - apply Z.eqb_neq in Hyx.
    destruct (Hother y Hyx) as [_ [_ [Hry _]]].
    apply (Hold y c). rewrite <- Hry. exact Hy.
Qed.

Lemma reasons_var_injective_assigns_one__record :
  forall old new x b d reason,
    assigns_one old new x b d reason ->
    reasons_var_injective old ->
    (reason = None \/ exists c, reason = Some c /\ clause_var_injective c) ->
    reasons_var_injective new.
Proof.
  intros old new x b d reason Hstep Hold Hnew y c Hy.
  destruct Hstep as
    [_ [_ [_ [Hxreason [_ [Hother _]]]]]].
  destruct (Z.eqb y x) eqn:Hyx.
  - apply Z.eqb_eq in Hyx. subst y. rewrite Hxreason in Hy.
    destruct Hnew as [->|[c' [-> Hinj]]]; [discriminate|].
    inversion Hy. subst c. exact Hinj.
  - apply Z.eqb_neq in Hyx.
    destruct (Hother y Hyx) as [_ [_ [Hry _]]].
    apply (Hold y c). rewrite <- Hry. exact Hy.
Qed.

Lemma reason_valid_assigns_one__record :
  forall old new x b d c,
    stable_view old ->
    assigns_one old new x b d (Some c) ->
    d = current_level old ->
    List.In (satisfying_literal x b) c ->
    (forall l, List.In l c -> literal_var l <> x ->
      eval_partial_literal (assignment old) l = Some false) ->
    reason_valid new x c.
Proof.
  intros old new x b d c [Hground Hclosed] Hstep Hd Hhead Hfalse.
  destruct Hstep as
    [Hxnone [Hxassign [Hxlevel [Hxreason [[rx [Hxrank Hdeps]] [Hother Hdb]]]]]].
  exists b, d, rx. split; [exact Hxassign|].
  split; [exact Hxlevel|]. split; [exact Hxrank|].
  split; [exact Hhead|].
  intros k Hk Hkx.
  pose proof (Hfalse k Hk Hkx) as Hevalold.
  destruct (Hother (literal_var k) Hkx) as [Ha [Hlev [Hreason Hrank]]].
  assert (Hevalnew : eval_partial_literal (assignment new) k = Some false).
  { unfold eval_partial_literal in *. rewrite Ha. exact Hevalold. }
  split; [exact Hevalnew|].
  assert (Hdep : reason_dependency new x (literal_var k)).
  { exists c, k. repeat split; try assumption. }
  destruct (Hdeps (literal_var k) Hdep) as [ry [Hry Hrylt]].
  destruct (eval_partial_literal_assigned
    (assignment old) k false Hevalold) as [bl Hbl].
  destruct (Hground (literal_var k) bl Hbl) as
    [dl [rl [Hdl [Hrl Hwhy]]]].
  exists dl, ry. repeat split.
  - rewrite Hlev. exact Hdl.
  - exact Hry.
  - subst d. destruct Hclosed as [_ [Hlevels _]].
    eapply Hlevels; eassumption.
  - exact Hrylt.
Qed.

Lemma clause_new_success_installs_object__record :
  forall n F A_arr A_inst entry words c current,
    clause_new_success_transition n F A_arr A_inst
      entry words c current ->
    List.In (c, clause_obj_of words true) (msolver_db current).
Proof.
  intros n F A_arr A_inst entry words c current Htrans.
  destruct Htrans as
    [Hfresh [Hcurrent [Hinv [Hpending [Hseed Hcert]]]]].
  subst current.
  unfold msolver_install_learnt_clause, msolver_db.
  cbn [msolver_propagation_overlay msolver_propagation_update ].
  apply List.in_or_app. right. apply List.in_or_app. right. simpl. auto.
Qed.

Lemma record_reason_opt_wf__record :
  forall n words c C k,
    List.Forall (lit_wf_c n) words ->
    record_reason_opt words c = Some C ->
    List.In k C -> literal_wf n k.
Proof.
  intros n words c C k Hwf Hreason Hin.
  unfold record_reason_opt in Hreason.
  destruct (Z.eq_dec c 0); [discriminate|].
  inversion Hreason; subst C.
  rewrite List.Forall_forall in Hwf.
  apply lits_denote_in_inv in Hin.
  destruct Hin as [l [Hin <-]].
  apply lit_denote_wf. apply Hwf. exact Hin.
Qed.

Lemma solver_shape_enqueue_fresh__record :
  forall M l c reason,
    solver_shape M ->
    ms_qtail M < ms_cap M ->
    ms_capacity_root_propagation_pending M = 0 ->
    solver_shape (msolver_enqueue_fresh M l c reason).
Proof.
  intros M l c reason Hshape Hroom Hpendingzero.
  destruct Hshape as
    [Hsize [Hcap [Htwice [Hassigns [Hlevels [Hreasons [Horderpos
    [Hactivity [Htags [Htrail [Hqhead [Hpending [Hpending01
    [Hpendingcase [Hqtail [Hwm [Hbinarylits [Hstats
    [Hroot [Hbinarynz Hbinaryeven]]]]]]]]]]]]]]]]]]]].
  unfold solver_shape, msolver_enqueue_fresh,
    msolver_propagation_overlay, msolver_propagation_update, mt_enqueue, mt_push.
  cbn. rewrite !Zlength_replace_Znth.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  repeat split; try assumption; try lia.
Qed.

Lemma satisfied_literal_push :
  forall n t l lim a,
    mtrail_wf n t -> lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
    eval_partial_literal (mt_pv t) a = Some true ->
    eval_partial_literal (mt_pv (mt_push t l lim)) a = Some true /\
    Znth (literal_var a) (mt_levels (mt_push t l lim)) 0 =
      Znth (literal_var a) (mt_levels t) 0.
Proof.

  intros n t l lim a Hwf Hl Hfresh Htrue.
  assert (Ha0 : 0 <= literal_var a).
  { destruct (Z_lt_ge_dec (literal_var a) 0); [|lia].
    unfold eval_partial_literal in Htrue.
    rewrite mt_pv_neg in Htrue by assumption. discriminate. }
  assert (Haassigns : literal_var a < Zlength (mt_assigns t)).
  { destruct (eval_partial_literal_assigned (mt_pv t) a true Htrue)
      as [b Hb].
    rewrite mt_pv_nonneg in Hb by exact Ha0.
    destruct (Z_lt_ge_dec
      (literal_var a) (Zlength (mt_assigns t))); [assumption|].
    assert (Hz : Znth (literal_var a) (mt_assigns t) 0 = 0)
      by (apply znth_out_of_bounds; lia).
    rewrite Hz in Hb. discriminate. }
  assert (Hav : literal_var a <> lit_var_c l).
  { intro Heq.
    destruct (eval_partial_literal_assigned (mt_pv t) a true Htrue)
      as [b Hb].
    rewrite Heq in Hb.
    rewrite (mt_pv_zero_cell t (lit_var_c l)) in Hb.
    - discriminate.
    - apply lit_var_c_in_range in Hl. lia.
    - exact Hfresh. }
  split.
  - unfold eval_partial_literal in *.
    rewrite mt_pv_nonneg in Htrue by exact Ha0.
    unfold mt_pv, mt_push.
    cbn [mt_assigns].
    destruct (0 <=? literal_var a) eqn:Ha.
    2: { apply Z.leb_gt in Ha. lia. }
    unfold assigns_pv, assigns_val in *.
    rewrite Znth_replace_Znth_Diff.
    + exact Htrue.
    + apply lit_var_c_in_range in Hl.
      rewrite (mtw_assigns_len Hwf). exact Hl.
    + apply Z.leb_le in Ha.
      lia.
    + congruence.
  - unfold mt_push. cbn [mt_levels].
    rewrite Znth_replace_Znth_Diff.
    + reflexivity.
    + apply lit_var_c_in_range in Hl.
      rewrite (mtw_levels_len Hwf). exact Hl.
    + assert (Harange : 0 <= literal_var a < Zlength (mt_levels t)).
      { split.
        - exact Ha0.
        - rewrite (mtw_assigns_len Hwf) in Haassigns.
          rewrite (mtw_levels_len Hwf). exact Haassigns. }
      exact Harange.
    + intro E. apply Hav. symmetry. exact E.
Qed.

Lemma assump_true_at_root_enqueue__record :
  forall n t l root a,
    mtrail_wf n t -> lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
    assump_true_at_root t root a ->
    assump_true_at_root (mt_enqueue t l) root a.
Proof.
  intros n t l root a Hwf Hl Hfresh [Htrue Hlevel].
  destruct (satisfied_literal_push n t l (mt_lim t) a Hwf Hl Hfresh Htrue)
    as [Htrue' Hlevel'].
  split; [exact Htrue'|].
  change (Znth (literal_var a) (mt_levels (mt_push t l (mt_lim t))) 0 <= root).
  rewrite Hlevel'. exact Hlevel.
Qed.

Lemma root_satisfied_enqueue__record :
  forall n t l c,
    mtrail_wf n t -> lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
    root_satisfied t c -> root_satisfied (mt_enqueue t l) c.
Proof.
  intros n t l c Hwf Hl Hfresh [a [Hin [Htrue Hlevel]]].
  destruct (satisfied_literal_push n t l (mt_lim t) a Hwf Hl Hfresh Htrue)
    as [Htrue' Hlevel'].
  exists a. split; [exact Hin |]. split; [exact Htrue' |].
  unfold mt_enqueue. rewrite Hlevel'. exact Hlevel.
Qed.

Lemma minisat_watch_frontier_enqueue_nodrain :
  forall n db t l,
    mtrail_wf n t -> lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
    minisat_watch_frontier n db (mt_assigns t) (mt_trail t) (mt_qhead t) ->
    minisat_watch_frontier n db
      (mt_assigns (mt_enqueue t l))
      (mt_trail (mt_enqueue t l))
      (mt_qhead (mt_enqueue t l)).
Proof.
  intros n db t l Hwf Hl Hfresh Hfront.
  unfold minisat_watch_frontier in *.
  eapply watch_frontier_shrink; [exact Hfront|].
  intros a [p [Hp [Hden [Htrue [i [Hi Hit]]]]]].
  unfold mt_enqueue, mt_push in Hi, Hit, Htrue.
  cbn [mt_qhead mt_trail mt_assigns] in Hi, Hit, Htrue.
  pose proof (mtw_qhead_range Hwf) as Hqr.
  assert (Hiold : 0 <= i < Zlength (mt_trail t)) by lia.
  assert (Hitold : Znth i (mt_trail t) 0 = p).
  { rewrite app_Znth1 in Hit by exact Hiold. exact Hit. }
  assert (Hpin : List.In p (mt_trail t)).
  { rewrite <- Hitold. apply Znth_In. exact Hiold. }
  assert (Hneq : lit_var_c p <> lit_var_c l).
  { intro Heq.
    pose proof (mtw_trail_true Hwf) as Htrailtrue.
    rewrite List.Forall_forall in Htrailtrue.
    pose proof (Htrailtrue p Hpin) as Hpassigned.
    rewrite Heq, Hfresh in Hpassigned.
    exact (lit_sig_nonzero p (eq_sym Hpassigned)). }
  exists p. split; [exact Hp|]. split; [exact Hden|].
  split.
  - unfold lit_true in *.
    rewrite Znth_replace_Znth_Diff in Htrue.
    + exact Htrue.
    + apply lit_var_c_in_range in Hl.
      rewrite (mtw_assigns_len Hwf). exact Hl.
    + apply lit_var_c_in_range in Hp.
      rewrite (mtw_assigns_len Hwf). exact Hp.
    + congruence.
  - exists i. split; [exact Hi|exact Hitold].
Qed.

Lemma minisat_watch_frontier_enqueue__record :
  forall n db t l,
    mtrail_wf n t -> lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
    mt_qhead t = Zlength (mt_trail t) ->
    minisat_watch_frontier n db (mt_assigns t) (mt_trail t) (mt_qhead t) ->
    minisat_watch_frontier n db
      (mt_assigns (mt_enqueue t l))
      (mt_trail (mt_enqueue t l))
      (mt_qhead (mt_enqueue t l)).
Proof.
  intros n db t l Hwf Hl Hfresh Hq Hfront.
  exact (minisat_watch_frontier_enqueue_nodrain n db t l Hwf Hl Hfresh Hfront).
Qed.

Lemma reasons_match_enqueue_fresh_core : forall n M l c reason,
  solver_shape M ->
  n = ms_size M ->
  reasons_match n (ms_core M) (msolver_db M) (ms_reason_words M)
    (ms_reason_of M) ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  ((c = 0 /\ reason = None) \/
   exists co, c <> 0 /\ Z.even c = true /\
     List.In (c, co) (msolver_db M) /\ reason = Some (denote_obj co)) ->
  reasons_match n (ms_core (msolver_enqueue_fresh M l c reason))
    (msolver_db (msolver_enqueue_fresh M l c reason))
    (ms_reason_words (msolver_enqueue_fresh M l c reason))
    (ms_reason_of (msolver_enqueue_fresh M l c reason)).
Proof.
  intros n M l c reason Hshape Hsize Hrmem Hl Hfresh Hreason v Hv.
  pose proof (Hrmem v Hv) as Hold.
  unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update, msolver_db.
  cbn [ms_core ms_reason_words ms_reason_of ms_prob ms_learnt].
  destruct (Z.eq_dec v (lit_var_c l)) as [->|Hne].
  - assert (Hvr : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    assert (Hva : 0 <= lit_var_c l < Zlength (mt_assigns (ms_core M))).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    rewrite Znth_replace_Znth_Same by exact Hvr.
    rewrite sat_function_update_eq.
    unfold reason_word_ok.
    destruct Hreason as [[-> ->]|[co [Hnz [Heven [Hin ->]]]]].
    + reflexivity.
    + assert (Hz : Z.eqb c 0 = false) by (apply Z.eqb_neq; exact Hnz).
      rewrite Hz. split.
      * unfold mt_enqueue, mt_push. cbn [mt_assigns].
        rewrite Znth_replace_Znth_Same by exact Hva.
        apply lit_sig_nonzero.
      * rewrite (even_not_tag c Heven).
        exists co. split; [exact Hin|reflexivity].
  - assert (Hvr : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    assert (Hvv : 0 <= v < Zlength (ms_reason_words M)).
    { unfold solver_shape in Hshape. lia. }
    rewrite Znth_replace_Znth_Diff.
    2: { exact Hvr. } 2: { exact Hvv. } 2: { congruence. }
    rewrite sat_function_update_neq by congruence.
    unfold reason_word_ok in Hold |- *.
    destruct (Z.eqb (Znth v (ms_reason_words M) 0) 0); [exact Hold|].
    destruct Hold as [Hassigned Hdecode]. split.
    + unfold mt_enqueue, mt_push. cbn [mt_assigns].
      assert (Hva : 0 <= lit_var_c l < Zlength (mt_assigns (ms_core M))).
      { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
      assert (Hav : 0 <= v < Zlength (mt_assigns (ms_core M))).
      { unfold solver_shape in Hshape. lia. }
      rewrite Znth_replace_Znth_Diff.
      * exact Hassigned.
      * exact Hva.
      * exact Hav.
      * congruence.
    + assert (Htrail :
          trail_lit_of (mt_enqueue (ms_core M) l) v =
          trail_lit_of (ms_core M) v).
      { unfold trail_lit_of, mt_enqueue, mt_push. cbn [mt_assigns].
        assert (Htarget :
          0 <= lit_var_c l < Zlength (mt_assigns (ms_core M))).
        { apply lit_var_c_in_range in Hl.
          unfold solver_shape in Hshape. lia. }
        assert (Hvassigns :
          0 <= v < Zlength (mt_assigns (ms_core M))).
        { unfold solver_shape in Hshape. lia. }
        rewrite Znth_replace_Znth_Diff;
          [reflexivity|exact Htarget|exact Hvassigns|congruence]. }
      unfold msolver_db in Hdecode.
      rewrite Htrail. exact Hdecode.
Qed.

Lemma reasons_match_enqueue_fresh__record :
  forall n F A_arr A_inst M l c reason,
    msolver_inv_weak n F A_arr A_inst M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    ((c = 0 /\ reason = None) \/
     exists co, c <> 0 /\ Z.even c = true /\
       List.In (c, co) (msolver_db M) /\ reason = Some (denote_obj co)) ->
    reasons_match n (ms_core (msolver_enqueue_fresh M l c reason))
      (msolver_db (msolver_enqueue_fresh M l c reason))
      (ms_reason_words (msolver_enqueue_fresh M l c reason))
      (ms_reason_of (msolver_enqueue_fresh M l c reason)).
Proof.
  intros n F A_arr A_inst M l c reason Hinv Hl Hfresh Hreason.
  exact (reasons_match_enqueue_fresh_core n M l c reason
    (msw_shape Hinv) (msw_size Hinv) (msw_reasons_mem Hinv) Hl Hfresh Hreason).
Qed.

Lemma reason_head_ok_enqueue_fresh_core : forall n M l c reason,
  solver_shape M ->
  n = ms_size M ->
  reason_head_ok M ->
  db_wf n (msolver_db M) ->
  lit_wf_c n l ->
  ((c = 0) \/
   exists co, c <> 0 /\ Z.even c = true /\
     List.In (c, co) (msolver_db M) /\
     lit_var_c (co_watch0 co) = lit_var_c l) ->
  reason_head_ok (msolver_enqueue_fresh M l c reason).
Proof.
  intros n M l c reason Hshape Hsize Hhead Hdbwf Hl Hreason.
  unfold reason_head_ok in *.
  unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update, msolver_db.
  cbn [ms_size ms_reason_words ms_prob ms_learnt].
  intros v co Hv Htag Hnz Hin.
  destruct (Z.eq_dec v (lit_var_c l)) as [->|Hne].
  - assert (Hvr : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    rewrite Znth_replace_Znth_Same in Htag, Hnz, Hin by exact Hvr.
    destruct Hreason as [->|[co' [Hcnz [Heven [Hin' Hwatch]]]]].
    + contradiction.
    + assert (Heq : co = co').
      { eapply db_wf_lookup_unique;
          [exact Hdbwf|exact Hin|exact Hin']. }
      subst co'. exact Hwatch.
  - assert (Hvr : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    assert (Hvv : 0 <= v < Zlength (ms_reason_words M)).
    { unfold solver_shape in Hshape. lia. }
    assert (Hword :
      Znth v (replace_Znth (lit_var_c l) c (ms_reason_words M)) 0 =
      Znth v (ms_reason_words M) 0).
    { apply Znth_replace_Znth_Diff;
        [exact Hvr|exact Hvv|congruence]. }
    rewrite Hword in Htag, Hnz, Hin.
    eapply Hhead; eassumption.
Qed.

Lemma reason_head_ok_enqueue_fresh__record :
  forall n F A_arr A_inst M l c reason,
    msolver_inv_weak n F A_arr A_inst M ->
    lit_wf_c n l ->
    ((c = 0) \/
     exists co, c <> 0 /\ Z.even c = true /\
       List.In (c, co) (msolver_db M) /\ lit_var_c (co_watch0 co) = lit_var_c l) ->
    reason_head_ok (msolver_enqueue_fresh M l c reason).
Proof.
  intros n F A_arr A_inst M l c reason Hinv Hl Hreason.
  exact (reason_head_ok_enqueue_fresh_core n M l c reason
    (msw_shape Hinv) (msw_size Hinv) (msw_reason_head Hinv) (msw_db_wf Hinv)
    Hl Hreason).
Qed.

(** Updating a fresh variable's reason and level preserves every tagged
    binary reason, regardless of the new level. Stable reasons keep their
    partners assigned, so neither endpoint can be the fresh variable. *)
Lemma binary_reason_same_level_replace_core : forall n M M' l c level,
  solver_shape M ->
  n = ms_size M ->
  mtrail_wf n (ms_core M) ->
  binary_reason_same_level M ->
  reasons_match n (ms_core M) (msolver_db M) (ms_reason_words M)
    (ms_reason_of M) ->
  stable_view (msolver_view n M) ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  (c = 0 \/ Z.even c = true) ->
  ms_size M' = ms_size M ->
  ms_reason_words M' = replace_Znth (lit_var_c l) c (ms_reason_words M) ->
  mt_levels (ms_core M') =
    replace_Znth (lit_var_c l) level (mt_levels (ms_core M)) ->
  binary_reason_same_level M'.
Proof.
  intros n M M' l c level Hshape Hsize Htrailwf Hrbin Hrmem Hstable
    Hl Hfresh Hc Hsize' Hwords' Hlevels'.
  unfold binary_reason_same_level.
  rewrite Hsize', Hwords', Hlevels'.
  intros v Hv Htag.
  assert (Htargetr : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
  { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
  assert (Hvr : 0 <= v < Zlength (ms_reason_words M)).
  { unfold solver_shape in Hshape. lia. }
  destruct (Z.eq_dec v (lit_var_c l)) as [->|Hvne].
  - rewrite Znth_replace_Znth_Same in Htag by exact Htargetr.
    destruct Hc as [->|Heven].
    + discriminate.
    + rewrite (even_not_tag c Heven) in Htag. discriminate.
  - assert (Hword :
      Znth v (replace_Znth (lit_var_c l) c (ms_reason_words M)) 0 =
      Znth v (ms_reason_words M) 0).
    { apply Znth_replace_Znth_Diff;
        [exact Htargetr|exact Hvr|congruence]. }
    rewrite Hword in Htag |- *.
    destruct (Hrbin v ltac:(lia) Htag)
      as [Htagwf [Hleveq Hdifferent]].
    set (w := Znth v (ms_reason_words M) 0) in *.
    set (u := lit_var_c (tag_lit w)) in *.
    assert (Hwpos : 0 < w).
    { eapply tag_pos_of_lit_wf; eassumption. }
    assert (Hownerlive : Znth v (mt_assigns (ms_core M)) 0 <> 0).
    { pose proof (Hrmem v ltac:(lia)) as Hreasonok.
      unfold reason_word_ok in Hreasonok.
      assert (Hz : Z.eqb (Znth v (ms_reason_words M) 0) 0 = false).
      { apply Z.eqb_neq. unfold w in Hwpos. lia. }
      rewrite Hz in Hreasonok. exact (proj1 Hreasonok). }
    assert (Howner : exists b, mt_pv (ms_core M) v = Some b).
    { rewrite mt_pv_nonneg by lia.
      pose proof (Forall_Znth_elim _ _ _ 0 v (mtw_cells Htrailwf)) as Hcell.
      rewrite (mtw_assigns_len Htrailwf) in Hcell.
      specialize (Hcell ltac:(lia)).
      destruct Hcell as [Hz|[Hz|Hz]]; rewrite Hz;
        [exists false; reflexivity|contradiction|exists true; reflexivity]. }
    destruct Howner as [b Howner].
    destruct Hstable as [Hground _].
    destruct (Hground v b Howner) as
      [d [rx [Hvd [Hvrank Hwhy]]]].
    assert (Hposne : trail_pos (ms_core M) v <> None).
    { intro Hnonepos.
      pose proof (proj2 (view_unassigned_iff n (ms_core M) v Htrailwf)
        Hnonepos) as Hnonepv.
      rewrite Hnonepv in Howner. discriminate. }
    destruct (trail_pos (ms_core M) v) as [kv|] eqn:Hpos;
      [|contradiction].
    unfold msolver_view, view_of in Hwhy.
    cbn [reason_of] in Hwhy. rewrite Hpos in Hwhy. cbn in Hwhy.
    pose proof (reason_word_ok_tag
      (ms_core M) v (msolver_db M) w (ms_reason_of M v)
      Hwpos Htag (Hrmem v ltac:(lia))) as Hsome.
    destruct Hwhy as [Hnone|[C [HC Hvalid]]].
    + rewrite Hnone in Hsome. discriminate.
    + rewrite HC in Hsome. inversion Hsome. subst C.
      destruct Hvalid as [bv [dv [rv [Ha [Hd [Hr [Hhead Htail]]]]]]].
      assert (Hune : u <> lit_var_c l).
      { intro Hueq.
        pose proof (Htail (literal_neg (lit_denote (tag_lit w)))) as Hdep.
        assert (Huv : literal_var (literal_neg (lit_denote (tag_lit w))) <> v).
        { rewrite literal_var_neg, lit_var_c_denote. exact Hdifferent. }
        destruct (Hdep (or_intror (or_introl eq_refl)) Huv) as [Heval _].
        destruct (eval_partial_literal_assigned
          (mt_pv (ms_core M))
          (literal_neg (lit_denote (tag_lit w))) false Heval) as [bu Hbu].
        rewrite literal_var_neg, lit_var_c_denote in Hbu.
        unfold u in Hueq. rewrite Hueq in Hbu.
        rewrite (mt_pv_zero_cell (ms_core M) (lit_var_c l)) in Hbu.
        - discriminate.
        - apply lit_var_c_in_range in Hl. lia.
        - exact Hfresh. }
      split; [exact Htagwf|]. split; [|exact Hdifferent].
      assert (Htargetl : 0 <= lit_var_c l < Zlength (mt_levels (ms_core M))).
      { apply lit_var_c_in_range in Hl. rewrite (mtw_levels_len Htrailwf). lia. }
      assert (Hvl : 0 <= v < Zlength (mt_levels (ms_core M))).
      { rewrite (mtw_levels_len Htrailwf). lia. }
      assert (Hul : 0 <= u < Zlength (mt_levels (ms_core M))).
      { unfold u. apply lit_var_c_in_range in Htagwf.
        rewrite (mtw_levels_len Htrailwf). lia. }
      rewrite Znth_replace_Znth_Diff;
        [|exact Htargetl|exact Hul|congruence].
      rewrite Znth_replace_Znth_Diff;
        [exact Hleveq|exact Htargetl|exact Hvl|congruence].
Qed.

Lemma binary_reason_same_level_enqueue_fresh_core : forall n M l c reason,
  solver_shape M ->
  n = ms_size M ->
  mtrail_wf n (ms_core M) ->
  binary_reason_same_level M ->
  reasons_match n (ms_core M) (msolver_db M) (ms_reason_words M)
    (ms_reason_of M) ->
  stable_view (msolver_view n M) ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  (c = 0 \/ Z.even c = true) ->
  binary_reason_same_level (msolver_enqueue_fresh M l c reason).
Proof.
  intros n M l c reason Hshape Hsize Htrailwf Hrbin Hrmem Hstable Hl Hfresh Hc.
  eapply binary_reason_same_level_replace_core with
    (M := M) (l := l) (c := c) (level := Zlength (mt_lim (ms_core M)));
    try eassumption; reflexivity.
Qed.

Lemma binary_reason_same_level_enqueue_fresh__record :
  forall n F A_arr A_inst M l c reason,
    msolver_inv_weak n F A_arr A_inst M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    (c = 0 \/ Z.even c = true) ->
    binary_reason_same_level (msolver_enqueue_fresh M l c reason).
Proof.
  intros n F A_arr A_inst M l c reason Hinv Hl Hfresh Hc.
  exact (binary_reason_same_level_enqueue_fresh_core n M l c reason
    (msw_shape Hinv) (msw_size Hinv) (msw_trail_wf Hinv) (msw_reason_bin Hinv)
    (msw_reasons_mem Hinv) (msw_stable Hinv) Hl Hfresh Hc).
Qed.

Lemma record_enqueue_reason_cases__record :
  forall n F A_arr A_inst entry words c M,
    record_allocated n F A_arr A_inst entry words c M ->
    (c = 0 /\ record_reason_opt words c = None) \/
    exists co,
      c <> 0 /\ Z.even c = true /\
      List.In (c, co) (msolver_db M) /\
      record_reason_opt words c = Some (denote_obj co) /\
      lit_var_c (co_watch0 co) = lit_var_c (Znth 0 words 0).
Proof.
  intros n F A_arr A_inst entry words c M Halloc.
  destruct Halloc as
    [Hkind [Hcert [Hinv [Hq [Hpending [Hseed Hmodel]]]]]].
  destruct Hkind as [[Hlen [-> ->]]|[Hlen [Hcnz Htrans]]].
  - left. split; [reflexivity|].
    unfold record_reason_opt. destruct (Z.eq_dec 0 0); [reflexivity|contradiction].
  - right. exists (clause_obj_of words true).
    assert (Hin : List.In (c, clause_obj_of words true) (msolver_db M)).
    { eapply clause_new_success_installs_object__record. exact Htrans. }
    repeat split.
    + exact Hcnz.
    + eapply db_wf_even; [exact (msi_db_wf Hinv)|exact Hin].
    + exact Hin.
    + unfold record_reason_opt. destruct (Z.eq_dec c 0); [contradiction|reflexivity].
Qed.

Lemma current_reasonless_record_enqueue__record :
  forall n F A_arr A_inst entry words c M,
    record_allocated n F A_arr A_inst entry words c M ->
    current_reasonless_earliest n (msolver_record_enqueue M words c).
Proof.
  intros n F A_arr A_inst entry words c M Halloc.
  destruct Halloc as
    [Hkind [Hcert [Hinv [Hq [Hpending [Hseed Hmodel]]]]]].
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as [Hlen [Hwf [Hnd [Hent [Hfresh [Hfalse Hroot]]]]]].
  pose proof (msi_weak Hinv) as Hweak.
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_size Hweak) as Hsize.
  pose proof (msw_trail_wf Hweak) as Htrailwf.
  destruct Hkind as [[Hunit [Hczero Hentry]]|[Hlong [Hcnz Htrans]]].
  - subst c. subst M.
    unfold current_reasonless_earliest.
    intros d Hrange.
    exfalso.
    specialize (Hroot Hunit).
    unfold solver_at_root in Hroot.
    unfold msolver_record_enqueue, record_reason_opt, msolver_enqueue_fresh,
      msolver_propagation_overlay, msolver_propagation_update in Hrange.
    cbn [ms_root_level ms_core mt_lim] in Hrange.
    change (Zlength (mt_lim (ms_core entry)) = ms_root_level entry) in Hroot.
    change (ms_root_level entry < d <=
      Zlength (mt_lim (ms_core entry))) in Hrange.
    lia.
  - pose proof (msi_reasonless_current Hinv) as Hold.
    unfold current_reasonless_earliest in Hold |- *.
    intros d Hrange v Hlevel Hword.
    set (l := Znth 0 words 0) in *.
    assert (Hl : lit_wf_c n l).
    { unfold l. apply (Forall_Znth_elim _ _ _ 0 0 Hwf). lia. }
    assert (Hassign : assigns_one (msolver_view n M)
      (msolver_view n (msolver_record_enqueue M words c))
      (lit_var_c l) (lit_pol l) (Zlength (mt_lim (ms_core M)))
      (record_reason_opt words c)).
    { unfold msolver_record_enqueue, msolver_enqueue_fresh,
        msolver_propagation_overlay, msolver_propagation_update, msolver_view, msolver_db.
      cbn [ms_core ms_reason_of ms_prob ms_learnt].
      eapply view_of_assign.
      - exact Htrailwf.
      - exact Hl.
      - unfold l. exact Hfresh.
      - intros y Hy. apply sat_function_update_neq.
        intro Heq. apply Hy. symmetry. unfold l. exact Heq.
      - apply sat_function_update_eq.
      - intros C k HC Hk.
        eapply record_reason_opt_wf__record;
          [exact Hwf|exact HC|exact Hk]. }
    destruct Hassign as [_ [_ [_ [_ [_ [Hother _]]]]]].
    change (ms_root_level M < d <= Zlength (mt_lim (ms_core M))) in Hrange.
    destruct (Z.eq_dec v (lit_var_c l)) as [->|Hvne].
    + assert (Hvr : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
      { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
      unfold msolver_record_enqueue, msolver_enqueue_fresh,
        msolver_propagation_overlay, msolver_propagation_update in Hword.
      cbn [ms_reason_words] in Hword.
      rewrite Znth_replace_Znth_Same in Hword by exact Hvr.
      contradiction.
    + destruct (Hother v Hvne) as [Ha [Hlev [Hreason Hrankeq]]].
      rewrite Hlev in Hlevel.
      assert (Hv : 0 <= v < n).
      { unfold msolver_view, view_of in Hlevel.
        cbn [level_of] in Hlevel.
        destruct (trail_pos (ms_core M) v) as [k|] eqn:Hpos;
          cbn [option_map] in Hlevel; [|discriminate].
        apply find_var_pos_some_in in Hpos.
        apply trail_var_range with (t := ms_core M); assumption. }
      assert (Htargetr : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
      { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
      assert (Hvr : 0 <= v < Zlength (ms_reason_words M)).
      { unfold solver_shape in Hshape. lia. }
      unfold msolver_record_enqueue, msolver_enqueue_fresh,
        msolver_propagation_overlay, msolver_propagation_update in Hword.
      cbn [ms_reason_words] in Hword.
      rewrite Znth_replace_Znth_Diff in Hword;
        [|exact Htargetr|exact Hvr|
          intro Heq; apply Hvne; symmetry; exact Heq].
      destruct (Hold d Hrange v Hlevel Hword) as [Hr Hrank].
      split.
      * unfold msolver_record_enqueue, msolver_enqueue_fresh,
          msolver_propagation_overlay, msolver_propagation_update.
        cbn [ms_reason_of].
        rewrite sat_function_update_neq.
        -- exact Hr.
        -- intro Heq. apply Hvne. symmetry. unfold l. exact Heq.
      * rewrite Hrankeq. exact Hrank.
Qed.

Lemma db_complete_enqueue_fresh_core : forall n F M l c reason,
  db_complete F M ->
  mtrail_wf n (ms_core M) ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  db_complete F (msolver_enqueue_fresh M l c reason).
Proof.
  intros n F M l c reason Hdbc Htwf Hl Hfresh C HC.
  destruct (Hdbc C HC) as [[C' [Hin Hperm]]|Hroot].
  - left. exists C'. split; [|exact Hperm].
    unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update.
    cbn [ms_prob]. exact Hin.
  - right.
    unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update.
    cbn [ms_core].
    eapply root_satisfied_enqueue__record;
      [exact Htwf|exact Hl|exact Hfresh|exact Hroot].
Qed.

Lemma db_complete_enqueue_fresh__record :
  forall n F A_arr A_inst M l c reason,
    msolver_inv_weak n F A_arr A_inst M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    db_complete F (msolver_enqueue_fresh M l c reason).
Proof.
  intros n F A_arr A_inst M l c reason Hinv Hl Hfresh.
  exact (db_complete_enqueue_fresh_core n F M l c reason
    (msw_db_complete Hinv) (msw_trail_wf Hinv) Hl Hfresh).
Qed.

Lemma record_trail_implied_enqueue__record :
  forall n F A_arr A_inst M words,
    msolver_inv_weak n F A_arr A_inst M ->
    record_clause_cert n F M words ->
    trail_implied F
      (mt_enqueue (ms_core M) (Znth 0 words 0)).
Proof.
  intros n F A_arr A_inst M words Hinv Hcert.
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as
    [Hlen [Hwf [Hnd [Hent [Hfresh [Hfalse Hroot]]]]]].
  destruct words as [|w ws].
  { rewrite Zlength_nil in Hlen. lia. }
  cbn [Znth].
  eapply trail_implied_unit with (rc := lits_denote (w :: ws)).
  - exact (msw_trail_wf Hinv).
  - exact (msw_trail_impl Hinv).
  - exact Hent.
  - left. reflexivity.
  - intros k Hk Hne.
    cbn [lits_denote] in Hk.
    destruct Hk as [Hk|Hktail].
    { subst k. contradiction. }
    pose proof (Hfalse k Hktail) as Heval.
    destruct (lits_denote_in_inv k ws Hktail) as [p [Hp Hpk]].
    subst k.
    inversion Hwf as [|? ? Hwwf Hwswf]; subst.
    rewrite List.Forall_forall in Hwswf.
    pose proof (Hwswf p Hp) as Hpwf.
    assert (Hp0 : 0 <= p) by (destruct Hpwf; lia).
    assert (Heval' :
      eval_partial_literal (assigns_pv (mt_assigns (ms_core M)))
        (lit_denote p) = Some false).
    { unfold eval_partial_literal in Heval |- *.
      rewrite mt_pv_nonneg in Heval.
      - exact Heval.
      - rewrite lit_var_c_denote.
        apply lit_var_c_in_range in Hpwf. lia. }
    assert (Hnegtrue :
      eval_partial_literal (assigns_pv (mt_assigns (ms_core M)))
        (lit_denote (lit_neg_c p)) = Some true).
    { apply (proj2 (lit_neg_true_iff_false
        (mt_assigns (ms_core M)) p Hp0)). exact Heval'. }
    pose proof (lit_neg_c_wf n p Hpwf) as Hnegwf.
    assert (Hlittrue :
      lit_true (mt_assigns (ms_core M)) (lit_neg_c p)).
    { assert (Hneg0 : 0 <= lit_neg_c p) by (destruct Hnegwf; lia).
      apply (proj2 (lit_true_iff
        (mt_assigns (ms_core M)) (lit_neg_c p) Hneg0)).
      exact Hnegtrue. }
    destruct (mtrail_wf_trail_covers n (ms_core M)
      (msw_trail_wf Hinv) (lit_neg_c p)
      Hnegwf Hlittrue) as [j [Hj Hjlit]].
    exists j. split; [exact Hj|]. rewrite Hjlit.
    apply lit_denote_neg. exact Hp0.
Qed.

Lemma heap_covers_enqueue_fresh__record :
  forall n h t l,
    mtrail_wf n t ->
    lit_wf_c n l ->
    heap_covers n h (mt_assigns t) (mt_trail t) (mt_qhead t) ->
    heap_covers n h
      (mt_assigns (mt_enqueue t l))
      (mt_trail (mt_enqueue t l))
      (mt_qhead (mt_enqueue t l)).
Proof.
  intros n h t l Hwf Hl Hcovers.
  eapply heap_covers_enqueue; [exact Hcovers|reflexivity| |].
  - intros v Hv Hassigned.
    unfold mt_enqueue, mt_push. cbn [mt_assigns].
    assert (Htarget : 0 <= lit_var_c l < Zlength (mt_assigns t)).
    { apply lit_var_c_in_range in Hl.
      rewrite (mtw_assigns_len Hwf). exact Hl. }
    assert (Hvr : 0 <= v < Zlength (mt_assigns t)).
    { rewrite (mtw_assigns_len Hwf). exact Hv. }
    destruct (Z.eq_dec (lit_var_c l) v) as [Heq|Hne].
    + subst v. rewrite Znth_replace_Znth_Same by exact Htarget.
      apply lit_sig_nonzero.
    + rewrite Znth_replace_Znth_Diff;
        [exact Hassigned|exact Htarget|exact Hvr|exact Hne].
  - intros i Hi.
    unfold mt_enqueue, mt_push. cbn [mt_trail].
    apply app_Znth1.
    pose proof (mtw_qhead_range Hwf). lia.
Qed.

Lemma record_assigns_one__record :
  forall n F A_arr A_inst M words c,
    msolver_inv_weak n F A_arr A_inst M ->
    record_clause_cert n F M words ->
    assigns_one (msolver_view n M)
      (msolver_view n (msolver_record_enqueue M words c))
      (lit_var_c (Znth 0 words 0)) (lit_pol (Znth 0 words 0))
      (Zlength (mt_lim (ms_core M))) (record_reason_opt words c).
Proof.
  intros n F A_arr A_inst M words c Hinv Hcert.
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as
    [Hlen [Hwf [Hnd [Hent [Hfresh [Hfalse Hroot]]]]]].
  assert (Hl : lit_wf_c n (Znth 0 words 0)).
  { eapply Forall_Znth_elim; [exact Hwf|lia]. }
  unfold msolver_record_enqueue, msolver_view,
    msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update, msolver_db.
  cbn [ms_core ms_reason_of ms_prob ms_learnt].
  eapply view_of_assign.
  - exact (msw_trail_wf Hinv).
  - exact Hl.
  - exact Hfresh.
  - intros y Hy. apply sat_function_update_neq.
    intro Heq. apply Hy. symmetry. exact Heq.
  - apply sat_function_update_eq.
  - intros C k HC Hk.
    eapply record_reason_opt_wf__record;
      [exact Hwf|exact HC|exact Hk].
Qed.

Lemma record_reason_valid_enqueue__record :
  forall n F A_arr A_inst M words c,
    msolver_inv_weak n F A_arr A_inst M ->
    record_clause_cert n F M words ->
    c <> 0 ->
    reason_valid (msolver_view n (msolver_record_enqueue M words c))
      (lit_var_c (Znth 0 words 0)) (lits_denote words).
Proof.
  intros n F A_arr A_inst M words c Hinv Hcert Hcnz.
  pose proof (record_assigns_one__record
    n F A_arr A_inst M words c Hinv Hcert) as Hassign.
  assert (Hreason : record_reason_opt words c = Some (lits_denote words)).
  { unfold record_reason_opt.
    destruct (Z.eq_dec c 0) as [Heq|Hne]; [contradiction|reflexivity]. }
  rewrite Hreason in Hassign.
  eapply reason_valid_assigns_one__record.
  - exact (msw_stable Hinv).
  - exact Hassign.
  - reflexivity.
  - destruct words as [|w ws].
    + unfold record_clause_cert, record_ready_cert in Hcert.
      destruct Hcert as [Hlen _]. rewrite Zlength_nil in Hlen. lia.
    + cbn [Znth lits_denote]. rewrite <- lit_denote_satisfying.
      left. reflexivity.
  - intros k Hk Hkne.
    unfold record_clause_cert, record_ready_cert in Hcert.
    destruct Hcert as
      [Hlen [Hwf [Hnd [Hent [Hfresh [Hfalse Hroot]]]]]].
    destruct words as [|w ws].
    { rewrite Zlength_nil in Hlen. lia. }
    cbn [Znth lits_denote] in Hk, Hkne.
    destruct Hk as [Hk|Hk].
    + subst k. rewrite lit_var_c_denote in Hkne. contradiction.
    + exact (Hfalse k Hk).
Qed.

Lemma msolver_inv_record_enqueue__record :
  forall n F A_arr A_inst entry words c M,
    record_allocated n F A_arr A_inst entry words c M ->
    msolver_inv n F A_arr A_inst (msolver_record_enqueue M words c).
Proof.
  intros n F A_arr A_inst entry words c M Halloc0.
  pose proof Halloc0 as Halloc.
  destruct Halloc as
    [Hkind [Hcert [Hinv [Hq [Hpending [Hseed Hmodel]]]]]].
  pose proof (msi_weak Hinv) as Hweak.
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_trail_wf Hweak) as Htrailwf.
  set (l := Znth 0 words 0).
  set (reason := record_reason_opt words c).
  assert (Hl : lit_wf_c n l).
  { unfold l. unfold record_clause_cert, record_ready_cert in Hcert.
    destruct Hcert as [_ [Hwf _]].
    eapply Forall_Znth_elim; [exact Hwf|lia]. }
  assert (Hfresh : Znth (lit_var_c l)
      (mt_assigns (ms_core M)) 0 = 0).
  { unfold l. unfold record_clause_cert, record_ready_cert in Hcert.
    tauto. }
  pose proof (record_allocated_enqueue_input__record
    n F A_arr A_inst entry words c M Halloc0) as Hinput.
  unfold enqueue_input in Hinput.
  destruct Hinput as
    [Hlin [Htwice [Halen [Hllen [Hrlen [Htlen
      [Hqbound [Hroom Hcells]]]]]]]].
  specialize (Hroom Hfresh).
  assert (Hcaproom : ms_qtail M < ms_cap M).
  { unfold solver_shape in Hshape. lia. }
  assert (Hshape' : solver_shape
      (msolver_enqueue_fresh M l c reason)).
  { eapply solver_shape_enqueue_fresh__record.
    - exact Hshape.
    - exact Hcaproom.
    - exact Hpending. }
  pose proof (record_assigns_one__record
    n F A_arr A_inst M words c Hweak Hcert) as Hassign.
  assert (Hoptional : forall P : clause -> Prop,
    (c <> 0 -> P (lits_denote words)) ->
    reason = None \/ exists C, reason = Some C /\ P C).
  { intros P HP. unfold reason, record_reason_opt.
    destruct (Z.eq_dec c 0) as [Hcz|Hcnz].
    - left. reflexivity.
    - right. exists (lits_denote words). split.
      + reflexivity.
      + apply HP. exact Hcnz. }
  assert (Hsemantic :
    reason = None \/
    exists C, reason = Some C /\
      reason_valid (msolver_view n (msolver_record_enqueue M words c))
        (lit_var_c l) C).
  { apply Hoptional. intros Hcnz.
    unfold l.
    eapply record_reason_valid_enqueue__record;
      [exact Hweak|exact Hcert|exact Hcnz]. }
  assert (Hreasonent :
    reason = None \/
    exists C, reason = Some C /\ entails_clause F C).
  { apply Hoptional. intros _.
    unfold record_clause_cert, record_ready_cert in Hcert. tauto. }
  assert (Hreasoninj :
    reason = None \/
    exists C, reason = Some C /\ clause_var_injective C).
  { apply Hoptional. intros _.
    apply NoDup_map_var_injective.
    rewrite map_literal_var_lits_denote.
    unfold record_clause_cert, record_ready_cert in Hcert. tauto. }
  assert (Hstable : stable_view
    (msolver_view n (msolver_record_enqueue M words c))).
  { eapply stable_view_assigns_one__record.
    - exact (msw_stable Hweak).
    - exact Hassign.
    - reflexivity.
    - split; [apply Zlength_nonneg|reflexivity].
    - exact Hsemantic. }
  assert (Hent : reasons_entailed F
    (msolver_view n (msolver_record_enqueue M words c))).
  { eapply reasons_entailed_assigns_one__record;
      [exact Hassign|exact (msw_reasons_ent Hweak)|exact Hreasonent]. }
  assert (Hinj : reasons_var_injective
    (msolver_view n (msolver_record_enqueue M words c))).
  { eapply reasons_var_injective_assigns_one__record;
      [exact Hassign|exact (msw_reasons_inj Hweak)|exact Hreasoninj]. }
  pose proof (record_enqueue_reason_cases__record
    n F A_arr A_inst entry words c M Halloc0) as Hcases.
  assert (Hheadcases : c = 0 \/
    exists co, c <> 0 /\ Z.even c = true /\
      List.In (c, co) (msolver_db M) /\
      lit_var_c (co_watch0 co) = lit_var_c l).
  { destruct Hcases as [[Hcz Hnone]|[co [Hcnz [Heven [Hin [Hsome Hwatch]]]]]].
    - left. exact Hcz.
    - right. exists co. repeat split.
      + exact Hcnz.
      + exact Heven.
      + exact Hin.
      + exact Hwatch. }
  pose proof (record_enqueue_reason_cases__record
    n F A_arr A_inst entry words c M Halloc0) as Hcases2.
  assert (Hreasoncases :
    (c = 0 /\ reason = None) \/
    exists co, c <> 0 /\ Z.even c = true /\
      List.In (c, co) (msolver_db M) /\
      reason = Some (denote_obj co)).
  { unfold reason.
    destruct Hcases2 as
      [[Hcz Hnone]|[co [Hcnz [Heven [Hin [Hsome Hwatch]]]]]].
    - left. split.
      + exact Hcz.
      + exact Hnone.
    - right. exists co. repeat split.
      + exact Hcnz.
      + exact Heven.
      + exact Hin.
      + exact Hsome. }
  assert (Hevencases : c = 0 \/ Z.even c = true).
  { destruct Hheadcases as [Hcz|[co [Hcnz [Heven [Hin Hwatch]]]]].
    - left. exact Hcz.
    - right. exact Heven. }
  assert (Hdrain : mt_qhead (ms_core M) =
      Zlength (mt_trail (ms_core M))).
  { unfold solver_shape in Hshape. lia. }
  assert (Htrailimpl : trail_implied F (mt_enqueue (ms_core M) l)).
  { unfold l.
    eapply record_trail_implied_enqueue__record.
    - exact Hweak.
    - exact Hcert. }
  assert (Hweak' : msolver_inv_weak n F A_arr A_inst
      (msolver_enqueue_fresh M l c reason)).
  { constructor.
    - cbn. exact (msw_size Hweak).
    - exact (msw_n_range Hweak).
    - exact Hshape'.
    - exact (msw_F_wf Hweak).
    - exact (msw_A_wf Hweak).
    - cbn. eapply mtrail_wf_enqueue.
      + exact Htrailwf.
      + exact Hl.
      + exact Hfresh.
    - cbn. exact (msw_level_bound Hweak).
    - cbn. exact (msw_root_range Hweak).
    - cbn. rewrite (decisions_upto_enqueue n (ms_core M) l)
        by exact Htrailwf.
      exact (msw_assumptions Hweak).
    - exact (msw_assump_incl Hweak).
    - cbn. rewrite List.Forall_forall.
      intros a Ha.
      pose proof (msw_assump_sat Hweak) as Hassump.
      rewrite List.Forall_forall in Hassump.
      eapply assump_true_at_root_enqueue__record.
      + exact Htrailwf.
      + exact Hl.
      + exact Hfresh.
      + exact (Hassump a Ha).
    - change (stable_view
        (msolver_view n (msolver_record_enqueue M words c))).
      exact Hstable.
    - change (reasons_entailed F
        (msolver_view n (msolver_record_enqueue M words c))).
      exact Hent.
    - change (reasons_var_injective
        (msolver_view n (msolver_record_enqueue M words c))).
      exact Hinj.
    - cbn. exact Htrailimpl.
    - cbn. exact (msw_db_wf Hweak).
    - cbn. exact (msw_db_matches Hweak).
    - cbn. exact (msw_db_implied Hweak).
    - unfold l, reason.
      eapply db_complete_enqueue_fresh__record.
      + exact Hweak.
      + exact Hl.
      + exact Hfresh.
    - cbn. exact (msw_learnt_db Hweak).
    - cbn. exact (msw_prob_db Hweak).
    - cbn. exact (msw_binary_out Hweak).
    - eapply reasons_match_enqueue_fresh__record;
        [exact Hweak|exact Hl|exact Hfresh|exact Hreasoncases].
    - eapply reason_head_ok_enqueue_fresh__record;
        [exact Hweak|exact Hl|exact Hheadcases].
    - eapply binary_reason_same_level_enqueue_fresh__record;
        [exact Hweak|exact Hl|exact Hfresh|exact Hevencases].
    - cbn. exact (msw_wmap_exact Hweak).
    - cbn. exact (msw_tags_clear Hweak).
    - cbn. exact (msw_heap_wf Hweak).
    - cbn. exact (msw_cla_inc_nonnegative Hweak).
    - cbn. exact (msw_seed Hweak). }
  change (msolver_inv n F A_arr A_inst
    (msolver_enqueue_fresh M l c reason)).
  constructor.
  - exact Hweak'.
  - cbn. apply prop_level_enqueue. exact (msi_prop_level Hinv).
  - cbn. eapply minisat_watch_frontier_enqueue__record;
      [exact Htrailwf|exact Hl|exact Hfresh|exact Hdrain|].
    exact (msi_watch_frontier Hinv).
  - cbn. eapply heap_covers_enqueue_fresh__record;
      [exact Htrailwf|exact Hl|exact (msi_heap_covers Hinv)].
  - unfold l, reason.
    eapply current_reasonless_record_enqueue__record.
    exact Halloc0.
Qed.

Lemma record_allocated_cla_decay__record :
  forall n F A_arr A_inst entry words c M,
    record_allocated n F A_arr A_inst entry words c M ->
    ms_cla_decay M = ms_cla_decay entry.
Proof.
  intros n F A_arr A_inst entry words c M Halloc.
  destruct Halloc as [Hkind _].
  destruct Hkind as [[Hlen [Hcz HM]]|[Hlen [Hcnz Htrans]]].
  - subst M. reflexivity.
  - destruct Htrans as [Hfresh [HM _]].
    subst M.
    unfold msolver_install_learnt_clause,
      msolver_propagation_overlay, msolver_propagation_update. reflexivity.
Qed.


Lemma removable_dfs_loop_init__record :
  forall n M l minl C,
    analysis_tags_exact n (ms_tags M) (ms_tagged M) ->
    assigned_below_current (msolver_view n M) (lit_var_c l) ->
    reason_target_wf n M (lit_var_c l)
      (Znth (lit_var_c l) (ms_reason_words M) 0) C ->
    0 <= minl <= UINT_MAX ->
    removable_dfs_loop_inv n M l minl
      (ms_tagged M) (ms_tags M) (ms_tagged M)
      (lit_var_c l :: nil) nil.
Proof.
  intros n M l minl C Htags Hassigned Hreason Hminl.
  unfold removable_dfs_loop_inv.
  exists (@nil Z).
  split; [rewrite app_nil_r; reflexivity|].
  split; [exact Htags|].
  split.
  - constructor.
    + intro Hin. inversion Hin.
    + constructor.
  - split.
    + constructor.
      * intro Hin. inversion Hin.
      * constructor.
    + split.
      * reflexivity.
      * split.
        -- intros x [<- | []]. exact Hassigned.
        -- split.
           ++ intros v [<- | []].
              exists (Znth (lit_var_c l) (ms_reason_words M) 0), C.
              exact Hreason.
           ++ split.
              ** unfold dfs_witness. intros x Hin. inversion Hin.
              ** exact Hminl.
Qed.

