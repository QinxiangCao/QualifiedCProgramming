From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.Reals.Reals.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.

Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.
Tactic Notation "msat_order_select_sift_child_bound" ident(sz) :=
  (LLM_pre_process ltac:(lia || int_auto));
  match goal with
  | Hs : order_select_sift_inv ?nn _ _ _ _ ?hb _ _ _ _ _ |- _ =>
      msat_order_select_bound_sift_child_index Hs nn sz hb
  end.

Lemma msat_fp64_eq_finite_refl : forall x,
  fp64_isFinite x -> fp64_eq x x.
Proof.
  intros x Hfinite. unfold fp64_eq, fp64_compare.
  rewrite Binary.Bcompare_correct by exact Hfinite.
  rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
Qed.

Ltac msat_order_select_orp_left :=
  lazymatch goal with
  | |- _ |-- _ || _ => Left
  end.

Ltac msat_order_select_orp_right :=
  lazymatch goal with
  | |- _ |-- _ || _ => Right
  end.

Ltac msat_order_select_cursor_open :=
  (LLM_pre_process ltac:(lia || int_auto));
  msat_order_select_orp_left.

Tactic Notation "msat_order_select_cursor_ranges" ident(s_v) ident(cap_v)
    ident(heap_v) ident(n_v) ident(size_v) ident(next_v) ident(x_v)
    ident(h1) ident(h2) ident(h3) ident(h4) ident(h5) ident(h6) :=
  assert (h1 : INT_MIN <= cap_v <= INT_MAX) by lia;
  assert (h2 : INT_MIN <= Zlength heap_v <= INT_MAX) by lia;
  prop_rewrite (store_int_range (&(s_v # "solver_t" ->ₛ "size")) n_v);
  Intros_p h3;
  prop_rewrite (store_int_range (&("size")) size_v);
  Intros_p h4;
  prop_rewrite (store_int_range (&("next")) next_v);
  Intros_p h5;
  prop_rewrite (store_int_range (&("x")) x_v);
  Intros_p h6;
  change (INT_MIN <= cap_v <= INT_MAX) in h1;
  change (INT_MIN <= Zlength heap_v <= INT_MAX) in h2;
  change (INT_MIN <= n_v <= INT_MAX) in h3;
  change (INT_MIN <= size_v <= INT_MAX) in h4;
  change (INT_MIN <= next_v <= INT_MAX) in h5;
  change (INT_MIN <= x_v <= INT_MAX) in h6;
  split_pure_spatial;
  [ cancel
  | split_pures; dump_pre_spatial;
    solve [ auto | lia | rewrite Znth_replace_Znth_Same by lia; lia ] ].

Ltac msat_order_select_offsets_all leftidx rightidx heap :=
  replace (leftidx - 0) with leftidx in * by lia;
  replace (rightidx - 0) with rightidx in * by lia;
  replace (Znth leftidx heap 0 - 0) with (Znth leftidx heap 0) in * by lia;
  replace (Znth rightidx heap 0 - 0) with (Znth rightidx heap 0) in * by lia.

Ltac msat_order_select_offsets_goal leftidx rightidx heap :=
  replace (leftidx - 0) with leftidx by lia;
  replace (rightidx - 0) with rightidx by lia;
  replace (Znth leftidx heap 0 - 0) with (Znth leftidx heap 0) by lia;
  replace (Znth rightidx heap 0 - 0) with (Znth rightidx heap 0) by lia.

Ltac msat_sift_next_reads
    selected n size heap orderpos Hheaplen Hsize Hsift
    seed_shadow seed_value before activity_ptr activity0 :=
  msat_order_select_offsets_all
    (2 * selected + 1) (2 * selected + 1 + 1) heap;
  destruct (Z_le_gt_dec size (2 * selected + 1)) as [Hnone | Hleft];
  [ assert (Hleft_past : Znth (2 * selected + 1) heap 0 = 0) by
      (apply Znth_zero_past_end__order_select; rewrite Hheaplen, Hsize; lia);
    assert (Hright_past : Znth ((2 * selected + 1) + 1) heap 0 = 0) by
      (apply Znth_zero_past_end__order_select; rewrite Hheaplen, Hsize; lia);
    msat_order_select_orp_left;
    msat_order_select_orp_left;
    Exists seed_shadow seed_value before heap orderpos;
    rewrite <- Hheaplen;
    ((Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]));
    rewrite ?Hleft_past, ?Hright_past; lia
  | destruct (Z_le_gt_dec size ((2 * selected + 1) + 1))
      as [Honly_left | Hboth];
    [ assert (Hleft_range : 0 <= Znth (2 * selected + 1) heap 0 < n) by
        (eapply order_select_sift_inv_cell_range__order_select;
         [ exact Hsift | rewrite Hheaplen, Hsize; lia | lia ]);
      assert (Hright_past : Znth ((2 * selected + 1) + 1) heap 0 = 0) by
        (apply Znth_zero_past_end__order_select;
         rewrite Hheaplen, Hsize; lia);
      msat_order_select_orp_left;
      msat_order_select_orp_right;
      Exists seed_shadow seed_value before heap orderpos;
      rewrite <- Hheaplen;
      msat_order_select_offsets_goal
        (2 * selected + 1) (2 * selected + 1 + 1) heap;
      ((Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]));
      sep_apply_l_atomic
        (DoubleArray.seg_split_to_missing_i activity_ptr 0
          (Znth (2 * selected + 1) heap 0) n activity0 msat_fp64_zero);
      [ dump_pre_spatial; exact Hleft_range
      | unfold StoreDoubleAsElement.storeA, double_Znth;
        replace (Znth (2 * selected + 1) heap 0 - 0)
          with (Znth (2 * selected + 1) heap 0) by lia;
        cancel ]
    | assert (Hleft_range : 0 <= Znth (2 * selected + 1) heap 0 < n) by
        (eapply order_select_sift_inv_cell_range__order_select;
         [ exact Hsift | rewrite Hheaplen, Hsize; lia | lia ]);
      assert (Hright_range : 0 <= Znth ((2 * selected + 1) + 1) heap 0 < n) by
        (eapply order_select_sift_inv_cell_range__order_select;
         [ exact Hsift | rewrite Hheaplen, Hsize; lia | lia ]);
      assert (Hchildren_neq : Znth (2 * selected + 1) heap 0 <>
          Znth ((2 * selected + 1) + 1) heap 0) by
        (eapply order_select_sift_inv_cells_neq__order_select;
         [ exact Hsift | rewrite Hheaplen, Hsize; lia
         | rewrite Hheaplen, Hsize; lia | lia | lia | lia ]);
      msat_order_select_orp_right;
      Exists seed_shadow seed_value before heap orderpos;
      rewrite <- Hheaplen;
      msat_order_select_offsets_goal
        (2 * selected + 1) (2 * selected + 1 + 1) heap;
      ((Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]));
      sep_apply
        (double_array_seg_split_to_missing2__order_select activity_ptr
          (Znth (2 * selected + 1) heap 0)
          (Znth ((2 * selected + 1) + 1) heap 0)
          n activity0 Hleft_range Hright_range Hchildren_neq);
      unfold double_Znth;
      replace (Znth (2 * selected + 1) heap 0 - 0)
        with (Znth (2 * selected + 1) heap 0) by lia;
      replace (Znth (2 * selected + 1 + 1) heap 0 - 0)
        with (Znth (2 * selected + 1 + 1) heap 0) by lia;
      msat_manual_entailer_with ltac:(lia) ] ].

Tactic Notation "msat_order_select_sift_capacity"
    ident(s_v) ident(optr) ident(cap_v) :=
  let hcap := fresh "Hcap" in
  let hroom := fresh "Hroom" in
  match goal with
  | hinv : order_select_sift_inv ?n_v _ _ _ _ ?before_v ?now_v _ _ _ _ |- _ =>
  rewrite Znth_replace_Znth_Same by lia;
  assert (Hbounds : 0 <= Zlength now_v <= n_v /\
      0 <= n_v /\ n_v <= INT_MAX /\ 2 * n_v <= INT_MAX);
  [ pose proof hinv as Hinv_bounds;
    unfold order_select_sift_inv in Hinv_bounds;
    destruct Hinv_bounds as
      (Htwice & Hpopped & Hincl & Hassigns & Hvalues & Hassigned &
       Hcovers & Hhole);
    unfold order_heap_one_hole in Hhole;
    destruct Hhole as
      (Hposlen & Hheaplen & Hhole_range & Hxrange & Hnodup & Hrange &
       Hperm & Hinverse & Hout);
    assert (Hn : 0 <= n_v) by lia;
    assert (Hlen : Zlength (list_without_Znth 0 before_v) <= n_v);
    [ rewrite Zlength_correct;
      apply (NoDup_Z_bounded_length
        (list_without_Znth 0 before_v) n_v Hn Hnodup);
      intros u Hu; rewrite Forall_forall in Hrange; exact (Hrange u Hu)
    | ];
    rewrite Hheaplen; lia
  | ];
  assert (hcap : INT_MIN <= cap_v <= INT_MAX) by lia;
  prop_rewrite (IntArray.undef_seg_valid
    optr (Zlength now_v) cap_v);
  Intros_p hroom;
  msat_manual_entailer_with ltac:(int_auto)
  end.

Tactic Notation "msat_order_select_sift_siblings"
    ident(act_ptr) ident(act0) ident(n_v) ident(child_v) ident(heap_v)
    ident(hz2) ident(hz3) ident(hz4) ident(hz5) ident(hz6) :=
  bind_fact ( 0 <= Znth child_v heap_v 0 ) as hz2;
  bind_fact ( Znth child_v heap_v 0 < n_v ) as hz3;
  bind_fact ( 0 <= Znth (child_v + 1 - 0) heap_v 0 ) as hz4;
  bind_fact ( Znth (child_v + 1 - 0) heap_v 0 < n_v ) as hz5;
  bind_fact ( Znth child_v heap_v 0 <> Znth (child_v + 1 - 0) heap_v 0 )
    as hz6;
  replace (child_v + 1 - 0) with (child_v + 1) in * by lia;
  replace (Znth child_v heap_v 0 - 0)
    with (Znth child_v heap_v 0) in * by lia;
  replace (Znth (child_v + 1) heap_v 0 - 0)
    with (Znth (child_v + 1) heap_v 0) in * by lia;
  sep_apply
    (double_array_missing2_refold act_ptr
      (Znth child_v heap_v 0) (Znth (child_v + 1) heap_v 0)
      n_v act0 (conj hz2 hz3) (conj hz4 hz5) hz6).

(* [chld] says
   whether the goal still spells the child index as [child - 0]; [wide] says
   whether the two sibling activity cells have to be refolded, which is the
   only other difference between the four members. *)
Tactic Notation "msat_order_select_sift_promote" ident(hz) ident(hinv)
    ident(hp) ident(op) constr(chld) constr(wide)
    ident(hz2) ident(hz3) ident(hz4) ident(hz5) ident(hz6) :=
  (LLM_pre_process ltac:(lia || int_auto));
  lazymatch goal with
  | Hsi : order_select_sift_inv ?n ?next ?x ?i ?heap0 ?sift_heap_before
            ?sift_heap_now ?sift_orderpos_now ?assigns0 ?trail0 ?qhead,
    Hseed : fp64_eq ?sift_seed_value_now (Z_to_fp64 ?sift_seed_shadow_now),
    Hact : Zlength ?activity0 = ?n,
    Hchild : ?child = 2 * ?i + 1
    |- context [ IntArray.undef_seg ?order_ptr _ ?order_cap ] =>
  lazymatch goal with
  | |- context [ IntArray.full ?orderpos_ptr n _ ] =>
  lazymatch goal with
  | |- context [ DoubleArray.seg ?activity_ptr 0 n activity0 ] =>
      bind_fact ( Znth (next - 0) assigns0 0 <> 0 ) as hz;
      bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before sift_heap_now
        sift_orderpos_now assigns0 trail0 qhead ) as hinv;
      replace (next - 0) with next in * by lia;
      lazymatch chld with
      | true => replace (child - 0) with child in * by lia
      | false => idtac
      end;
      lazymatch wide with
      | true =>
          msat_order_select_sift_siblings activity_ptr activity0 n child
            sift_heap_now hz2 hz3 hz4 hz5 hz6
      | false => idtac
      end;
      set (hp := replace_Znth i x sift_heap_now);
      set (op := replace_Znth (Znth i hp 0) i sift_orderpos_now);
      assert (Hmoved : Znth i hp 0 = x);
      [ subst hp; rewrite Znth_replace_Znth_Same by lia; reflexivity | ];
      assert (Hloop : order_select_loop_inv n heap0 hp op assigns0 trail0 qhead);
      [ subst op; rewrite Hmoved;
        eapply order_select_sift_close_assigned__order_select
          with (popped := next) (before := sift_heap_before);
        [ exact hinv | exact hz ]
      | ];
      assert (Hheaplen : Zlength hp = Zlength sift_heap_now);
      [ subst hp; rewrite Zlength_replace_Znth; reflexivity | ];
      assert (Hcap_range : INT_MIN <= order_cap <= INT_MAX) by lia;
      prop_apply_p (IntArray.undef_seg_valid
        order_ptr (Zlength sift_heap_now) order_cap);
      Intros_p Hcap_room;
      sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n op);
      sep_apply_l_atomic (IntArray.full_to_seg order_ptr
        (Zlength sift_heap_now) hp);
      Exists sift_seed_shadow_now sift_seed_value_now hp op;
      rewrite <- Hheaplen;
      (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]);
      csimpl; cancel
  end
  end
  end.

Ltac msat_order_select_sift_close
    s_pre order_ptr order_cap orderpos_ptr activity_ptr :=
  lazymatch goal with
  | Hsi : order_select_sift_inv ?n ?next ?x ?i ?heap0 ?sift_heap_before
            ?sift_heap_now ?sift_orderpos_now ?assigns0 ?trail0 ?qhead,
    Hseed : fp64_eq ?sift_seed_value_now (Z_to_fp64 ?sift_seed_shadow_now),
    Hact : Zlength ?activity0 = ?n,
    Hz : Znth (?next - 0) ?assigns0 0 = 0,
    Ha : 0 <= Znth (?child - 0) ?sift_heap_now 0,
    Hb : Znth (?child - 0) ?sift_heap_now 0 < ?n,
    Hc : 0 <= Znth (?child + 1 - 0) ?sift_heap_now 0,
    Hd : Znth (?child + 1 - 0) ?sift_heap_now 0 < ?n,
    He : Znth (?child - 0) ?sift_heap_now 0
           <> Znth (?child + 1 - 0) ?sift_heap_now 0 |- _ =>
      replace (next - 0) with next in * by lia;
      replace (child - 0) with child in * by lia;
      replace (child + 1 - 0) with (child + 1) in * by lia;
      replace (Znth child sift_heap_now 0 - 0)
        with (Znth child sift_heap_now 0) in * by lia;
      replace (Znth (child + 1) sift_heap_now 0 - 0)
        with (Znth (child + 1) sift_heap_now 0) in * by lia;
      assert (Hati : Znth i (replace_Znth i x sift_heap_now) 0 = x)
        by (rewrite Znth_replace_Znth_Same; lia);
      rewrite Hati in *;
      pose proof (order_select_sift_close_post__order_select
        n next x i heap0 sift_heap_before sift_heap_now sift_orderpos_now
        assigns0 trail0 qhead Hsi Hz) as Hpost;
      assert (Hcap_range : INT_MIN <= order_cap <= INT_MAX) by lia;
      prop_apply_p (IntArray.undef_seg_valid
        order_ptr (Zlength sift_heap_now) order_cap);
      Intros_p Hcap_room;
      sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
        (replace_Znth x i sift_orderpos_now));
      sep_apply_l_atomic (IntArray.full_to_seg order_ptr
        (Zlength sift_heap_now) (replace_Znth i x sift_heap_now));
      sep_apply_l_atomic (double_array_missing2_refold
        activity_ptr (Znth child sift_heap_now 0)
        (Znth (child + 1) sift_heap_now 0) n activity0
        (conj Ha Hb) (conj Hc Hd) He);
      Exists sift_seed_shadow_now sift_seed_value_now
        (replace_Znth i x sift_heap_now) (replace_Znth x i sift_orderpos_now);
      rewrite <- (Zlength_replace_Znth sift_heap_now i x);
      sep_apply (Veci.rep_intro &(s_pre # "solver_t" ->ₛ "order") order_ptr (replace_Znth i x sift_heap_now) order_cap _ _ _ eq_refl eq_refl eq_refl ltac:(rewrite Zlength_replace_Znth; lia) ltac:(lia) ltac:(vec_buf_solve));
      ((Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]))
  end.

Ltac msat_clause_remove_close
    s is_learnt hdr count found1 long_clause learnt_stats :=
  msat_subst_lit_retvals;
  sep_apply full_to_wlists_rep;
  unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals in *;
  lazymatch goal with
  | Hready : clause_remove_ready ?n ?c ?words ?wm ?stats,
    Hremove : first_occurrence _
      (Znth (lit_neg_c (Znth 0 ?words 0)) ?wm nil) ?found0 |- _ =>
    let Hdiv := fresh "Hclause_size" in
    let Hlen := fresh "Hclause_min_length" in
    let Hsize := fresh "Hclause_length_nonneg" in
    let Hhdr := fresh "Hclause_header_nonneg" in
    let Hb := fresh "Hlong_clause" in
    bind_fact (hdr = clause_hdr_word is_learnt (Zlength words) ÷ 2) as Hdiv;
    unfold clause_remove_ready in Hready;
    destruct Hready as (Hlen & _);
    assert (Hsize : 0 <= Zlength words) by apply Zlength_nonneg;
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength words))
      by (apply clause_hdr_word_nonneg; exact Hsize);
    rewrite zdiv_equiv in Hdiv by lia;
    rewrite clause_hdr_word_div2 in Hdiv by lia;
    assert (Hb : (2 <? Zlength words)%Z = long_clause) by
      (lazymatch long_clause with
       | true => apply Z.ltb_lt; lia
       | false => apply Z.ltb_ge; lia
       end);
    let x5 := lazymatch learnt_stats with
      | true => constr:(Znth 5 stats 0)
      | false => constr:(unsigned_last_nbits (Znth 5 stats 0 - 1) 64)
      end in
    let x6 := lazymatch learnt_stats with
      | true => constr:(Znth 6 stats 0)
      | false => constr:(unsigned_last_nbits
          (Znth 6 stats 0 - unsigned_last_nbits count 64) 64)
      end in
    let x7 := lazymatch learnt_stats with
      | true => constr:(unsigned_last_nbits (Znth 7 stats 0 - 1) 64)
      | false => constr:(Znth 7 stats 0)
      end in
    let x8 := lazymatch learnt_stats with
      | true => constr:(unsigned_last_nbits
          (Znth 8 stats 0 - unsigned_last_nbits count 64) 64)
      | false => constr:(Znth 8 stats 0)
      end in
    let next_wm := fresh "wm_after_remove" in
    let next_stats := fresh "stats_after_remove" in
    set (next_wm :=
      replace_Znth (lit_neg_c (Znth 1 words 0))
        (remove_nth found1 (Znth (lit_neg_c (Znth 1 words 0))
            (replace_Znth (lit_neg_c (Znth 0 words 0))
              (remove_nth found0
                (Znth (lit_neg_c (Znth 0 words 0)) wm nil)) wm)
            nil))
        (replace_Znth (lit_neg_c (Znth 0 words 0))
          (remove_nth found0 (Znth (lit_neg_c (Znth 0 words 0)) wm nil)) wm));
    set (next_stats :=
      Znth 0 stats 0 :: Znth 1 stats 0 :: Znth 2 stats 0 ::
      Znth 3 stats 0 :: Znth 4 stats 0 :: x5 :: x6 :: x7 :: x8 ::
      Znth 9 stats 0 :: Znth 10 stats 0 :: nil);
    sep_apply
      (stats_rep_from_solver_cells__clause_new s
        (Znth 0 stats 0) (Znth 1 stats 0) (Znth 2 stats 0)
        (Znth 3 stats 0) (Znth 4 stats 0) x5 x6 x7 x8
        (Znth 9 stats 0) (Znth 10 stats 0));
    unfold clause_remove_post;
    Exists next_wm; Exists next_stats;
    unfold clause_remove_result, wmap_remove_first;
    subst next_stats;
    split_pure_spatial;
    [ cancel; cancel (&( s # "solver_t" ->ₛ "size") # Int |-> n)
    | dump_pre_spatial;
      split;
      [ exists found0, found1;
        exists
          (replace_Znth (lit_neg_c (Znth 0 words 0))
            (remove_nth found0 (Znth (lit_neg_c (Znth 0 words 0)) wm nil)) wm);
        subst next_wm;
        unfold clause_watch_word; rewrite Hb;
        split;
        [ exact Hremove
        | split; [ reflexivity | split; [ assumption | reflexivity ] ] ]
      | repeat split; solve [auto | int_auto] ] ]
  end.

Ltac msat_clause_simplify_hdr_word_safety :=
  msat_split_after_llm;
  match goal with
  | Hlim : clause_hdr_word ?isl (Zlength ?cw) <= 2147483647,
    Hrv : ?rv = clause_hdr_word ?isl (Zlength ?cw) ÷ 2 |- _ =>
      dump_pre_spatial;
      assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
        by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
      rewrite zdiv_equiv in Hrv by lia;
      rewrite clause_hdr_word_div2 in Hrv by apply Zlength_nonneg;
      unfold clause_hdr_word in Hlim;
      destruct isl; lia
  end.

Tactic Notation "msat_clause_simplify_scan_step" ident(nn) ident(ii) ident(cw)
    ident(asg) ident(isl) ident(rv) ident(rv2) ident(rv3) ident(clit) ident(cval)
    ident(lts) ident(aptr) constr(cellval) uconstr(hpol) :=
  ( let hcell := fresh "H_cell" in
    let hpolarity := fresh "H_polarity" in
    let hsign := fresh "H_sign" in
    let hhalf := fresh "H_hdr_half" in
    let hinv := fresh "H_scan_inv" in
    ( bind_fact ( Znth rv3 (replace_Znth (lit_var_c clit) cval asg) 0 <> cellval ) as hcell;
      bind_fact ( hpol ) as hpolarity;
      bind_fact ( rv2 = lit_sign_c clit ) as hsign;
      bind_fact ( rv = clause_hdr_word isl (Zlength cw) ÷ 2 ) as hhalf;
      bind_fact ( clause_simplify_scan_inv nn cw asg ii ) as hinv;
      unfold clause_simplify_scan_inv in hinv;
      destruct hinv as (Hi & Halen & Hlits & Hcells & Hprefix);
      assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
        by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
      rewrite zdiv_equiv in hhalf by lia;
      rewrite clause_hdr_word_div2 in hhalf by apply Zlength_nonneg;
      lazymatch goal with
      | |- _ |-- “ _ ” =>
        unfold clause_simplify_scan_inv;
        repeat split; auto; try lia;
        intros j Hj;
        destruct (Z.lt_ge_cases j ii) as [Hji | Hji];
        [ apply Hprefix; lia
        | assert (j = ii) by lia; subst j;
          subst rv3 cval clit;
          rewrite replace_Znth_Znth in hcell by lia;
          unfold packed_lit_satisfying_value, lit_sign_c in hpolarity, hsign |- *;
          destruct (Z.odd (Znth ii cw 0)); simpl in *; lia ]
      | |- _ =>
        subst rv3 cval clit;
        rewrite replace_Znth_Znth by lia;
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full lts ii (Zlength cw) (Znth ii cw 0) cw);
        [ dump_pre_spatial; lia
        | rewrite replace_Znth_Znth by lia;
          sep_apply_l_atomic (CharArray.full_to_seg aptr nn asg);
          sep_apply_l_atomic (IntArray.full_to_seg lts (Zlength cw) cw);
          cancel ]
      end ) ).

(* The fact is located by its shape, so
   the tactic can be called from a nested arm that does not know its name. *)

(* Fresh fact
   names avoid resolving [in H] binders when the tactic is defined. *)
Tactic Notation "msat_clause_simplify_scan_exit" ident(nn) ident(ii) ident(cw)
    ident(asg) ident(isl) ident(rv) ident(rv2) ident(rv3) ident(clit) ident(cval)
    ident(lts) ident(cp) ident(aptr) constr(cellval) uconstr(hpol) :=
  ( let hcell := fresh "H_cell" in
    let hpolarity := fresh "H_polarity" in
    let hsign := fresh "H_sign" in
    let hhalf := fresh "H_hdr_half" in
    let hinv := fresh "H_scan_inv" in
    ( bind_fact ( Znth rv3 (replace_Znth (lit_var_c clit) cval asg) 0 = cellval ) as hcell;
      bind_fact ( hpol ) as hpolarity;
      bind_fact ( rv2 = lit_sign_c clit ) as hsign;
      bind_fact ( rv = clause_hdr_word isl (Zlength cw) ÷ 2 ) as hhalf;
      bind_fact ( clause_simplify_scan_inv nn cw asg ii ) as hinv;
      unfold clause_simplify_scan_inv in hinv;
      destruct hinv as (Hi & Halen & Hlits & Hcells & Hprefix);
      assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
        by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
      rewrite zdiv_equiv in hhalf by lia;
      rewrite clause_hdr_word_div2 in hhalf by apply Zlength_nonneg;
      lazymatch goal with
      | |- _ |-- “ _ ” =>
        unfold clause_simplify_result, packed_lit_satisfying_value;
        left; split; [reflexivity|];
        exists ii; split; [lia|];
        subst rv3 cval clit;
        rewrite replace_Znth_Znth in hcell by lia;
        unfold lit_sign_c in hpolarity, hsign |- *;
        destruct (Z.odd (Znth ii cw 0)); simpl in *; lia
      | |- _ =>
        subst lts rv3 cval clit;
        rewrite replace_Znth_Znth by lia;
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
            (clause_lits_addr cp) ii (Zlength cw) (Znth ii cw 0) cw);
        [ dump_pre_spatial; lia
        | rewrite replace_Znth_Znth by lia;
          sep_apply_l_atomic (CharArray.full_to_seg aptr nn asg);
          sep_apply_l_atomic (IntArray.full_to_seg (clause_lits_addr cp) (Zlength cw) cw);
          cancel ]
      end ) ).

Ltac snv_unfold_all_unfolded_post :=
  unfold solver_rep_growable, solver_rep_at,
         solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
         solver_levels_slice_at, solver_scalars_rep,
         solver_vecs_rep, solver_fp_rep, solver_trail_array_rep,
         setnvars_frame_at, setnvars_open_at, setnvars_arrays_at.

Ltac msat_setnvars_order_update_pre :=
  msat_split_after_llm; snv_shape;
  let hp := fresh "Hpre" in
  let hp2 := fresh "Hpre2" in
  (match goal with
   | H : solver_support_inv _ _ _ _ ?root ?M |- _ =>
       pose proof (solver_support_inv_order_update_pre__api_reentry
         _ _ _ _ root M H ltac:(lia) ltac:(lia)) as hp
   end;
   pose proof hp as hp2;
   match goal with H : ms_size _ = _ |- _ => rewrite H in hp2 end).

Ltac msat_enqueue_assign_frame qtail asgl lvls rsns trail rsnp trlp asgp n
    Hsig Heq :=
  unfold enqueue_post_at, enqueue_state_at, enqueue_transition;
  Exists qtail asgl lvls rsns trail rsnp trlp;
  rewrite Hsig in Heq;
  sep_apply_l_atomic (CharArray.full_to_seg asgp n asgl);
  split_pure_spatial; [ cancel | split_pures; dump_pre_spatial; try lia ].

Ltac msat_enqueue_assign_keep_close s rv lpre l0 asgl qtail lvls rsns trail
    rsnp trlp asgp n :=
  let Hrv := fresh "H_retval_2" in
  let Hsig := fresh "Hsig" in
  let Heq := fresh "Heq" in
  bind_fact ( rv = lit_sign_c lpre ) as Hrv;
  try rewrite replace_Znth_Znth in *;
  assert (Hsig : lit_sig l0 = s)
    by (subst lpre; unfold lit_sign_c in Hrv; unfold lit_sig;
        destruct (Z.odd l0); lia);
  destruct (Z.eq_dec (Znth (lit_var_c l0) asgl 0) (lit_sig l0)) as [Heq | Heq];
  msat_enqueue_assign_frame qtail asgl lvls rsns trail rsnp trlp asgp n Hsig Heq;
  lazymatch type of Heq with
  | _ <> _ => right; left
  | _ = _ => left
  end;
  solve [repeat split; auto; lia].

Ltac msat_enqueue_assign_bump_close s rv lpre rv3 l0 asgl qtail lvls rsns
    trail rsnp trlp asgp lvlp n lim reasonp :=
  let Hrv := fresh "H_retval_2" in
  let Hsig := fresh "Hsig" in
  bind_fact ( rv = lit_sign_c lpre ) as Hrv;
  try rewrite replace_Znth_Znth in *;
  subst lpre; subst rv3;
  assert (Hsig : lit_sig l0 = s)
    by (unfold lit_sign_c in Hrv; unfold lit_sig; destruct (Z.odd l0); lia);
  rewrite !replace_Znth_replace_Znth_Same by lia;
  unfold enqueue_post_at, enqueue_state_at, enqueue_transition;
  Exists (qtail + 1)
    (replace_Znth (lit_var_c l0) (lit_sig l0) asgl)
    (replace_Znth (lit_var_c l0) (Zlength lim) lvls)
    (replace_Znth (lit_var_c l0) reasonp rsns)
    (trail ++ l0 :: nil) rsnp trlp;
  rewrite Hsig;
  sep_apply_l_atomic
    (CharArray.full_to_seg asgp n (replace_Znth (lit_var_c l0) s asgl));
  sep_apply_l_atomic
    (IntArray.full_to_seg lvlp n
       (replace_Znth (lit_var_c l0) (Zlength lim) lvls));
  sep_apply_l_atomic
    (PtrArray.full_to_seg rsnp n
       (replace_Znth (lit_var_c l0) reasonp rsns));
  split_pure_spatial;
  [ cancel
  | split_pures;
    [ dump_pre_spatial; right; right; repeat split; auto
    | dump_pre_spatial;
      rewrite !Zlength_replace_Znth;
      rewrite Zlength_app, Zlength_cons, Zlength_nil;
      lia ] ].

(* Retain the requested prefix and the suffix allocation, forgetting only
   suffix values. *)
Ltac msat_forget_array_suffix split_segment forget_segment merge_undefined
    p cut live cap words :=
  sep_apply_l_atomic (split_segment p 0 cut live words);
  [ dump_pre_spatial; lia
  | sep_apply_l_atomic
      (forget_segment p cut live (sublist (cut - 0) (live - 0) words));
    sep_apply_l_atomic (merge_undefined p cut live cap);
    [ dump_pre_spatial; lia | idtac ] ].

Lemma record_install_allocated : forall n F Aarr Ainst M words c,
  msolver_inv n F Aarr Ainst M -> record_clause_cert n F M words ->
  mt_qhead (ms_core M) = ms_qtail M ->
  ms_capacity_root_propagation_pending M = 0 -> msolver_seed_shadow M ->
  2 <= Zlength words -> clause_allocator_fresh M c ->
  lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
  record_allocated n F Aarr Ainst M words c
    (msolver_install_learnt_clause M c words).
Proof.
 intros n F Aarr Ainst M words c Hinv Hcert Hq Hp Hseed Hlen Hfresh Hne.
 pose proof Hcert as [_ [Hwf _]].
 pose proof (lit_neg_c_wf _ _ (Forall_lit_wf_Znth n words 0 Hwf ltac:(lia))) as Hi.
 pose proof (lit_neg_c_wf _ _ (Forall_lit_wf_Znth n words 1 Hwf ltac:(lia))) as Hj.
 unfold lit_wf_c in Hi,Hj.
 assert (Hinstalled : msolver_inv n F Aarr Ainst (msolver_install_learnt_clause M c words)).
 { rewrite msolver_install_learnt_clause_gen.
   pose proof (msolver_inv_install_gen n F Aarr Ainst M c words 1 ltac:(lia)
     Hinv Hfresh Hcert Hlen Hne Hi Hj) as H.
   rewrite cn_F_learnt, sel_learnt_learnt in H. exact H. }
 assert (Hinstalled_cert : record_clause_cert n F (msolver_install_learnt_clause M c words) words).
 { pose proof (clause_install_cert_install_gen n F M c words 1 ltac:(lia) Hcert) as H.
   rewrite cn_F_learnt, sel_learnt_learnt in H. exact H. }
 apply clause_new_success_record_allocated__prep_pub_cap_exit; [exact Hlen|exact Hq|].
 split; [exact Hfresh|]. split; [reflexivity|].
 split; [exact Hinstalled|]. split; [exact Hp|]. split; assumption.
Qed.

(* Close the two watch holes of [clause_new] with the pushed watch vectors. *)
Lemma wlists_clause_new_refold : forall wl M c words,
  Zlength (ms_wm M) = 2 * ms_size M ->
  0 <= lit_neg_c (Znth 0 words 0) < 2 * ms_size M ->
  0 <= lit_neg_c (Znth 1 words 0) < 2 * ms_size M ->
  lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
  VecpArray.missing2 wl (lit_neg_c (Znth 0 words 0))
    (lit_neg_c (Znth 1 words 0)) (2 * ms_size M) (ms_wm M) **
  Vecp.rep (Vecp.slot wl (lit_neg_c (Znth 0 words 0)))
    (Znth (lit_neg_c (Znth 0 words 0)) (ms_wm M) nil ++
     (clause_watch_word c words (Znth 1 words 0) :: nil)) **
  Vecp.rep (Vecp.slot wl (lit_neg_c (Znth 1 words 0)))
    (Znth (lit_neg_c (Znth 1 words 0)) (ms_wm M) nil ++
     (clause_watch_word c words (Znth 0 words 0) :: nil))
  |-- VecpArray.full wl (2 * ms_size M) (clause_new_watch_map M c words).
Proof.
  intros wl M c words Hlen Hi Hj Hne.
  unfold clause_new_watch_map, wmap_push_word.
  rewrite (Znth_replace_Znth_Diff nil (ms_wm M) (lit_neg_c (Znth 0 words 0))
    (lit_neg_c (Znth 1 words 0))) by lia.
  change (Vecp.rep (Vecp.slot wl (lit_neg_c (Znth 0 words 0))))
    with (VecpArray.vec_store wl (lit_neg_c (Znth 0 words 0))).
  change (Vecp.rep (Vecp.slot wl (lit_neg_c (Znth 1 words 0))))
    with (VecpArray.vec_store wl (lit_neg_c (Znth 1 words 0))).
  sep_apply (VecpArray.missing2_merge_to_full wl (lit_neg_c (Znth 0 words 0))
    (lit_neg_c (Znth 1 words 0)) (2 * ms_size M) (ms_wm M)); [ | lia .. ].
  rewrite (replace_Znth_comm (lit_neg_c (Znth 0 words 0)) (lit_neg_c (Znth 1 words 0)))
    by (rewrite ?Zlength_replace_Znth; lia).
  cancel.
Qed.

Lemma record_pending_install : forall s begin lvl n F Aarr Ainst M words c wl,
 msolver_inv n F Aarr Ainst M -> record_clause_cert n F M words ->
 mt_qhead (ms_core M) = ms_qtail M ->
 ms_capacity_root_propagation_pending M = 0 -> msolver_seed_shadow M ->
 clause_new_pending_at_root s begin lvl n F Aarr Ainst M words c 1 wl (ms_root_level M)
 |-- EX Mstage : msolver,
 “ record_allocated n F Aarr Ainst M words c Mstage ” &&
 (solver_record_rep_at s Mstage wl lvl (db_words (ms_learnt M)) **
 IntArray.seg begin 0 (Zlength words) words).
Proof.
 intros s begin lvl n F Aarr Ainst M words c wl Hinv Hcert Hq Hp Hseed.
 unfold clause_new_pending_at_root. Intros.
 destruct H as [Hsel [Hn [Hstage [Hfresh Hne]]]].
 pose proof (msi_shape Hinv) as Hshape.
 pose proof (solver_shape_wm_len M Hshape) as Hwm.
 destruct Hstage as [_ [Hlen Hstagerest]].
 pose proof Hcert as [_ [Hwf _]].
 pose proof (lit_neg_c_wf _ _ (Forall_lit_wf_Znth n words 0 Hwf ltac:(lia))) as Hi.
 pose proof (lit_neg_c_wf _ _ (Forall_lit_wf_Znth n words 1 Hwf ltac:(lia))) as Hj.
 unfold lit_wf_c in Hi,Hj.
 set (Mnew := msolver_install_learnt_clause M c words).
 pose proof (record_install_allocated n F Aarr Ainst M words c Hinv Hcert Hq Hp Hseed Hlen Hfresh Hne) as Halloc.
 change (record_allocated n F Aarr Ainst M words c Mnew) in Halloc.
 pose proof (msi_shape (proj1 (proj2 (proj2 Halloc)))) as Hshape_new.
 Exists Mnew.
 unfold clause_new_transaction_rest_at_gen.
 rewrite clause_new_frame_at_gen_learnt.
 split_pure_spatial.
 - cancel (IntArray.seg begin 0 (Zlength words) words).
   sep_apply (wlists_clause_new_refold wl M c words Hwm ltac:(lia) ltac:(lia) Hne).
   assert (Hsingle : MiniSatClause.rep c true words |-- clause_db_rep ((c,clause_obj_of words true)::nil)).
   { simpl. cancel (MiniSatClause.rep c true words). cancel. }
   rewrite sel_learnt_learnt, sel_db_learnt, sel_vec_learnt.
   sep_apply Hsingle.
   sep_apply (clause_db_rep_app_intro (ms_learnt M) ((c,clause_obj_of words true)::nil)).
   unfold solver_record_rep_at.
   unfold clause_new_frame_at.
   Intros act asg opos rsn trl tgs.
   Exists act asg opos rsn trl tgs.
   unfold Mnew.
   rewrite msolver_install_learnt_clause_gen.
   unfold clause_new_scalars_frame, solver_vecs_without_learnts_rep, clause_new_ptrs_frame, solver_fp_rep,
   solver_var_arrays_rep, solver_trail_array_rep, solver_wlists_handle, wlists_rep.
   unfold msolver_install_clause, msolver_propagation_overlay, msolver_propagation_update.
   cbn -[Znth replace_Znth clause_new_watch_map DoubleArray.seg IntArray.seg PtrArray.seg CharArray.seg store_double store_float Z.mul].
   split_pure_spatial.
   + rewrite Hn. msat_manual_entailer_with ltac:(assumption || lia).
   + split_pures.
     * dump_pre_spatial. exact Hshape_new.
     * dump_pre_spatial. rewrite clause_new_watch_map_Zlength. exact Hwm.
 - dump_pre_spatial. exact Halloc.
Qed.

Lemma record_rep_open : forall s M wl lvl,
  solver_rep_levels_wl_at s M wl lvl
  |-- solver_record_rep_at s M wl lvl (db_words (ms_learnt M)).
Proof.
  intros s M wl lvl.
  unfold solver_rep_levels_wl_at.
  Intros act asg opos rsn trl tgs.
  unfold solver_record_rep_at, clause_new_frame_at.
  Exists act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, clause_new_scalars_frame, solver_vecs_without_learnts_rep,
    clause_new_ptrs_frame, solver_scalars_rep, solver_vecs_rep,
    solver_ptrs_rep, solver_var_arrays_rep, solver_wlists_handle, db_words.
  msat_entailer_with lia.
Qed.

Lemma record_finish_publish_inv :
  forall n F A_arr A_inst entry enqueued words c cla_inc current,
  record_finish_with_capacity n F A_arr A_inst entry enqueued words c cla_inc current ->
  msolver_inv n F A_arr A_inst current /\
  ms_capacity_root_propagation_pending current = 0 /\
  msolver_seed_shadow current /\
  ms_model current = ms_model entry /\
  ms_cla_decay current = ms_cla_decay entry /\
  ms_cap current = ms_cap entry /\
  minisat_record_reuse entry words current.
Proof.
  intros n F A_arr A_inst entry enqueued words c cla_inc current [_ Hpost].
  exact Hpost.
Qed.

Lemma record_rep_close : forall s M wl lvl,
  solver_record_rep_at s M wl lvl (db_words (ms_learnt M))
  |-- solver_rep_levels_wl_at s M wl lvl.
Proof.
  intros s M wl lvl.
  unfold solver_record_rep_at, clause_new_frame_at.
  Intros act asg opos rsn trl tgs.
  unfold solver_rep_levels_wl_at.
  Exists act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, clause_new_scalars_frame, solver_vecs_without_learnts_rep,
    clause_new_ptrs_frame, solver_scalars_rep, solver_vecs_rep,
    solver_ptrs_rep, solver_var_arrays_rep, solver_wlists_handle, db_words.
  msat_entailer_with lia.
Qed.

Lemma record_rep_enqueue_focus : forall s M lvl wl stored,
  solver_record_rep_at s M wl lvl stored |--
  EX asg : Z,
    enqueue_state_at s asg lvl (ms_size M) (ms_cap M) (ms_qtail M)
      (mt_assigns (ms_core M)) (mt_levels (ms_core M))
      (ms_reason_words M) (mt_trail (ms_core M))
      (mt_lim (ms_core M)) **
    solver_record_enqueue_frame_at s M wl stored.
Proof.
  intros s M lvl wl stored.
  unfold solver_record_rep_at, clause_new_frame_at,
    solver_record_enqueue_frame_at, solver_record_enqueue_cells_at,
    solver_record_enqueue_vecs_frame, enqueue_state_at,
    solver_scalars_without_qtail_rep, clause_new_scalars_frame,
    solver_vecs_without_learnts_rep, clause_new_ptrs_frame, solver_wlists_handle,
    solver_trail_array_rep, solver_var_arrays_rep, db_words.
  Intros act asg opos rsn trl tgs.
  Exists asg rsn trl act opos tgs.
  msat_entailer_with ltac:(unfold solver_shape in H; tauto).
Qed.

Lemma record_enqueue_refold :
  forall s assigns_ptr levels_ptr l c n cap qtail
         assigns levels reasons trail lim M reason_opt wl stored,
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
    solver_record_enqueue_frame_at s M wl stored
    |-- solver_record_rep_at s
          (msolver_enqueue_fresh M l c reason_opt)
          wl levels_ptr stored.
Proof.
  intros s assigns_ptr levels_ptr l c n cap qtail
         assigns levels reasons trail lim M reason_opt wl stored
         Hn Hcap Hqtail Hassigns Hlevels Hreasons Htrail Hlim
         Hshape Hfresh.
  msat_enqueue_refold_transition n cap qtail assigns levels reasons trail lim
    l Hfresh rsn trl Htransition qtail' assigns' levels' reasons' trail'.
    unfold solver_record_enqueue_frame_at, solver_record_enqueue_cells_at.
    Intros act opos tgs.
    unfold solver_record_rep_at, clause_new_frame_at.
    Exists act assigns_ptr opos rsn trl tgs.
    unfold solver_record_enqueue_vecs_frame, clause_new_scalars_frame, solver_vecs_without_learnts_rep, clause_new_ptrs_frame, solver_wlists_handle.
    msat_enqueue_refold_close Hshape.
Qed.

Tactic Notation "msat_binary_copy_start_close"
    ident(raw_suffix) constr(Hmemory) constr(Hprefix) constr(Htagged)
    constr(Hretval) constr(Hcurrent) :=
  lazymatch goal with
  | |- context [binary_watch_copy_progress] =>
      unfold binary_watch_copy_progress;
      exists nil, raw_suffix;
      split; [exact Hmemory|];
      split; [exact Hprefix|];
      split; [lia|];
      split; [reflexivity|];
      split; [rewrite Zlength_nil; lia|];
      split; [rewrite Zlength_nil; lia|];
      split;
      [ simpl; exact Htagged
      | rewrite Htagged, Zlength_replace_Znth; reflexivity ]
  | |- Znth _ _ _ = lit_neg_c _ =>
      reflexivity
  | |- Znth _ _ _ = tag_lit _ =>
      cbn [Znth]; rewrite Hretval, Hcurrent; reflexivity
  | |- Zlength _ = _ =>
      reflexivity
  end.

Lemma ms_binary_watch_copy_step__common :
  forall (words kept : list Z) (current : Z) (suffix : list Z)
         (ii jj src dst : Z) (memory : list Z),
    binary_watch_copy_progress words kept current suffix ii jj src dst memory ->
    src < Zlength words ->
    binary_watch_copy_progress words kept current suffix ii jj
      (src + 1) (dst + 1) (replace_Znth dst (Znth src memory 0) memory).
Proof.
  intros words kept current suffix ii jj src dst memory Hprog Hcursor.
  unfold binary_watch_copy_progress in Hprog |- *.
  destruct Hprog as [copied [rest [Hwords [Hkept [Hbounds [Hsuffix
    [Hsrc [Hdst [Hmemory Hmemory_len]]]]]]]]].
  destruct rest as [|x rest].
  - rewrite Hwords, Hsuffix, app_nil_r, !Zlength_app,
      Zlength_cons, Hkept in Hcursor.
    rewrite Hsrc in Hcursor. lia.
  - pose proof (Zlength_nonneg copied) as Hcopied_nonneg.
    assert (Hnext_words : Znth src words 0 = x).
    { rewrite Hwords, app_Znth2 by (rewrite Hkept, Hsrc; lia).
      rewrite Hsrc, Hkept.
      replace (ii + 1 + Zlength copied - ii) with (1 + Zlength copied) by lia.
      rewrite Znth_cons by lia.
      replace (1 + Zlength copied - 1) with (Zlength copied) by lia.
      rewrite Hsuffix, app_Znth2 by lia.
      replace (Zlength copied - Zlength copied) with 0 by lia.
      reflexivity. }
    assert (Hnext_memory : Znth src memory 0 = x).
    { rewrite Hmemory, Hsrc.
      rewrite (msat_binary_watch_write_after (jj + 1) copied
        (replace_Znth jj current words)
        0 (ii + 1 + Zlength copied)
        ltac:(lia) ltac:(lia)
        ltac:(rewrite Zlength_replace_Znth; rewrite <- Hsrc; exact Hcursor)).
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth; lia).
      rewrite <- Hsrc. exact Hnext_words. }
    exists (copied ++ (x :: nil)), rest.
    split; [exact Hwords|].
    split; [exact Hkept|].
    split; [exact Hbounds|].
    split.
    { rewrite Hsuffix.
      change (copied ++ (x :: rest) = (copied ++ (x :: nil)) ++ rest).
      rewrite <- app_assoc. reflexivity. }
    split.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    split.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    split.
    { rewrite msat_binary_watch_write_snoc, <- Hmemory.
      replace (jj + 1 + Zlength copied) with dst by lia.
      rewrite <- Hnext_memory. reflexivity. }
    rewrite Zlength_replace_Znth. exact Hmemory_len.
Qed.

Tactic Notation "msat_propagate_scan_step_close_nested_addr" constr(a) constr(cc) constr(ii)
    constr(wm) constr(sc) constr(hpre) constr(hidx) constr(hmem) :=
  Exists 2 (Znth a cc 0);
  assert (Hii0 : 0 <= ii < Zlength wm) by lia;
  assert (Hscan : Znth ii wm 0 = sc) by
    (rewrite hpre; rewrite app_Znth2 by lia; rewrite hidx;
     replace (ii - ii) with 0 by lia; reflexivity);
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  lazymatch goal with
  | |- _ |-- “ _ ” =>
    dump_pre_spatial;
    first [assumption | reflexivity | lia | tauto | rewrite hmem; exact Hscan]
  | |- _ |-- _ =>
    unfold solver_propagation_scan_core_at;
    unfold PtrArray.seg, stats_propagate_scan;
    msat_cancel_sound;
    rewrite <- !msat_dot_field_addr_arrow;
    unfold stats_inspects; lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel
  end.

Lemma replace_Znth_prefix_split :
  forall (memory : list Z) (dst src total : Z),
    0 <= dst ->
    dst < src ->
    src + 1 <= total ->
    total = Zlength memory ->
    replace_Znth dst (Znth src memory 0) memory =
    (replace_Znth dst (Znth src memory 0) (sublist 0 (dst + 1) memory) ++
      sublist (dst + 1) (src + 1) memory) ++
    sublist (src + 1) total memory.
Proof.
  intros memory dst src total Hdst Hsrc Htotal Hlen.
  subst total.
  assert (Hwhole :
    memory =
      sublist 0 (dst + 1) memory ++
      (sublist (dst + 1) (src + 1) memory ++
      sublist (src + 1) (Zlength memory) memory)).
  { rewrite <- (sublist_self memory (Zlength memory)) at 1
      by reflexivity.
    rewrite (sublist_split 0 (Zlength memory) (dst + 1) memory) by lia.
    rewrite (sublist_split (dst + 1) (Zlength memory) (src + 1) memory) by lia.
    reflexivity. }
  eapply eq_trans.
  - apply (f_equal (fun m : list Z =>
      replace_Znth dst (Znth src memory 0) m)).
    exact Hwhole.
  - rewrite replace_Znth_app_l by
      (try rewrite Zlength_sublist by lia; lia).
    apply app_assoc.
Qed.

(* The two [replace_Znth] equations
   and the [logical_words] equation are matched jointly with the fact that
   pins their free list, which is what makes each of them unambiguous.  Runs
   before any [destruct]: opening the transition fact would put a second
   [solver_propagation_scan_semantics] in the context. *)
Ltac msat_binary_keep_bind_facts :=
  match goal with
  | Ha : _ = replace_Znth _ (Znth _ ?tm _) ?tm, Hb : ?tm = replace_Znth _ _ _ |- _ =>
      rename Ha into H_tagged_enqueue_success_memory;
      rename Hb into H_tagged_memory
  end;
  match goal with
  | Hw : ms_wm _ = replace_Znth _ ?lw _, Hl : ?lw = _ ++ _ |- _ =>
      rename Hw into H_ms_wm; rename Hl into H_logical_words
  end;
  match goal with
  | H : enqueue_input _ _ _ _ _ _ _ |- _ => rename H into H_enqueue_input
  end;
  match goal with
  | H : solver_shape _ |- _ => rename H into H_solver_shape
  end;
  match goal with
  | H : msolver_seed_shadow _ |- _ => rename H into H_msolver_seed_shadow
  end;
  match goal with
  | H : propagation_caller_frame _ _ |- _ =>
      rename H into H_propagation_caller_frame
  end;
  match goal with
  | H : propagation_scan_frontier _ _ _ |- _ =>
      rename H into H_propagation_scan_frontier
  end;
  match goal with
  | H : solver_propagation_scan_semantics _ _ _ _ _ _ _ _ _ |- _ =>
      rename H into H_solver_propagation_scan_semantics
  end;
  match goal with
  | H : _ = ms_simpdb_props _ |- _ => rename H into H_simp_count
  end;
  match goal with
  | H : _ = Znth 2 (ms_stats _) 0 |- _ => rename H into H_prop_count
  end.

(* The conflicting arm is vacuous here: the transition returns 0 while the
   call site already established that the return value is 1. *)
Tactic Notation "msat_binary_keep_conflict" ident(hconflict) :=
  destruct hconflict as [_ [_ [Hret _]]];
  lia.

(* Two facts the fresh arm needs about the pre-state: the queue has room for
   one more literal (the enqueue contract's own implication, discharged by the
   unassigned test), and the root propagation counter is already zero. *)
Tactic Notation "msat_binary_keep_new_facts"
    ident(henq) ident(hzero) ident(hsem) :=
  match type of henq with
  | enqueue_input ?sz _ ?qt _ _ _ _ =>
      assert (Hqtail_room : qt < sz) by (
          unfold enqueue_input in henq;
          destruct henq as
            (_ & _ & _ & _ & _ & _ & _ & Hroom & _);
          apply Hroom;
          exact hzero
      )
  end;
  match type of hsem with
  | solver_propagation_scan_semantics _ _ _ _ ?M _ _ _ _ =>
      assert (Hpending_zero : ms_capacity_root_propagation_pending M = 0) by (
          pose proof hsem as Hsem0;
          unfold solver_propagation_scan_semantics in Hsem0;
          destruct Hsem0 as [[_ [Hweak _]] | [Hbad _]];
          [ exact (proj1 Hweak)
          | contradiction
          ]
      )
  end.

(* The queue frontier survives a successful enqueue: [qhead] is unchanged,
   the recorded literal is still the one at the entry head, the trail only
   grew at the end, and the rollback carrier is transported by the shared
   lemma. *)
Tactic Notation "msat_binary_keep_new_frontier"
    ident(hroute_enq) ident(hfrontier) ident(htrail_wf) ident(heq) :=
  match type of hroute_enq with
  | ?Mr = msolver_propagation_enqueue_success ?M ?tl _ _ =>
      match type of hfrontier with
      | propagation_scan_frontier ?Me _ ?pp =>
          assert (Hfrontier_route : propagation_scan_frontier Me Mr pp) by (
              rewrite hroute_enq;
              unfold propagation_scan_frontier in hfrontier |- *;
              destruct hfrontier as [Hqhead [Hp [Htail [Hsub Hready]]]];
              assert (Hready_route : propagation_heap_rollback_ready Mr pp) by (
                  rewrite hroute_enq;
                  eapply propagation_heap_rollback_ready_enqueue_success;
                  [ exact htrail_wf
                  | exact Hready
                  ]
              );
              refine (conj _ (conj _ (conj _ (conj _ _))));
              [ unfold msolver_propagation_enqueue_success;
                  rewrite heq;
                  cbn [msolver_propagation_overlay msolver_propagation_update mt_enqueue mt_push];
                  exact Hqhead
              | cbn [msolver_propagation_overlay msolver_propagation_update mt_enqueue mt_push];
                  exact Hp
              | unfold msolver_propagation_enqueue_success;
                  rewrite heq;
                  change (ms_qtail Me <= ms_qtail M + 1);
                  lia
              | unfold msolver_propagation_enqueue_success;
                  rewrite heq;
                  change (sublist 0 (ms_qtail Me)
                    (mt_trail (ms_core M) +:: tl) =
                    mt_trail (ms_core Me));
                  destruct (Z_lt_ge_dec (ms_qtail Me) 0) as
                    [Hentry_negative | Hentry_nonnegative];
                  [ unfold sublist in Hsub |- *;
                      destruct (ms_qtail Me); try lia;
                      cbn in Hsub |- *;
                      exact Hsub
                  | rewrite (sublist_split_app_l 0 (ms_qtail Me)
                        (mt_trail (ms_core M))
                        (tl :: nil)) by lia;
                      exact Hsub
                  ]
              | rewrite <- hroute_enq;
                  exact Hready_route
              ]
          )
      end
  end.

(* The fresh arm: the literal was unassigned, so the enqueue test is true and
   the route solver is the overlay of a successful enqueue. *)
Tactic Notation "msat_binary_keep_new_head"
    ident(hnew) ident(hmroute) ident(assigns_v) ident(levels_v)
    ident(reasons_v) ident(trail_v) ident(qtail_v) :=
  destruct hnew as
    [Hzero [_ [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]];
  unfold msolver_propagation_enqueue_success in hmroute;
  match type of Hzero with
  | ?e = _ =>
      assert (Heq : (e =? 0)%Z = true) by (apply Z.eqb_eq; exact Hzero);
      rewrite Heq in hmroute
  end;
  subst assigns_v;
  subst levels_v;
  subst reasons_v;
  subst trail_v;
  subst qtail_v.

(* The three msolver invariants transported to the route state: shape, seed
   shadow and caller frame all survive the enqueue overlay. *)
Tactic Notation "msat_binary_keep_new_overlay"
    ident(hmroute) ident(hshape) ident(hpending) ident(hseed)
    ident(hcaller) :=
  match type of hmroute with
  | ?Mr = _ =>
      assert (Hshape_route : solver_shape Mr) by (
          rewrite hmroute;
          unfold solver_shape, msolver_propagation_overlay, msolver_propagation_update, mt_enqueue, mt_push;
          cbn;
          unfold solver_shape in hshape;
          destruct hshape as
            (Hsize & Hcap & Htwice & Hassigns_len & Hlevels_len &
            Hreasons_len & Horderpos_len & Hactivity_len & Htags_len &
            Htrail_len & Hqhead_range & Hpending_range & Hpending_flag &
            Hqtail_range & Hwm_len & Hbinary_lits_len &
            Hstats_len & Hroot_level & Hbinary_nonzero & Hbinary_even);
          repeat split; try assumption; try lia;
            try (rewrite Zlength_replace_Znth; assumption);
            try (rewrite Zlength_app_cons; lia);
            try (let Hbad := fresh "Hbad" in
            intro Hbad; rewrite hpending in Hbad; discriminate);
            exact (proj2 Hbinary_even)
      );
      assert (Hseed_route : msolver_seed_shadow Mr) by (
          rewrite hmroute;
          unfold msolver_seed_shadow, msolver_propagation_overlay, msolver_propagation_update;
          cbn;
          exact hseed
      );
      match type of hcaller with
      | propagation_caller_frame ?M0v _ =>
          assert (Hcaller_route : propagation_caller_frame M0v Mr) by (
              rewrite hmroute;
              unfold propagation_caller_frame, msolver_propagation_overlay, msolver_propagation_update, mt_enqueue,
              mt_push;
              cbn;
              exact hcaller
          )
      end
  end.

Tactic Notation "msat_binary_keep_new_route_eqs"
    ident(k_v) ident(hrest) ident(hsem) ident(hshape) ident(hmroute)
    ident(heq) ident(cur_v) ident(p_v) ident(s_v) :=
  match type of hsem with
  | solver_propagation_scan_semantics ?nv _ _ _ ?M _ _ _ _ =>
      assert (Htrail_wf : mtrail_wf nv (ms_core M)) by (
          pose proof hsem as Hpresem;
          unfold solver_propagation_scan_semantics in Hpresem;
          destruct Hpresem as [[_ [Hweak _]] | [Hbad [Hnil _]]];
          [ unfold solver_propagation_weak in Hweak;
              destruct k_v as [Ainst | Aproc]; cbn in Hweak;
              [ exact (msw_trail_wf (proj2 Hweak))
              | exact (msa_trail_wf (proj2 Hweak))
              ]
          | rewrite hrest in Hnil;
              discriminate
          ]
      );
      assert (Htrail_length :
        Zlength (mt_trail (ms_core M)) = ms_qtail M) by (
          unfold solver_shape in hshape;
          tauto
      );
      match type of hmroute with
      | ?Mr = _ =>
          assert (Hroute_enqueue : Mr =
            msolver_propagation_enqueue_success M
            (tag_lit cur_v) (tag_of_lit p_v)
            (lit_denote (tag_lit cur_v) ::
            literal_neg (lit_denote p_v) :: nil)) by (
              rewrite hmroute;
              unfold msolver_propagation_enqueue_success;
              rewrite heq;
              reflexivity
          );
          assert (Hbinary_route :
            solver_binary_rep Mr = solver_binary_rep M) by (
              rewrite hmroute;
              unfold solver_binary_rep, msolver_propagation_overlay, msolver_propagation_update;
              cbn;
              reflexivity
          );
          assert (Hframe_route :
            solver_propagate_frame s_v Mr =
            solver_propagate_frame s_v M) by (
              rewrite hmroute;
              unfold solver_propagate_frame, solver_fp_rep,
                msolver_propagation_overlay, msolver_propagation_update, mt_enqueue, mt_push;
              cbn;
              reflexivity
          )
      end
  end.

(* Each transported invariant is offered both folded and unfolded
   because the goals state some of them about the overlay expression and
   some about the route state itself. *)
Tactic Notation "msat_binary_keep_new_side"
    ident(hwm) ident(hlogical) ident(hmroute) ident(hfrontier2)
    ident(hshape2) ident(hseed2) ident(hcaller2) :=
  try assumption;
  try (rewrite hwm, hlogical; reflexivity);
  try (unfold propagation_watch_scan_physical;
    repeat split; assumption);
  try (rewrite <- hmroute; exact hfrontier2);
  try (rewrite <- hmroute; exact hshape2);
  try (rewrite <- hmroute; exact hseed2);
  try (rewrite <- hmroute; exact hcaller2);
  try (rewrite hmroute in hfrontier2; exact hfrontier2);
  try (rewrite hmroute in hshape2; exact hshape2);
  try match goal with
  | |- propagation_scan_frontier _ ?Mg _ =>
      match type of hmroute with
      | ?Mr = _ =>
          assert (HMr : Mg = Mr) by (rewrite hmroute; reflexivity);
          rewrite HMr; exact hfrontier2
      end
  end;
  try match goal with
  | |- solver_shape ?Mg =>
      match type of hmroute with
      | ?Mr = _ =>
          assert (HMr : Mg = Mr) by (rewrite hmroute; reflexivity);
          rewrite HMr; exact hshape2
      end
  end.

(* The last spatial goal: the two [store_array_rec] blocks arrive in the
   opposite order, the two statistics counters have to be folded back, and
   the two nested [stats] field addresses are re-associated through the
   shared alias lemma. *)
Tactic Notation "msat_binary_keep_new_stats"
    ident(lvl_v) ident(rsn_v) ident(hroute_enq) ident(hsimp) ident(hprop)
    ident(s_v) :=
  match type of hroute_enq with
  | _ = msolver_propagation_enqueue_success ?M ?tl ?tp _ =>
      unfold CharArray.seg, IntArray.seg, PtrArray.seg, Znth;
      cbn
  end;
  rewrite hsimp;
  unfold Znth in hprop;
  cbn in hprop;
  rewrite hprop;
  assert (Hprop_address :
    &(s_v # "solver_t" ->ₛ "stats" .ₛ "propagations") =
    &(&(s_v # "solver_t" ->ₛ "stats") ->ₛ "propagations")) by (
      csimpl;
      reflexivity
  );
  assert (Hinspect_address :
    &(s_v # "solver_t" ->ₛ "stats" .ₛ "inspects") =
    &(&(s_v # "solver_t" ->ₛ "stats") ->ₛ "inspects")) by (
      csimpl;
      reflexivity
  );
  rewrite Hprop_address, Hinspect_address,
    (msat_nested_field_addr_alias s_v "solver_t" "stats" "stats_t"
       "propagations" _ eq_refl),
    (msat_nested_field_addr_alias s_v "solver_t" "stats" "stats_t"
       "inspects" _ eq_refl);
  cancel;
  lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel.

Tactic Notation "msat_binary_keep_route_bounds"
    ident(hphysical) ident(ii_v) ident(jj_v) ident(garbage_v) ident(confl_v)
    ident(hsem) ident(hrest) :=
  unfold propagation_watch_scan_physical in hphysical;
  destruct hphysical as
    [Hroute_scan [Hroute_memory [Hroute_jj [Hroute_ii Hroute_length]]]];
  assert (Hii0 : 0 <= ii_v) by
    (match goal with
     | H : Zlength _ = ii_v |- _ => rewrite <- H; apply Zlength_nonneg
     end);
  assert (Hii_positive : 0 < ii_v + 1) by lia;
  assert (Hjj0 : 0 <= jj_v + 1) by
    (rewrite <- Hroute_jj; apply Zlength_nonneg);
  assert (Hjjii : jj_v + 1 <= ii_v + 1) by
    (rewrite Zlength_app in Hroute_ii;
     pose proof (Zlength_nonneg garbage_v);
     lia);
  assert (Hconfl : confl_v = 0) by
    (unfold solver_propagation_scan_semantics in hsem;
     destruct hsem as [[Hc _] | [Hc [Hnil _]]];
     [ exact Hc
     | rewrite hrest in Hnil; discriminate ]);
  subst confl_v.

(* Shared by the assigned and the fresh arm: the written watch memory is the
   route memory (the write at [ii] puts back what [ii] already held), and the
   logical word list splits at the scanned literal. *)
Tactic Notation "msat_binary_keep_route_memory"
    ident(htesm) ident(htagged) ident(hmemory) ident(hlogical)
    ident(hrest) ident(hretained) :=
  match type of htesm with
  | ?tesm = _ =>
      match type of hmemory with
      | ?mr = _ =>
          assert (Htagged_memory : tesm = mr) by
            (rewrite htesm, replace_Znth_Znth, htagged, hmemory; reflexivity)
      end
  end;
  match type of hlogical with
  | ?lw = _ =>
      match type of hretained with
      | ?rr = _ =>
          match type of hrest with
          | _ = ?sc :: ?rt =>
              assert (Hlogical_route : lw = rr ++ rt) by
                (rewrite hlogical, hrest, hretained;
                 rewrite <- (app_assoc _ (sc :: nil) rt); reflexivity)
          end
      end
  end.

(* The assigned arm: the literal already carries its own sign, so the
   enqueue test is false and the route solver collapses to the scan solver. *)
Tactic Notation "msat_binary_keep_same_head"
    ident(hsame) ident(hmroute) ident(mroute_v) ident(assigns_v)
    ident(levels_v) ident(reasons_v) ident(trail_v) ident(qtail_v) :=
  destruct hsame as
    [Hassigned [_ [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]];
  match type of Hassigned with
  | ?e = _ =>
      assert (Hnz : e <> 0) by (rewrite Hassigned; apply lit_sig_nonzero);
      unfold msolver_propagation_enqueue_success in hmroute;
      assert (Heq : (e =? 0)%Z = false) by (apply Z.eqb_neq; exact Hnz);
      rewrite Heq in hmroute
  end;
  subst mroute_v;
  subst assigns_v;
  subst levels_v;
  subst reasons_v;
  subst trail_v;
  subst qtail_v.

Tactic Notation "msat_propagate_enqueue_route_shape" ident(ht) ident(hm)
    ident(aa) ident(ll) ident(rr) ident(tt) ident(qq) :=
  subst aa; subst ll; subst rr; subst tt; subst qq;
  unfold msolver_propagation_enqueue_success,
    msolver_propagation_db_wmap_update,
    msolver_propagation_overlay, msolver_propagation_update in hm;
  cbn in hm; rewrite ht in hm;
  cbn [msolver_propagation_overlay msolver_propagation_update ] in hm.

Lemma msat_propagate_scan_frontier_push :
  forall n Mentry Mscan Mroute p watch0 rw rc prob learnt,
    mtrail_wf n (ms_core Mscan) ->
    Zlength (mt_trail (ms_core Mscan)) = ms_qtail Mscan ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    Mroute = msolver_propagation_enqueue_success
      (msolver_propagation_db_wmap_update Mscan prob learnt
        (ms_wm Mscan)) watch0 rw rc ->
    propagation_scan_frontier Mentry Mscan p ->
    propagation_scan_frontier Mentry Mroute p.
Proof.
  intros n Mentry Mscan Mroute p watch0 rw rc prob learnt
    Hwf_scan Htrail_len Hzero HMroute Hfrontier.
  assert (Htest :
    (Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 =? 0)%Z = true)
    by (apply Z.eqb_eq; exact Hzero).
  unfold msolver_propagation_enqueue_success,
    msolver_propagation_db_wmap_update,
    msolver_propagation_overlay, msolver_propagation_update in HMroute.
  cbn in HMroute.
  rewrite Htest in HMroute.
  cbn [msolver_propagation_overlay msolver_propagation_update ] in HMroute.
  unfold propagation_scan_frontier in Hfrontier |- *.
  destruct Hfrontier as [Hqh [Hp [Htail [Hprefix Hrollback]]]].
  rewrite HMroute.
  cbn [mt_enqueue mt_push] in *.
  unfold propagation_heap_rollback_ready in Hrollback.
  destruct Hrollback as [Hqpos [Hfocus Hgate]].
  repeat split.
  - exact Hqh.
  - exact Hp.
  - change (ms_qtail Mentry <= ms_qtail Mscan + 1).
    apply Z.le_trans with (m := ms_qtail Mscan).
    + exact Htail.
    + exact (z_le_add_one__propagate (ms_qtail Mscan)).
  - unfold sublist in Hprefix |- *.
    cbn in Hprefix |- *.
    rewrite firstn_app.
    assert (Hnat :
      (Z.to_nat (ms_qtail Mentry) <= length (mt_trail (ms_core Mscan)))%nat).
    { destruct (Z_lt_ge_dec (ms_qtail Mentry) 0) as [Hneg | Hnonneg].
      - destruct (ms_qtail Mentry); cbn in *; lia.
      - assert (Hnonneg' : 0 <= ms_qtail Mentry) by lia.
        rewrite <- (Nat2Z.id (length (mt_trail (ms_core Mscan)))).
        rewrite <- Zlength_correct.
        apply (proj1 (Z2Nat.inj_le (ms_qtail Mentry)
          (Zlength (mt_trail (ms_core Mscan))) Hnonneg'
          (Zlength_nonneg (mt_trail (ms_core Mscan))))).
        rewrite Htrail_len. exact Htail. }
    replace (Z.to_nat (ms_qtail Mentry) -
      length (mt_trail (ms_core Mscan)))%nat with 0%nat by lia.
    cbn. rewrite app_nil_r. exact Hprefix.
  - exact Hqpos.
  - change (p = Znth (mt_qhead (ms_core Mscan) - 1)
      (mt_trail (ms_core Mscan) ++ (watch0 :: nil)) 0).
    rewrite app_Znth1.
    + exact Hfocus.
    + pose proof (mtw_qhead_range Hwf_scan); lia.
  - exact Hgate.
Qed.

Lemma msat_propagate_scan_live_core :
  forall n F A_arr K M p kept rest,
    solver_propagation_scan_semantics n F A_arr K M p 0 kept rest ->
    solver_shape M /\ mtrail_wf n (ms_core M).
Proof.
  intros n F A_arr K M p kept rest Hsem.
  destruct Hsem as [Hlive | Hbad].
  - destruct Hlive as [_ [Hweak _]]. destruct Hweak as [_ Hinv].
    destruct K as [A_inst | A_proc]; split.
    + exact (msw_shape Hinv).
    + exact (msw_trail_wf Hinv).
    + exact (msa_shape Hinv).
    + exact (msa_trail_wf Hinv).
  - exfalso. destruct Hbad as [Hnz _]. lia.
Qed.

Tactic Notation "msat_propagate_unit_pure_close" ident(hsh) ident(hsd)
    ident(hcl) ident(hfr) ident(hsm) ident(hph) ident(hlg) ident(hml)
    ident(hm) :=
  split_pures; dump_pre_spatial;
  try exact hsh; try exact hsd; try exact hcl; try exact hfr;
  try exact hsm; try exact hph; try exact hlg; try exact hml;
  try assumption; try reflexivity; try lia;
  try rewrite hm;
  cbn [mt_enqueue mt_push]; try assumption; try reflexivity; try lia.

Tactic Notation "msat_propagate_unit_route_facts" ident(hm) ident(hm0)
    ident(hs) ident(hc) ident(hd) ident(mr) ident(mc) ident(m0) ident(s) :=
  assert (Hseed_route : msolver_seed_shadow mr) by (rewrite hm; exact hs);
  assert (Hcaller_route : propagation_caller_frame m0 mr) by
    (rewrite hm; exact hc);
  assert (Hbinary : solver_binary_rep mr = solver_binary_rep mc) by
    (rewrite hm; unfold solver_binary_rep; reflexivity);
  assert (Hframe : solver_propagate_frame s mr =
      solver_propagate_frame s mc) by
    (destruct (db_pair_lits_update_words__propagate _ _ _ _ _ _ _ hd)
       as [Hprob_words Hlearnt_words];
     rewrite hm0; apply solver_propagate_frame_db_enqueue__propagate;
     assumption).

Tactic Notation "msat_propagate_unit_scan_refold" ident(hcm) ident(hmem)
    ident(hb) ident(hf) ident(hm) ident(pc) ident(s) ident(mc) :=
  rewrite hcm, <- hmem;
  unfold solver_propagation_scan_core_at;
  rewrite hb, hf, hm;
  unfold CharArray.seg, IntArray.seg, PtrArray.seg;
  unfold replace_Znth;
  msat_cancel_sound;
  exact (stats_propagate_scan_refold__propagate s pc (ms_stats mc)).

Definition propagation_scan_finish_arm_normal (condition finalized : Prop)
    (trl_finish rsn_finish : Z) (Mfinish : msolver) (lvl_finish levels_entry : Z)
    (n : Z) (F : cnf) (A_arr : list literal) (K : solver_propagation_context)
    (M0 : msolver) (confl jj : Z) (watch_memory retained : list Z)
    (scan_wm : list (list Z)) (p : Z)
    (scan_wcap s_pre wl assigns_entry : Z) : Assertion :=
  “ (lvl_finish = levels_entry) ”
  &&  “ (solver_shape Mfinish ) ”
  &&  “ (msolver_seed_shadow Mfinish ) ”
  &&  “ condition ”
  &&  “ finalized ”
  &&  “ (solver_propagation_loop_inv n F A_arr K M0 Mfinish confl ) ”
  &&  “ minisat_propagation_reuse_loop n M0 Mfinish confl ”
  &&  “ ((sublist (0) (jj) (watch_memory)) = retained) ”
  &&  “ ((ms_wm (Mfinish)) = (replace_Znth (p) (retained) (scan_wm))) ”
  &&  “ (0 <= (mt_qhead ((ms_core (Mfinish))))) ”
  &&  “ ((mt_qhead ((ms_core (Mfinish)))) <= (ms_qtail (Mfinish))) ”
  &&  “ ((ms_qtail (Mfinish)) <= (ms_size (Mfinish))) ”
  &&  “ ((ms_size (Mfinish)) <= (ms_cap (Mfinish))) ”
  &&  “ ((Zlength ((mt_trail ((ms_core (Mfinish)))))) = (ms_qtail (Mfinish))) ”
  &&  ((&((s_pre)  # "solver_t" ->ₛ "qhead")) # Int  |-> (mt_qhead ((ms_core (Mfinish)))))
  **  ((&((s_pre)  # "solver_t" ->ₛ "qtail")) # Int  |-> (ms_qtail (Mfinish)))
  **  ((&((s_pre)  # "solver_t" ->ₛ "simpdb_props")) # Int  |-> (ms_simpdb_props (Mfinish)))
  **  ((&((s_pre)  # "solver_t" ->ₛ "wlists")) # Ptr  |-> wl)
  **  ((&((s_pre)  # "solver_t" ->ₛ "assigns")) # Ptr  |-> assigns_entry)
  **  ((&((s_pre)  # "solver_t" ->ₛ "reasons")) # Ptr  |-> rsn_finish)
  **  ((&((s_pre)  # "solver_t" ->ₛ "levels")) # Ptr  |-> lvl_finish)
  **  ((&((s_pre)  # "solver_t" ->ₛ "trail")) # Ptr  |-> trl_finish)
  **  ((&((s_pre)  # "solver_t" ->ₛ "binary")) # Ptr  |-> (ms_binary (Mfinish)))
  **  (CharArray.seg assigns_entry 0 (ms_size (Mfinish)) (mt_assigns ((ms_core (Mfinish)))) )
  **  (solver_char_tail assigns_entry (ms_size (Mfinish)) (ms_cap (Mfinish)) )
  **  (PtrArray.seg rsn_finish 0 (ms_size (Mfinish)) (ms_reason_words (Mfinish)) )
  **  (solver_ptr_tail rsn_finish (ms_size (Mfinish)) (ms_cap (Mfinish)) )
  **  (IntArray.seg lvl_finish 0 (ms_size (Mfinish)) (mt_levels ((ms_core (Mfinish)))) )
  **  (solver_int_tail lvl_finish (ms_size (Mfinish)) (ms_cap (Mfinish)) )
  **  (IntArray.seg trl_finish 0 (ms_qtail (Mfinish)) (mt_trail ((ms_core (Mfinish)))) )
  **  (solver_int_tail trl_finish (ms_qtail (Mfinish)) (ms_cap (Mfinish)) )
  **  (Veci.rep &((s_pre)  # "solver_t" ->ₛ "trail_lim") (mt_lim ((ms_core (Mfinish)))) )
  **  (wlists_rep wl (ms_size (Mfinish)) (ms_wm (Mfinish)) )
  **  (clause_db_rep (ms_prob (Mfinish)) )
  **  (clause_db_rep (ms_learnt (Mfinish)) )
  **  (solver_binary_rep Mfinish )
  **  ((&((s_pre)  # "solver_t" ->ₛ "stats" .ₛ "propagations")) # UInt64  |-> (stats_propagations ((ms_stats
  (Mfinish)))))
  **  ((&((s_pre)  # "solver_t" ->ₛ "stats" .ₛ "inspects")) # UInt64  |-> (stats_inspects ((ms_stats (Mfinish)))))
  **  (solver_propagate_frame s_pre Mfinish )

  **  ((( &( "begin" ) )) # Ptr  |->_)
  **  ((( &( "endvar" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "j" ) )) # Ptr  |->_)
  **  ((( &( "ws" ) )) # Ptr  |->_).

Tactic Notation "msat_propagate_finish_frame"
    ident(lvl) ident(lvl0) ident(trl) ident(rsn) ident(mfin) :=
  let Hlvl := fresh "H_lvl_finish" in
  bind_fact ( lvl = lvl0 ) as Hlvl;
  Exists rsn trl mfin;
  split_pure_spatial;
  [ rewrite <- Hlvl; set_String_name;
    lazymatch goal with
    | |- context [ solver_propagate_frame ?sp mfin ] =>
        cancel (solver_propagate_frame sp mfin)
    end;
    cancel
  | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia ].

Tactic Notation "msat_propagate_binary_keep_length" ident(tm) :=
  split_pures; dump_pre_spatial;
  first
    [ lia
    | symmetry; apply Znth_replace_Znth_Same;
      rewrite !Zlength_replace_Znth; subst tm;
      rewrite !Zlength_replace_Znth; lia ].

Ltac msat_propagation_keep_scan_key close_pures :=
  (LLM_pre_process ltac:(lia || nia || int_auto)); split_pures; close_pures;
  match goal with
  | Hwm : ?wm = ?rp ++ ?sc :: ?rs,
    Hrp : Zlength ?rp = ?ii,
    Htag : is_tag ?sc = msat_true,
    Hphys : propagation_watch_scan_physical _ ?ret _ ?rst _ ?wm ?ii ?jj,
    Hsem : solver_propagation_scan_semantics ?n ?F ?Aa ?K ?Ms ?p ?cf ?ret ?rst,
    Hreuse : minisat_propagation_reuse_scan ?entry ?Ms ?p ?cf ?rst
    |- _ =>
      assert (Hrest : rst = sc :: rs)
        by (eapply propagation_watch_scan_rest_head__propagate;
            [ exact Hphys | exact Hwm | exact Hrp ]);
      unfold propagation_watch_scan_physical in Hphys;
      destruct Hphys as [Hinv [Hmem [Hkept [Hkg Hlen]]]];
      assert (Hii : 0 <= ii < Zlength wm) by lia;
      assert (Hjj : 0 <= jj < Zlength wm) by lia;
      assert (Hkeyi : Znth ii (replace_Znth ii sc wm) 0 = sc)
        by (apply Znth_replace_Znth_Same; exact Hii);
      assert (Hkeyj : Znth ii (replace_Znth jj sc wm) 0 = sc)
        by (destruct (Z.eq_dec jj ii) as [Heq|Hne];
            [ rewrite Heq; exact Hkeyi
            | rewrite (Znth_replace_Znth_Diff 0 wm jj ii sc Hjj Hii Hne);
              rewrite Hwm; rewrite app_Znth2 by lia; rewrite Hrp;
              replace (ii - ii) with 0 by lia; reflexivity ]);
      assert (Hcf_zero : cf = 0)
        by (destruct Hsem as [[Hc _] | [_ [Hnil _]]];
            [ exact Hc | rewrite Hrest in Hnil; discriminate ]);
      assert (Hreuse0 : minisat_propagation_reuse_scan entry Ms p 0 rst)
        by (rewrite <- Hcf_zero; exact Hreuse);
      unfold solver_propagation_scan_semantics in Hsem;
      assert (Hsem0 : solver_propagation_scan_semantics n F Aa K Ms p 0 ret rst)
        by (destruct Hsem as [Hlive | Hconf];
            [ destruct Hlive as [Hc Hrestsem];
              unfold solver_propagation_scan_semantics; left; split;
              [ reflexivity | exact Hrestsem ]
            | destruct Hconf as [_ [Hnil _]]; exfalso;
              rewrite Hrest in Hnil; discriminate ]);
      first [ exact Hrest
            | rewrite Hkeyi; exact Hrest
            | rewrite Hkeyj; exact Hrest
            | unfold tagged_word; rewrite Hkeyi; exact Htag
            | unfold tagged_word; rewrite Hkeyj; exact Htag
            | exact Hsem0
            | exact Hreuse0
            | solve [unfold minisat_propagation_reuse_scan in *; tauto]
            | match goal with
              | Hbeg : ?M = msolver_propagation_scan_begin _ _ _ |- _ =>
                  rewrite <- Hbeg; first [exact Hsem0 | exact Hreuse0 |
                    solve [unfold minisat_propagation_reuse_scan in *; tauto]]
              end ]
  end.

Ltac msat_propagate_unit_enqueue_input :=
  match goal with
  | Hshape : solver_shape ?Ms,
    Hsem : solver_propagation_scan_semantics _ _ _ ?K ?Ms _ _ _ _,
    Hinv : propagation_replacement_scan_inv ?n ?Ms _
             (propagation_normalized_clause ?w0 _ _) _ |- _ =>
      destruct Hsem as [Hscan | Hconf]; [ | destruct Hconf as [Hnz _]; lia ];
      destruct Hscan as (_ & Hweak & _);
      unfold solver_propagation_weak in Hweak;
      destruct Hweak as [_ Hweak];
      assert (Hwf : mtrail_wf n (ms_core Ms))
        by (destruct K; cbn in Hweak;
            [exact (msw_trail_wf Hweak) | exact (msa_trail_wf Hweak)]);
      assert (Hn : n = ms_size Ms)
        by (destruct K; cbn in Hweak;
            [exact (msw_size Hweak) | exact (msa_size Hweak)]);
      unfold propagation_replacement_scan_inv in Hinv;
      destruct Hinv as (Hoffset & Hall & _);
      assert (Hwatch : lit_wf_c n w0)
        by (rewrite Forall_forall in Hall; apply Hall;
            unfold propagation_normalized_clause; simpl; auto);
      pose proof Hshape as Hshape0; unfold solver_shape in Hshape0;
      destruct Hshape0 as
        (Hsizecap & Hcapmax & Htwice & Hassignlen & Hlevelslen &
         Hreasonlen & Horderposlen & Hactivitylen & Htagslen & Htraillen &
         Hqheadrange & Hpendingrange & Hrootbit & Hrootpending & Hqtailcap &
         Hwmlen & Hbinarylen & Hstatslen & Hrootnonneg &
         Hbinaryne & Hbinaryeven);
      assert (Hroom :
          Znth (lit_var_c w0) (mt_assigns (ms_core Ms)) 0 = 0 ->
          ms_qtail Ms < ms_size Ms)
        by (intros Hz;
            pose proof (lit_var_c_in_range n w0 Hwatch) as Hv;
            assert (Hnin :
                ~ In (lit_var_c w0)
                    (map lit_var_c (mt_trail (ms_core Ms))))
              by (intros Hin;
                  apply (proj2 (mtw_assigned_iff Hwf (lit_var_c w0) Hv)) in Hin;
                  contradiction);
            assert (Hnd : NoDup
                (map lit_var_c (mt_trail (ms_core Ms)) ++
                 cons (lit_var_c w0) nil))
              by (apply NoDup_snoc; [exact (mtw_trail_nodup Hwf) | exact Hnin]);
            pose proof (msat_map_lit_var_c_snoc_in_range n
                (mt_trail (ms_core Ms)) (lit_var_c w0)
                (mtw_trail_lits Hwf) Hv) as Hbounds;
            pose proof (NoDup_Z_bounded_length _ n (mtw_n_nonneg Hwf)
              Hnd Hbounds) as Hlen;
            rewrite length_app, length_map in Hlen; simpl in Hlen;
            rewrite Nat2Z.inj_add in Hlen; simpl in Hlen;
            rewrite <- Zlength_correct in Hlen;
            rewrite Hn in Hlen; lia);
      destruct Hwatch as [Hwatchlo Hwatchhi];
      assert (Hvals : Forall (fun x => -1 <= x <= 1)
          (mt_assigns (ms_core Ms)))
        by (rewrite Forall_forall; intros x Hx;
            pose proof (mtw_cells Hwf) as Hcells;
            rewrite Forall_forall in Hcells; specialize (Hcells x Hx);
            unfold lbool_cell in Hcells; lia);
      repeat split_pures; dump_pre_spatial;
      match goal with
      | |- enqueue_input _ _ _ _ _ _ _ => idtac
      | _ => lia
      end;
      pose proof (mtw_trail_bound Hwf) as Htrailbound;
      unfold enqueue_input; repeat split;
      try exact Htwice;
      try exact Hassignlen;
      try exact Hlevelslen;
      try exact Hreasonlen;
      try exact Htraillen;
      try exact Hroom;
      try exact Hvals;
      lia
  end.

Tactic Notation "msat_propagate_ptr_missing_merge" ident(bg) ident(k)
    ident(src) ident(mem) ident(idx) :=
  assert (Hi : idx = bg + k * sizeof(PTR)) by lia;
  subst idx;
  pose proof (fun lo => ptrarray_missing_i_index_range__lit_removable bg k lo (Zlength src) mem) as Hbounds;
  prop_apply_p (Hbounds 0);
  Intros;
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full bg k (Zlength src)
      (Znth k mem 0) mem).

Lemma msat_propagate_watch_prefix_write_refold :
forall
  (watch_memory: (@list Z))
  (ii: Z)
  (jj: Z)
  (source_words: (@list Z))
  (raw_prefix: (@list Z))
  (scan_current: Z)
  (raw_suffix: (@list Z))
  (begin: Z)
  (PreH1 : ((app (raw_prefix) ((cons (scan_current) (raw_suffix)))) = watch_memory))
  (PreH2 : ((Zlength (raw_prefix)) = ii))
  (PreH3 : (0 <= jj))
  (PreH4 : (jj < ii)) ,
  (propagation_ptr_segment begin 0 jj (sublist (0) (jj) (raw_prefix)) )
  **  (((begin + (jj * sizeof(PTR)))) # Ptr  |-> scan_current)
  **  (propagation_ptr_segment begin (jj + 1 ) ii (sublist ((jj + 1 )) (ii) (raw_prefix)) )
  **  (((begin + (ii * sizeof(PTR)))) # Ptr  |-> scan_current)
  **  (propagation_ptr_segment begin (ii + 1 ) (Zlength (source_words)) raw_suffix )
|--
  (PtrArray.full begin (Zlength (source_words)) (replace_Znth (jj) (scan_current) (watch_memory)) ).
Proof.
  intros.
  bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  pose proof (Znth_split 0 raw_prefix jj ltac:(lia)) as Hsplit.
  assert (Hreplace_prefix :
    replace_Znth jj scan_current raw_prefix =
      sublist 0 jj raw_prefix ++
        scan_current :: sublist (jj + 1) ii raw_prefix).
  {
    rewrite Hsplit at 1.
    rewrite replace_Znth_app_r by
      (rewrite Zlength_sublist by lia; lia).
    rewrite replace_Znth_nothing by
      (rewrite Zlength_sublist by lia; lia).
    rewrite Zlength_sublist by lia.
    replace (jj - (jj - 0)) with 0 by lia.
    unfold replace_Znth.
    simpl.
    rewrite H_Zlength.
    reflexivity.
  }
  rewrite <- H_raw_prefix.
  rewrite replace_Znth_app_l by lia.
  rewrite Hreplace_prefix.
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin jj scan_current).
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj raw_prefix) (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
    (sublist 0 jj raw_prefix ++ scan_current :: nil)
    (sublist (jj + 1) ii raw_prefix) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    ((sublist 0 jj raw_prefix ++ scan_current :: nil) ++
      sublist (jj + 1) ii raw_prefix)
    (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words)
    (((sublist 0 jj raw_prefix ++ scan_current :: nil) ++
      sublist (jj + 1) ii raw_prefix) ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  rewrite <- !app_assoc.
  simpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma msat_propagate_watch_current_write_refold :
forall
  (watch_memory: (@list Z))
  (ii: Z)
  (jj: Z)
  (source_words: (@list Z))
  (raw_prefix: (@list Z))
  (scan_current: Z)
  (raw_suffix: (@list Z))
  (begin: Z)
  (PreH1 : ((app (raw_prefix) ((cons (scan_current) (raw_suffix)))) = watch_memory))
  (PreH2 : ((Zlength (raw_prefix)) = ii))
  (PreH3 : (ii <= jj))
  (PreH4 : (jj <= ii)) ,
  (propagation_ptr_segment begin 0 ii raw_prefix )
  **  (((begin + (ii * sizeof(PTR)))) # Ptr  |-> scan_current)
  **  (propagation_ptr_segment begin (ii + 1 ) (Zlength (source_words)) raw_suffix )
|--
  (PtrArray.full begin (Zlength (source_words)) (replace_Znth (jj) (scan_current) (watch_memory)) ).
Proof.
  intros.
  bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  assert (Hjj : jj = ii) by lia.
  subst jj.
  assert (Hreplace : replace_Znth ii scan_current watch_memory = watch_memory).
  {
    rewrite <- H_raw_prefix.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (ii - Zlength raw_prefix) with 0 by lia.
    reflexivity.
  }
  rewrite Hreplace.
  rewrite <- H_raw_prefix.
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin 0 ii raw_prefix).
  Intros.
  prop_apply_p (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    raw_prefix (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words) (raw_prefix ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  replace ((raw_prefix ++ scan_current :: nil) ++ raw_suffix) with
    (raw_prefix ++ scan_current :: raw_suffix) by
    (rewrite <- app_assoc; reflexivity).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma msat_binary_watch_write_prefix :
  forall (xs prefix tail : list Z) (k : Z),
    Zlength prefix = k ->
    Zlength xs <= Zlength tail ->
    exists tail',
      binary_watch_write k xs (prefix ++ tail) = prefix ++ xs ++ tail' /\
      Zlength tail' = Zlength tail - Zlength xs.
Proof.
  intros xs prefix tail k Hprefix Hroom.
  destruct (binary_watch_write_prefix__propagate_dbu
    xs (prefix ++ tail) prefix k) as [tail' [Hwrite Hlength]].
  - rewrite <- Hprefix. apply Zlength_nonneg.
  - rewrite Zlength_app. lia.
  - exact Hprefix.
  - rewrite <- Hprefix. apply sublist_app_exact1.
  - exists tail'. split; [exact Hwrite|].
    rewrite Zlength_app in Hlength. lia.
Qed.

Lemma msat_binary_conflict_exit_package :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M0 Mentry Mscan : msolver)
         (p scan_current s begin i j endvar copy_src copy_dst ii jj : Z)
         (source_words retained moved rest garbage raw_prefix raw_suffix
          watch_memory copy_memory : list Z),
    solver_shape Mscan ->
    msolver_seed_shadow Mscan ->
    propagation_caller_frame M0 Mscan ->
    propagation_scan_frontier Mentry Mscan p ->
    rest = scan_current :: raw_suffix ->
    propagation_watch_scan_physical source_words retained moved rest garbage
      watch_memory ii jj ->
    binary_watch_copy_progress watch_memory raw_prefix scan_current
      raw_suffix ii jj copy_src copy_dst copy_memory ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) p
      (ms_binary (msolver_propagation_binary_conflict Mscan
        (tag_lit scan_current) p))
      (retained ++ rest) nil ->
    endvar = begin + Zlength source_words * sizeof ( PTR ) ->
    i = begin + copy_src * sizeof ( PTR ) ->
    j = begin + copy_dst * sizeof ( PTR ) ->
    i >= endvar ->
    0 <= copy_dst ->
    copy_dst <= copy_src ->
    copy_src <= Zlength source_words ->
    0 <= ms_binary Mscan ->
    (exists tail',
       propagation_binary_conflict_exit n F A_arr K M0 Mentry Mscan
         (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p)
         p scan_current (ms_binary Mscan) source_words retained moved rest
         copy_memory tail' (retained ++ rest)) /\
    i = begin + Zlength source_words * sizeof ( PTR ) /\
    j = begin + Zlength (retained ++ rest) * sizeof ( PTR ) /\
    0 < ms_binary Mscan /\
    ms_binary Mscan mod 2 = 0 /\
    solver_propagate_frame s
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) =
      solver_propagate_frame s Mscan.
Proof.
  intros n F A_arr K M0 Mentry Mscan p scan_current s begin i j endvar
    copy_src copy_dst ii jj source_words retained moved rest garbage
    raw_prefix raw_suffix watch_memory copy_memory
    Hshape Hseed Hframe Hfront Hrest Hphys H_binary_watch_copy_progress
    Hroute_sem H_endvar H_i PreH21 PreH18 PreH22 PreH23 PreH24 Hbinlo.
  pose proof msat_binary_watch_write_prefix as Hwrite_prefix.
  set (Mroute := msolver_propagation_binary_conflict Mscan
    (tag_lit scan_current) p) in *.
  unfold propagation_watch_scan_physical in Hphys.
  destruct Hphys as
    (Hscaninv & Hwatchmemory & Hretlen & Hprefixlen & Hwatchlen).
  unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
  destruct H_binary_watch_copy_progress as
    (copied & uncopied & Hcopywords & Hrawprefixlen & Hjjrange &
     Hsuffixparts & Hsrcidx & Hdstidx & Hcopydef & Hcopylen).
  assert (Hsrcend : copy_src = Zlength source_words).
  {
    pose proof ptr_size_pos.
    apply Z.le_antisymm; [exact PreH24 |].
    apply (proj2 (Z.mul_le_mono_pos_r _ _ _ H)).
    rewrite H_i, H_endvar in PreH18.
    change (sizeof (PTR)) with (Z.of_nat ptr_size) in PreH18.
    lia.
  }
  assert (Hrawlen : Zlength raw_suffix = Zlength copied).
  {
    rewrite Hcopywords, Zlength_app, Zlength_cons in Hwatchlen.
    lia.
  }
  assert (Huncopiedlen : Zlength uncopied = 0).
  {
    rewrite Hsuffixparts, Zlength_app in Hrawlen. lia.
  }
  assert (Huncopied : uncopied = nil).
  {
    destruct uncopied as [|u uncopied]; [reflexivity|].
    rewrite Zlength_cons in Huncopiedlen.
    pose proof (Zlength_nonneg uncopied). lia.
  }
  subst uncopied. rewrite app_nil_r in Hsuffixparts. subst raw_suffix.
  assert (Hdstend : copy_dst = Zlength (retained ++ rest)).
  {
    rewrite Zlength_app, Hrest, Zlength_cons. lia.
  }
  assert (Hiend : i = begin + Zlength source_words * sizeof(PTR)).
  {
    solve_arch.
  }
  assert (Hjend : j = begin + Zlength (retained ++ rest) * sizeof(PTR)).
  {
    solve_arch.
  }
  assert (Hscanfinal :
    wlist_scan_inv source_words (retained ++ rest) moved nil).
  {
    unfold wlist_scan_inv in *.
    rewrite app_nil_r. rewrite <- app_assoc.
    eapply Permutation_trans; [|exact Hscaninv].
    apply Permutation_app_head. apply Permutation_app_comm.
  }
  assert (Hroom :
    Zlength (scan_current :: copied) <= Zlength (garbage ++ rest)).
  {
    rewrite Zlength_app, Hrest, Zlength_cons.
    pose proof (Zlength_nonneg garbage). lia.
  }
  destruct (Hwrite_prefix (scan_current :: copied) retained
    (garbage ++ rest) jj Hretlen Hroom) as
    (tail' & Hwritten & Htaillen).
  assert (Hcopyfromwrite :
    copy_memory = binary_watch_write jj (scan_current :: copied)
      watch_memory).
  {
    rewrite Hcopydef. cbn [binary_watch_write]. reflexivity.
  }
  assert (Hcopydecomp :
    copy_memory = (retained ++ rest) ++ tail').
  {
    rewrite Hcopyfromwrite, Hwatchmemory, Hwritten, Hrest.
    apply app_assoc.
  }
  assert (Hphysical_final :
    propagation_watch_scan_physical source_words (retained ++ rest)
      moved nil tail' copy_memory
      (Zlength source_words) (Zlength (retained ++ rest))).
  {
    unfold propagation_watch_scan_physical.
    refine (conj Hscanfinal (conj _ (conj eq_refl (conj _ _)))).
    - rewrite app_nil_r. exact Hcopydecomp.
    - rewrite <- Hcopydecomp. lia.
    - lia.
  }
  assert (Hroute_shape : solver_shape Mroute).
  {
    subst Mroute. unfold solver_shape in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    tauto.
  }
  assert (Hroute_seed : msolver_seed_shadow Mroute).
  {
    subst Mroute. unfold msolver_seed_shadow in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    exact Hseed.
  }
  assert (Hroute_frame : propagation_caller_frame M0 Mroute).
  {
    subst Mroute. unfold propagation_caller_frame in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    exact Hframe.
  }
  assert (Hroute_front : propagation_scan_frontier Mentry Mroute p).
  {
    subst Mroute. unfold propagation_scan_frontier in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    exact Hfront.
  }
  assert (Hroute_transition :
    propagation_binary_conflict_transition n F A_arr K Mscan p
      scan_current (retained ++ rest) Mroute).
  {
    apply propagation_binary_conflict_transition_intro.
    - reflexivity.
    - exact Hroute_sem.
  }
  assert (Hconflict_step :
    propagation_scan_conflict_step source_words retained moved rest
      copy_memory tail' (retained ++ rest)).
  {
    unfold propagation_scan_conflict_step.
    split; [reflexivity|exact Hphysical_final].
  }
  assert (Hexit :
    propagation_binary_conflict_exit n F A_arr K M0 Mentry Mscan Mroute
      p scan_current (ms_binary Mscan) source_words retained moved rest
      copy_memory tail' (retained ++ rest)).
  {
    unfold propagation_binary_conflict_exit.
    refine (conj Hroute_shape (conj Hroute_seed
      (conj Hroute_frame (conj Hroute_front
        (conj Hroute_transition (conj Hconflict_step
          (conj _ (conj Hphysical_final _)))))))).
    - exact Hroute_sem.
    - subst Mroute. cbn [msolver_propagation_binary_conflict
        msolver_propagation_overlay msolver_propagation_update ]. reflexivity.
  }
  assert (Hbinary_pos : 0 < ms_binary Mscan).
  {
    pose proof (solver_shape_binary_nonnull Mscan Hshape).
    lia.
  }
  assert (Hbinary_even : ms_binary Mscan mod 2 = 0).
  {
    apply clause_ptr_mod2.
    unfold solver_shape in Hshape.
    tauto.
  }
  split; [exists tail'; exact Hexit|].
  split; [exact Hiend|].
  split; [exact Hjend|].
  split; [exact Hbinary_pos|].
  split; [exact Hbinary_even|].
  assert (Hfr_route :
    solver_propagate_frame s
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) =
    solver_propagate_frame s Mscan).
  { unfold msolver_propagation_binary_conflict.
    apply solver_propagate_frame_overlay__propagate; reflexivity. }
  exact Hfr_route.
Qed.

Lemma msat_binary_conflict_route_semantics :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z) (retained rest raw_suffix : list Z)
         (scan_wm : list (list Z)),
    solver_propagation_weak n F A_arr K Mscan ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) ->
    solver_shape Mscan ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    prop_level (ms_core Mscan) ->
    heap_covers n (msolver_heap Mscan) (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) ->
    current_reasonless_earliest n Mscan ->
    minisat_watch_frontier_except n (msolver_db Mscan)
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) (lit_denote p) ->
    tagged_word scan_current ->
    rest = scan_current :: raw_suffix ->
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 <> 0 ->
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 <>
      lit_sig (tag_lit scan_current) ->
    ms_wm Mscan = replace_Znth p (retained ++ rest) scan_wm ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) p
      (ms_binary (msolver_propagation_binary_conflict Mscan
        (tag_lit scan_current) p))
      (retained ++ rest) nil.
Proof.
  intros n F A_arr K Mscan p scan_current retained rest raw_suffix
    scan_wm Hweak Hroute_weak Hshape Hp_wf Hprocessed
    Hlivelevel Hproplevel Hlivecovers Hliveearliest Hwatch_except
    Htagged Hrest Henq_assigned Henq_notsig H_ms_wm.
  set (Mroute := msolver_propagation_binary_conflict Mscan
    (tag_lit scan_current) p) in *.
  assert (Hdbwf : db_wf n (msolver_db Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_db_wf) (@msa_db_wf). }
  assert (Hwmexact : wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_wmap_exact) (@msa_wmap_exact). }
  assert (Hdbimplied : db_implied F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_implied) (@msa_db_implied). }
  assert (Hdbmatches : db_matches_cnf F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_matches) (@msa_db_matches). }
  assert (Hbinaryout : ~ In (ms_binary Mscan) (map fst (msolver_db Mscan))).
  { msat_propagate_project_weak_field Hweak K (@msw_binary_out) (@msa_binary_out). }
  assert (Hheapwf : heap_wf n (msolver_heap Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_heap_wf) (@msa_heap_wf). }
  assert (Htrailwf : mtrail_wf n (ms_core Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_trail_wf) (@msa_trail_wf). }
  assert (Hp_range : 0 <= p < Zlength scan_wm).
  { pose proof Hwmexact as [Hwmlen _].
    rewrite H_ms_wm, Zlength_replace_Znth in Hwmlen.
    destruct Hp_wf; lia. }
  assert (Hcurrent_in : In scan_current (Znth p (ms_wm Mscan) nil)).
  {
    rewrite H_ms_wm, Znth_replace_Znth_Same by lia.
    apply in_or_app. right. rewrite Hrest. left. reflexivity.
  }
  destruct (wmap_tag_witness n (msolver_db Mscan) (ms_wm Mscan)
      p scan_current Hdbwf Hwmexact
      ltac:(destruct Hp_wf; lia) Hcurrent_in Htagged)
    as [binary_owner [binary_obj [Hbinary_obj [Hbinary_len Hbinary_perm]]]].
  assert (Hpacked_perm :
    Permutation (co_lits binary_obj)
      (tag_lit scan_current :: lit_neg_c p :: nil)).
  {
    eapply Permutation_trans; [exact Hbinary_perm|]. apply perm_swap.
  }
  pose proof (db_wf_obj n (msolver_db Mscan) binary_owner binary_obj
    Hdbwf Hbinary_obj) as Hobjwf.
  destruct Hobjwf as [Hobjlen [Hobjlits Hobjnodup]].
  assert (Hpacked_wf :
    Forall (lit_wf_c n) (tag_lit scan_current :: lit_neg_c p :: nil)).
  {
    rewrite Forall_forall in Hobjlits |- *.
    intros l Hl. apply Hobjlits.
    eapply Permutation_in; [apply Permutation_sym; exact Hpacked_perm|exact Hl].
  }
  assert (Hpacked_nodup :
    NoDup (map lit_var_c (tag_lit scan_current :: lit_neg_c p :: nil))).
  {
    apply (Permutation_NoDup (Permutation_map lit_var_c Hpacked_perm)).
    exact Hobjnodup.
  }
  assert (Hbinary_entails :
    entails_clause F
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil)).
  {
    eapply tagged_reason_entailed;
      [exact Hdbwf|exact Hwmexact|destruct Hp_wf; lia|
       exact Hcurrent_in|exact Htagged|].
    intros owner obj Hentry.
    unfold msolver_db in Hentry. apply in_app_or in Hentry.
    destruct Hentry as [Hprob | Hlearnt].
    - unfold db_matches_cnf in Hdbmatches.
      rewrite Forall_forall in Hdbmatches.
      destruct (Hdbmatches (denote_obj obj)
        (db_clauses_in (ms_prob Mscan) owner obj Hprob))
        as [original [Horiginal Hperm]].
      eapply entails_clause_perm; [apply Permutation_sym; exact Hperm|].
      apply entails_clause_in. exact Horiginal.
    - unfold db_implied in Hdbimplied.
      rewrite Forall_forall in Hdbimplied.
      apply Hdbimplied. apply (db_clauses_in (ms_learnt Mscan)
        owner obj Hlearnt).
  }
  assert (Hbinary_false :
    clause_false (assigns_pv (mt_assigns (ms_core Mscan)))
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil)).
  {
    unfold clause_false. intros l Hl.
    destruct Hl as [<- | [<- | []]].
    - apply lit_false_iff.
      + pose proof (Forall_inv Hpacked_wf) as Hcur_wf; destruct Hcur_wf; lia.
      + assert (Hv : 0 <= lit_var_c (tag_lit scan_current) < n).
        { apply lit_var_c_in_range. exact (Forall_inv Hpacked_wf). }
        pose proof (Forall_Znth_elim Z lbool_cell
          (mt_assigns (ms_core Mscan)) 0
          (lit_var_c (tag_lit scan_current)) (mtw_cells Htrailwf)) as Hcell.
        rewrite (mtw_assigns_len Htrailwf) in Hcell.
        specialize (Hcell Hv). unfold lbool_cell in Hcell.
        destruct Hcell as [Hcell | [Hcell | Hcell]];
          destruct (lit_sig_values (tag_lit scan_current)) as [Hsig | Hsig];
          rewrite Hsig in Henq_notsig; lia.
    - rewrite <- (lit_denote_neg p ltac:(destruct Hp_wf; lia)).
      apply lit_false_iff.
      + pose proof (Forall_inv (Forall_inv_tail Hpacked_wf)) as Hneg_wf;
        destruct Hneg_wf; lia.
      + destruct Hprocessed as [Hptrue _].
        unfold lit_true, lit_false in *.
        rewrite lit_var_c_neg, lit_sig_neg. lia.
  }
  assert (Hbinary_wf :
    Forall (literal_wf n)
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil)).
  {
    rewrite <- (lit_denote_neg p ltac:(destruct Hp_wf; lia)).
    change (Forall (literal_wf n)
      (lits_denote (tag_lit scan_current :: lit_neg_c p :: nil))).
    apply lits_denote_wf. exact Hpacked_wf.
  }
  assert (Hbinary_nodup :
    NoDup (map literal_var
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil))).
  {
    rewrite <- (lit_denote_neg p ltac:(destruct Hp_wf; lia)).
    change (NoDup (map literal_var
      (lits_denote (tag_lit scan_current :: lit_neg_c p :: nil)))).
    apply lits_denote_nodup_vars. exact Hpacked_nodup.
  }
  unfold solver_propagation_scan_semantics. right.
  split.
  - subst Mroute. cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ].
    exact (solver_shape_binary_nonnull Mscan Hshape).
  - split.
    + reflexivity.
    + split.
      * unfold propagation_cancel_ready.
        refine (conj Hroute_weak
          (conj _ (conj _ (conj _ (conj _
            (conj _ (conj _ (conj _ _)))))))).
        all: subst Mroute;
          cbn [msolver_propagation_binary_conflict
            msolver_propagation_overlay msolver_propagation_update ]; assumption.
      * exists (lit_denote (tag_lit scan_current) ::
          literal_neg (lit_denote p) :: nil).
        split.
        -- unfold propagation_conflict_cert.
           repeat split; try assumption.
           exists (literal_neg (lit_denote p)).
           split; [right; left; reflexivity|].
           rewrite literal_var_neg, lit_var_c_denote. exact Hlivelevel.
        -- unfold conflict_ptr_denotes. left.
           subst Mroute. cbn [msolver_propagation_binary_conflict
             msolver_propagation_overlay msolver_propagation_update ].
           split; [reflexivity|]. split.
           ++ change (lit_denote (tag_lit scan_current) ::
                literal_neg (lit_denote p) :: nil =
                lit_denote (tag_lit scan_current) ::
                lit_denote (lit_neg_c p) :: nil).
              rewrite lit_denote_neg by (destruct Hp_wf; lia).
              reflexivity.
           ++ split; [exact Hbinaryout|discriminate].
Qed.

Lemma msat_binary_conflict_route_weak :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p).
Proof.
  intros n F A_arr K Mscan p scan_current Hweak.
  unfold solver_propagation_weak in *.
  destruct K;
    destruct Hweak as [Hpending Hinv];
    (split; [exact Hpending|]);
    destruct Hinv;
    constructor;
    cbn [msolver_propagation_binary_conflict msolver_propagation_overlay msolver_propagation_update ] in *;
    try assumption;
    unfold solver_shape in *; cbn in *; tauto.
Qed.

Lemma msat_enqueue_fresh_assump_at_root :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    0 <= lit_var_c q < n ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    forall root a,
      literal_wf n a ->
      assump_true_at_root (ms_core Mscan) root a ->
      assump_true_at_root (mt_enqueue (ms_core Mscan) q) root a.
Proof.
  intros n Mscan p q Htwf Hqrange Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  intros root a Hawf [Hatrue Halevel].
  assert (Hneq : literal_var a <> lit_var_c q).
  {
    intro Heq.
    destruct (eval_partial_literal_assigned _ _ _ Hatrue) as [b Hb].
    rewrite Heq in Hb.
    change (mt_pv (ms_core Mscan) (lit_var_c q) = None) in Hqnone.
    rewrite Hqnone in Hb. discriminate.
  }
  pose proof (Hothers (literal_var a) Hneq) as [Haeq _].
  change (mt_pv (mt_enqueue (ms_core Mscan) q) (literal_var a) =
    mt_pv (ms_core Mscan) (literal_var a)) in Haeq.
  split.
  - unfold eval_partial_literal in Hatrue |- *.
    rewrite Haeq. exact Hatrue.
  - unfold mt_enqueue, mt_push. cbn.
    unfold literal_wf, var_in_range in Hawf.
    change (Znth (literal_var a)
      (replace_Znth (lit_var_c q)
        (Zlength (mt_lim (ms_core Mscan)))
        (mt_levels (ms_core Mscan))) 0 <= root).
    rewrite (Znth_replace_Znth_Diff 0 (mt_levels (ms_core Mscan))
      (lit_var_c q) (literal_var a)
      (Zlength (mt_lim (ms_core Mscan)))).
    + exact Halevel.
    + rewrite (mtw_levels_len Htwf). exact Hqrange.
    + rewrite (mtw_levels_len Htwf). exact Hawf.
    + intro Heq. apply Hneq. symmetry. exact Heq.
Qed.

Lemma msat_enqueue_fresh_focus_false :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    lit_var_c q <> lit_var_c p ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    eval_partial_literal (assignment (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)))
      (literal_neg (lit_denote p)) = Some false.
Proof.
  intros n Mscan p q Hp_wf Hprocessed Hqpneq Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  assert (Hpviewtrue : eval_partial_literal (assignment (msolver_view n Mscan))
  (lit_denote p) = Some true).
  {
  destruct Hprocessed as [Hptrue _].
  pose proof (proj1 (lit_true_iff (mt_assigns (ms_core Mscan)) p
    (proj1 Hp_wf)) Hptrue) as Hpt.
  rewrite msolver_view_assignment.
  unfold eval_partial_literal in Hpt |- *.
  rewrite lit_var_c_denote.
  rewrite mt_pv_nonneg by
    (exact (proj1 (lit_var_c_in_range n p Hp_wf))).
  unfold assigns_pv, assigns_val in Hpt.
  rewrite lit_var_c_denote in Hpt.
  exact Hpt.
  }
  assert (Hpviewfalse : eval_partial_literal (assignment (msolver_view n Mscan))
  (literal_neg (lit_denote p)) = Some false).
  {
  rewrite eval_partial_literal_neg, Hpviewtrue. reflexivity.
  }
  pose proof (Hothers (lit_var_c p) (fun Heq => Hqpneq (eq_sym Heq)))
    as [Haeq _].
  unfold eval_partial_literal in Hpviewfalse |- *.
  rewrite literal_var_neg, lit_var_c_denote in Hpviewfalse.
  rewrite literal_var_neg, lit_var_c_denote, Haeq.
  exact Hpviewfalse.
Qed.

Lemma msat_enqueue_success_overlay_form :
  forall (Mscan : msolver) (p q : Z),
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) =
    msolver_propagation_overlay Mscan (mt_enqueue (ms_core Mscan) q)
      (ms_qtail Mscan + 1)
      (replace_Znth (lit_var_c q) (tag_of_lit p) (ms_reason_words Mscan))
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
        (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
      (ms_prob Mscan) (ms_learnt Mscan) (ms_binary_lits Mscan)
      (ms_wm Mscan) (ms_stats Mscan).
Proof.
  intros Mscan p q Hfreshcell.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hfreshb : (Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0
    =? 0)%Z = true) by (apply Z.eqb_eq; exact Hfreshcell).
  unfold Mpost, msolver_propagation_enqueue_success.
  rewrite Hfreshb. reflexivity.
Qed.

Lemma msat_level_cell_offcell_agree :
  forall (n : Z) (Mscan : msolver) (q : Z),
    mtrail_wf n (ms_core Mscan) ->
    0 <= lit_var_c q < n ->
    forall v, 0 <= v < n -> v <> lit_var_c q ->
      Znth v (replace_Znth (lit_var_c q) (Zlength (mt_lim (ms_core Mscan)))
        (mt_levels (ms_core Mscan))) 0 = Znth v (mt_levels (ms_core Mscan)) 0.
Proof.
  intros n Mscan q Htwf Hqrange.
  { intros v Hv Hvq.
    apply (Znth_replace_Znth_Diff 0 (mt_levels (ms_core Mscan))
      (lit_var_c q) v (Zlength (mt_lim (ms_core Mscan))));
      [rewrite (mtw_levels_len Htwf); exact Hqrange
      |rewrite (mtw_levels_len Htwf); exact Hv
      |intro E; apply Hvq; symmetry; exact E]. }
Qed.

Lemma msat_reason_word_offcell_agree :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    Zlength (ms_reason_words Mscan) = n ->
    0 <= lit_var_c q < n ->
    forall v, 0 <= v < n -> v <> lit_var_c q ->
      Znth v (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0 = Znth v (ms_reason_words Mscan) 0.
Proof.
  intros n Mscan p q Hwordslen Hqrange.
  { intros v Hv Hvq.
    apply (Znth_replace_Znth_Diff 0 (ms_reason_words Mscan)
      (lit_var_c q) v (tag_of_lit p));
      [rewrite Hwordslen; exact Hqrange|rewrite Hwordslen; exact Hv
      |intro E; apply Hvq; symmetry; exact E]. }
Qed.

Lemma msat_enqueue_fresh_reason_bin :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    lit_wf_c n p ->
    n = ms_size Mscan ->
    Zlength (ms_reason_words Mscan) = n ->
    0 <= lit_var_c q < n ->
    lit_var_c q <> lit_var_c p ->
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    binary_reason_same_level Mscan ->
    Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0 =
      Zlength (mt_lim (ms_core Mscan)) ->
    (forall v, 0 <= v < n ->
       is_tag (Znth v (ms_reason_words Mscan) 0) = true ->
       lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> lit_var_c q) ->
    binary_reason_same_level (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros n Mscan p q Htwf Hp_wf Hsize Hwordslen Hqrange Hqpneq Hfreshcell
    Hreasonbin Hprawlevel Hno_old_tag_target.
  pose proof (msat_enqueue_success_overlay_form Mscan p q Hfreshcell)
    as HMpost.
  pose proof (msat_reason_word_offcell_agree n Mscan p q Hwordslen Hqrange)
    as Hoffq_words.
  pose proof (msat_level_cell_offcell_agree n Mscan q Htwf Hqrange)
    as Hoffq_levels.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  rewrite HMpost. unfold binary_reason_same_level.
  unfold msolver_propagation_overlay, msolver_propagation_update.
  cbn.
  intros v Hv Htagpost.
  change (0 <= v < ms_size Mscan) in Hv.
  change (is_tag (Znth v
    (replace_Znth (lit_var_c q) (tag_of_lit p)
      (ms_reason_words Mscan)) 0) = true) in Htagpost.
  destruct (Z.eq_dec v (lit_var_c q)) as [-> | Hvq].
  - rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
      (lit_var_c q) (tag_of_lit p)) in Htagpost;
      [|rewrite Hwordslen; exact Hqrange].
    assert (Hwordq : nth (Z.to_nat (lit_var_c q))
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0 = tag_of_lit p).
    {
      change (Znth (lit_var_c q)
        (replace_Znth (lit_var_c q) (tag_of_lit p)
          (ms_reason_words Mscan)) 0 = tag_of_lit p).
      rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
        (lit_var_c q) (tag_of_lit p)); [reflexivity|].
      rewrite Hwordslen. exact Hqrange.
    }
    rewrite Hwordq.
    rewrite tag_lit_of.
    split.
    + rewrite <- Hsize. exact Hp_wf.
    + split.
      * assert (Hlevelp : nth (Z.to_nat (lit_var_c p))
          (replace_Znth (lit_var_c q)
            (Zlength (mt_lim (ms_core Mscan)))
            (mt_levels (ms_core Mscan))) 0 =
          Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0).
        {
          change (Znth (lit_var_c p)
            (replace_Znth (lit_var_c q)
              (Zlength (mt_lim (ms_core Mscan)))
              (mt_levels (ms_core Mscan))) 0 =
            Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0).
          rewrite (Hoffq_levels (lit_var_c p)
            (lit_var_c_in_range n p Hp_wf)
            (fun E => Hqpneq (eq_sym E))). reflexivity.
        }
        assert (Hlevelq : nth (Z.to_nat (lit_var_c q))
            (replace_Znth (lit_var_c q)
              (Zlength (mt_lim (ms_core Mscan)))
              (mt_levels (ms_core Mscan))) 0 =
            Zlength (mt_lim (ms_core Mscan))).
        {
          change (Znth (lit_var_c q)
            (replace_Znth (lit_var_c q)
              (Zlength (mt_lim (ms_core Mscan)))
              (mt_levels (ms_core Mscan))) 0 =
            Zlength (mt_lim (ms_core Mscan))).
          rewrite (Znth_replace_Znth_Same 0 (mt_levels (ms_core Mscan))
            (lit_var_c q) (Zlength (mt_lim (ms_core Mscan))));
            [reflexivity|].
          rewrite (mtw_levels_len Htwf). exact Hqrange.
        }
        rewrite Hlevelp, Hlevelq. exact Hprawlevel.
      * intro Heq. apply Hqpneq. symmetry. exact Heq.
  - assert (Hvold : 0 <= v < ms_size Mscan) by exact Hv.
    rewrite (Hoffq_words v ltac:(rewrite Hsize; exact Hv) Hvq)
      in Htagpost.
    assert (Hwordv : nth (Z.to_nat v)
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0 =
      Znth v (ms_reason_words Mscan) 0).
    {
      change (Znth v
        (replace_Znth (lit_var_c q) (tag_of_lit p)
          (ms_reason_words Mscan)) 0 =
        Znth v (ms_reason_words Mscan) 0).
      exact (Hoffq_words v ltac:(rewrite Hsize; exact Hv) Hvq).
    }
    rewrite Hwordv.
    pose proof (Hreasonbin v Hvold Htagpost) as
      [Htargetwf [Hlevelsold Htargetne]].
    assert (Htargetq : lit_var_c
      (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> lit_var_c q).
    { apply Hno_old_tag_target; [rewrite Hsize; exact Hv|exact Htagpost]. }
    change (lit_wf_c (ms_size Mscan)
      (tag_lit (Znth v (ms_reason_words Mscan) 0)) /\
      Znth (lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)))
        (replace_Znth (lit_var_c q)
          (Zlength (mt_lim (ms_core Mscan)))
          (mt_levels (ms_core Mscan))) 0 =
      Znth v (replace_Znth (lit_var_c q)
          (Zlength (mt_lim (ms_core Mscan)))
          (mt_levels (ms_core Mscan))) 0 /\
      lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> v).
    split; [exact Htargetwf|]. split.
    + rewrite (Hoffq_levels
        (lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)))
        (lit_var_c_in_range n _ ltac:(rewrite Hsize; exact Htargetwf))
        Htargetq).
      rewrite (Hoffq_levels v ltac:(rewrite Hsize; exact Hv) Hvq).
      exact Hlevelsold.
    + exact Htargetne.
Qed.

Lemma msat_enqueue_fresh_reason_entailed :
  forall (n : Z) (F : cnf) (Mscan : msolver) (p scan_current : Z),
    db_wf n (msolver_db Mscan) ->
    wmap_exact n (msolver_db Mscan) (ms_wm Mscan) ->
    lit_wf_c n p ->
    In scan_current (Znth p (ms_wm Mscan) nil) ->
    tagged_word scan_current ->
    (forall ptr obj, In (ptr, obj) (msolver_db Mscan) ->
       entails_clause F (denote_obj obj)) ->
    entails_clause F
      (cons (lit_denote (tag_lit scan_current))
        (cons (literal_neg (lit_denote p)) nil)).
Proof.
  intros n F Mscan p scan_current Hdbwf Hwmexact Hp_wf Hwmword
    H_tagged_word Hdbent.
  set (q := tag_lit scan_current) in *.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  unfold rc.
  eapply tagged_reason_entailed.
  - exact Hdbwf.
  - exact Hwmexact.
  - exact Hp_wf.
  - exact Hwmword.
  - exact H_tagged_word.
  - exact Hdbent.
Qed.

Lemma msat_enqueue_fresh_reason_head_ok :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    0 <= lit_var_c q < n ->
    Zlength (ms_reason_words Mscan) = n ->
    n = ms_size Mscan ->
    reason_head_ok (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros n F A_arr K Mscan p q Hweak Hfreshcell Hqrange Hwordslen Hsize.
  pose proof (msat_enqueue_success_overlay_form Mscan p q Hfreshcell)
    as HMpost.
  pose proof (msat_reason_word_offcell_agree n Mscan p q Hwordslen Hqrange)
    as Hoffq_words.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hold : reason_head_ok Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_reason_head) (@msa_reason_head). }
  rewrite HMpost. unfold reason_head_ok in Hold |- *.
  cbn [msolver_propagation_overlay msolver_propagation_update ].
  intros v co0 Hv Htag Hnonzero Hin.
  destruct (Z.eq_dec v (lit_var_c q)) as [-> | Hvq].
  - change (is_tag (Znth (lit_var_c q)
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0) = false) in Htag.
    rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
      (lit_var_c q) (tag_of_lit p)) in Htag;
      [rewrite is_tag_of in Htag; discriminate|].
    rewrite Hwordslen. exact Hqrange.
  - change (is_tag (Znth v
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0) = false) in Htag.
    change (Znth v (replace_Znth (lit_var_c q) (tag_of_lit p)
      (ms_reason_words Mscan)) 0 <> 0) in Hnonzero.
    change (In (Znth v (replace_Znth (lit_var_c q) (tag_of_lit p)
      (ms_reason_words Mscan)) 0, co0) (msolver_db Mscan)) in Hin.
    rewrite (Hoffq_words v ltac:(rewrite Hsize; exact Hv) Hvq)
      in Htag, Hnonzero, Hin.
    eapply Hold; eassumption.
Qed.

Lemma msat_enqueue_fresh_reason_lits_wf :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    lit_wf_c n q ->
    lit_wf_c n p ->
    forall c k, Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) = Some c -> In k c -> literal_wf n k.
Proof.
  intros n Mscan p q Hqwf Hp_wf.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  intros c k Hc Hk. inversion Hc. subst c. unfold rc in Hk.
  destruct Hk as [<- | [<- | []]].
  - apply lit_denote_wf. exact Hqwf.
  - rewrite <- (lit_denote_neg p) by (destruct Hp_wf; lia).
    apply lit_denote_wf. apply lit_neg_c_wf. exact Hp_wf.
Qed.

Lemma msat_enqueue_fresh_reason_valid :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    lit_var_c q <> lit_var_c p ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    eval_partial_literal (assignment (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)))
      (literal_neg (lit_denote p)) = Some false ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reason_valid (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)).
Proof.
  intros n Mscan p q Hqpneq Hplevel Hp_post_false Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  exists (lit_pol q), (Zlength (mt_lim (ms_core Mscan))), rq.
  split; [exact Hqassigned|].
  split; [exact Hqlevel|].
  split; [exact Hqrank|].
  split.
  { unfold rc. left. rewrite lit_denote_satisfying. reflexivity. }
  intros l Hl Hlv.
  unfold rc in Hl.
  destruct Hl as [Hl | [Hl | []]].
  - subst l. rewrite lit_var_c_denote in Hlv. contradiction.
  - subst l.
    split; [exact Hp_post_false|].
    assert (Hdep : reason_dependency Vpost (lit_var_c q) (lit_var_c p)).
    {
      unfold reason_dependency.
      exists rc, (literal_neg (lit_denote p)).
      repeat split.
      - exact Hqreason.
      - unfold rc. right. left. reflexivity.
      - rewrite literal_var_neg, lit_var_c_denote. reflexivity.
      - intro Heq. apply Hqpneq. symmetry. exact Heq.
      - exact Hp_post_false.
    }
    destruct (Hdependencies (lit_var_c p) Hdep) as [rp [Hrp Hrplt]].
    exists (Zlength (mt_lim (ms_core Mscan))), rp.
    split.
    { pose proof (Hothers (lit_var_c p)
        (fun Heq => Hqpneq (eq_sym Heq))) as [_ [Hleq _]].
      rewrite literal_var_neg, lit_var_c_denote.
      rewrite Hleq. exact Hplevel. }
    split.
    { rewrite literal_var_neg, lit_var_c_denote. exact Hrp. }
    split; [lia|exact Hrplt].
Qed.

Lemma msat_enqueue_fresh_reasons_entailed :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    entails_clause F (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reasons_entailed F (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)).
Proof.
  intros n F A_arr K Mscan p q Hweak Hreasonent Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  assert (Hold : reasons_entailed F (msolver_view n Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_ent) (@msa_reasons_ent). }
  unfold reasons_entailed in Hold |- *.
  intros x c Hxc.
  destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
  - rewrite Hqreason in Hxc. inversion Hxc. exact Hreasonent.
  - pose proof (Hothers x Hxq) as [_ [_ [Hreq _]]].
    apply (Hold x c). rewrite <- Hreq. exact Hxc.
Qed.

Lemma msat_enqueue_fresh_reasons_injective :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    lit_var_c q <> lit_var_c p ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reasons_var_injective (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)).
Proof.
  intros n F A_arr K Mscan p q Hweak Hqpneq Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  assert (Hold : reasons_var_injective (msolver_view n Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_inj) (@msa_reasons_inj). }
  unfold reasons_var_injective in Hold |- *.
  intros x c Hxc.
  destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
  - rewrite Hqreason in Hxc. inversion Hxc. subst c.
    apply NoDup_map_var_injective. unfold rc.
    apply tagged_reason_nodup_vars. exact Hqpneq.
  - pose proof (Hothers x Hxq) as [_ [_ [Hreq _]]].
    apply (Hold x c). rewrite <- Hreq. exact Hxc.
Qed.

Lemma msat_enqueue_fresh_reasons_match :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    lit_wf_c n p ->
    0 <= lit_var_c q < n ->
    Zlength (ms_reason_words Mscan) = n ->
    reasons_match n (ms_core Mscan) (msolver_db Mscan)
      (ms_reason_words Mscan) (ms_reason_of Mscan) ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reasons_match n (mt_enqueue (ms_core Mscan) q) (msolver_db Mscan)
      (replace_Znth (lit_var_c q) (tag_of_lit p) (ms_reason_words Mscan))
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
        (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)))).
Proof.
  intros n Mscan p q Htwf Hp_wf Hqrange Hwordslen Hreasonsmem Hassignone.
  pose proof (msat_reason_word_offcell_agree n Mscan p q Hwordslen Hqrange)
    as Hoffq_words.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  unfold reasons_match. intros v Hv.
  destruct (Z.eq_dec v (lit_var_c q)) as [-> | Hvq].
  - rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
      (lit_var_c q) (tag_of_lit p));
      [|rewrite Hwordslen; exact Hqrange].
    rewrite sat_function_update_eq.
    assert (Hqcell : Znth (lit_var_c q)
      (mt_assigns (mt_enqueue (ms_core Mscan) q)) 0 <> 0).
    {
      unfold mt_enqueue, mt_push. cbn.
      change (Znth (lit_var_c q)
        (replace_Znth (lit_var_c q) (lit_sig q)
          (mt_assigns (ms_core Mscan))) 0 <> 0).
      rewrite (Znth_replace_Znth_Same 0 (mt_assigns (ms_core Mscan))
        (lit_var_c q) (lit_sig q));
        [apply lit_sig_nonzero|].
      rewrite (mtw_assigns_len Htwf). exact Hqrange.
    }
    pose proof (reason_word_of_tag (mt_enqueue (ms_core Mscan) q)
      (lit_var_c q) (msolver_db Mscan) p
      (proj1 Hp_wf) Hqcell) as Hok.
    change (mt_pv (mt_enqueue (ms_core Mscan) q) (lit_var_c q) =
      Some (lit_pol q)) in Hqassigned.
    pose proof (trail_lit_of_denote (mt_enqueue (ms_core Mscan) q)
      (lit_var_c q) (lit_pol q) (proj1 Hqrange) Hqassigned) as Hden.
    rewrite <- lit_denote_satisfying in Hden.
    unfold rc. rewrite Hden in Hok. exact Hok.
  - rewrite (Hoffq_words v Hv Hvq).
    rewrite sat_function_update_neq by (intro E; apply Hvq; symmetry; exact E).
    specialize (Hreasonsmem v Hv).
    assert (Hassignv : Znth v
      (mt_assigns (mt_enqueue (ms_core Mscan) q)) 0 =
      Znth v (mt_assigns (ms_core Mscan)) 0).
    {
      unfold mt_enqueue, mt_push. cbn.
      change (Znth v (replace_Znth (lit_var_c q) (lit_sig q)
        (mt_assigns (ms_core Mscan))) 0 =
        Znth v (mt_assigns (ms_core Mscan)) 0).
      rewrite (Znth_replace_Znth_Diff 0 (mt_assigns (ms_core Mscan))
        (lit_var_c q) v (lit_sig q));
        [reflexivity|rewrite (mtw_assigns_len Htwf); exact Hqrange
        |rewrite (mtw_assigns_len Htwf); exact Hv
        |intro E; apply Hvq; symmetry; exact E].
    }
    assert (Hlitv : trail_lit_of (mt_enqueue (ms_core Mscan) q) v =
      trail_lit_of (ms_core Mscan) v).
    { unfold trail_lit_of. rewrite Hassignv. reflexivity. }
    unfold reason_word_ok in Hreasonsmem |- *.
    rewrite Hassignv, Hlitv. exact Hreasonsmem.
Qed.

Lemma msat_enqueue_fresh_stable_view :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    stable_view (msolver_view n Mscan) ->
    reason_valid (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    stable_view (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)).
Proof.
  intros n Mscan p q Hstable Hreasonvalidq Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  unfold stable_view in Hstable |- *.
  destruct Hstable as [Hground Hclosed]. split.
  - unfold grounded_at in Hground |- *.
    intros x b Hxb.
    destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
    + rewrite Hqassigned in Hxb. inversion Hxb. subst b.
      exists (Zlength (mt_lim (ms_core Mscan))), rq.
      split; [exact Hqlevel|]. split; [exact Hqrank|].
      right. exists rc. split; [exact Hqreason|exact Hreasonvalidq].
    + pose proof (Hothers x Hxq) as [Haeq [Hleq [Hreq Hrankeq]]].
      rewrite Haeq in Hxb.
      destruct (Hground x b Hxb) as [d [rx [Hlev [Hrank Hro]]]].
      exists d, rx. split; [rewrite Hleq; exact Hlev|].
      split; [rewrite Hrankeq; exact Hrank|].
      destruct Hro as [Hnone | [c [Hsome Hvalid]]].
      * left. rewrite Hreq. exact Hnone.
      * right. exists c. split; [rewrite Hreq; exact Hsome|].
        destruct Hvalid as
          [b0 [d0 [rx0 [Ha0 [Hl0 [Hr0 [Hin0 Hside]]]]]]].
        exists b0, d0, rx0.
        split; [rewrite Haeq; exact Ha0|].
        split; [rewrite Hleq; exact Hl0|].
        split; [rewrite Hrankeq; exact Hr0|].
        split; [exact Hin0|].
        intros l Hl Hlx.
        destruct (Hside l Hl Hlx) as [Heval [dy [ry [Hly [Hry Hord]]]]].
        assert (Hlq : literal_var l <> lit_var_c q).
        {
          intro Heq.
          destruct (eval_partial_literal_assigned _ _ _ Heval) as [bb Hbb].
          rewrite Heq, Hqnone in Hbb. discriminate.
        }
        pose proof (Hothers (literal_var l) Hlq)
          as [Hla [Hll [_ Hlr]]].
        split.
        { unfold eval_partial_literal in Heval |- *. rewrite Hla. exact Heval. }
        exists dy, ry. repeat split.
        { rewrite Hll. exact Hly. }
        { rewrite Hlr. exact Hry. }
        all: tauto.
  - unfold closed_levels in Hclosed |- *.
    destruct Hclosed as [Hcur [Hbound Hdec]].
    split; [exact Hcur|]. split.
    + intros x b d Hxb Hxd.
      destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
      * rewrite Hqlevel in Hxd. inversion Hxd. subst d.
        unfold Vpost. cbn [view_of mt_enqueue mt_push].
        split; [apply Zlength_nonneg|reflexivity].
      * pose proof (Hothers x Hxq) as [Haeq [Hleq _]].
        rewrite Haeq in Hxb. rewrite Hleq in Hxd.
        exact (Hbound x b d Hxb Hxd).
    + intros d Hd. destruct (Hdec d Hd) as [x [[b Hxb] [Hxl Hxr]]].
      assert (Hxq : x <> lit_var_c q).
      { intro Heq. subst x. rewrite Hqnone in Hxb. discriminate. }
      pose proof (Hothers x Hxq) as [Haeq [Hleq [Hreq _]]].
      exists x. split.
      * exists b. rewrite Haeq. exact Hxb.
      * split; [rewrite Hleq; exact Hxl|]. rewrite Hreq. exact Hxr.
Qed.

Lemma msat_enqueue_fresh_trail_implied :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    mtrail_wf n (ms_core Mscan) ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    entails_clause F (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) ->
    trail_implied F (mt_enqueue (ms_core Mscan) q).
Proof.
  intros n F A_arr K Mscan p q Hweak Htwf Hprocessed Hreasonent.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  eapply trail_implied_unit with (rc := rc).
  - exact Htwf.
  - unfold solver_propagation_weak in Hweak.
    destruct K; destruct Hweak as [_ Hinv].
    + exact (msw_trail_impl Hinv).
    + exact (msa_trail_impl Hinv).
  - exact Hreasonent.
  - unfold rc. left. reflexivity.
  - intros k Hk Hkq.
    unfold rc in Hk.
    destruct Hk as [Hk | [Hk | []]]; [congruence|].
    subst k.
    destruct Hprocessed as [_ [idx [Hidx Hpidx]]].
    exists idx. split.
    { pose proof (mtw_qhead_range Htwf). lia. }
    rewrite literal_neg_involutive, Hpidx. reflexivity.
Qed.

Lemma msat_enqueue_success_fresh_form :
  forall (Mscan : msolver) (p q : Z),
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) =
    msolver_enqueue_fresh Mscan q (tag_of_lit p) (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros Mscan p q Hfreshcell.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  unfold Mpost.
  apply propagation_enqueue_success_fresh__propagate_dbu.
  exact Hfreshcell.
Qed.

Lemma msat_enqueue_fresh_weak :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    mtrail_wf n (ms_core Mscan) ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    solver_shape (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    mtrail_wf n (mt_enqueue (ms_core Mscan) q) ->
    stable_view (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) ->
    reasons_entailed F (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) ->
    reasons_var_injective (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) ->
    trail_implied F (mt_enqueue (ms_core Mscan) q) ->
    reasons_match n (mt_enqueue (ms_core Mscan) q) (msolver_db Mscan)
      (replace_Znth (lit_var_c q) (tag_of_lit p) (ms_reason_words Mscan))
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
        (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)))) ->
    reason_head_ok (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    binary_reason_same_level (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    (forall root a,
       literal_wf n a ->
       assump_true_at_root (ms_core Mscan) root a ->
       assump_true_at_root (mt_enqueue (ms_core Mscan) q) root a) ->
    solver_propagation_weak n F A_arr K (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros n F A_arr K Mscan p q Hweak Htwf Hqwf Hfreshcell Hshape' Htrailwf'
    Hstable' Hreasonsent' Hreasonsinj' Htrailimpl' Hreasonsmem' Hreasonhead'
    Hreasonbin' Hassump_preserve.
  pose proof (msat_enqueue_success_overlay_form Mscan p q Hfreshcell)
    as HMpost.
  pose proof (msat_enqueue_success_fresh_form Mscan p q Hfreshcell)
    as HMfresh.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hviewpost : msolver_view n Mpost = Vpost).
  {
    rewrite HMpost. unfold Vpost, msolver_view, msolver_clauses, msolver_db.
    reflexivity.
  }
  assert (Hdbcomplete_preserve :
    cnf_wf n F -> db_complete F Mscan -> db_complete F Mpost).
  { intros _ _. rewrite HMfresh.
    destruct Hweak as [_ HK]. destruct K as [A_inst | A_proc]; cbn in HK.
    - eapply db_complete_enqueue_fresh__record;
        [exact HK|exact Hqwf|exact Hfreshcell].
    - eapply db_complete_enqueue_fresh_assuming__propagate_dbu;
        [exact HK|exact Hqwf|exact Hfreshcell]. }
  unfold solver_propagation_weak in *.
  split.
  - rewrite HMpost. exact (proj1 Hweak).
  -
    destruct K as [A_inst | A_proc]; cbn in *;
      pose proof (proj2 Hweak) as Hold; destruct Hold; constructor.
    all: lazymatch goal with
         | |- solver_shape _ => exact Hshape'
         | |- mtrail_wf _ _ => rewrite HMpost; exact Htrailwf'
         | |- trail_implied _ _ => rewrite HMpost; exact Htrailimpl'
         | |- stable_view _ => rewrite Hviewpost; exact Hstable'
         | |- reasons_entailed _ _ => rewrite Hviewpost; exact Hreasonsent'
         | |- reasons_var_injective _ => rewrite Hviewpost; exact Hreasonsinj'
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- reasons_match _ _ _ _ _ => rewrite HMpost; exact Hreasonsmem'
         | |- reason_head_ok _ => exact Hreasonhead'
         | |- binary_reason_same_level _ => exact Hreasonbin'
         | |- db_complete _ _ => apply Hdbcomplete_preserve; assumption
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- (exists _, _) =>
             lazymatch goal with
             | H : (exists _, _) |- _ => destruct H as [A_x [Hdec Hincl]]
             end;
             exists A_x; split; [|exact Hincl];
             rewrite HMpost; cbn;
             rewrite (decisions_upto_enqueue n (ms_core Mscan) q
               (Zlength (mt_lim (ms_core Mscan))) Htwf); exact Hdec
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- decisions_upto _ _ = _ =>
             rewrite HMpost; cbn;
             rewrite (decisions_upto_enqueue n (ms_core Mscan) q
               (ms_root_level Mscan) Htwf); assumption
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- Forall (assump_true_at_root _ _) _ =>
             rewrite HMpost; cbn; rewrite Forall_forall; intros a Ha;
             apply Hassump_preserve
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- literal_wf _ _ =>
             lazymatch goal with
             | Hwf : Forall (literal_wf _) ?A |- _ =>
                 rewrite Forall_forall in Hwf;
                 first [ apply Hwf; assumption
                       | lazymatch goal with
                         | Hin : incl _ A |- _ => apply Hwf, Hin; assumption
                         end ]
             end
         | _ => idtac
         end.
    all: (lazymatch goal with
         | |- assump_true_at_root _ _ _ =>
             lazymatch goal with
             | Hsat : Forall (assump_true_at_root _ _) _ |- _ =>
                 rewrite Forall_forall in Hsat; apply Hsat; assumption
             end
         | _ => idtac
         end);
      (lazymatch goal with
         | |- _ => first [ assumption | rewrite HMpost; assumption ]
         end).
Qed.

Lemma msat_no_old_tag_targets_fresh :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    n = ms_size Mscan ->
    stable_view (msolver_view n Mscan) ->
    reasons_match n (ms_core Mscan) (msolver_db Mscan)
      (ms_reason_words Mscan) (ms_reason_of Mscan) ->
    binary_reason_same_level Mscan ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    forall v, 0 <= v < n ->
      is_tag (Znth v (ms_reason_words Mscan) 0) = true ->
      lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> lit_var_c q.
Proof.
  intros n Mscan p q Htwf Hsize Hstable Hreasonsmem Hreasonbin Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  intros v Hv Htag Heqtarget.
  pose proof (Hreasonsmem v Hv) as Hmatch.
  assert (Hwordnonzero : Znth v (ms_reason_words Mscan) 0 <> 0).
  { intro Hz. rewrite Hz in Htag. discriminate. }
  pose proof (reason_word_ok_nonzero_assigned
    (ms_core Mscan) v (msolver_db Mscan)
    (Znth v (ms_reason_words Mscan) 0) (ms_reason_of Mscan v)
    Hwordnonzero Hmatch) as Hvcell.
  assert (Hassignv : exists b,
    assignment (msolver_view n Mscan) v = Some b).
  {
    change (exists b, mt_pv (ms_core Mscan) v = Some b).
    destruct (mt_pv (ms_core Mscan) v) as [b|] eqn:Hpv;
      [eauto|exfalso].
    apply (proj1 (mt_pv_none_iff n (ms_core Mscan) v Htwf)) in Hpv.
    apply Hpv. apply (proj1 (mtw_assigned_iff Htwf v Hv)). exact Hvcell.
  }
  destruct Hassignv as [b Hassignv].
  pose proof (Hreasonbin v (ltac:(rewrite <- Hsize; exact Hv)) Htag)
    as [Htargetwf [Hlevelsold Htargetneold]].
  assert (Hwordpos : 0 < Znth v (ms_reason_words Mscan) 0).
  { eapply tag_pos_of_lit_wf; eassumption. }
  pose proof (reason_word_ok_tag (ms_core Mscan) v (msolver_db Mscan)
    (Znth v (ms_reason_words Mscan) 0) (ms_reason_of Mscan v)
    Hwordpos Htag Hmatch) as Hraw.
  assert (Hviewraw : reason_of (msolver_view n Mscan) v =
    ms_reason_of Mscan v).
  {
    unfold msolver_view, view_of. cbn.
    destruct (trail_pos (ms_core Mscan) v) eqn:Hpos.
    - reflexivity.
    - apply (proj2 (view_unassigned_iff n (ms_core Mscan) v Htwf)) in Hpos.
      change (mt_pv (ms_core Mscan) v = Some b) in Hassignv.
      rewrite Hpos in Hassignv. discriminate.
  }
  destruct Hstable as [Hground _].
  destruct (Hground v b Hassignv) as [d [rv [Hvlev [Hvrank Hgroundv]]]].
  destruct Hgroundv as [Hnone | [c [Hsome Hvalid]]].
  - rewrite Hviewraw, Hraw in Hnone. discriminate.
  - rewrite Hviewraw, Hraw in Hsome. inversion Hsome. subst c.
    unfold reason_valid in Hvalid.
    destruct Hvalid as [b0 [d0 [r0
      [Ha0 [Hl0 [Hr0 [Hhead Hside]]]]]]].
    specialize (Hside
      (literal_neg (lit_denote
        (tag_lit (Znth v (ms_reason_words Mscan) 0))))
      (or_intror (or_introl eq_refl))).
    assert (Htargetne : literal_var
      (literal_neg (lit_denote
        (tag_lit (Znth v (ms_reason_words Mscan) 0)))) <> v).
    {
      rewrite literal_var_neg, lit_var_c_denote.
      exact Htargetneold.
    }
    specialize (Hside Htargetne).
    destruct Hside as [Hfalse _].
    destruct (eval_partial_literal_assigned _ _ _ Hfalse) as [bt Hbt].
    rewrite literal_var_neg, lit_var_c_denote, Heqtarget in Hbt.
    rewrite Hqnone in Hbt. discriminate.
Qed.

Lemma msat_propagate_db_entailed :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver),
    solver_propagation_weak n F A_arr K Mscan ->
    forall ptr obj, In (ptr, obj) (msolver_db Mscan) ->
      entails_clause F (denote_obj obj).
Proof.
  intros n F A_arr K Mscan Hweak.
  intros ptr obj Hin.
  assert (Hinc : In (denote_obj obj) (msolver_clauses Mscan)).
  { unfold msolver_clauses. eapply db_clauses_in. exact Hin. }
  unfold solver_propagation_weak in Hweak.
  destruct K; destruct Hweak as [_ Hinv].
  - eapply msolver_inv_db_entailed; [exact Hinv|].
    rewrite msolver_view_installed. exact Hinc.
  - unfold msolver_clauses, msolver_db in Hinc.
    rewrite db_clauses_app in Hinc.
    apply in_app_or in Hinc as [Hprob | Hlearnt].
    + pose proof (msa_db_matches Hinv) as Hmatches.
      unfold db_matches_cnf in Hmatches.
      rewrite Forall_forall in Hmatches.
      destruct (Hmatches _ Hprob) as [c0 [Hc0 Hperm0]].
      eapply entails_clause_perm.
      * apply Permutation_sym. exact Hperm0.
      * apply entails_clause_in. exact Hc0.
    + pose proof (msa_db_implied Hinv) as Himplied.
      unfold db_implied in Himplied.
      rewrite Forall_forall in Himplied.
      exact (Himplied _ Hlearnt).
Qed.

Lemma msat_propagate_weak_core_fields :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver),
    solver_propagation_weak n F A_arr K Mscan ->
    db_wf n (msolver_db Mscan) /\
    mtrail_wf n (ms_core Mscan) /\
    solver_shape Mscan /\
    wmap_exact n (msolver_db Mscan) (ms_wm Mscan) /\
    stable_view (msolver_view n Mscan) /\
    reasons_match n (ms_core Mscan) (msolver_db Mscan)
      (ms_reason_words Mscan) (ms_reason_of Mscan) /\
    binary_reason_same_level Mscan /\
    n = ms_size Mscan.
Proof.
  intros n F A_arr K Mscan Hweak.
  split. { msat_propagate_project_weak_field Hweak K (@msw_db_wf) (@msa_db_wf). }
  split. { msat_propagate_project_weak_field Hweak K (@msw_trail_wf) (@msa_trail_wf). }
  split. { msat_propagate_project_weak_field Hweak K (@msw_shape) (@msa_shape). }
  split.
  { msat_propagate_project_weak_field Hweak K (@msw_wmap_exact) (@msa_wmap_exact). }
  split. { msat_propagate_project_weak_field Hweak K (@msw_stable) (@msa_stable). }
  split.
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_mem) (@msa_reasons_mem). }
  split.
  { msat_propagate_project_weak_field Hweak K (@msw_reason_bin) (@msa_reason_bin). }
  msat_propagate_project_weak_field Hweak K (@msw_size) (@msa_size).
Qed.

Lemma msat_scan_focus_level_is_root :
  forall (n : Z) (Mscan : msolver) (p : Z),
    mtrail_wf n (ms_core Mscan) ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0 =
      Zlength (mt_lim (ms_core Mscan)).
Proof.
  intros n Mscan p Htwf Hprocessed Hplevel.
  destruct Hprocessed as [Hptrue [ip [Hip Hptrail]]].
  assert (Hipfull : 0 <= ip < Zlength (mt_trail (ms_core Mscan))).
  { pose proof (mtw_qhead_range Htwf). lia. }
  pose proof (trail_pos_of_index (ms_core Mscan) ip
    (mtw_trail_nodup Htwf) Hipfull) as Hpos.
  unfold trail_var in Hpos. rewrite Hptrail in Hpos.
  unfold msolver_view, view_of in Hplevel. cbn in Hplevel.
  rewrite Hpos in Hplevel.
  cbn in Hplevel.
  assert (Hidxlevel : level_of_index (ms_core Mscan) ip =
    Zlength (mt_lim (ms_core Mscan))).
  { rewrite <- (Z2Nat.id ip) by lia. now injection Hplevel. }
  pose proof (mtw_levels_agree Htwf ip Hipfull) as Hagree.
  unfold trail_var in Hagree. rewrite Hptrail in Hagree.
  rewrite Hagree. exact Hidxlevel.
Qed.

Lemma msat_enqueue_fresh_scan_semantics :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z) (retained rest raw_suffix : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    tagged_word scan_current ->
    rest = scan_current :: raw_suffix ->
    lit_wf_c n (tag_lit scan_current) ->
    In scan_current (Znth p (ms_wm Mscan) nil) ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix ->
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    ms_qtail Mscan + 1 <= ms_cap Mscan ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_enqueue_success Mscan (tag_lit scan_current)
        (tag_of_lit p)
        (cons (lit_denote (tag_lit scan_current))
          (cons (literal_neg (lit_denote p)) nil)))
      p 0 (retained ++ scan_current :: nil) raw_suffix.
Proof.
  intros n F A_arr K Mscan p scan_current retained rest raw_suffix
    Hsem H_tagged_word H_rest Hqwf Hwmword Hcarrier_scan Hfreshcell Hcapbound.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hconflict]; [|decompose [and] Hconflict; lia].
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hcovers &
     Hreasonless & Hplevel & Hp_wf & Hprocessed & Hfrontier & Hcarrier).
  destruct (msat_propagate_weak_core_fields n F A_arr K Mscan Hweak) as
    (Hdbwf & Htwf & Hshape & Hwmexact & Hstable & Hreasonsmem & Hreasonbin &
     Hsize).
  pose proof (msat_propagate_db_entailed n F A_arr K Mscan Hweak) as Hdbent.
  pose proof (msat_enqueue_fresh_reason_entailed n F Mscan p scan_current
    Hdbwf Hwmexact Hp_wf Hwmword H_tagged_word Hdbent) as Hreasonent.
  pose proof (msat_enqueue_success_overlay_form Mscan p
    (tag_lit scan_current) Hfreshcell) as HMpost.
  pose proof (msat_enqueue_success_fresh_form Mscan p
    (tag_lit scan_current) Hfreshcell) as HMfresh.
  set (q := tag_lit scan_current) in *.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hqrange : 0 <= lit_var_c q < n)
    by (apply lit_var_c_in_range; exact Hqwf).
  assert (Hqpneq : lit_var_c q <> lit_var_c p).
  { eapply processed_fresh_target_different; eassumption. }
  pose proof (msat_enqueue_fresh_reason_lits_wf n Mscan p q Hqwf Hp_wf)
    as Hreasonwf.
  assert (Htrailwf' : mtrail_wf n (mt_enqueue (ms_core Mscan) q)).
  { apply mtrail_wf_enqueue; assumption. }
  assert (Hrcwords : rc = lits_denote (cons q (cons (lit_neg_c p) nil))).
  { unfold rc, lits_denote. cbn [map].
    rewrite (lit_denote_neg p) by (destruct Hp_wf; lia). reflexivity. }
  assert (Hwordswf : Forall (lit_wf_c n) (cons q (cons (lit_neg_c p) nil))).
  { constructor; [exact Hqwf|].
    constructor; [apply lit_neg_c_wf; exact Hp_wf|constructor]. }
  assert (Hassignone : assigns_one (msolver_view n Mscan)
    (view_of n (mt_enqueue (ms_core Mscan) q)
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
      (msolver_clauses Mscan))
    (lit_var_c q) (lit_pol q) (Zlength (mt_lim (ms_core Mscan)))
    (Some rc)).
  { rewrite Hrcwords.
    apply (propagation_unit_assigns_one_fresh__propagate_dbu
             n Mscan q (tag_of_lit p) (cons q (cons (lit_neg_c p) nil)));
      [exact Htwf|exact Hqwf|exact Hfreshcell|exact Hwordswf]. }
  pose proof (msat_enqueue_fresh_trail_implied n F A_arr K Mscan p q Hweak
    Htwf Hprocessed Hreasonent) as Htrailimpl'.
  pose proof Hassignone as Hassignone_packed.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in Hassignone.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  pose proof (msat_enqueue_fresh_focus_false n Mscan p q Hp_wf Hprocessed
    Hqpneq Hassignone_packed) as Hp_post_false.
  pose proof (msat_enqueue_fresh_reason_valid n Mscan p q Hqpneq Hplevel
    Hp_post_false Hassignone_packed) as Hreasonvalidq.
  pose proof (msat_enqueue_fresh_stable_view n Mscan p q Hstable
    Hreasonvalidq Hassignone_packed) as Hstable'.
  assert (Hviewpost : msolver_view n Mpost = Vpost).
  {
    rewrite HMpost. unfold Vpost, msolver_view, msolver_clauses, msolver_db.
    reflexivity.
  }
  assert (Hshape' : solver_shape Mpost).
  { rewrite HMfresh.
    apply solver_shape_enqueue_fresh__record.
    - exact Hshape.
    - lia.
    - exact (proj1 Hweak). }
  pose proof (msat_enqueue_fresh_reasons_entailed n F A_arr K Mscan p q
    Hweak Hreasonent Hassignone_packed) as Hreasonsent'.
  pose proof (msat_enqueue_fresh_reasons_injective n F A_arr K Mscan p q
    Hweak Hqpneq Hassignone_packed) as Hreasonsinj'.
  pose proof (msat_enqueue_fresh_assump_at_root n Mscan p q Htwf Hqrange
    Hassignone_packed) as Hassump_preserve.
  assert (Hwordslen : Zlength (ms_reason_words Mscan) = n).
  {
    unfold solver_shape in Hshape.
    rewrite Hsize. intuition.
  }
  pose proof (msat_enqueue_fresh_reasons_match n Mscan p q Htwf Hp_wf
    Hqrange Hwordslen Hreasonsmem Hassignone_packed) as Hreasonsmem'.
  pose proof (msat_enqueue_fresh_reason_head_ok n F A_arr K Mscan p q Hweak
    Hfreshcell Hqrange Hwordslen Hsize) as Hreasonhead'.
  pose proof (msat_scan_focus_level_is_root n Mscan p Htwf Hprocessed
    Hplevel) as Hprawlevel.
  pose proof (msat_no_old_tag_targets_fresh n Mscan p q Htwf Hsize Hstable
    Hreasonsmem Hreasonbin Hassignone_packed) as Hno_old_tag_target.
  pose proof (msat_enqueue_fresh_reason_bin n Mscan p q Htwf Hp_wf Hsize
    Hwordslen Hqrange Hqpneq Hfreshcell Hreasonbin Hprawlevel
    Hno_old_tag_target) as Hreasonbin'.
  assert (Hreasonless' : current_reasonless_earliest n Mpost).
  { rewrite HMfresh.
    eapply current_reasonless_enqueue_fresh__propagate_dbu.
    - exact Hshape.
    - exact Htwf.
    - exact Hqwf.
    - pose proof (proj1 (tag_of_lit_reason_wf n p Hp_wf)). lia.
    - exact Hreasonless.
    - exact Hassignone_packed. }
  pose proof (msat_enqueue_fresh_weak n F A_arr K Mscan p q Hweak Htwf
    Hqwf Hfreshcell Hshape' Htrailwf' Hstable' Hreasonsent' Hreasonsinj'
    Htrailimpl' Hreasonsmem' Hreasonhead' Hreasonbin' Hassump_preserve)
    as Hweak'.
  assert (Hproplevel' : prop_level (ms_core Mpost)).
  { rewrite HMpost. apply prop_level_enqueue. exact Hproplevel. }
  assert (Hcovers' : heap_covers n (msolver_heap Mpost)
    (mt_assigns (ms_core Mpost)) (mt_trail (ms_core Mpost))
    (mt_qhead (ms_core Mpost))).
  { rewrite HMfresh.
    eapply heap_covers_enqueue_fresh__record;
      [exact Htwf|exact Hqwf|exact Hcovers]. }
  assert (Hheapready' : propagation_heap_ready n Mpost).
  { left. exact Hcovers'. }
  destruct (processed_enqueue_fresh_equiv__propagate_dbu
    n (ms_core Mscan) q Htwf Hqwf Hfreshcell) as [_ Hfwd].
  assert (Hprocessed_forward : forall w,
    lit_wf_c n w ->
    processed (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) w ->
    processed (mt_assigns (ms_core Mpost))
      (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)) w).
  { rewrite HMfresh. exact Hfwd. }
  assert (Hprocessed' : processed (mt_assigns (ms_core Mpost))
    (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)) p).
  { apply Hprocessed_forward; [exact Hp_wf|exact Hprocessed]. }
  assert (Hplevel' : level_of (msolver_view n Mpost) (lit_var_c p) =
    Some (Zlength (mt_lim (ms_core Mpost)))).
  {
    rewrite Hviewpost.
    destruct (Hothers (lit_var_c p)
      (fun E => Hqpneq (eq_sym E))) as [_ [Hlevelp _]].
    rewrite Hlevelp, Hplevel, HMpost. reflexivity.
  }
  assert (Hfrontier' : minisat_watch_frontier_except n (msolver_db Mpost)
    (mt_assigns (ms_core Mpost)) (mt_trail (ms_core Mpost))
    (mt_qhead (ms_core Mpost)) (lit_denote p)).
  { rewrite HMfresh.
    eapply minisat_watch_frontier_except_enqueue_fresh__propagate_dbu;
      [exact Htwf|exact Hqwf|exact Hfreshcell|exact Hfrontier]. }
  assert (Hcarrier' : minisat_focus_scan_carrier
    (msolver_db Mpost) p
    (minisat_processed n (mt_assigns (ms_core Mpost))
      (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)))
    (retained ++ scan_current :: nil) raw_suffix).
  { rewrite HMfresh.
    eapply minisat_focus_scan_carrier_enqueue_fresh__propagate_dbu;
      [exact Htwf|exact Hqwf|exact Hfreshcell|exact Hcarrier_scan]. }
  unfold solver_propagation_scan_semantics. left.
  split; [reflexivity|].
  split; [exact Hweak'|].
  split; [exact Hproplevel'|].
  split; [exact Hheapready'|].
  split; [exact Hcovers'|].
  split; [exact Hreasonless'|].
  split; [exact Hplevel'|].
  split; [exact Hp_wf|].
  split; [exact Hprocessed'|].
  split; [exact Hfrontier'|exact Hcarrier'].
Qed.

Lemma msat_enqueue_same_identity :
  forall (Mscan : msolver) (p scan_current : Z),
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 =
      lit_sig (tag_lit scan_current) ->
    msolver_propagation_enqueue_success Mscan
      (tag_lit scan_current) (tag_of_lit p)
      (cons (lit_denote (tag_lit scan_current))
        (cons (literal_neg (lit_denote p)) nil)) = Mscan.
Proof.
  intros Mscan p scan_current Hqtrue.
  unfold msolver_propagation_enqueue_success.
  destruct ((Znth (lit_var_c (tag_lit scan_current))
    (mt_assigns (ms_core Mscan)) 0 =? 0)%Z) eqn:Heq.
  - apply Z.eqb_eq in Heq. rewrite Hqtrue in Heq.
    exfalso. apply (lit_sig_nonzero (tag_lit scan_current)). exact Heq.
  - reflexivity.
Qed.

Lemma msat_scan_target_unprocessed :
  forall (n : Z) (Mscan : msolver) (p scan_current qtail' : Z)
         (assigns' levels' reasons' trail' : list Z),
    enqueue_transition (tag_lit scan_current) (tag_of_lit p)
      (ms_qtail Mscan) 1 qtail' (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan)) (mt_lim (ms_core Mscan))
      assigns' levels' reasons' trail' ->
    lit_wf_c n (tag_lit scan_current) ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    ~ minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan))
        (literal_neg (lit_denote (tag_lit scan_current))).
Proof.
  intros n Mscan p scan_current qtail' assigns' levels' reasons' trail'
    H Hqwf Hprocessed.
  unfold enqueue_transition in H.
  destruct H as [Hsame | [Hconflict | Hfresh]].
  - destruct Hsame as (Hqtrue & _).
    rewrite <- (lit_denote_neg (tag_lit scan_current)) by
      (destruct Hqwf; lia).
    rewrite minisat_processed_denote by (apply lit_neg_c_wf; exact Hqwf).
    intros [Hnegtrue _].
    eapply lit_true_false_contra; [exact Hqtrue|].
    unfold lit_true in Hnegtrue.
    rewrite lit_var_c_neg, lit_sig_neg in Hnegtrue.
    unfold lit_false. exact Hnegtrue.
  - exfalso. decompose [and] Hconflict; lia.
  - destruct Hfresh as (Hfreshcell & _).
    intros [w [Hwwf [Hden Hproc]]].
    pose proof (processed_fresh_target_different
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) w (tag_lit scan_current)
      Hproc Hfreshcell) as Hneq.
    apply Hneq.
    pose proof (f_equal literal_var Hden) as Hvar.
    rewrite literal_var_neg, !lit_var_c_denote in Hvar.
    symmetry. exact Hvar.
Qed.

Lemma msat_scan_current_focus_facts :
  forall (n : Z) (Mscan : msolver) (p scan_current qtail' : Z)
         (assigns' levels' reasons' trail' retained rest raw_suffix : list Z),
    db_wf n (msolver_db Mscan) ->
    wmap_exact n (msolver_db Mscan) (ms_wm Mscan) ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    tagged_word scan_current ->
    rest = scan_current :: raw_suffix ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      retained rest ->
    enqueue_transition (tag_lit scan_current) (tag_of_lit p)
      (ms_qtail Mscan) 1 qtail' (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan)) (mt_lim (ms_core Mscan))
      assigns' levels' reasons' trail' ->
    lit_wf_c n (tag_lit scan_current) /\
    In scan_current (Znth p (ms_wm Mscan) nil) /\
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix.
Proof.
  intros n Mscan p scan_current qtail' assigns' levels' reasons' trail'
    retained rest raw_suffix
    Hdbwf Hwmexact Hp_wf Hprocessed H_tagged_word H_rest Hcarrier Henqueue.
  unfold tagged_word in H_tagged_word.
  unfold minisat_focus_scan_carrier in Hcarrier.
  destruct Hcarrier as
    [scanned [pending [Hperm [Hscanned_words [Hpending_words Hsafe]]]]].
  rewrite H_rest in Hpending_words.
  destruct pending as [|[focus_owner focus_word] pending'];
    [discriminate|].
  cbn in Hpending_words.
  injection Hpending_words as Hword Hpending_words.
  subst focus_word.
  assert (Htoken : In (focus_owner, scan_current)
    (minisat_focus_contributions (msolver_db Mscan) p)).
  {
    eapply Permutation_in; [exact Hperm|].
    apply in_or_app. right. left. reflexivity.
  }
  unfold minisat_focus_contributions in Htoken.
  apply in_flat_map in Htoken as [[clause_ptr co] [Hco Hentry]].
  unfold minisat_entry_focus_contributions in Hentry.
  apply in_map_iff in Hentry as [entry_word [Hentry Hentry_word]].
  inversion Hentry. subst focus_owner entry_word.
  assert (Hptr_not_tag : is_tag clause_ptr = false).
  {
    apply even_not_tag. eapply db_wf_even; eassumption.
  }
  assert (Hqwatch : tag_lit scan_current = co_watch0 co \/
                     tag_lit scan_current = co_watch1 co).
  {
    unfold entry_watchers in Hentry_word.
    apply in_app_or in Hentry_word as [Hfirst | Hsecond].
    - destruct ((lit_neg_c (co_watch0 co) =? p)%Z) eqn:Heq;
        [|cbn in Hfirst; contradiction].
      destruct ((3 <=? Zlength (co_lits co))%Z) eqn:Hbig;
        cbn in Hfirst; destruct Hfirst as [Hfirst | []].
      + subst scan_current. rewrite Hptr_not_tag in H_tagged_word. discriminate.
      + subst scan_current. rewrite tag_lit_of. right. reflexivity.
    - destruct ((lit_neg_c (co_watch1 co) =? p)%Z) eqn:Heq;
        [|cbn in Hsecond; contradiction].
      destruct ((3 <=? Zlength (co_lits co))%Z) eqn:Hbig;
        cbn in Hsecond; destruct Hsecond as [Hsecond | []].
      + subst scan_current. rewrite Hptr_not_tag in H_tagged_word. discriminate.
      + subst scan_current. rewrite tag_lit_of. left. reflexivity.
  }
  assert (Hqwf : lit_wf_c n (tag_lit scan_current)).
  {
    assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
    destruct Hqwatch as [Hqwatch | Hqwatch]; rewrite Hqwatch.
    - eapply obj_wf_watch0; eassumption.
    - eapply obj_wf_watch1; eassumption.
  }
  pose proof (msat_scan_target_unprocessed n Mscan p scan_current qtail'
    assigns' levels' reasons' trail' Henqueue Hqwf Hprocessed) as Hnotneg.
  assert (Hwmword : In scan_current (Znth p (ms_wm Mscan) nil)).
  {
    assert (Hexpect : In scan_current (expected_watchers (msolver_db Mscan) p)).
    {
      unfold expected_watchers. apply in_flat_map.
      exists (clause_ptr, co). split; assumption.
    }
    pose proof Hwmexact as [_ Hwm].
    eapply Permutation_in; [apply Permutation_sym; apply Hwm|exact Hexpect].
    exact Hp_wf.
  }
  assert (Hcurrsafe : minisat_occurrence_safe
    (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
    (minisat_occurrence_of_entry (clause_ptr, co))).
  {
    unfold minisat_occurrence_safe, minisat_occurrence_of_entry.
    cbn [watch_left watch_right].
    destruct Hqwatch as [Hqw | Hqw]; rewrite <- Hqw; intros Hboth;
      apply Hnotneg; tauto.
  }
  assert (Hcarrier_scan : minisat_focus_scan_carrier
    (msolver_db Mscan) p
    (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
    (retained ++ scan_current :: nil) raw_suffix).
  {
    unfold minisat_focus_scan_carrier.
    exists (scanned ++ (minisat_occurrence_of_entry (clause_ptr, co),
      scan_current) :: nil), pending'.
    split.
    + rewrite <- app_assoc. exact Hperm.
    + split.
      * rewrite <- Hscanned_words.
        unfold minisat_focus_words.
        rewrite map_app. reflexivity.
      * split; [exact Hpending_words|].
        apply Forall_app. split; [exact Hsafe|].
        constructor; [exact Hcurrsafe|constructor].
  }
  split; [exact Hqwf|].
  split; [exact Hwmword|exact Hcarrier_scan].
Qed.

Lemma msat_scan_keep_step_exists :
  forall (source_words retained moved rest garbage watch_memory
          raw_suffix : list Z) (ii jj scan_current : Z),
    propagation_watch_scan_physical source_words retained moved rest garbage
      watch_memory ii jj ->
    rest = scan_current :: raw_suffix ->
    exists garbage_route memory_route,
      propagation_scan_keep_step source_words retained moved rest
        watch_memory ii jj scan_current (retained ++ scan_current :: nil)
        raw_suffix garbage_route memory_route.
Proof.
  intros source_words retained moved rest garbage watch_memory raw_suffix
    ii jj scan_current H_propagation_watch_scan_physical H_rest.
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as
    (Hscan & Hmemory & Hretlen & Hprefixlen & Hmemorylen).
  subst rest.
  destruct garbage as [|g gs].
  - exists nil, watch_memory.
    unfold propagation_scan_keep_step.
    split; [reflexivity|].
    split; [reflexivity|].
    split.
    + assert (Hnth : Znth jj watch_memory 0 = scan_current).
      {
        rewrite Hmemory.
        rewrite app_Znth2 by (rewrite Hretlen; lia).
        replace (jj - Zlength retained) with 0 by lia.
        reflexivity.
      }
      rewrite <- Hnth.
      symmetry. apply replace_Znth_Znth.
    + unfold propagation_watch_scan_physical.
      split. { apply wlist_scan_keep. exact Hscan. }
      split.
      { rewrite Hmemory.
        change (retained ++ (scan_current :: raw_suffix) =
          (retained ++ (scan_current :: nil)) ++ raw_suffix).
        rewrite <- app_assoc. reflexivity. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil, Hretlen. lia. }
      split.
      { rewrite app_nil_r in Hprefixlen.
        rewrite !Zlength_app. cbn. rewrite Hretlen. lia. }
      exact Hmemorylen.
  - exists (gs ++ scan_current :: nil),
      (replace_Znth jj scan_current watch_memory).
    unfold propagation_scan_keep_step.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    unfold propagation_watch_scan_physical.
    split. { apply wlist_scan_keep. exact Hscan. }
    split.
    { rewrite Hmemory.
      rewrite replace_Znth_app_r by (rewrite Hretlen; lia).
      rewrite replace_Znth_nothing by lia.
      replace (jj - Zlength retained) with 0 by lia.
      cbn.
      rewrite <- !app_assoc. reflexivity. }
    split.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil, Hretlen. lia. }
    split.
    { rewrite !Zlength_app in Hprefixlen |- *.
      rewrite !Zlength_app_cons.
      rewrite Zlength_cons in Hprefixlen.
      lia.
    }
    rewrite Zlength_replace_Znth. exact Hmemorylen.
Qed.

Lemma msat_scan_step_semantics_keep :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z) (retained rest raw_suffix : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix ->
    solver_propagation_scan_semantics n F A_arr K Mscan p 0
      (retained ++ scan_current :: nil) raw_suffix.
Proof.
  intros n F A_arr K Mscan p scan_current retained rest raw_suffix
    Hsem Hcarrier_scan.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hconflict]; [|decompose [and] Hconflict; lia].
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hcovers &
     Hreasonless & Hplevel & Hp_wf & Hprocessed & Hfrontier & Hcarrier).
  unfold solver_propagation_scan_semantics. left.
  split; [reflexivity|].
  split; [exact Hweak|].
  split; [exact Hproplevel|].
  split; [exact Hheapready|].
  split; [exact Hcovers|].
  split; [exact Hreasonless|].
  split; [exact Hplevel|].
  split; [exact Hp_wf|].
  split; [exact Hprocessed|].
  split; [exact Hfrontier|exact Hcarrier_scan].
Qed.

Lemma msat_sublist_two_tail : forall (a0 a1 : Z) (tl : list Z),
  sublist 2 (Zlength (a0 :: a1 :: tl)) (a0 :: a1 :: tl) = tl.
Proof.
  intros a0 a1 tl.
  replace (a0 :: a1 :: tl) with ((a0 :: a1 :: nil) ++ tl) by reflexivity.
  assert (Hrange : 2 <= 2 <= Zlength ((a0 :: a1 :: nil) ++ tl)).
  { split; [lia|]. rewrite Zlength_app.
    change (2 <= 2 + Zlength tl). pose proof (Zlength_nonneg tl). lia. }
  rewrite (sublist_split_app_r 2 (Zlength ((a0 :: a1 :: nil) ++ tl)) 2
    (a0 :: a1 :: nil) tl ltac:(reflexivity) Hrange).
  replace (Zlength ((a0 :: a1 :: nil) ++ tl) - 2) with (Zlength tl) by
    (rewrite Zlength_app, !Zlength_cons, Zlength_nil; lia).
  apply sublist_self. reflexivity.
Qed.

Lemma msat_propagate_clause_watch_facts :
  forall n Mscan p scan_current co a0 a1 tl new_lits co_new
         false_lit watch0_2 sig,
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tl ->
    3 <= Zlength (a0 :: a1 :: tl) ->
    real_watch_pair p (a0 :: a1 :: tl) ->
    watch0_2 + false_lit =
      Znth 0 (a0 :: a1 :: tl) 0 + Znth 1 (a0 :: a1 :: tl) 0 ->
    false_lit = lit_neg_c p ->
    sig = 1 - 2 * lit_sign_c watch0_2 ->
    Znth (lit_var_c watch0_2) (mt_assigns (ms_core Mscan)) 0 = sig ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    new_lits = propagation_normalized_clause watch0_2 false_lit
      (a0 :: a1 :: tl) ->
    co_new = clause_obj_with_lits co new_lits ->
    Permutation new_lits (a0 :: a1 :: tl) /\
    minisat_entry_focus_contributions p (scan_current, co) =
      (minisat_occurrence_of_entry (scan_current, co), scan_current) :: nil /\
    minisat_entry_focus_contributions p (scan_current, co_new) =
      (minisat_occurrence_of_entry (scan_current, co_new), scan_current) :: nil /\
    minisat_occurrence_safe
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (minisat_occurrence_of_entry (scan_current, co_new)) /\
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current, co_new) l)) /\
    ((co_watch0 co_new = co_watch1 co /\ co_watch1 co_new = co_watch0 co) \/
     (co_watch0 co_new = co_watch0 co /\ co_watch1 co_new = co_watch1 co)) /\
    (lit_false (mt_assigns (ms_core Mscan)) (co_watch0 co) \/
     new_lits = a0 :: a1 :: tl).
Proof.
  intros n Mscan p scan_current co a0 a1 tl new_lits co_new
    false_lit watch0_2 sig Hdbwf Hin Hlits Hbig Hrwp Hw02 Hfl Hsig Hznth
    Hp Hprocessed Hnewlits Hconew.
  pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin) as Hobj.
  unfold obj_wf in Hobj. rewrite Hlits in Hobj.
  destruct Hobj as [Hlen [Hall Hnodup]].
  assert (Htl : sublist 2 (Zlength (a0 :: a1 :: tl)) (a0 :: a1 :: tl) = tl)
    by (apply msat_sublist_two_tail).
  unfold propagation_normalized_clause in Hnewlits.
  rewrite Htl in Hnewlits.
  assert (Hnewco : co_lits co_new = watch0_2 :: false_lit :: tl)
    by (rewrite Hconew; unfold clause_obj_with_lits; cbn [co_lits];
        exact Hnewlits).
  assert (Hwatchcases :
      (a0 = false_lit /\ watch0_2 = a1) \/ (a1 = false_lit /\ watch0_2 = a0)).
  { unfold real_watch_pair in Hrwp.
    rewrite !Znth0_cons in Hrwp, Hw02.
    rewrite !Znth_cons in Hrwp, Hw02 by lia.
    replace (1 - 1) with 0 in Hrwp, Hw02 by lia.
    rewrite !Znth0_cons in Hrwp, Hw02.
    destruct Hrwp as [Hw | Hw].
    - left. rewrite <- Hfl in Hw. split; [exact Hw|lia].
    - right. rewrite <- Hfl in Hw. split; [exact Hw|lia]. }
  inversion Hall as [|x xs Hwf0 Hall1]; subst x xs.
  inversion Hall1 as [|x xs Hwf1 Halltl]; subst x xs.
  inversion Hnodup as [|x xs Hnot0 Hnd1]; subst x xs.
  inversion Hnd1 as [|x xs Hnot1 Hndtl]; subst x xs.
  assert (Hvardiff : lit_var_c a0 <> lit_var_c a1).
  { intro Heq. apply Hnot0. simpl. left. symmetry. exact Heq. }
  assert (Hnegfalse : lit_neg_c false_lit = p).
  { rewrite Hfl. apply lit_neg_c_involutive. }
  assert (Hotherneg : lit_neg_c watch0_2 <> p).
  { intro Heq.
    assert (Hv := f_equal lit_var_c Heq).
    rewrite lit_var_c_neg in Hv.
    assert (Hvfalse : lit_var_c false_lit = lit_var_c p).
    { rewrite Hfl, lit_var_c_neg. reflexivity. }
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]]; subst; apply Hvardiff; lia. }
  assert (Hotherb : (lit_neg_c watch0_2 =? p)%Z = false)
    by (apply Z.eqb_neq; exact Hotherneg).
  assert (Hfalseb : (lit_neg_c false_lit =? p)%Z = true)
    by (apply Z.eqb_eq; exact Hnegfalse).
  assert (Hwatchtrue : lit_true (mt_assigns (ms_core Mscan)) watch0_2).
  { unfold lit_true. rewrite Hznth, Hsig.
    unfold lit_sig, lit_sign_c. destruct (Z.odd watch0_2); reflexivity. }
  assert (Hfalsefalse : lit_false (mt_assigns (ms_core Mscan)) false_lit).
  { destruct Hprocessed as [Hptrue _].
    unfold lit_true in Hptrue. unfold lit_false.
    rewrite Hfl, lit_var_c_neg, lit_sig_neg. lia. }
  assert (Hentryold : minisat_entry_focus_contributions p (scan_current, co) =
      (minisat_occurrence_of_entry (scan_current, co), scan_current) :: nil).
  { unfold minisat_entry_focus_contributions, entry_watchers.
    cbn [fst snd]. unfold co_watch0, co_watch1. rewrite Hlits.
    assert (Hb : (3 <=? Zlength (a0 :: a1 :: tl))%Z = true)
      by (apply Z.leb_le; exact Hbig).
    rewrite Hb.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - rewrite Ha0, Hfalseb. rewrite <- Hw, Hotherb. reflexivity.
    - rewrite <- Hw, Hotherb. rewrite Ha1, Hfalseb. reflexivity. }
  assert (Hentrynew :
      minisat_entry_focus_contributions p (scan_current, co_new) =
      (minisat_occurrence_of_entry (scan_current, co_new), scan_current) :: nil).
  { unfold minisat_entry_focus_contributions, entry_watchers.
    cbn [fst snd]. unfold co_watch0, co_watch1. rewrite Hnewco.
    assert (Hb : (3 <=? Zlength (watch0_2 :: false_lit :: tl))%Z = true).
    { apply Z.leb_le. rewrite !Zlength_cons in Hbig |- *. exact Hbig. }
    rewrite Hb.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    rewrite Hotherb, Hfalseb. reflexivity. }
  assert (Honewsafe : minisat_occurrence_safe
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (minisat_occurrence_of_entry (scan_current, co_new))).
  { assert (Hleft : watch_left (minisat_occurrence_of_entry (scan_current, co_new))
        = lit_denote watch0_2).
    { unfold minisat_occurrence_of_entry, watch_left, co_watch0.
      cbn. rewrite Hnewco. reflexivity. }
    unfold minisat_occurrence_safe. intro Hboth. destruct Hboth as [Hbad _].
    rewrite Hleft in Hbad.
    assert (Hwfwatch : lit_wf_c n watch0_2).
    { destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]]; subst; assumption. }
    assert (Hwfneg : lit_wf_c n (lit_neg_c watch0_2))
      by (apply lit_neg_c_wf; exact Hwfwatch).
    rewrite <- (lit_denote_neg watch0_2) in Hbad by (destruct Hwfwatch; lia).
    apply (proj1 (minisat_processed_denote n
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) (lit_neg_c watch0_2) Hwfneg)) in Hbad.
    destruct Hbad as [Hnegtrue _].
    unfold lit_true in Hwatchtrue, Hnegtrue.
    rewrite lit_var_c_neg, lit_sig_neg in Hnegtrue.
    destruct (lit_sig_values watch0_2); lia. }
  assert (Hentryperm : forall l,
      Permutation (entry_watchers (scan_current, co) l)
        (entry_watchers (scan_current, co_new) l)).
  { intros l. unfold entry_watchers, co_watch0, co_watch1.
    cbn [fst snd]. rewrite Hlits, Hnewco.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    rewrite !Zlength_cons.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - subst a0 watch0_2. apply Permutation_app_comm.
    - subst a1 watch0_2. reflexivity. }
  repeat split.
  - rewrite Hnewlits.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    + subst a0 watch0_2. apply perm_swap.
    + subst a1 watch0_2. reflexivity.
  - exact Hentryold.
  - exact Hentrynew.
  - exact Honewsafe.
  - exact Hentryperm.
  - unfold co_watch0, co_watch1. rewrite Hlits, Hnewco.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    + left. subst a0 watch0_2. split; reflexivity.
    + right. subst a1 watch0_2. split; reflexivity.
  - destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    + left. unfold co_watch0. rewrite Hlits. rewrite Znth0_cons.
      subst a0. exact Hfalsefalse.
    + right. rewrite Hnewlits. subst a1 watch0_2. reflexivity.
Qed.

Tactic Notation "msat_propagate_db_entry_spatial" ident(pr) ident(po)
    ident(sc) ident(cn) ident(nl) ident(htail) ident(hlearnt)
    ident(hptr) ident(lts) ident(tl) :=
  lazymatch goal with
  | |- _ |-- ?Q =>
      lazymatch Q with
      | context C [clause_db_rep (pr ++ (sc, cn) :: po)] =>
          let Q' := context C [clause_db_rep pr ** clause_db_rep ((sc, cn) :: po)] in
          let hc := fresh "Hcut" in
          assert (hc : Q' |-- Q)
            by (sep_apply (clause_db_rep_app_intro pr ((sc, cn) :: po)); cancel);
          sep_apply_r_atomic hc;
          clear hc
      end
  end;
  rewrite clause_db_rep_cons;
  unfold MiniSatClause.rep, cn, clause_obj_with_lits, nl,
    propagation_normalized_clause; cbn [fst snd co_lits co_learnt];
  rewrite htail, hlearnt;
  unfold clause_lits_pointer in hptr; subst lts;
  split_pure_spatial;
  [ sep_apply store_ptr_undef_store_ptr;
    sep_apply store_char_undef_store_char;
    repeat rewrite Zlength_cons; cbn;
    cancel;
    lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel
  | repeat rewrite Zlength_cons; cbn;
    dump_pre_spatial; split; [ | split ];
    [ pose proof (Zlength_nonneg tl); lia
    | match goal with
      | Hw : db_wf ?nn ?dbb, Hi : In (?q, ?cobj) ?dbb |- _ =>
          pose proof (db_wf_ptr_pos nn dbb q cobj Hw Hi); lia
      end
    | apply clause_ptr_mod2;
      match goal with
      | Hw : db_wf ?nn ?dbb, Hi : In (?q, ?cobj) ?dbb |- _ =>
          exact (db_wf_even nn dbb q cobj Hw Hi)
      end ] ].

Lemma msat_db_pair_update_identity :
  forall prob learnt q old_lits new_lits prob' learnt',
    db_pair_lits_update prob learnt q old_lits new_lits prob' learnt' ->
    new_lits = old_lits ->
    prob' = prob /\ learnt' = learnt.
Proof.
  intros prob learnt q old_lits new_lits prob' learnt' Hupdate Heq.
  subst new_lits.
  destruct Hupdate as
    [[co [pre [post [Hp [Hold [Hp' Hl']]]]]]
    |[co [pre [post [Hl [Hold [Hp' Hl']]]]]]].
  - assert (Hco : clause_obj_with_lits co old_lits = co).
    { unfold clause_obj_with_lits. rewrite <- Hold. destruct co. reflexivity. }
    rewrite Hco in Hp'. rewrite Hp', Hp. split; [reflexivity|exact Hl'].
  - assert (Hco : clause_obj_with_lits co old_lits = co).
    { unfold clause_obj_with_lits. rewrite <- Hold. destruct co. reflexivity. }
    rewrite Hco in Hl'. rewrite Hl', Hl. split; [exact Hp'|reflexivity].
Qed.

(* The database-level half of the clause-normalisation obligation, shared by
   the problem-database and the learnt-database branch: the two branches
   differ only in the segment [dpre]/[dpost] that surrounds the rewritten
   entry, so stating the split as an equation on the concatenated database
   makes the whole argument branch-independent. *)
Lemma msat_propagate_route_facts :
  forall n F A_arr K Mscan Mroute p scan_current co co_new
         a0 a1 tl new_lits prob_route learnt_route dpre dpost
         retained raw_suffix,
    msolver_db Mscan = dpre ++ (scan_current, co) :: dpost ->
    prob_route ++ learnt_route = dpre ++ (scan_current, co_new) :: dpost ->
    db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current
      (a0 :: a1 :: tl) new_lits prob_route learnt_route ->
    Mroute = msolver_propagation_db_wmap_update Mscan prob_route learnt_route
      (ms_wm Mscan) ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    Permutation new_lits (a0 :: a1 :: tl) ->
    minisat_entry_focus_contributions p (scan_current, co) =
      (minisat_occurrence_of_entry (scan_current, co), scan_current) :: nil ->
    minisat_entry_focus_contributions p (scan_current, co_new) =
      (minisat_occurrence_of_entry (scan_current, co_new), scan_current) :: nil ->
    minisat_occurrence_safe
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (minisat_occurrence_of_entry (scan_current, co_new)) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current, co_new) l)) ->
    ((co_watch0 co_new = co_watch1 co /\ co_watch1 co_new = co_watch0 co) \/
     (co_watch0 co_new = co_watch0 co /\ co_watch1 co_new = co_watch1 co)) ->
    (lit_false (mt_assigns (ms_core Mscan)) (co_watch0 co) \/
     new_lits = a0 :: a1 :: tl) ->
    solver_propagation_weak n F A_arr K Mscan ->
    prop_level (ms_core Mscan) ->
    propagation_heap_ready n Mscan ->
    heap_covers n (msolver_heap Mscan) (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) ->
    current_reasonless_earliest n Mscan ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    minisat_watch_frontier_except n (msolver_db Mscan)
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) (lit_denote p) ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      retained (scan_current :: raw_suffix) ->
    propagation_real_satisfied_transition n F A_arr K Mscan p
      prob_route learnt_route (retained ++ scan_current :: nil)
      raw_suffix Mroute.
Proof.
  intros n F A_arr K Mscan Mroute p scan_current co co_new
    a0 a1 tl new_lits prob_route learnt_route dpre dpost retained raw_suffix
    Hdb Hdb2 Hupdate HM Hdbwf Hin Hperm Hentryold Hentrynew Honewsafe
    Hentryperm Hswap Hhead Hweak Hprop Hheapready Hheapcovers Hreasonless
    Hlevel Hp Hprocessed Hfrontier Hscan.
  set (fpre := minisat_focus_contributions dpre p).
  set (fpost := minisat_focus_contributions dpost p).
  assert (Hcurrentreal : is_tag scan_current = false)
    by (apply even_not_tag; eapply db_wf_even; eassumption).
  assert (Hfocusold : minisat_focus_contributions (msolver_db Mscan) p =
      fpre ++ (minisat_occurrence_of_entry (scan_current, co), scan_current)
        :: fpost).
  { rewrite Hdb.
    rewrite minisat_focus_contributions_app__propagate_dbu.
    rewrite minisat_focus_contributions_cons__propagate_dbu.
    rewrite Hentryold. unfold fpre, fpost. cbn. reflexivity. }
  assert (Hfocusnew : minisat_focus_contributions
      (prob_route ++ learnt_route) p =
      fpre ++ (minisat_occurrence_of_entry (scan_current, co_new), scan_current)
        :: fpost).
  { rewrite Hdb2.
    rewrite minisat_focus_contributions_app__propagate_dbu.
    rewrite minisat_focus_contributions_cons__propagate_dbu.
    rewrite Hentrynew. unfold fpre, fpost. cbn. reflexivity. }
  assert (Hfocusroute : minisat_focus_scan_carrier
      (prob_route ++ learnt_route) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix).
  { eapply focus_scan_carrier_db_pair_token_replace__propagate_dbu
      with (olddb := msolver_db Mscan) (co := co) (pre := fpre) (post := fpost)
        (onew := minisat_occurrence_of_entry (scan_current, co_new)).
    - exact Hdbwf.
    - exact Hin.
    - exact Hcurrentreal.
    - exact Hfocusold.
    - exact Hfocusnew.
    - exact Honewsafe.
    - exact Hscan. }
  pose proof (msat_db_entry_swap_expected_watchers (msolver_db Mscan)
    (prob_route ++ learnt_route) dpre dpost scan_current co co_new
    Hdb Hdb2 Hentryperm) as Hexpected.
  assert (Hfrontierroute : minisat_watch_frontier_except n
      (prob_route ++ learnt_route) (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) (lit_denote p)).
  { unfold minisat_watch_frontier_except,
      minisat_watch_occurrences in Hfrontier |- *.
    unfold watch_frontier_except in Hfrontier |- *.
    rewrite Forall_forall in Hfrontier |- *.
    intros o Ho. apply in_map_iff in Ho as [[q obj] [<- Hentry]].
    rewrite Hdb2 in Hentry.
    destruct (in_app_or _ _ _ Hentry) as [Hepre | Hecons].
    - apply Hfrontier. apply in_map. rewrite Hdb.
      apply in_or_app. left. exact Hepre.
    - destruct Hecons as [Heq | Hepost].
      + inversion Heq; subst q obj.
        specialize (Hfrontier (minisat_occurrence_of_entry (scan_current, co))).
        assert (Holdin : In (minisat_occurrence_of_entry (scan_current, co))
            (map minisat_occurrence_of_entry (msolver_db Mscan)))
          by (apply in_map; exact Hin).
        specialize (Hfrontier Holdin).
        unfold minisat_occurrence_of_entry in Hfrontier |- *.
        cbn [watch_left watch_right] in Hfrontier |- *.
        destruct Hswap as [[Hl Hr] | [Hl Hr]]; rewrite Hl, Hr; tauto.
      + apply Hfrontier. apply in_map. rewrite Hdb.
        apply in_or_app. right. simpl. right. exact Hepost. }
  assert (Hweakroute : solver_propagation_weak n F A_arr K
      (msolver_propagation_db_wmap_update Mscan prob_route learnt_route
        (ms_wm Mscan))).
  { destruct Hhead as [Hheadfalse | Hsame].
    - unfold solver_propagation_weak in Hweak |- *.
      destruct Hweak as [Hroot Hctx]. split.
      + unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hroot.
      + eapply (ctx_db_pair_lits_no_owner__propagate_dbu n F A_arr K Mscan).
        * exact Hctx.
        * exact Hupdate.
        * exact Hperm.
        * exact Hexpected.
        * eapply (ctx_no_live_reason_owner_head_false__propagate_dbu
            n F A_arr K Mscan); eassumption.
    - destruct (msat_db_pair_update_identity (ms_prob Mscan) (ms_learnt Mscan)
        scan_current (a0 :: a1 :: tl) new_lits prob_route learnt_route
        Hupdate Hsame) as [Hprobid Hlearntid].
      assert (HMid : msolver_propagation_db_wmap_update Mscan prob_route
          learnt_route (ms_wm Mscan) = Mscan).
      { rewrite Hprobid, Hlearntid.
        unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update. destruct Mscan. reflexivity. }
      rewrite HMid. exact Hweak. }
  unfold propagation_real_satisfied_transition. split; [exact HM|].
  rewrite HM. left. split; [reflexivity|]. split; [exact Hweakroute|].
  split; [exact Hprop|]. split; [exact Hheapready|].
  split; [exact Hheapcovers|]. split; [exact Hreasonless|].
  split; [exact Hlevel|]. split; [exact Hp|]. split; [exact Hprocessed|].
  split; [exact Hfrontierroute | exact Hfocusroute].
Qed.

Lemma msat_propagate_scan_keep_step :
  forall source_words retained moved rest garbage watch_memory ii jj
         scan_current raw_suffix,
    propagation_watch_scan_physical source_words retained moved rest garbage
      watch_memory ii jj ->
    rest = scan_current :: raw_suffix ->
    exists garbage_route,
      propagation_scan_keep_step source_words retained moved rest
        watch_memory ii jj scan_current (retained ++ scan_current :: nil)
        raw_suffix garbage_route (replace_Znth jj scan_current watch_memory).
Proof.
  intros source_words retained moved rest garbage watch_memory ii jj
    scan_current raw_suffix Hphysical Hrest.
  unfold propagation_watch_scan_physical in Hphysical.
  destruct Hphysical as [Hinv [Hmem [Hjj [Hii Hlenmem]]]].
  rewrite Hrest in Hinv, Hmem.
  destruct garbage as [|g gs].
  - exists nil. unfold propagation_scan_keep_step.
    split; [exact Hrest|]. split; [reflexivity|]. split; [reflexivity|].
    unfold propagation_watch_scan_physical. repeat split.
    + apply wlist_scan_keep. exact Hinv.
    + rewrite Hmem, <- Hjj. rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by lia.
      replace (Zlength retained - Zlength retained) with 0 by lia.
      cbn. rewrite <- app_assoc. reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Hjj. lia.
    + cbn in Hii. rewrite app_nil_r in Hii.
      rewrite app_nil_r, Zlength_app. cbn. lia.
    + rewrite Zlength_replace_Znth. exact Hlenmem.
  - exists (gs ++ scan_current :: nil). unfold propagation_scan_keep_step.
    split; [exact Hrest|]. split; [reflexivity|]. split; [reflexivity|].
    unfold propagation_watch_scan_physical. repeat split.
    + apply wlist_scan_keep. exact Hinv.
    + rewrite Hmem, <- Hjj. rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by lia.
      replace (Zlength retained - Zlength retained) with 0 by lia.
      cbn. rewrite <- !app_assoc. reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Hjj. lia.
    + rewrite !Zlength_app in Hii |- *.
      assert (Hrl : Zlength (retained ++ scan_current :: nil) =
          Zlength retained + 1).
      { rewrite Zlength_app. cbn. lia. }
      assert (Hgsl : Zlength (gs ++ scan_current :: nil) = Zlength gs + 1).
      { rewrite Zlength_app. cbn. lia. }
      rewrite Hrl, Hgsl. rewrite Zlength_cons in Hii. lia.
    + rewrite Zlength_replace_Znth. exact Hlenmem.
Qed.

Lemma msat_propagate_real_migrated_exit :
  forall n F A_arr K M0 Mentry Mscan prob_after learnt_after p scan_wm logical_words
    candidate scan_current clause_contents watch0 false_lit lits stop k
    offset retained rest raw_suffix source_words moved garbage watch_memory candidate_post_memory
    migration_post_memory ii jj simp_count prop_count,
    solver_shape Mscan ->
    msolver_seed_shadow Mscan ->
    propagation_caller_frame M0 Mscan ->
    propagation_scan_frontier Mentry Mscan p ->
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    rest = scan_current :: raw_suffix ->
    propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ->
    candidate_post_memory = watch_memory ->
    Znth ii candidate_post_memory 0 = scan_current ->
    migration_post_memory =
      replace_Znth ii (Znth ii candidate_post_memory 0) candidate_post_memory ->
    false_lit = lit_neg_c p ->
    real_watch_pair p clause_contents ->
    watch0 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ->
    propagation_scan_candidate_layout scan_current lits stop k offset false_lit
      p candidate (2 * lit_sign_c candidate - 1) clause_contents ->
    Znth (lit_var_c candidate) (mt_assigns (ms_core Mscan)) 0 <> 2 * lit_sign_c candidate - 1 ->
    propagation_destination_ok (2 * ms_size Mscan) p
      (lit_neg_c candidate) ->
    propagation_scan_slot Mscan p scan_wm logical_words ->
    simp_count = ms_simpdb_props Mscan ->
    prop_count = Znth 2 (ms_stats Mscan) 0 ->
    db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents
      (propagation_migrated_clause watch0 candidate false_lit offset clause_contents)
      prob_after learnt_after ->
    minisat_propagation_reuse_scan M0 Mscan p 0 rest ->
    Zlength (ms_wm Mscan) = 2 * n /\
    0 <= lit_neg_c candidate < 2 * n /\
    lit_neg_c candidate <> p /\
    propagation_real_migrated_exit_carrier n F A_arr K M0 Mentry Mscan
      (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
        (propagation_move_wmap p (lit_neg_c candidate) scan_wm
          (retained ++ raw_suffix) scan_current)
        )
      p prob_after learnt_after scan_wm
       candidate scan_current source_words retained moved
      rest watch_memory ii jj (moved ++ (scan_current :: nil)) raw_suffix
      (garbage ++ (scan_current :: nil)) migration_post_memory simp_count prop_count /\
    minisat_propagation_reuse_scan M0
      (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
        (propagation_move_wmap p (lit_neg_c candidate) scan_wm
          (retained ++ raw_suffix) scan_current)
        ) p 0 raw_suffix.
Proof.
  intros n F A_arr K M0 Mentry Mscan prob_after learnt_after p scan_wm logical_words
    candidate scan_current clause_contents watch0 false_lit lits stop k
    offset retained rest raw_suffix source_words moved garbage watch_memory candidate_post_memory
    migration_post_memory ii jj simp_count prop_count H_solver_shape H_msolver_seed_shadow H_propagation_caller_frame
    H_propagation_scan_frontier H_solver_propagation_scan_semantics H_rest H_propagation_watch_scan_physical
    H_candidate_post_memory H_Znth H_migration_post_memory H_false_lit H_real_watch_pair H_watch0
    H_propagation_scan_candidate_layout H_Znth_2 H_propagation_destination_ok H_propagation_scan_slot H_simp_count
    H_prop_count Hupdate Hreuse_entry.
  pose proof H_solver_propagation_scan_semantics as Hsembase.
  rewrite H_rest in Hsembase.
  pose proof Hsembase as Hsem0.
  destruct Hsem0 as [Hlive | Hdead].
  2: {
    destruct Hdead as [Hnz _].
    lia.
  }
  destruct Hlive as [_ [Hweak [Hlevel [Hheap [Hcovers [Hreasonless [Hp_level [Hp_wf [Hprocessed [Hfrontier
      Hcarrier]]]]]]]]]].
  destruct (solver_propagation_weak_reason_core n F A_arr K Mscan Hweak) as [Hsize [Hreasons _]].
  assert (Hcommon : db_wf n (msolver_db Mscan) /\ mtrail_wf n (ms_core Mscan) /\ stable_view (msolver_view n Mscan)
      /\ reason_head_ok Mscan /\ wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
  {
    unfold solver_propagation_weak in Hweak.
    destruct K as [A_inst | A_proc]; cbn in Hweak; destruct Hweak as [_ Hctx].
    - split; [exact (msw_db_wf Hctx)|].
    split; [exact (msw_trail_wf Hctx)|].
    split; [exact (msw_stable Hctx)|].
    split; [exact (msw_reason_head Hctx)|exact (msw_wmap_exact Hctx)].
    - split; [exact (msa_db_wf Hctx)|].
    split; [exact (msa_trail_wf Hctx)|].
    split; [exact (msa_stable Hctx)|].
    split; [exact (msa_reason_head Hctx)|exact (msa_wmap_exact Hctx)].
  }
  destruct Hcommon as [Hdbwf [Htrail [Hstable [Hhead Hwmapold]]]].
  destruct (propagation_migrated_clause_structure__propagate_dbu n Mscan p scan_current clause_contents watch0 false_lit lits stop k offset candidate (2 * lit_sign_c
      candidate - 1) prob_after learnt_after Hdbwf H_propagation_scan_candidate_layout H_real_watch_pair H_watch0
      Hupdate) as [co [a0 [a1 [tail [Hcontents [Hin [Hco [Htail [Hwatch [Hcandidate [Hcandin [Hcandwf [Hcandhead
      [Hwatchneq [Hcandneq Hperm]]]]]]]]]]]]]]].
  pose proof H_propagation_scan_candidate_layout as Hlayout.
  unfold propagation_scan_candidate_layout in Hlayout.
  destruct Hlayout as [_ [_ [_ [_ [_ [Hoffset [_ _]]]]]]].
  assert (Hoffset_co : 2 <= offset < Zlength (a0 :: a1 :: tail)) by (rewrite <- Hcontents; exact Hoffset); pose
      proof Hupdate as Hupdate_co; rewrite Hcontents in Hupdate_co.
  assert (Hnoowner : forall v, 0 <= v < n -> Znth v (ms_reason_words Mscan) 0 <> scan_current).
  {
    eapply no_live_reason_owner_candidate_not_false__propagate_dbu; [exact Hsize|exact
        Hdbwf|exact Htrail|exact Hstable|exact Hreasons| exact Hhead|exact Hin|exact Hcandin|exact Hcandwf|exact
        Hcandhead|exact H_Znth_2].
  }
  pose proof (propagation_migrated_entry_watchers_delta__propagate_dbu n p scan_current co a0 a1 tail watch0 false_lit candidate offset Hp_wf H_false_lit Hco Hwatch
      Hoffset_co) as Hentrydelta; rewrite <- Hcontents in Hentrydelta.
  pose proof H_propagation_scan_slot as Hslot.
  destruct Hslot as [Hwm Hprange].
  pose proof (solver_shape_wm_len Mscan H_solver_shape) as Hwmlen.
  rewrite <- Hsize in Hwmlen.
  assert (Hscanlen : Zlength scan_wm = 2 * n).
  {
    rewrite Hwm, Zlength_replace_Znth in Hwmlen.
    exact Hwmlen.
  }
  assert (Hp : 0 <= p < 2 * n) by lia.
  pose proof H_propagation_destination_ok as Hdestination.
  rewrite <- Hsize in Hdestination.
  pose proof Hdestination as Hdest_n.
  unfold propagation_destination_ok in Hdestination.
  destruct Hdestination as [Hholenonneg [Htargetrange Htargetneq]].
  pose proof (focus_scan_carrier_words_expected__propagate_dbu _ _ _ _ _ Hcarrier) as
      Hexpectedold.
  assert (Hsourceold : Permutation logical_words (expected_watchers (msolver_db Mscan) p)).
  {
    pose proof (proj2 Hwmapold _ Hp) as Hx.
    rewrite Hwm, Znth_replace_Znth_Same in Hx by lia.
    exact Hx.
  }
  assert (Hsource : Permutation ((retained ++ raw_suffix) ++ (scan_current :: nil)) logical_words).
  {
    eapply Permutation_trans.
    2: {
      eapply Permutation_trans; [exact Hexpectedold|apply Permutation_sym; exact Hsourceold].
    }
    rewrite <- app_assoc.
    apply Permutation_app_head.
    apply Permutation_app_comm.
  }
  destruct (propagation_move_wmap_cells__propagate_dbu n Mscan p
      (lit_neg_c candidate) scan_wm logical_words (retained
      ++ raw_suffix) scan_current co (propagation_migrated_clause watch0 candidate false_lit offset clause_contents)
      H_propagation_scan_slot Hp Hdest_n Hsource Hentrydelta Hwmlen) as [Hmove_len Hcells].
  assert (Hco_contents : co_lits co = clause_contents).
  {
    rewrite Hco, Hcontents.
    reflexivity.
  }
  pose proof (db_pair_lits_update_wmap_move__propagate_dbu n (ms_prob Mscan) (ms_learnt
      Mscan) scan_current clause_contents (propagation_migrated_clause watch0 candidate false_lit offset
      clause_contents) prob_after learnt_after (ms_wm Mscan) (propagation_move_wmap p (lit_neg_c
      candidate) scan_wm (retained ++ raw_suffix) scan_current) co Hdbwf Hin Hco_contents Hupdate
      Hwmapold Hmove_len Hcells) as Hwmapnew.
  pose proof (solver_propagation_weak_db_wmap_move__propagate_dbu n F A_arr K Mscan
      scan_current clause_contents (propagation_migrated_clause watch0 candidate false_lit offset clause_contents)
      prob_after learnt_after (propagation_move_wmap p (lit_neg_c candidate) scan_wm
      (retained ++ raw_suffix) scan_current) Hweak Hupdate Hperm Hnoowner ltac:(rewrite Hmove_len,
      Hwmlen; reflexivity) Hwmapnew) as Hweakroute.
  pose proof (propagation_migrated_frontier_transport__propagate_dbu n Mscan p scan_current co a0 a1 tail watch0 false_lit candidate offset prob_after learnt_after Hdbwf Hin
      Hco Hoffset_co Hcandwf H_Znth_2 Hupdate_co Hfrontier) as Hfrontierroute.
  pose proof (propagation_migrated_focus_transport__propagate_dbu n Mscan p scan_current co a0 a1 tail watch0 false_lit candidate offset prob_after learnt_after
      (minisat_processed n (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      retained raw_suffix Hdbwf Hin Hco Hwatch Hp_wf H_false_lit Hoffset_co Hwatchneq Hcandneq Hupdate_co Hcarrier)
      as Hcarrierroute.
  pose proof (propagation_migrated_scan_semantics__propagate_dbu n F A_arr K Mscan p retained scan_current raw_suffix prob_after learnt_after (propagation_move_wmap p (lit_neg_c candidate) scan_wm (retained ++ raw_suffix) scan_current)
      Hsembase
      Hweakroute Hfrontierroute Hcarrierroute) as Hsemroute.
  destruct (propagation_migrated_physical_step__propagate_dbu source_words retained moved
      rest garbage watch_memory candidate_post_memory migration_post_memory raw_suffix ii jj scan_current H_rest
      H_propagation_watch_scan_physical H_candidate_post_memory H_Znth H_migration_post_memory) as [Hmemory [Hstep
      Hphysical]].
  assert (Hsplitwm : ms_wm (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
      (propagation_move_wmap p (lit_neg_c candidate) scan_wm (retained ++ raw_suffix) scan_current)) =
      replace_Znth p (retained ++ raw_suffix)
        (replace_Znth (lit_neg_c candidate)
           (Znth (lit_neg_c candidate) scan_wm nil ++ (scan_current :: nil)) scan_wm)).
  {
    transitivity (propagation_move_wmap p (lit_neg_c candidate) scan_wm
      (retained ++ raw_suffix) scan_current); [reflexivity|].
    unfold propagation_move_wmap.
    apply replace_Znth_comm; lia.
  }
  set (Mroute := msolver_propagation_db_wmap_update Mscan prob_after learnt_after (propagation_move_wmap p (lit_neg_c candidate) scan_wm (retained ++ raw_suffix) scan_current)
      ).
  assert (Hreuseroute : minisat_propagation_reuse_scan M0 Mroute
    p 0 raw_suffix).
  {
    set (normalized := watch0 :: lit_neg_c p :: tail).
    set (migrated := propagation_migrated_clause
      watch0 candidate false_lit offset clause_contents).
    assert (Hnormalized : propagation_normalized_clause
      watch0 (lit_neg_c p) clause_contents = normalized).
    { unfold propagation_normalized_clause, normalized. rewrite Htail. reflexivity. }
    assert (Hnormperm : Permutation normalized clause_contents).
    { unfold normalized. rewrite Hcontents, <- H_false_lit.
      destruct Hwatch as [[Ha Hw]|[Ha Hw]]; subst;
        [apply perm_swap|apply Permutation_refl]. }
    assert (Hfactor : exists norm_prob norm_learnt,
      db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan)
        scan_current clause_contents normalized norm_prob norm_learnt /\
      db_pair_lits_update norm_prob norm_learnt
        scan_current normalized migrated prob_after learnt_after).
    { destruct Hupdate as
        [[obj [pre [post [Hprob_before [Hwords [Hp' Hl']]]]]]
        |[obj [pre [post [Hlearnt_before [Hwords [Hp' Hl']]]]]]].
      - exists (pre ++ (scan_current, clause_obj_with_lits obj normalized) :: post),
          (ms_learnt Mscan). split.
        + left. exists obj, pre, post. repeat split; assumption || reflexivity.
        + left. exists (clause_obj_with_lits obj normalized), pre, post.
          repeat split; assumption || reflexivity.
      - exists (ms_prob Mscan),
          (pre ++ (scan_current, clause_obj_with_lits obj normalized) :: post). split.
        + right. exists obj, pre, post. repeat split; assumption || reflexivity.
        + right. exists (clause_obj_with_lits obj normalized), pre, post.
          repeat split; assumption || reflexivity. }
    destruct Hfactor as [norm_prob [norm_learnt [Hnormupdate Hmoveupdate]]].
    set (Mnorm := msolver_propagation_db_wmap_update Mscan
      norm_prob norm_learnt (ms_wm Mscan)).
    assert (Hreusenorm : minisat_propagation_reuse_scan M0 Mnorm
      p 0 (scan_current :: raw_suffix)).
    { unfold Mnorm. eapply minisat_propagation_reuse_normalize__api_reentry
        with (current := scan_current) (a0 := a0) (a1 := a1)
          (tail := tail) (other := watch0).
      - rewrite <- Hcontents, Hnormalized. exact Hnormupdate.
      - rewrite <- H_false_lit. exact Hwatch.
      - rewrite <- H_rest. exact Hreuse_entry. }
    assert (Hdbnorm : db_wf n (msolver_db Mnorm)).
    { eapply db_pair_lits_update_db_wf__propagate_dbu;
        [exact Hdbwf|exact Hnormperm|exact Hnormupdate]. }
    assert (Hdbroute : db_wf n (prob_after ++ learnt_after)).
    { eapply db_pair_lits_update_db_wf__propagate_dbu;
        [exact Hdbwf|exact Hperm|exact Hupdate]. }
    assert (Hreal : is_tag scan_current = false).
    { apply even_not_tag. exact (db_wf_even n (msolver_db Mscan)
        scan_current co Hdbwf Hin). }
    set (newtail := replace_Znth (offset - 2) false_lit tail).
    assert (Hmigrated : migrated = watch0 :: candidate :: newtail).
    { unfold migrated, propagation_migrated_clause. rewrite Htail.
      rewrite !replace_Znth_cons by lia.
      replace (offset - 1 - 1) with (offset - 2) by lia. reflexivity. }
    assert (Hmoveperm : Permutation normalized (watch0 :: candidate :: newtail)).
    { rewrite <- Hmigrated. eapply Permutation_trans;
        [exact Hnormperm|apply Permutation_sym; exact Hperm]. }
    assert (Hcandidate_safe : ~ lit_false (mt_assigns (ms_core Mnorm)) candidate).
    { unfold lit_false. change (Znth (lit_var_c candidate)
        (mt_assigns (ms_core Mscan)) 0 <> - lit_sig candidate).
      replace (- lit_sig candidate) with (2 * lit_sign_c candidate - 1)
        by (unfold lit_sig, lit_sign_c; destruct (Z.odd candidate); reflexivity).
      exact H_Znth_2. }
    change (minisat_propagation_reuse_scan M0
      (msolver_propagation_db_wmap_update Mnorm prob_after learnt_after
        (propagation_move_wmap p (lit_neg_c candidate)
          scan_wm (retained ++ raw_suffix) scan_current)
        ) p 0 raw_suffix).
    eapply minisat_propagation_reuse_migrate__api_reentry
      with (n := n) (current := scan_current) (other := watch0)
        (oldtail := tail) (candidate := candidate) (newtail := newtail).
    - exact Hdbnorm.
    - exact Hdbroute.
    - exact Hreal.
    - rewrite <- Hmigrated. exact Hmoveupdate.
    - exact Hmoveperm.
    - exact (proj1 Hprocessed).
    - exact Hcandidate_safe.
    - exact Hreusenorm.
  }
  assert (Hshaperoute : solver_shape Mroute).
  {
    unfold solver_propagation_weak in Hweakroute.
    destruct K as [A_inst|A_proc]; cbn in Hweakroute; [exact (msw_shape (proj2 Hweakroute))| exact (msa_shape (proj2
        Hweakroute))].
  }
  assert (Hseedroute : msolver_seed_shadow Mroute).
  {
    unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_msolver_seed_shadow.
  }
  assert (Hcallerroute : propagation_caller_frame M0 Mroute).
  {
    unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_propagation_caller_frame.
  }
  assert (Hscanroute : propagation_scan_frontier Mentry Mroute p).
  {
    unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_propagation_scan_frontier.
  }
  assert (Hexit : propagation_real_migrated_exit_carrier n F A_arr K M0 Mentry Mscan Mroute p
      prob_after learnt_after scan_wm
      candidate scan_current source_words retained moved rest watch_memory ii jj (moved ++ (scan_current :: nil))
      raw_suffix (garbage ++ (scan_current :: nil)) migration_post_memory simp_count prop_count).
  {
    eapply propagation_real_migrated_exit_intro__propagate_dbu; [reflexivity|exact
        Hstep|exact Hshaperoute|exact Hseedroute|exact Hcallerroute| exact Hscanroute|exact Hsemroute| | |exact
        Hmemory|exact Hphysical| exact Hsplitwm].
    - unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_simp_count.
    - unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_prop_count.
  }
  split; [exact Hwmlen|].
  split; [exact Htargetrange|].
  split; [exact Htargetneq|].
  split; [exact Hexit|exact Hreuseroute].
Qed.

Lemma msat_propagate_scan_db_wf :
  forall n F A_arr K M p kept rest,
    solver_propagation_scan_semantics n F A_arr K M p 0 kept rest ->
    db_wf n (msolver_db M).
Proof.
  intros n F A_arr K M p kept rest Hsem.
  destruct Hsem as [Hlive | Hbad].
  - destruct Hlive as [_ [Hweak _]]. destruct Hweak as [_ Hinv].
    destruct K as [A_inst | A_proc].
    + exact (msw_db_wf Hinv).
    + exact (msa_db_wf Hinv).
  - exfalso. destruct Hbad as [Hnz _]. lia.
Qed.

Lemma msat_propagate_scan_begin_binary_rep :
  forall (M : msolver) (simpdb_props propagation_count : Z),
    solver_binary_rep
      (msolver_propagation_scan_begin M simpdb_props propagation_count) =
    solver_binary_rep M.
Proof. reflexivity. Qed.

Lemma msat_propagate_scan_begin_frame_eq :
  forall (s : Z) (M : msolver) (simpdb_props propagation_count : Z),
    Zlength (ms_stats M) = 11 ->
    solver_propagate_frame s
      (msolver_propagation_scan_begin M simpdb_props propagation_count) =
    solver_propagate_frame s M.
Proof.
  intros s M simpdb_props propagation_count Hstatslen.
  unfold solver_propagate_frame, solver_fp_rep, stats_propagate_frame,
    stats_starts, stats_decisions, stats_conflicts, stats_clauses,
    stats_clauses_literals, stats_learnts, stats_learnts_literals,
    stats_max_literals, stats_tot_literals,
    msolver_propagation_scan_begin, msolver_propagation_scan,
    msolver_propagation_update, stats_set_propagations.
  simpl.
  rewrite !Zlength_replace_Znth.
  rewrite !Znth_replace_Znth_Diff by lia.
  reflexivity.
Qed.

(** Closes the spatial goal at the start of a propagation scan.  [Mscan] is
    a local definition [msolver_propagation_scan_begin M _ _], and the context
    holds [Zlength (ms_stats M) = 11].  The step keeps the binary scratch
    object and the propagate frame, and once it is unfolded both sides hold
    the same heap. *)
Ltac msat_propagate_scan_begin_spatial Mscan :=
  subst Mscan;
  rewrite msat_propagate_scan_begin_binary_rep;
  rewrite msat_propagate_scan_begin_frame_eq by assumption;
  unfold msolver_propagation_scan_begin, msolver_propagation_scan,
    msolver_propagation_update, stats_set_propagations;
  simpl;
  try rewrite Znth_replace_Znth_Diff by lia;
  try rewrite Z.add_0_r;
  match goal with
  | |- ?P |-- ?Q =>
    assert (Hspatial_identity : P |-- Q) by
      (msat_cancel_sound; lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel);
    exact Hspatial_identity
  end.

(** Entailment at the start of a propagation scan over the watch list of the
    trail literal at the queue head.  The scan starts with every watcher
    pending, an empty kept list and the propagation count bumped; [Mscan] is
    the solver after [msolver_propagation_scan_begin], and
    [propagation_scan_begin_initial__analyze] gives the scan facts.  [trl],
    [rsn] and [simp] are the trail, reasons and [simpdb_props] values the
    heap holds. *)
Ltac msat_propagate_scan_begin trl rsn simp :=
  unfold stats_propagations, stats_inspects;
  lazymatch goal with
  | Hshape : solver_shape ?M1,
    Hinv : solver_propagation_inv ?n ?F ?A_arr ?K ?M1,
    Hcallfr : propagation_caller_frame ?M0 ?M1,
    Hqtail : ms_qtail ?M1 - mt_qhead (ms_core ?M1) > 0,
    Hreuse_loop : minisat_propagation_reuse_loop ?n ?M0 ?M1 ?cf,
    Hcf : ?cf = 0,
    Hseed : msolver_seed_shadow ?M1,
    Hzlen2 : Zlength (mt_trail (ms_core ?M1)) = ms_qtail ?M1,
    Hwords : ?words = Znth (Znth (mt_qhead (ms_core ?M1)) (mt_trail (ms_core ?M1)) 0)
      (ms_wm ?M1) nil,
    Hslot : ?slot_ret = Vecp.slot ?wl
      (Znth (mt_qhead (ms_core ?M1)) (mt_trail (ms_core ?M1)) 0)
    |- context [Vecp.rep_ptr ?slot_ret ?p _] =>
    let Mscan := fresh "Mscan" in
    rewrite <- Hwords in *;
    match goal with
    | Hretval : ?buf_ret = p |- _ => is_var buf_ret; subst buf_ret
    end;
    subst slot_ret;
    sep_apply (Vecp.rep_ptr_bounds
      (Vecp.slot wl (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)) p words);
    Intros;
    Exists trl rsn simp
      (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
      (ms_wm M1)
      words words (@nil Z) (@nil Z) words 0 0 (@nil Z) words M1;
    set (Mscan := msolver_propagation_scan_begin M1 simp
      (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64));
    Exists Mscan;
    rewrite Hcf in Hreuse_loop;
    assert (Hwatch_map : wmap_exact n (msolver_db M1) (ms_wm M1))
      by (destruct (propagation_inv_context_facts__analyze n F A_arr K M1 Hinv)
        as (_ & _ & _ & _ & _ & _ & Hmap); exact Hmap);
    destruct Hwatch_map as [Hmap_length Hmap];
    assert (Hmap_index :
        0 <= Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0 < 2 * n)
      by lia;
    assert (Hpending : incl (expected_watchers (msolver_db M1)
      (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)) words)
      by (specialize (Hmap (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
        Hmap_index);
        rewrite <- Hwords in Hmap; intros word Hin;
        eapply Permutation_in; [apply Permutation_sym; exact Hmap|exact Hin]);
    assert (Hreuse_scan : minisat_propagation_reuse_scan M0 Mscan
      (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0) cf words)
      by (rewrite Hcf; exact (minisat_propagation_reuse_scan_begin__api_reentry
        n M0 M1 (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
        simp (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
        words Hreuse_loop eq_refl Hpending));
    assert (Hstatslen : Zlength (ms_stats M1) = 11)
      by (unfold solver_shape in Hshape; intuition);
    pose proof (propagation_scan_begin_initial__analyze
      n F A_arr K M0 M1
      (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
      simp
      (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
      cf words Hshape Hinv Hseed Hcallfr Hqtail
      (eq_sym Hzlen2) eq_refl Hwords Hcf) as Hscan;
    change (solver_shape Mscan /\
      msolver_seed_shadow Mscan /\
      propagation_caller_frame M0 Mscan /\
      propagation_scan_frontier M1 Mscan
        (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0) /\
      solver_propagation_scan_semantics n F A_arr K Mscan
        (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
        cf (@nil Z) words) in Hscan;
    destruct Hscan as
      [Hshape_scan [Hseed_scan [Hcaller_scan [Hfrontier_scan Hsem_scan]]]];
    subst n;
    split_pure_spatial;
    [ msat_propagate_scan_begin_spatial Mscan
    | split_pures; dump_pre_spatial;
        try assumption; try reflexivity; try lia;
        try (unfold propagation_watch_scan_physical, wlist_scan_inv;
          simpl; repeat split; try reflexivity; apply Zlength_nonneg);
        unfold Mscan, msolver_propagation_scan_begin,
          msolver_propagation_scan, msolver_propagation_update, stats_set_propagations;
        cbn [mt_set_qhead];
        try rewrite Znth_replace_Znth_Same by lia;
        try rewrite Znth_replace_Znth_Diff by lia;
        try assumption; try reflexivity; try lia; try apply Zlength_nonneg;
        try (rewrite Hwords, replace_Znth_Znth; reflexivity);
        change
          (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64 =
           Znth 2
             (replace_Znth 2
               (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
               (ms_stats M1)) 0);
        rewrite Znth_replace_Znth_Same by lia; reflexivity ]
  end.

Lemma msat_propagate_unit_conflict_binary_rep :
  forall (Mscan : msolver) (prob' learnt' : dbmap) (wm : list (list Z)),
    solver_binary_rep
      (msolver_propagation_db_wmap_update Mscan prob' learnt' wm) =
    solver_binary_rep Mscan.
Proof.
  intros. unfold solver_binary_rep,
    msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
  reflexivity.
Qed.

Lemma msat_propagate_unit_conflict_frame_eq :
  forall (s : Z) (Mscan : msolver) (prob' learnt' : dbmap)
         (wm : list (list Z)),
    map fst prob' = map fst (ms_prob Mscan) ->
    map fst learnt' = map fst (ms_learnt Mscan) ->
    solver_propagate_frame s
      (msolver_propagation_db_wmap_update Mscan prob' learnt' wm) =
    solver_propagate_frame s Mscan.
Proof.
  intros s Mscan prob' learnt' wm Hp Hl.
  unfold msolver_propagation_db_wmap_update, solver_propagate_frame,
    solver_fp_rep, msolver_propagation_overlay, msolver_propagation_update. cbn.
  rewrite Hp, Hl. reflexivity.
Qed.

Lemma msat_propagate_unit_conflict_keys_replace :
  forall (pre post : dbmap) (q : Z) (c1 c2 : clause_obj) (l : dbmap),
    l = pre ++ (q, c1) :: post ->
    map fst (pre ++ (q, c2) :: post) = map fst l.
Proof.
  intros pre post q c1 c2 l Hl. subst l.
  rewrite !map_app. cbn. reflexivity.
Qed.

(* The rewritten clause object is still well-formed: its literal list is a
   permutation of the old one, so length, literal bounds and variable
   distinctness all transport. *)
Lemma msat_propagate_unit_conflict_new_obj_wf :
  forall (n : Z) (co : clause_obj) (watch0 false_lit a0 a1 : Z)
         (tail : list Z),
    2 <= Zlength_aux 2 Z tail ->
    Forall (lit_wf_c n) (a0 :: a1 :: tail) ->
    NoDup (map lit_var_c (a0 :: a1 :: tail)) ->
    Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail) ->
    obj_wf n (clause_obj_with_lits co (watch0 :: false_lit :: tail)).
Proof.
  intros n co watch0 false_lit a0 a1 tail Hlen Hall Hnodup Hperm.
  unfold clause_obj_with_lits, obj_wf. cbn.
  split; [exact Hlen|]. split.
  - rewrite Forall_forall in Hall |- *. intros x Hx. apply Hall.
    eapply Permutation_in; [exact Hperm|exact Hx].
  - apply (Permutation_NoDup
      (Permutation_sym (Permutation_map lit_var_c Hperm))).
    exact Hnodup.
Qed.

Lemma msat_propagate_unit_conflict_route_db_wf :
  forall (n : Z) (Mscan : msolver) (co co_new : clause_obj)
         (scan_current : Z) (pre2 post2 prob' learnt' : dbmap),
    db_wf n (msolver_db Mscan) ->
    obj_wf n co_new ->
    msolver_db Mscan = pre2 ++ (scan_current, co) :: post2 ->
    prob' ++ learnt' = pre2 ++ (scan_current, co_new) :: post2 ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current, co_new) l)) ->
    map fst (prob' ++ learnt') = map fst (msolver_db Mscan)
    /\ (forall q obj, q <> scan_current -> In (q, obj) (msolver_db Mscan) ->
          In (q, obj) (prob' ++ learnt'))
    /\ (forall q obj, In (q, obj) (prob' ++ learnt') ->
          In (q, obj) (msolver_db Mscan) \/ (q, obj) = (scan_current, co_new))
    /\ (forall l, Permutation (expected_watchers (msolver_db Mscan) l)
          (expected_watchers (prob' ++ learnt') l))
    /\ In (scan_current, co_new) (prob' ++ learnt')
    /\ db_wf n (prob' ++ learnt').
Proof.
  intros n Mscan co co_new scan_current pre2 post2 prob' learnt'
    Hdbwf Hobjnew Hold Hnew Hentry_perm.
  assert (Hkeys : map fst (prob' ++ learnt') = map fst (msolver_db Mscan)).
  { rewrite Hold, Hnew. rewrite !map_app. cbn. reflexivity. }
  pose proof (msat_db_entry_swap_mem_cases (msolver_db Mscan)
    (prob' ++ learnt') pre2 post2 scan_current co co_new Hold Hnew) as Hcases.
  pose proof (msat_db_entry_swap_mem_fwd (msolver_db Mscan)
    (prob' ++ learnt') pre2 post2 scan_current co co_new Hold Hnew) as Hother.
  pose proof (msat_db_entry_swap_expected_watchers (msolver_db Mscan)
    (prob' ++ learnt') pre2 post2 scan_current co co_new Hold Hnew
    Hentry_perm) as Hexp.
  assert (Hsel : In (scan_current, co_new) (prob' ++ learnt')).
  { rewrite Hnew. apply in_or_app. right. simpl. auto. }
  split; [exact Hkeys|]. split; [exact Hother|]. split; [exact Hcases|].
  split; [exact Hexp|]. split; [exact Hsel|].
  unfold db_wf in Hdbwf |- *.
  destruct Hdbwf as [Hk [Hptrs Hobjs]].
  split; [rewrite Hkeys; exact Hk|]. split.
  - rewrite Forall_forall in Hptrs |- *. intros e He.
    assert (Hemap : In (fst e) (map fst (prob' ++ learnt'))).
    { apply in_map. exact He. }
    rewrite Hkeys in Hemap.
    apply in_map_iff in Hemap as [eold [Hfst Heold]].
    specialize (Hptrs eold Heold). rewrite <- Hfst. exact Hptrs.
  - rewrite Forall_forall in Hobjs |- *. intros [q obj] He.
    destruct (Hcases q obj He) as [Hin2 | Heq].
    + apply Hobjs. exact Hin2.
    + inversion Heq; subst. exact Hobjnew.
Qed.

Lemma msat_propagate_unit_conflict_route_ready :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj) (scan_current p watch0 false_lit a0 a1 : Z)
         (tail retained rest : list Z) (prob' learnt' : dbmap),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tail ->
    obj_wf n (clause_obj_with_lits co (watch0 :: false_lit :: tail)) ->
    Forall (lit_false (mt_assigns (ms_core Mscan)))
      (watch0 :: false_lit :: tail) ->
    false_lit = lit_neg_c p ->
    (forall v, 0 <= v < n ->
       Znth v (ms_reason_words Mscan) 0 <> scan_current) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)) ->
    ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0)) ->
    map fst (prob' ++ learnt') = map fst (msolver_db Mscan) ->
    (forall q obj, q <> scan_current -> In (q, obj) (msolver_db Mscan) ->
       In (q, obj) (prob' ++ learnt')) ->
    (forall q obj, In (q, obj) (prob' ++ learnt') ->
       In (q, obj) (msolver_db Mscan) \/
       (q, obj) = (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail))) ->
    (forall l, Permutation (expected_watchers (msolver_db Mscan) l)
       (expected_watchers (prob' ++ learnt') l)) ->
    In (scan_current,
        clause_obj_with_lits co (watch0 :: false_lit :: tail))
      (prob' ++ learnt') ->
    db_wf n (prob' ++ learnt') ->
    db_matches_cnf F (msolver_propagation_db_wmap_update Mscan prob' learnt'
      (ms_wm Mscan)) ->
    db_complete F (msolver_propagation_db_wmap_update Mscan prob' learnt'
      (ms_wm Mscan)) ->
    db_implied F (msolver_propagation_db_wmap_update Mscan prob' learnt'
      (ms_wm Mscan)) ->
    prob_db prob' ->
    learnt_db learnt' ->
    entails_clause F
      (denote_obj (clause_obj_with_lits co (watch0 :: false_lit :: tail))) ->
    db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
      prob' learnt' ->
    propagation_unit_conflict_ready n F A_arr K Mscan p scan_current watch0
      false_lit (a0 :: a1 :: tail) retained rest prob' learnt'
      (msolver_propagation_db_wmap_update Mscan prob' learnt'
        (ms_wm Mscan)).
Proof.
  intros n F A_arr K Mscan co scan_current p watch0 false_lit a0 a1 tail
    retained rest prob' learnt' Hsem Hdbwf Hin Hlits Hobjnew Hnew_false
    H_false_lit
    Hno_reason_ptr Hentry_perm Hwatchcases Hkeys_route Hlookup_other Hcases
    Hexpected_perm Hselected_route Hdbwf_route Hdbmatches_route
    Hdbcomplete_route Hdbimplied_route Hprobdb_route Hlearntdb_route
    Hentails_new Hdbupdate.
  destruct Hsem as [Hlive | Hdead]; [|destruct Hdead as [Hzero _]; lia].
  destruct Hlive as
    [_ [Hweak [Hprop [_ [Hheapcovers [Hreasonless
      [Hlevel [Hp [Hprocessed [Hfrontier _]]]]]]]]]].
  set (new_lits := watch0 :: false_lit :: tail) in *.
  set (co_new := clause_obj_with_lits co new_lits) in *.
  set (Mroute := msolver_propagation_db_wmap_update Mscan prob' learnt'
    (ms_wm Mscan)) in *.
  assert (Hbinary_route :
      ~ In (ms_binary Mscan) (map fst (prob' ++ learnt'))).
  { rewrite Hkeys_route.
    msat_propagate_project_weak_field Hweak K (@msw_binary_out)
      (@msa_binary_out). }
  assert (Hreasons_old : reasons_match n (ms_core Mscan)
      (msolver_db Mscan) (ms_reason_words Mscan) (ms_reason_of Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_mem)
      (@msa_reasons_mem). }
  assert (Hreasons_route : reasons_match n (ms_core Mscan)
      (prob' ++ learnt') (ms_reason_words Mscan) (ms_reason_of Mscan)).
  { unfold reasons_match in Hreasons_old |- *. intros v Hv.
    specialize (Hreasons_old v Hv).
    unfold reason_word_ok in Hreasons_old |- *.
    destruct ((Znth v (ms_reason_words Mscan) 0 =? 0)%Z) eqn:Hz;
      [exact Hreasons_old|].
    destruct (is_tag (Znth v (ms_reason_words Mscan) 0)) eqn:Htag;
      [exact Hreasons_old|].
    destruct Hreasons_old as [Hassignedv [obj [Hlookup Hr]]].
    split; [exact Hassignedv|]. exists obj. split; [|exact Hr].
    apply Hlookup_other; [apply Hno_reason_ptr; exact Hv|exact Hlookup]. }
  pose proof (msat_db_entry_swap_mem_bwd (msolver_db Mscan)
    (prob' ++ learnt') scan_current co_new Hcases) as Hlookup_route_old.
  assert (Hsize_old : n = ms_size Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_size) (@msa_size). }
  assert (Hreasonhead_old : reason_head_ok Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_reason_head)
      (@msa_reason_head). }
  assert (Hreasonhead_route : reason_head_ok Mroute).
  { unfold reason_head_ok in Hreasonhead_old |- *.
    intros v obj Hv Htag Hnz Hlookup.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update in *; cbn in *.
    apply (Hreasonhead_old v obj); try assumption.
    apply Hlookup_route_old; [|exact Hlookup].
    apply Hno_reason_ptr. rewrite Hsize_old. exact Hv. }
  assert (Hwmap_old : wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_wmap_exact)
      (@msa_wmap_exact). }
  assert (Hwmap_route : wmap_exact n (prob' ++ learnt') (ms_wm Mscan)).
  { unfold wmap_exact in Hwmap_old |- *.
    destruct Hwmap_old as [Hlenwm Hold]. split; [exact Hlenwm|].
    intros l Hl. specialize (Hold l Hl).
    eapply Permutation_trans; [exact Hold|apply Hexpected_perm]. }
  assert (Hweak_route : solver_propagation_weak n F A_arr K Mroute).
  { unfold solver_propagation_weak in Hweak |- *.
    destruct Hweak as [Hroot Hweak]. split; [exact Hroot|].
    destruct K;
    (cbn in Hweak |- *; destruct Hweak;
      unfold Mroute, msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update; cbn;
      constructor; try exact Hdbwf_route; try exact Hdbmatches_route;
        try exact Hdbcomplete_route; try exact Hdbimplied_route;
        try exact Hprobdb_route; try exact Hlearntdb_route;
        try exact Hbinary_route; try exact Hreasons_route;
        try exact Hreasonhead_route; try exact Hwmap_route;
        try assumption). }
  assert (Hfrontier_route : minisat_watch_frontier_except n
      (prob' ++ learnt') (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan))
      (lit_denote p)).
  { unfold minisat_watch_frontier_except,
      minisat_watch_occurrences in Hfrontier |- *.
    unfold watch_frontier_except in Hfrontier |- *.
    rewrite Forall_forall in Hfrontier |- *.
    intros o Ho. apply in_map_iff in Ho as [[q obj] [<- Hentry]].
    destruct (Hcases q obj Hentry) as [Hold | Heq].
    - apply Hfrontier. apply in_map. exact Hold.
    - inversion Heq; subst q obj.
      specialize (Hfrontier (minisat_occurrence_of_entry
        (scan_current, co))).
      assert (Holdin : In (minisat_occurrence_of_entry
          (scan_current, co))
          (map minisat_occurrence_of_entry (msolver_db Mscan))).
      { apply in_map. exact Hin. }
      specialize (Hfrontier Holdin).
      destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
      + subst a0. subst watch0.
        unfold minisat_occurrence_of_entry, co_watch0, co_watch1,
          co_new, clause_obj_with_lits, new_lits in *.
        rewrite Hlits in Hfrontier. cbn in *. tauto.
      + subst a1. subst watch0.
        unfold minisat_occurrence_of_entry, co_watch0, co_watch1,
          co_new, clause_obj_with_lits, new_lits in *.
        rewrite Hlits in Hfrontier. cbn in *. exact Hfrontier. }
  assert (Hheapwf_old : heap_wf n (msolver_heap Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_heap_wf)
      (@msa_heap_wf). }
  assert (Hcancel_route : propagation_cancel_ready n F A_arr K Mroute p).
  { unfold propagation_cancel_ready.
    split; [exact Hweak_route|]. split; [exact Hprop|].
    split; [exact Hp|]. split; [exact Hprocessed|].
    split; [exact Hlevel|]. split; [exact Hfrontier_route|].
    split; [exact Hheapwf_old|]. split;
      [exact Hheapcovers|exact Hreasonless]. }
  assert (Hclause_false_new : clause_false
      (assigns_pv (mt_assigns (ms_core Mroute))) (denote_obj co_new)).
  { unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
    unfold denote_obj.
    change (clause_false (assigns_pv (mt_assigns (ms_core Mscan)))
      (lits_denote new_lits)).
    apply lits_denote_false_iff.
    - destruct Hobjnew as [_ [Hwfnew _]].
      unfold co_new, clause_obj_with_lits in Hwfnew; cbn in Hwfnew.
      eapply Forall_impl; [|exact Hwfnew]. intros x Hx. destruct Hx. lia.
    - exact Hnew_false. }
  assert (Hwfden_new : Forall (literal_wf n) (denote_obj co_new)).
  { unfold denote_obj. apply lits_denote_wf.
    destruct Hobjnew as [_ [Hwfnew _]]. exact Hwfnew. }
  assert (Hnodupden_new : NoDup (map literal_var (denote_obj co_new))).
  { unfold denote_obj. apply lits_denote_nodup_vars.
    destruct Hobjnew as [_ [_ Hndnew]]. exact Hndnew. }
  assert (Hcurrent_new : exists l, In l (denote_obj co_new) /\
      level_of (msolver_view n Mroute) (literal_var l) =
        Some (Zlength (mt_lim (ms_core Mroute)))).
  { exists (lit_denote false_lit). split.
    - unfold denote_obj, co_new, clause_obj_with_lits, new_lits,
        lits_denote. cbn. auto.
    - unfold Mroute, msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
      rewrite lit_var_c_denote, H_false_lit, lit_var_c_neg. exact Hlevel. }
  assert (Hcert_new : propagation_conflict_cert n F Mroute
      (denote_obj co_new)).
  { unfold propagation_conflict_cert. repeat split;
      try exact Hentails_new; try exact Hclause_false_new;
      try exact Hwfden_new; try exact Hnodupden_new;
      try exact Hcurrent_new. }
  assert (Hptr_ne_binary : scan_current <> ms_binary Mroute).
  { intro Heq. apply Hbinary_route.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update in Heq; cbn in Heq. rewrite <- Heq.
    apply in_map_iff. exists (scan_current, co_new).
    split; [reflexivity|exact Hselected_route]. }
  assert (Hptrden_new : conflict_ptr_denotes Mroute scan_current
      (denote_obj co_new)).
  { right. exists co_new. split; [exact Hptr_ne_binary|]. split.
    - unfold Mroute, msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update; cbn. exact Hselected_route.
    - reflexivity. }
  assert (Hscan_conflict : solver_propagation_scan_semantics
      n F A_arr K Mroute p scan_current (retained ++ rest) nil).
  { right. split.
    - pose proof (db_wf_ptr_pos n (msolver_db Mscan) scan_current co
        Hdbwf Hin). lia.
    - split; [reflexivity|]. split; [exact Hcancel_route|].
      exists (denote_obj co_new). split;
        [exact Hcert_new|exact Hptrden_new]. }
  split; [exact Hdbupdate|].
  unfold propagation_unit_conflict_transition. split;
    [reflexivity|exact Hscan_conflict].
Qed.

(* Here ms_prob is untouched, so
   db_matches_cnf and db_complete transport by reduction, and the work is on
   db_implied and learnt_db: the new object is a permutation of a clause the
   formula already entails and keeps the learnt tag. *)
Lemma msat_propagate_unit_conflict_learnt_ready :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj) (pre post : dbmap)
         (scan_current p watch0 false_lit a0 a1 : Z)
         (tail retained rest : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tail ->
    ms_learnt Mscan = pre ++ (scan_current, co) :: post ->
    2 <= Zlength_aux 2 Z tail ->
    Forall (lit_wf_c n) (a0 :: a1 :: tail) ->
    NoDup (map lit_var_c (a0 :: a1 :: tail)) ->
    Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail) ->
    Forall (lit_false (mt_assigns (ms_core Mscan)))
      (watch0 :: false_lit :: tail) ->
    false_lit = lit_neg_c p ->
    (forall v, 0 <= v < n ->
       Znth v (ms_reason_words Mscan) 0 <> scan_current) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)) ->
    ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0)) ->
    propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail) =
      watch0 :: false_lit :: tail ->
    propagation_unit_conflict_ready n F A_arr K Mscan p scan_current watch0
      false_lit (a0 :: a1 :: tail) retained rest (ms_prob Mscan)
      (pre ++ (scan_current,
         clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
      (msolver_propagation_db_wmap_update Mscan (ms_prob Mscan)
        (pre ++ (scan_current,
           clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
        (ms_wm Mscan)).
Proof.
  intros n F A_arr K Mscan co pre post scan_current p watch0 false_lit a0 a1
    tail retained rest Hsem Hdbwf Hin Hlits Hlearnt_split Hlen Hall Hnodup
    Hperm Hnew_false H_false_lit Hno_reason_ptr Hentry_perm Hwatchcases
    Hnew_eq.
  pose proof Hsem as Hscan_arms.
  destruct Hscan_arms as [Hlive | Hdead]; [|destruct Hdead as [Hzero _]; lia].
  destruct Hlive as
    [_ [Hweak [Hprop [_ [Hheapcovers [Hreasonless
      [Hlevel [Hp [Hprocessed [Hfrontier _]]]]]]]]]].
  set (new_lits := watch0 :: false_lit :: tail) in *.
  set (co_new := clause_obj_with_lits co new_lits) in *.
  set (learnt_route := pre ++ (scan_current, co_new) :: post) in *.
  set (Mroute := msolver_propagation_db_wmap_update Mscan (ms_prob Mscan)
    learnt_route (ms_wm Mscan)) in *.
  assert (Hdbupdate : db_pair_lits_update (ms_prob Mscan)
      (ms_learnt Mscan) scan_current (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit
        (a0 :: a1 :: tail)) (ms_prob Mscan) learnt_route).
  { right. exists co, pre, post. repeat split; try assumption;
      try reflexivity.
    unfold learnt_route, co_new. rewrite Hnew_eq. reflexivity. }
  pose proof Hdbupdate as Hupdate_lits.
  rewrite Hnew_eq in Hupdate_lits.
  destruct (db_pair_lits_update_learnt_entry_bi__propagate_dbu
    _ _ _ _ _ _ _ Hperm Hupdate_lits) as [Hlearntforward _].
  assert (Hobjnew : obj_wf n co_new).
  { apply (msat_propagate_unit_conflict_new_obj_wf n co watch0 false_lit a0 a1 tail); assumption. }
  assert (Hsplit_old : msolver_db Mscan =
      (ms_prob Mscan ++ pre) ++ (scan_current, co) :: post).
  { unfold msolver_db. rewrite Hlearnt_split.
    rewrite <- app_assoc. reflexivity. }
  assert (Hnewsplit : ms_prob Mscan ++ learnt_route =
      (ms_prob Mscan ++ pre) ++ (scan_current, co_new) :: post).
  { unfold learnt_route. rewrite <- app_assoc. reflexivity. }
  destruct (msat_propagate_unit_conflict_route_db_wf n Mscan co co_new scan_current
      (ms_prob Mscan ++ pre) post (ms_prob Mscan) learnt_route
      Hdbwf Hobjnew Hsplit_old Hnewsplit Hentry_perm)
    as [Hkeys_route [Hlookup_other [Hcases [Hexpected_perm
       [Hselected_route Hdbwf_route]]]]].
  assert (Hdbmatches_old : db_matches_cnf F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_matches)
      (@msa_db_matches). }
  assert (Hdbimplied_old : db_implied F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_implied)
      (@msa_db_implied). }
  assert (Hprobdb_route : prob_db (ms_prob Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_prob_db)
      (@msa_prob_db). }
  assert (Hdbmatches_route : db_matches_cnf F Mroute).
  { unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update, db_matches_cnf; cbn.
    unfold db_matches_cnf in Hdbmatches_old. exact Hdbmatches_old. }
  assert (Hdbimplied_route : db_implied F Mroute).
  { unfold db_implied in Hdbimplied_old |- *.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
    eapply db_implied_entries_transport__propagate_dbu;
      [exact Hlearntforward | exact Hdbimplied_old]. }
  assert (Hdbcomplete_route : db_complete F Mroute).
  { unfold solver_propagation_weak in Hweak.
    destruct Hweak as [_ Hweak].
    assert (Hold : db_complete F Mscan).
    { destruct K; [exact (msw_db_complete Hweak)
                  |exact (msa_db_complete Hweak)]. }
    unfold db_complete in Hold |- *.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn. exact Hold. }
  assert (Hlearntdb_old : learnt_db (ms_learnt Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_learnt_db)
      (@msa_learnt_db). }
  assert (Hlearntdb_route : learnt_db learnt_route).
  { unfold learnt_route, co_new.
    apply learnt_db_replace_lits__propagate_dbu.
    rewrite <- Hlearnt_split. exact Hlearntdb_old. }
  assert (Hentails_new : entails_clause F (denote_obj co_new)).
  { unfold db_implied in Hdbimplied_route.
    rewrite Forall_forall in Hdbimplied_route.
    apply Hdbimplied_route. unfold db_clauses. apply in_map_iff.
    exists (scan_current, co_new). split; [reflexivity|].
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
    unfold learnt_route. apply in_or_app. right. simpl. auto. }
  apply (msat_propagate_unit_conflict_route_ready n F A_arr K Mscan co scan_current p watch0
    false_lit a0 a1 tail retained rest (ms_prob Mscan) learnt_route);
    assumption.
Qed.

(* The rewritten entry lives in ms_prob, so
   db_matches_cnf and db_complete have to be re-proved against the new problem
   list (the new object denotes a permutation of the old clause), while the
   learnt side is untouched. *)
Lemma msat_propagate_unit_conflict_prob_ready :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj) (pre post : dbmap)
         (scan_current p watch0 false_lit a0 a1 : Z)
         (tail retained rest : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tail ->
    ms_prob Mscan = pre ++ (scan_current, co) :: post ->
    2 <= Zlength_aux 2 Z tail ->
    Forall (lit_wf_c n) (a0 :: a1 :: tail) ->
    NoDup (map lit_var_c (a0 :: a1 :: tail)) ->
    Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail) ->
    Forall (lit_false (mt_assigns (ms_core Mscan)))
      (watch0 :: false_lit :: tail) ->
    false_lit = lit_neg_c p ->
    (forall v, 0 <= v < n ->
       Znth v (ms_reason_words Mscan) 0 <> scan_current) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)) ->
    ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0)) ->
    propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail) =
      watch0 :: false_lit :: tail ->
    propagation_unit_conflict_ready n F A_arr K Mscan p scan_current watch0
      false_lit (a0 :: a1 :: tail) retained rest
      (pre ++ (scan_current,
         clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
      (ms_learnt Mscan)
      (msolver_propagation_db_wmap_update Mscan
        (pre ++ (scan_current,
           clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
        (ms_learnt Mscan) (ms_wm Mscan)).
Proof.
  intros n F A_arr K Mscan co pre post scan_current p watch0 false_lit a0 a1
    tail retained rest Hsem Hdbwf Hin Hlits Hprob Hlen Hall Hnodup Hperm
    Hnew_false H_false_lit Hno_reason_ptr Hentry_perm Hwatchcases Hnew_eq.
  pose proof Hsem as Hscan_arms.
  destruct Hscan_arms as [Hlive | Hdead]; [|destruct Hdead as [Hzero _]; lia].
  destruct Hlive as
    [_ [Hweak [Hprop [_ [Hheapcovers [Hreasonless
      [Hlevel [Hp [Hprocessed [Hfrontier _]]]]]]]]]].
  set (new_lits := watch0 :: false_lit :: tail) in *.
  set (co_new := clause_obj_with_lits co new_lits) in *.
  set (prob_route := pre ++ (scan_current, co_new) :: post) in *.
  set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
    (ms_learnt Mscan) (ms_wm Mscan)) in *.
  assert (Hdbupdate : db_pair_lits_update (ms_prob Mscan)
      (ms_learnt Mscan) scan_current (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit
        (a0 :: a1 :: tail)) prob_route (ms_learnt Mscan)).
  { left. exists co, pre, post. repeat split; try assumption.
    unfold prob_route, co_new. rewrite Hnew_eq. reflexivity. }
  pose proof Hdbupdate as Hupdate_lits.
  rewrite Hnew_eq in Hupdate_lits.
  destruct (db_pair_lits_update_prob_entry_bi__propagate_dbu
    _ _ _ _ _ _ _ Hperm Hupdate_lits) as [Hprobforward Hprobreverse].
  assert (Hobjnew : obj_wf n co_new).
  { apply (msat_propagate_unit_conflict_new_obj_wf n co watch0 false_lit a0 a1 tail); assumption. }
  assert (Hsplit_old : msolver_db Mscan =
      pre ++ (scan_current, co) :: (post ++ ms_learnt Mscan)).
  { unfold msolver_db. rewrite Hprob. rewrite <- app_assoc. reflexivity. }
  assert (Hnewsplit : prob_route ++ ms_learnt Mscan =
      pre ++ (scan_current, co_new) :: (post ++ ms_learnt Mscan)).
  { unfold prob_route. rewrite <- app_assoc. reflexivity. }
  destruct (msat_propagate_unit_conflict_route_db_wf n Mscan co co_new scan_current
      pre (post ++ ms_learnt Mscan) prob_route (ms_learnt Mscan)
      Hdbwf Hobjnew Hsplit_old Hnewsplit Hentry_perm)
    as [Hkeys_route [Hlookup_other [Hcases [Hexpected_perm
       [Hselected_route Hdbwf_route]]]]].
  assert (Hdbmatches_old : db_matches_cnf F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_matches)
      (@msa_db_matches). }
  assert (Hdbmatches_route : db_matches_cnf F
      (msolver_propagation_db_wmap_update Mscan prob_route
        (ms_learnt Mscan) (ms_wm Mscan))).
  { unfold db_matches_cnf in Hdbmatches_old |- *. cbn.
    eapply db_matches_entries_transport__propagate_dbu;
      [exact Hprobforward | exact Hdbmatches_old]. }
  assert (Hdbcomplete_old : db_complete F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_complete)
      (@msa_db_complete). }
  assert (Hdbcomplete_route : db_complete F Mroute).
  { unfold db_complete in Hdbcomplete_old |- *.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn.
    eapply db_complete_entries_transport__propagate_dbu;
      [exact Hprobreverse | exact Hdbcomplete_old]. }
  assert (Hprobdb_old : prob_db (ms_prob Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_prob_db)
      (@msa_prob_db). }
  assert (Hprobdb_route : prob_db prob_route).
  { unfold prob_route, co_new.
    apply prob_db_replace_lits__propagate_dbu.
    rewrite <- Hprob. exact Hprobdb_old. }
  assert (Hdbimplied_route : db_implied F Mroute).
  { unfold db_implied, Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn.
    msat_propagate_project_weak_field Hweak K (@msw_db_implied)
      (@msa_db_implied). }
  assert (Hlearntdb_route : learnt_db (ms_learnt Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_learnt_db)
      (@msa_learnt_db). }
  assert (Hentails_new : entails_clause F (denote_obj co_new)).
  { unfold db_matches_cnf in Hdbmatches_route. cbn in Hdbmatches_route.
    rewrite Forall_forall in Hdbmatches_route.
    assert (HCin : In (denote_obj co_new) (db_clauses prob_route)).
    { unfold db_clauses. apply in_map_iff.
      exists (scan_current, co_new). split; [reflexivity|].
      unfold prob_route. apply in_or_app. right. simpl. auto. }
    destruct (Hdbmatches_route _ HCin) as [C0 [HC0 HP0]].
    apply (entails_clause_perm F C0 (denote_obj co_new)).
    - apply Permutation_sym. exact HP0.
    - apply entails_clause_in. exact HC0. }
  apply (msat_propagate_unit_conflict_route_ready n F A_arr K Mscan co scan_current p watch0
    false_lit a0 a1 tail retained rest prob_route (ms_learnt Mscan));
    assumption.
Qed.

Ltac msat_propagate_unit_conflict_route_close Mscan Hdbwf Hin :=
  Intros; split_pure_spatial;
  [ replace (nth (Pos.to_nat 2%positive) (ms_stats Mscan) 0)
      with (Znth 2 (ms_stats Mscan) 0) by reflexivity;
    replace (nth (Pos.to_nat 3%positive) (ms_stats Mscan) 0)
      with (Znth 3 (ms_stats Mscan) 0) by reflexivity;
    unfold PtrArray.seg; cancel;
    apply store_ptr_undef_store_ptr
  | dump_pre_spatial; split; [ | split ];
    [ lia
    | pose proof (db_wf_ptr_pos _ _ _ _ Hdbwf Hin); lia
    | apply clause_ptr_mod2; eapply db_wf_even; [exact Hdbwf | exact Hin] ] ].

(* Returning the head split as an existential lets each arm
   rewrite the spec-level literal list in its own goal with one substitution *)
Lemma msat_propagate_unit_conflict_scan_shape :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj)
         (scan_current p watch0 false_lit : Z)
         (clause_contents : list Z),
    solver_propagation_weak n F A_arr K Mscan ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = clause_contents ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <> 0 ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <>
      lit_sig watch0 ->
    propagation_replacement_scan_inv n Mscan false_lit
      (propagation_normalized_clause watch0 false_lit clause_contents)
      (Zlength (propagation_normalized_clause watch0 false_lit
         clause_contents)) ->
    false_lit = lit_neg_c p ->
    real_watch_pair p clause_contents ->
    watch0 + false_lit =
      Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ->
    exists a0 a1 tail,
      clause_contents = a0 :: a1 :: tail
      /\ 2 <= Zlength_aux 2 Z tail
      /\ Forall (lit_wf_c n) (a0 :: a1 :: tail)
      /\ NoDup (map lit_var_c (a0 :: a1 :: tail))
      /\ propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail)
           = watch0 :: false_lit :: tail
      /\ sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail
      /\ Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail)
      /\ ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0))
      /\ Forall (lit_false (mt_assigns (ms_core Mscan)))
           (watch0 :: false_lit :: tail)
      /\ (forall v, 0 <= v < n ->
            Znth v (ms_reason_words Mscan) 0 <> scan_current)
      /\ (forall l, Permutation (entry_watchers (scan_current, co) l)
            (entry_watchers (scan_current,
               clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)).
Proof.
  intros n F A_arr K Mscan co scan_current p watch0 false_lit
    clause_contents Hweak Hdbwf Hin Hlits Hassigned Hnotsig
    Hscaninv Hfalse_lit Hpair Hwatch0.
  pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin)
    as Hobj.
  unfold obj_wf in Hobj. rewrite Hlits in Hobj.
  destruct Hobj as [Hlen [Hall Hnodup]].
  destruct clause_contents as [|a0 tail0]; cbn in Hlen; [lia|].
  destruct tail0 as [|a1 tail]; cbn in Hlen; [lia|].
  destruct (propagation_normalized_conflict_scan_facts n F A_arr K Mscan co
      scan_current p watch0 false_lit a0 a1 tail
      Hweak Hin Hlits Hall Hassigned Hnotsig
      Hscaninv Hfalse_lit Hpair Hwatch0)
    as [Htail [Hperm [Hwatchcases [_ [Hnew_false [_
       [_ [Hno_reason_ptr Hentry_perm]]]]]]]].
  exists a0, a1, tail.
  split; [reflexivity|]. split; [exact Hlen|]. split; [exact Hall|].
  split; [exact Hnodup|]. split.
  { unfold propagation_normalized_clause. rewrite Htail. reflexivity. }
  split; [exact Htail|]. split; [exact Hperm|].
  split; [exact Hwatchcases|]. split; [exact Hnew_false|].
  split; [exact Hno_reason_ptr|exact Hentry_perm].
Qed.

Tactic Notation "msat_clause_cmp_alias_stop"
    ident(y_pre) ident(x_pre) ident(x_activity) ident(db) ident(activities)
    ident(x_words) constr(rule) :=
  (LLM_pre_process ltac:(lia || int_auto)); subst y_pre;
  bind_fact ( 0 < x_pre ) as H_x_pre;
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2;
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative;
  assert (Hxmod : x_pre mod 2 = 0)
    by (apply rem_two_mod_two__clause_cmp; assumption);
  unfold msat_true;
  sep_apply (rule db activities x_pre x_words x_activity); [cancel | assumption ..].

Ltac msat_clause_cmp_hdr_word_nonneg :=
  (LLM_pre_process ltac:(lia || int_auto));
  apply derivable1s_coq_prop_r;
  apply clause_hdr_word_nonneg;
  apply Zlength_nonneg.

Ltac msat_reducedb_focus_head_clause :=
  (LLM_pre_process ltac:(lia || int_auto));
  match goal with
  | Hdc : db_compaction_inv ?Mc ?ws ?i ?j,
    Hmi : msolver_inv ?n _ _ _ ?Mc |- _ =>
      let cco := fresh "co" in
      let cp := fresh "p" in
      let hinl := fresh "Hinlearnt" in
      let hvar := fresh "Hvar" in
      let htwo := fresh "Htwo" in
      let cpre := fresh "pre" in
      let cpost := fresh "post" in
      let hlearnt := fresh "Hlearnt" in
      let act := fresh "activity" in
      let hclause := fresh "Hclause" in
      ( assert (Hcomp := Hdc);
        destruct Hcomp as [Hj0 [Hji [Hi Hwords]]];
        assert (Hsuffix : In (Znth (i - 0) ws 0)
          (sublist i (Zlength ws) ws))
          by (replace (Znth (i - 0) ws 0) with
                (Znth 0 (sublist i (Zlength ws) ws) 0);
              [ apply Znth_In; rewrite Zlength_sublist by lia; lia
              | symmetry; rewrite Znth_sublist by lia; f_equal; lia ]);
        assert (Hptr : In (Znth (i - 0) ws 0) (map fst (ms_learnt Mc)))
          by (rewrite Hwords; apply in_or_app; right; exact Hsuffix);
        apply in_map_iff in Hptr;
        destruct Hptr as [[cp cco] [Hp hinl]];
        simpl in Hp; subst cp;
        assert (Hin : In (Znth (i - 0) ws 0, cco) (msolver_db Mc))
          by (unfold msolver_db; apply in_or_app; right; exact hinl);
        assert (Hobj : obj_wf n cco)
          by (eapply db_wf_obj; [ exact (msi_db_wf Hmi) | exact Hin ]);
        destruct Hobj as [Hlen [Hwf Hnd]];
        assert (Htag : co_learnt cco = true)
          by (pose proof (msi_learnt_db Hmi) as hlearnt;
              unfold learnt_db in hlearnt;
              rewrite Forall_forall in hlearnt;
              specialize (hlearnt (Znth (i - 0) ws 0, cco) hinl);
              simpl in hlearnt; exact hlearnt);
        assert (Hsize : n = ms_size Mc) by exact (msi_size Hmi);
        assert (Hlit : lit_wf_c n (Znth 0 (co_lits cco) 0))
          by (apply obj_wf_watch0; repeat split; assumption);
        assert (hvar : 0 <= lit_var_c (Znth 0 (co_lits cco) 0) /\
          lit_var_c (Znth 0 (co_lits cco) 0) < n)
          by (apply lit_var_c_in_range; exact Hlit);
        assert (Hvarsize : lit_var_c (Znth 0 (co_lits cco) 0) < ms_size Mc)
          by (rewrite <- Hsize; exact (proj2 hvar));
        destruct (in_split _ _ hinl) as [cpre [cpost Hsplit]];
        assert (Hfocus :
          clause_db_rep (ms_learnt Mc) |--
          MiniSatClause.rep (Znth (i - 0) ws 0) true (co_lits cco) **
          clause_db_pair_remainder db_nil
            (cpre ++ (Znth (i - 0) ws 0, cco) :: cpost)
            (Znth (i - 0) ws 0) true (co_lits cco))
          by (rewrite Hsplit;
              sep_apply (clause_db_rep_app_elim cpre
                ((Znth (i - 0) ws 0, cco) :: cpost));
              change (clause_db_rep cpre **
                (MiniSatClause.rep (Znth (i - 0) ws 0) (co_learnt cco)
                   (co_lits cco) ** clause_db_rep cpost) |--
                MiniSatClause.rep (Znth (i - 0) ws 0) true (co_lits cco) **
                clause_db_pair_remainder db_nil
                  (cpre ++ (Znth (i - 0) ws 0, cco) :: cpost)
                  (Znth (i - 0) ws 0) true (co_lits cco));
              rewrite Htag;
              unfold clause_db_pair_remainder;
              Right; Exists cco cpre cpost;
              unfold db_nil; rewrite clause_db_rep_nil;
              split_pure_spatial;
              [ cancel (clause_db_rep cpre); cancel
              | split_pures; dump_pre_spatial;
                split; [ reflexivity | split; [ reflexivity | exact Htag ] ] ]);
        sep_apply Hfocus;
        unfold MiniSatClause.rep at 1;
        Intros_p hclause;
        destruct hclause as [Hlen0 [Hposw Heven]];
        unfold activity_state at 1;
        Intros act;
        assert (Hhdr : clause_hdr_word true (Zlength (co_lits cco)) / 2 =
          Zlength (co_lits cco))
          by (apply clause_hdr_word_div2; exact Hlen0);
        assert (Hrem : Znth (i - 0) ws 0 % 2 = 0)
          by (assert (htwo : (2 : Z) <> 0) by lia;
              apply (proj2 (Z.rem_divide _ 2 htwo));
              apply (proj1 (Z.mod_divide _ 2 htwo));
              exact Heven);
        assert (Hquot : clause_hdr_word msat_true (Zlength (co_lits cco)) ÷ 2 =
          Zlength (co_lits cco))
          by (unfold msat_true;
              rewrite zdiv_equiv;
              [ exact Hhdr | unfold clause_hdr_word; lia | lia ]);
        Exists (co_lits cco) act;
        split_pure_spatial;
        [ rewrite Hsplit; unfold msat_true;
          cancel (clause_db_pair_remainder db_nil
            (cpre ++ (Znth (i - 0) ws 0, cco) :: cpost)
            (Znth (i - 0) ws 0) true (co_lits cco));
          cancel
        | split_pures; dump_pre_spatial;
          first
            [ assumption
            | lia
            | exact (proj1 hvar)
            | match goal with
              | Hcl : msat_fp64_count_limit _ ?el |- msat_fp64_nonnegative ?el =>
                  apply Hcl; lia
              end ] ] )
  end.

Tactic Notation "msat_reducedb_focus_learnt" constr(n) constr(F) constr(A_arr)
    constr(A_inst) constr(Mc) constr(i) constr(ws) ident(lts) constr(ltsv) constr(act)
    ident(Hinv) ident(Hfp) ident(Hpos) ident(Hev) ident(Hne) :=
  bind_fact ( msolver_inv n F A_arr A_inst Mc ) as Hinv;
  bind_fact ( msat_fp32_nonnegative act ) as Hfp;
  bind_fact ( 0 < Znth (i - 0) ws 0 ) as Hpos;
  bind_fact ( Znth (i - 0) ws 0 % 2 = 0 ) as Hev;
  bind_fact ( Znth (lit_var_c (Znth (0 - 0) ltsv 0) - 0) (ms_reason_words Mc) 0
              <> Znth (i - 0) ws 0 ) as Hne;
      unfold clause_db_pair_remainder;
      Split;
      [ Intros co pre post;
        unfold db_nil in *;
        match goal with
        | Hc : _ /\ _ |- _ =>
            destruct Hc as [Hdb [Hlits Htag]];
            symmetry in Hdb;
            apply app_eq_nil in Hdb;
            destruct Hdb as [_ Hfalse];
            discriminate Hfalse
        end
      | let cco := fresh "co" in
        let cpre := fresh "pre" in
        let cpost := fresh "post" in
        ( Intros cco cpre cpost;
          match goal with
          | Hc : _ /\ _ |- _ =>
          destruct Hc as [Hdb [Hlits Htag]];
          subst lts;
          assert (Hinlearnt : In (Znth (i - 0) ws 0, cco) (ms_learnt Mc))
            by (rewrite Hdb; apply in_or_app; right; simpl; auto);
          assert (Hin : In (Znth (i - 0) ws 0, cco) (msolver_db Mc))
            by (unfold msolver_db; apply in_or_app; right; exact Hinlearnt);
          assert (Hobj : obj_wf n cco)
            by (eapply db_wf_obj; [ exact (msi_db_wf Hinv) | exact Hin ]);
          destruct Hobj as [Hlen [Hwf Hnd]];
          assert (Hdistinct : lit_var_c (Znth 0 (co_lits cco) 0) <>
                              lit_var_c (Znth 1 (co_lits cco) 0))
            by (destruct (co_lits cco) as [|a xs] eqn:Hco;
                [ change (2 <= 0) in Hlen; lia
                | destruct xs as [|b xs];
                  [ change (2 <= 1) in Hlen; lia
                  | inversion Hnd as [|x l Hnot Htail];
                    let heq := fresh "Heq" in
                    ( intro heq; apply Hnot; simpl; left; simpl in heq;
                      symmetry; exact heq ) ] ]);
          assert (Hshape := msi_shape Hinv);
          assert (Hsize : n = ms_size Mc) by exact (msi_size Hinv);
          assert (Hdim : 0 <= ms_size Mc /\ ms_size Mc <= ms_cap Mc /\
            2 * ms_size Mc <= INT_MAX /\ Zlength (ms_stats Mc) = 11)
            by (unfold solver_shape in Hshape; tauto);
          assert (Hreasonlen := solver_shape_reasons_len Mc Hshape);
          assert (Hwmlen := solver_shape_wm_len Mc Hshape);
          assert (Hwatch0 : In (clause_watch_word (Znth (i - 0) ws 0)
            (co_lits cco) (Znth 1 (co_lits cco) 0))
            (Znth (lit_neg_c (Znth 0 (co_lits cco) 0)) (ms_wm Mc) nil))
            by (unfold clause_watch_word;
                destruct (Z.ltb 2 (Zlength (co_lits cco))) eqn:Hbig;
                [ apply Z.ltb_lt in Hbig;
                  assert (Hthree : 3 <= Zlength (co_lits cco)) by lia;
                  exact (wmap_present_real0 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Hthree)
                | apply Z.ltb_ge in Hbig;
                  assert (Htwo : Zlength (co_lits cco) = 2) by lia;
                  exact (wmap_present_bin0 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Htwo) ]);
          assert (Hwatch1 : In (clause_watch_word (Znth (i - 0) ws 0)
            (co_lits cco) (Znth 0 (co_lits cco) 0))
            (Znth (lit_neg_c (Znth 1 (co_lits cco) 0)) (ms_wm Mc) nil))
            by (unfold clause_watch_word;
                destruct (Z.ltb 2 (Zlength (co_lits cco))) eqn:Hbig;
                [ apply Z.ltb_lt in Hbig;
                  assert (Hthree : 3 <= Zlength (co_lits cco)) by lia;
                  exact (wmap_present_real1 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Hthree)
                | apply Z.ltb_ge in Hbig;
                  assert (Htwo : Zlength (co_lits cco) = 2) by lia;
                  exact (wmap_present_bin1 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Htwo) ]);
          assert (Hunlocked : clause_unlocked_words (Znth (i - 0) ws 0)
            (ms_reason_words Mc))
            by (assert (Hreason0 : Znth (lit_var_c (co_watch0 cco))
                  (ms_reason_words Mc) 0 <> Znth (i - 0) ws 0)
                  by (unfold co_watch0; rewrite Z.sub_0_r in Hne; exact Hne);
                eapply solver_simplify_head_unlocked;
                [ exact (msi_weak Hinv) | exact Hin | exact Hreason0 ]);
          unfold clause_remove_pre, solver_wlists_handle,
            clause_remove_ready, clause_unlocked_words;
          Right; Exists cco cpre cpost;
          split_pure_spatial;
          [ cancel (clause_db_rep db_nil);
            sep_apply_r_atomic (clause_rep_refold__reducedb (Znth (i - 0) ws 0)
              (co_lits cco) act (Zlength_nonneg (co_lits cco)) Hpos
              (rem_zero_mod_zero__reducedb _ (Z.lt_le_incl _ _ Hpos) Hev) Hfp);
            cancel
          | split_pures; dump_pre_spatial;
            [ assumption | assumption | assumption | lia | lia
            | rewrite <- Hsize; repeat split; first [ assumption | lia ]
            | split; [ exact Hdb | split; [ reflexivity | exact Htag ] ] ] ]
          end ) ].

Lemma msat_db_compaction_shift :
  forall (words : list Z) (i j : Z),
    0 <= j -> j <= i -> i < Zlength words ->
    sublist 0 j words ++ sublist i (Zlength words) words =
    sublist 0 (j + 1) (replace_Znth j (Znth i words 0) words) ++
    sublist (i + 1) (Zlength words) (replace_Znth j (Znth i words 0) words).
Proof.
  intros words i j Hj Hji Hi.
  set (a := Znth i words 0).
  set (A := sublist 0 j words).
  set (B := sublist (j + 1) (Zlength words) words).
  assert (HA : Zlength A = j).
  { unfold A. apply Zlength_sublist0. lia. }
  assert (HBlen : Zlength B = Zlength words - (j + 1)).
  { unfold B. apply Zlength_sublist. lia. }
  assert (HR : replace_Znth j a words = A ++ a :: B).
  { unfold A, B, a.
    apply (replace_Znth_split j (Znth i words 0) words). lia. }
  assert (HRlen : Zlength (A ++ a :: B) = Zlength words).
  { rewrite <- HR. apply Zlength_replace_Znth. }
  assert (HW : words = A ++ Znth j words 0 :: B).
  { unfold A, B. apply (Znth_split 0 words j). lia. }
  assert (HP : sublist 0 (j + 1) (A ++ a :: B) = A ++ a :: nil).
  { rewrite (sublist_split 0 (j + 1) j (A ++ a :: B)) by lia.
    rewrite (sublist_split_app_l 0 j A (a :: B)) by lia.
    rewrite (sublist_split_app_r j (j + 1) j A (a :: B)) by lia.
    replace (j - j) with 0 by lia.
    replace (j + 1 - j) with 1 by lia.
    f_equal.
    apply sublist_self. symmetry. exact HA. }
  assert (HS : sublist (i + 1) (Zlength words) (A ++ a :: B) =
               sublist (i + 1) (Zlength words) words).
  { rewrite HW at 3.
    rewrite (sublist_split_app_r (i + 1) (Zlength words) j A (a :: B)) by lia.
    rewrite (sublist_split_app_r (i + 1) (Zlength words) j A
      (Znth j words 0 :: B)) by lia.
    rewrite (sublist_cons2 (i + 1 - j) (Zlength words - j) a B) by
      (try lia; rewrite Zlength_cons, HBlen; lia).
    rewrite (sublist_cons2 (i + 1 - j) (Zlength words - j)
      (Znth j words 0) B) by
      (try lia; rewrite Zlength_cons, HBlen; lia).
    reflexivity. }
  rewrite HR, HP, HS.
  rewrite (sublist_split i (Zlength words) (i + 1) words) by lia.
  rewrite (sublist_single 0 i words) by lia.
  unfold a.
  rewrite app_assoc.
  simpl. reflexivity.
Qed.

Tactic Notation "msat_search_model_copy_entry" ident(hr) ident(nn)
  ident(ff) ident(aa) ident(ai) ident(ms) :=
  bind_fact ( solver_search_model_ready nn ff aa ai ms ) as hr;
  msat_search_close_model_copy_entry_facts hr nn ff aa ai ms.

Tactic Notation "msat_search_cla_inc_nonneg" ident(hinv) ident(nn)
  ident(ff) ident(aa) ident(ai) ident(mr) :=
  (LLM_pre_process ltac:(lia || int_auto));
  bind_fact ( msolver_inv nn ff aa ai mr ) as hinv;
  split_pures; dump_pre_spatial;
  [ auto | exact (@msi_cla_inc_nonnegative nn ff aa ai mr hinv) ].

Ltac msat_search_selection_state_range :=
  (LLM_pre_process ltac:(lia || int_auto));
  match goal with
  | Hs : solver_search_selection_state _ _ _ _ _ _ |- _ =>
      unfold solver_search_selection_state in Hs;
      destruct Hs as [Hinv Hrest1];
      destruct Hrest1 as [Hlevel Hrest2];
      destruct Hrest2 as [Hwatch Hrest3];
      destruct Hrest3 as [Hreason Hrest4];
      destruct Hrest4 as [Hpending Hrest5];
      destruct Hrest5 as [Hqtail Hrest6];
      destruct Hrest6 as [Hseed Hrest7];
      destruct Hrest7 as [Hmodel Hrest8];
      destruct Hrest8 as [Hfinite Hrest9];
      destruct Hrest9 as [H2n Hrest10];
      destruct Hrest10 as [Hrange Hrest11];
      destruct Hrest11 as [Hnth Hheap];
      destruct Hrange as [Hretval7 Hretval7_lt];
      (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)])
  end.

Ltac msat_search_decision_lit_var_entail :=
  (LLM_pre_process ltac:(lia || int_auto));
  match goal with
  | H2 : ?r2 = lit_neg_c ?rw,
    H7 : ?rw = ?rv + ?rv,
    He : enqueue_input _ _ _ _ _ _ _,
    Hs : solver_search_selection_state _ _ _ _ ?rv ?Ms |- _ =>
      msat_search_close_decision_lit_var_entail H2 H7 He Hs r2 rv Ms
  end.

Lemma msat_stats_starts_refold :
  forall p st v,
    Zlength st = 11 ->
    (&( p # "stats_t" ->ₛ "starts") # UInt64 |-> v) **
    stats_without_starts_rep p st
    |-- stats_rep p (replace_Znth 0 v st).
Proof.
  intros p st v Hlen.
  unfold stats_without_starts_rep, stats_rep.
  unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals.
  rewrite Zlength_replace_Znth.
  rewrite (Znth_replace_Znth_Same 0 st 0 v) by lia.
  rewrite !Znth_replace_Znth_Diff by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma msat_forall_zero_repeat :
  forall xs : list Z,
    Forall (fun z => z = 0) xs -> xs = repeat 0 (length xs).
Proof.
  intros xs Hxs. induction Hxs; simpl.
  - reflexivity.
  - subst x. f_equal. exact IHHxs.
Qed.

Ltac msat_addclause_shape_spatial_close :=
  ac_shape;
  ac_sign;
  ac_spatial;
  try dump_pre_spatial;
  try solve [auto | ac_close].

(* Length
   bounds rule out an empty tail; establish last < x before spatial closing.
   Substitute the call-return index equations before simplifying the
   unchanged assignment-cell write. *)
Tactic Notation "msat_addclause_dedup_keep" ident(sortl) ident(inpt)
    ident(tll) ident(keptl) ident(qidx) ident(kidx) ident(lastv) ident(msol)
    ident(endv) :=
  assert (Hl : Zlength sortl = Zlength inpt)
    by (eapply Permutation_Zlength_Z; eassumption);
  destruct tll as [| junk tl];
  [ exfalso; rewrite app_nil_r in *; lia
  | rewrite ?Z.sub_0_r in *;
    match goal with H : Zlength keptl = qidx |- _ => rewrite <- H in * end;
    assert (Hin : In (Znth kidx (keptl ++ junk :: tl) 0) inpt)
      by (eapply all_from_Znth; ac_prem);
    assert (Hlt : lastv < Znth kidx (keptl ++ junk :: tl) 0)
      by (eapply dedup_keep_bound with (src := sortl) (q := Zlength keptl)
            (n := Zlength inpt); ac_prem);
    assert (Hge : all_ge (Znth kidx (keptl ++ junk :: tl) 0)
                         (sublist (kidx + 1) (Zlength inpt) sortl))
      by (eapply dedup_keep_all_ge with (src := sortl) (q := Zlength keptl);
          ac_prem);
    assert (Htl : tl = sublist (Zlength keptl + 1) (Zlength inpt) sortl)
      by (eapply sublist_tail_of with (hd := junk) (n := Zlength inpt); ac_prem);
    assert (Hass : Znth (lit_var_c (Znth kidx (keptl ++ junk :: tl) 0))
                        (mt_assigns (ms_core msol)) 0 = 0)
      by (repeat match goal with
                 | Hr : ?r = lit_var_c _ |- _ => is_var r; rewrite Hr in *; clear Hr
                 end;
          first
            [ match goal with
              | H : Znth (lit_var_c _) _ 0 = 0 |- _ =>
                  exact H
              end
            | match goal with
              | H : context[replace_Znth ?i (Znth ?i ?l 0) ?l] |- _ =>
                  rewrite (replace_Znth_same i l 0) in H; [ exact H | ac_lia ]
              end ]);
    assert (Hcursor : Znth kidx (keptl ++ junk :: tl) 0 = Znth kidx sortl 0)
      by (eapply Znth_buffer_eq_src with
            (q := Zlength keptl) (n := Zlength inpt); ac_prem);
    match goal with
    | Hp : addclause_prefix_equiv ?F (sublist 0 kidx sortl) keptl |- _ =>
        assert (Hprefix_next : addclause_prefix_equiv F
            (sublist 0 (kidx + 1) sortl)
            (keptl ++ (Znth kidx (keptl ++ junk :: tl) 0 :: nil)))
          by (rewrite (sublist_snoc 0) by lia; rewrite <- Hcursor;
              apply addclause_prefix_keep; exact Hp)
    end;
    rewrite replace_Znth_hole;
    Exists tl (keptl ++ Znth kidx (keptl ++ junk :: tl) 0 :: nil)
              (Zlength keptl + 1) (kidx + 1);
    rewrite <- app_assoc; simpl app;
    match goal with H : endv = _ |- _ => rewrite <- H in * end;
    split_pure_spatial;
    [ msat_cancel_sound; lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel
    | split_pures; dump_pre_spatial;
      solve [ auto
            | ac_close
            | ac_lia
            | eapply keep_forall; ac_prem
            | eapply keep_all_from; ac_prem
            | eapply addclause_dedup_step; ac_prem ] ] ].

Tactic Notation "msat_addclause_dedup_skip" ident(sorted) ident(input)
    ident(tl) ident(kept) ident(q) ident(k) ident(endv) :=
  assert (Hl : Zlength sorted = Zlength input)
    by (eapply Permutation_Zlength_Z; eassumption);
  rewrite ?Z.sub_0_r in *;
  repeat match goal with
  | H : ?r = lit_var_c _ |- _ => is_var r; subst r
  end;
  ac_selfrepl;
  assert (Hcursor : Znth k (kept ++ tl) 0 = Znth k sorted 0)
    by (eapply (Znth_buffer_eq_src kept tl sorted q (Zlength input) k); ac_prem);
  match goal with
  | Hp : addclause_prefix_equiv ?F (sublist 0 k sorted) kept,
    HI : solver_support_inv _ ?F _ _ _ ?M |- _ =>
      assert (Hprefix_next : addclause_prefix_equiv F
          (sublist 0 (k + 1) sorted) kept)
        by (rewrite (sublist_snoc 0) by lia; rewrite <- Hcursor;
            first
            [ solve [eapply addclause_prefix_duplicate; [exact Hp |];
                     eapply addclause_last_member; [congruence | ac_arith]]
            | eapply addclause_prefix_false; [exact Hp |];
              eapply (addclause_root_false (ms_size M) F (ms_core M));
                [exact (msi_trail_wf HI) | exact (msi_trail_impl HI) |
                 eassumption | eassumption |];
              eapply (addclause_assigned_false (ms_size M) (ms_core M));
                [exact (msi_trail_wf HI) | eassumption | ac_arith |];
              unfold lit_sig; unfold lit_sign_c in *;
              destruct (Z.odd (Znth k (kept ++ tl) 0)); simpl in *; lia ])
  end;
  Exists tl kept q (k + 1);
  match goal with H : endv = _ |- _ => rewrite <- H in * end;
  split_pure_spatial;
  [ cancel (&( "endvar") # Ptr |-> endv); cancel
  | split_pures; dump_pre_spatial;
    solve [ auto | ac_close | eapply all_ge_tail; [ lia | lia | lia | eassumption ] ] ].

Ltac ac_completed :=
  first [ assumption | intro Hentry;
    first [ assumption | tauto
    | apply minisat_watch_completed_addclause_finish__api_reentry; tauto
    | match goal with
      | HI : solver_support_inv ?n _ _ _ _ ?M |-
          minisat_watch_completed (msolver_enqueue_fresh ?M ?l ?r ?ro) =>
        eapply (minisat_watch_completed_enqueue_fresh__api_reentry n M l r ro);
          [exact (msw_db_wf (msi_weak HI)) | exact (msi_trail_wf HI) |
           eassumption | eassumption | tauto]
      end ] ].

Ltac ac_support_transition :=
  unfold addclause_support_transition;
  split; [unfold addclause_transition | ac_completed].

(* Avoid repeat split on the transition: it would unfold and
   fragment msolver_inv. *)
Tactic Notation "msat_addclause_return_frame" ident(M) ident(kept) ident(tl)
    ident(F) tactic0(arm) :=
  unfold addclause_support_post_at;
  Exists M (kept ++ tl) F;
  split_pure_spatial;
  [ sep_apply solver_assigns_focus_close_levels_wl;
    sep_apply solver_rep_growable_of_wl;
    cancel
  | dump_pre_spatial; ac_support_transition;
    split; [ assumption |];
    split; [ assumption |];
    split; [ assumption |];
    split; [ change (2 * ms_cap M <= INT_MAX); assumption |];
    split; [ intros _; split; [ assumption | split; assumption ] |];
    arm ].

Ltac msat_addclause_entailed_return M kept tail Hent :=
  lazymatch type of Hent with entails_clause ?F _ =>
    msat_addclause_return_frame M kept tail F
      (right; split; [reflexivity |]; split; [assumption |];
       apply addclause_entailed_equiv; exact Hent)
  end.

Ltac msat_addclause_root_input M Hin :=
  eapply addclause_root_satisfied_input; [exact Hin |];
  match goal with HI : solver_support_inv _ _ _ _ 0 M |- _ =>
    eapply addclause_root_true;
      [exact (msi_trail_wf HI) | exact (msi_trail_impl HI) |
       eassumption | eassumption |]
  end.

Ltac msat_addclause_sort_cursor_close :=
  msat_split_after_llm; ac_shape; ac_sign; ac_spatial;
  (Intros; split_pures; dump_pre_spatial; solve [auto | (ac_close)]).

Ltac msat_simplify_propagation_frame Msp Mp sp ap lp wl :=
  let Hempty := fresh "H_model_empty" in
  let Hpositive := fresh "H_decay_positive" in
  bind_fact ( ms_model Msp = nil -> ms_model Mp = nil ) as Hempty;
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Msp) ->
    msat_fp32_positive_finite (ms_cla_decay Mp) ) as Hpositive;
  unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at;
  sep_apply_l_atomic
    (solver_rep_assigns_levels_at_levels_at sp Mp ap lp wl);
  Left;
  Exists Mp;
  apply split_pure_and_spatial_goals;
  [ dump_pre_spatial; reflexivity
  | split_pure_spatial;
    [ cancel
    | dump_pre_spatial;
      repeat match goal with |- _ /\ _ => split end;
      solve [auto | lia] ] ].

(* ===== solver_simplify delete-step helpers ===== *)
Lemma msat_simplify13_db_rest_after_remove :
  forall s type b Mcur c wm' stats' reasons lvl wl asg,
    (type = 0 /\ b = false) \/ (type = 1 /\ b = true) ->
    solver_simplify_db_rest_at s type
      (msolver_remove_clause Mcur b c wm' stats') reasons lvl wl asg =
    (&(s # "solver_t" ->ₛ "size") # Int |-> ms_size Mcur **
     solver_wlists_handle s wl **
     wlists_rep wl (ms_size Mcur) wm' **
     &(s # "solver_t" ->ₛ "reasons") # Ptr |-> reasons **
     PtrArray.seg reasons 0 (ms_size Mcur) (ms_reason_words Mcur) **
     solver_ptr_tail reasons (ms_size Mcur) (ms_cap Mcur) **
     stats_rep &(s # "solver_t" ->ₛ "stats") stats' **
     solver_simplify_clause_frame_at s type Mcur asg lvl).
Proof.
  intros s type b Mcur c wm' stats' reasons lvl wl asg Htype.
  unfold solver_simplify_db_rest_at, solver_simplify_clause_frame_at,
    clause_new_scalars_frame, solver_fp_rep, solver_other_db_vec_rep,
    solver_levels_slice_at, solver_other_clause_db_rep.
  destruct Htype as [[-> ->] | [-> ->]];
    cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ]; reflexivity.
Qed.

Lemma msat_simplify13_delete_step_from_inv :
  forall n F A_arr type b Mcur words i jcur wm' stats',
    b = solver_selected_is_learnt type ->
    msolver_inv_assuming_strong n F A_arr A_arr Mcur ->
    msolver_inv_assuming_strong n F A_arr A_arr
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') ->
    Zlength (mt_lim (ms_core Mcur)) = 0 ->
    mt_qhead (ms_core Mcur) = ms_qtail Mcur ->
    ms_capacity_root_propagation_pending Mcur = 0 ->
    msolver_seed_shadow Mcur ->
    solver_simplify_db_compaction_inv type Mcur words i jcur ->
    i < Zlength words ->
    solver_simplify_compaction_step n F A_arr type Mcur words i jcur
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') words jcur.
Proof.
  intros n F A_arr type b Mcur words i jcur wm' stats'
    Hb H_msolver_inv Hinvnext H_Zlength H_mt_qhead
    H_ms_capacity_root_propagation_pending H_msolver_seed_shadow
    H_solver_simplify_db_compaction_inv H_i.
  pose proof (solver_assuming_level_zero_normalized__api_reentry
    n F A_arr Mcur H_msolver_inv H_Zlength) as Hnormal.
  subst b.
  set (Mnext := msolver_remove_clause Mcur (solver_selected_is_learnt type)
    (Znth i words 0) wm' stats').
  assert (Hlimnext : Zlength (mt_lim (ms_core Mnext)) = 0).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_Zlength. }
  assert (Hqnext : mt_qhead (ms_core Mnext) = ms_qtail Mnext).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_mt_qhead. }
  assert (Hpendingnext :
      ms_capacity_root_propagation_pending Mnext = 0).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_ms_capacity_root_propagation_pending. }
  assert (Hseednext : msolver_seed_shadow Mnext).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_msolver_seed_shadow. }
  assert (Hmodelnext : ms_model Mnext = ms_model Mcur).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    reflexivity. }
  assert (Hdecaynext : ms_cla_decay Mnext = ms_cla_decay Mcur).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    reflexivity. }
  assert (Hcompnext : solver_simplify_db_compaction_inv type Mnext
      words (i + 1) jcur).
  { unfold Mnext.
    exact (solver_simplify_db_compaction_inv_remove__simplify
      n F A_arr (@nil literal) type (msolver_set_root Mcur 0) words i jcur
      (Znth i words 0) wm' stats' (msi_weak Hnormal)
      H_solver_simplify_db_compaction_inv H_i eq_refl). }
  unfold solver_simplify_compaction_step.
  split.
  - right. split; [reflexivity |]. split; [reflexivity |].
    exists wm', stats'. unfold solver_simplify_delete_transition.
    split.
    + unfold Mnext. reflexivity.
    + split; [exact Hinvnext |].
      split; [exact Hlimnext |].
      split; [exact Hqnext |].
      split; [exact Hpendingnext |].
      exact Hseednext.
  - split; [exact Hinvnext |].
    split; [exact Hlimnext |].
    split; [exact Hqnext |].
    split; [exact Hpendingnext |].
    split; [exact Hseednext |].
    split; [exact Hmodelnext |].
    split; [exact Hdecaynext | exact Hcompnext].
Qed.

Lemma msat_simplify13_delete_arm_facts :
  forall n F A_arr type b Mcur words i jcur co co1 pre post wm' stats',
    (type = 0 /\ b = false) \/ (type = 1 /\ b = true) ->
    msolver_inv_assuming_strong n F A_arr A_arr Mcur ->
    solver_selected_db type Mcur = pre ++ (Znth i words 0, co1) :: post ->
    db_lookup (solver_selected_db type Mcur) (Znth i words 0) co ->
    clause_simplify_result (co_lits co) (mt_assigns (ms_core Mcur)) 1 ->
    Zlength (mt_lim (ms_core Mcur)) = 0 ->
    mt_qhead (ms_core Mcur) = ms_qtail Mcur ->
    ms_capacity_root_propagation_pending Mcur = 0 ->
    msolver_seed_shadow Mcur ->
    solver_simplify_db_compaction_inv type Mcur words i jcur ->
    i < Zlength words ->
    clause_remove_result (Znth i words 0) (co_lits co) (ms_wm Mcur) wm' ->
    Zlength stats' = 11 ->
    clause_unlocked_words (Znth i words 0) (ms_reason_words Mcur) ->
    co1 = co /\
    solver_selected_db type
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') = pre ++ post /\
    solver_simplify_compaction_step n F A_arr type Mcur words i jcur
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') words jcur.
Proof.
  intros n F A_arr type b Mcur words i jcur co co1 pre post wm' stats'
    Htype H_msolver_inv Hsplit H_db_lookup H_clause_simplify_result
    H_Zlength H_mt_qhead H_ms_capacity_root_propagation_pending
    H_msolver_seed_shadow H_solver_simplify_db_compaction_inv H_i
    Hremove Hstats Hunlocked.
  assert (Hmain : co1 = co /\
      solver_selected_db type
        (msolver_remove_clause Mcur b (Znth i words 0) wm' stats')
        = pre ++ post /\
      msolver_inv_assuming_strong n F A_arr A_arr
        (msolver_remove_clause Mcur b (Znth i words 0) wm' stats')).
  { destruct Htype as [[-> ->] | [-> ->]].
    - unfold solver_selected_db in Hsplit, H_db_lookup.
      simpl in Hsplit, H_db_lookup.
      assert (Hin1 : In (Znth i words 0, co1) (msolver_db Mcur)).
      { unfold msolver_db. apply in_or_app. left. rewrite Hsplit.
        apply in_or_app. right. left. reflexivity. }
      assert (Hinco : In (Znth i words 0, co) (msolver_db Mcur)).
      { unfold db_lookup in H_db_lookup. unfold msolver_db.
        apply in_or_app. left. exact H_db_lookup. }
      assert (Heq : co1 = co).
      { eapply db_wf_lookup_unique.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hin1.
        - exact Hinco. }
      subst co1.
      assert (Hfresh : ~ In (Znth i words 0) (map fst pre)).
      { eapply db_wf_prob_split_fresh__simplify.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hsplit. }
      assert (Hobj : obj_wf n co).
      { eapply db_wf_obj.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hinco. }
      assert (Hroot : root_satisfied (ms_core Mcur) (denote_obj co)).
      { unfold denote_obj.
        eapply clause_simplify_result_root_satisfied__simplify.
        - exact (msa_trail_wf (msas_weak H_msolver_inv)).
        - exact H_Zlength.
        - exact (proj1 (proj2 Hobj)).
        - exact H_clause_simplify_result. }
      split; [reflexivity |]. split.
      { unfold solver_selected_db, msolver_remove_clause,
          msolver_propagation_overlay, msolver_propagation_update.
        cbn. rewrite Hsplit.
        apply db_remove_ptr_split__reducedb. exact Hfresh. }
      { eapply solver_assuming_remove_problem_at_zero__api_reentry.
        - exact H_msolver_inv.
        - exact H_Zlength.
        - exact Hsplit.
        - exact Hfresh.
        - exact Hremove.
        - exact Hstats.
        - exact Hunlocked.
        - exact Hroot. }
    - unfold solver_selected_db in Hsplit, H_db_lookup.
      simpl in Hsplit, H_db_lookup.
      assert (Hin1 : In (Znth i words 0, co1) (msolver_db Mcur)).
      { unfold msolver_db. apply in_or_app. right. rewrite Hsplit.
        apply in_or_app. right. left. reflexivity. }
      assert (Hinco : In (Znth i words 0, co) (msolver_db Mcur)).
      { unfold db_lookup in H_db_lookup. unfold msolver_db.
        apply in_or_app. right. exact H_db_lookup. }
      assert (Heq : co1 = co).
      { eapply db_wf_lookup_unique.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hin1.
        - exact Hinco. }
      subst co1.
      assert (Hfresh : ~ In (Znth i words 0) (map fst pre)).
      { eapply db_wf_learnt_split_fresh__reducedb.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hsplit. }
      split; [reflexivity |]. split.
      { unfold solver_selected_db, msolver_remove_clause,
          msolver_propagation_overlay, msolver_propagation_update.
        cbn. rewrite Hsplit.
        apply db_remove_ptr_split__reducedb. exact Hfresh. }
      { eapply solver_assuming_remove_learnt_at_zero__api_reentry.
        - exact H_msolver_inv.
        - exact H_Zlength.
        - exact Hsplit.
        - exact Hfresh.
        - exact Hremove.
        - exact Hstats.
        - exact Hunlocked. } }
  destruct Hmain as [Heq [Hdbnext Hinvnext]].
  split; [exact Heq |]. split; [exact Hdbnext |].
  eapply msat_simplify13_delete_step_from_inv;
    [ | exact H_msolver_inv | exact Hinvnext | exact H_Zlength
    | exact H_mt_qhead | exact H_ms_capacity_root_propagation_pending
    | exact H_msolver_seed_shadow
    | exact H_solver_simplify_db_compaction_inv | exact H_i ].
  destruct Htype as [[-> ->] | [-> ->]]; reflexivity.
Qed.

Lemma msat_simplify_close_learnt :
  forall s M reasons lvl wl asg,
  mt_lim (ms_core M) = (@nil Z) ->
  solver_shape M ->
  Vecp.rep (solver_selected_vec s 1)
    (db_words (solver_selected_db 1 M)) **
  clause_db_rep (solver_selected_db 1 M) **
  &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  Veci.rep &(s # "solver_t" ->ₛ "trail_lim") (@nil Z) **
  solver_simplify_db_rest_at s 1 M reasons lvl wl asg
  |-- solver_rep_reasons_levels_wl_at s M reasons lvl wl.
Proof.
  intros s M reasons lvl wl asg Hlim Hshape.
  unfold solver_rep_reasons_levels_wl_at.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_db_rest_at,
    solver_simplify_clause_frame_at, solver_selected_vec, solver_selected_db,
    solver_other_db_vec_rep, solver_other_clause_db_rep,
    solver_wlists_handle, solver_scalars_rep, clause_new_scalars_frame,
    solver_vecs_rep, solver_trail_array_rep, solver_levels_slice_at, db_words.
  Intros act opos trl tgs.
  Exists act asg opos trl tgs.
  cbn. rewrite Hlim. msat_manual_entailer_with lia.
Qed.

Tactic Notation "msat_solve_assign_cell_not_int_min" ident(rv) :=
  match goal with
  | Hs : msolver_inv_assuming_strong _ _ _ (assumption_prefix ?raw ?k) ?Mc |- _ =>
      msat_solve_close_assign_cell_not_int_min Hs raw k Mc rv
  end.

Tactic Notation "msat_solve_lbool_cell_arm" ident(mc) ident(rv) :=
  match goal with
  | H : msolver_inv_assuming_strong _ _ _ _ _ |- _ =>
      assert (lbool_cell (Znth rv (mt_assigns (ms_core mc)) 0)) as Hcell0
        by (apply (Forall_Znth_elim _ _ _ 0 rv
              (mtw_cells (msa_trail_wf (msas_weak H)))); lia)
  end;
  match goal with
  | Hc : lbool_cell _ |- _ =>
      unfold lbool_cell in Hc; destruct Hc as [Hv | [Hv | Hv]]
  end;
  rewrite Z.sub_0_r;
  rewrite signed_last_nbits_eq by lia;
  msat_manual_entailer_with ltac:(lia).

Tactic Notation "msat_solve_selector_join"
    ident(kk) ident(rw) ident(mc) ident(nn) ident(rv2) :=
  repeat rewrite Z.sub_0_r in *;
  subst rv2;
  assert (Hcell : lbool_cell
    (Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0))
    by (eapply Forall_Znth_elim;
        [ match goal with
          | H : msolver_inv_assuming_strong _ _ _ _ mc |- _ =>
              exact (mtw_cells (msa_trail_wf (msas_weak H)))
          end
        | match goal with
          | H : Zlength (mt_assigns (ms_core mc)) = _ |- _ => rewrite H
          end;
          assert (Hwf : lit_wf_c nn (Znth kk rw 0))
            by (apply Forall_lit_wf_Znth; [assumption | lia]);
          exact (lit_var_c_in_range _ _ Hwf) ]);
  assert (Hrepr : signed_last_nbits
    (Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0) 8 =
    Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0)
    by (apply signed_last_nbits_eq; [lia |];
        unfold lbool_cell in Hcell;
        destruct Hcell as [Hc | [Hc | Hc]]; rewrite Hc; lia);
  assert (Hreprn : signed_last_nbits
    (-Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0) 8 =
    -Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0)
    by (apply signed_last_nbits_eq; [lia |];
        unfold lbool_cell in Hcell;
        destruct Hcell as [Hc | [Hc | Hc]]; rewrite Hc; lia);
  rewrite ?Hrepr, ?Hreprn;
  assert (Hnonempty : rw <> nil)
    by (intro E; subst rw; rewrite Zlength_nil in *; lia);
  pose proof (lit_sign_c_range (Znth kk rw 0));
  (repeat split; solve [auto | (nia)]).

Tactic Notation "msat_solve_assume_fresh_pure" :=
  (LLM_pre_process ltac:(lia || int_auto));
  unfold assumption_fresh_ready in *;
  split_pures; dump_pre_spatial;
  rewrite ?Z.sub_0_r;
  match goal with H : ms_size _ = _ |- _ => rewrite ?H end;
  solve [reflexivity | tauto].

Ltac msat_restore_array_read merge_segment p index len words :=
  sep_apply (merge_segment p 0 index len (Znth index words 0) words ltac:(lia));
  rewrite Z.sub_0_r, ?replace_Znth_Znth.

Tactic Notation "msat_removable_scratch_carry" constr(Mnext)
    constr(Hready) constr(Hseed) "as" ident(Hreadyout) ident(Hseedout)
    ident(Hequivout) :=
  lazymatch type of Hready with
  | analysis_cancel_ready ?n ?F ?A ?K ?M ?focus =>
      assert (Hreadyout : analysis_cancel_ready n F A K Mnext focus)
        by (change (analysis_cancel_ready n F A K M focus); exact Hready);
      assert (Hseedout : msolver_seed_shadow Mnext)
        by (change (msolver_seed_shadow M); exact Hseed);
      assert (Hequivout : analysis_core_equiv M Mnext)
        by (unfold analysis_core_equiv; repeat split; reflexivity)
  end.

Tactic Notation "msat_lit_var_parity_bounds" ident(x) :=
  msat_split_after_llm;
  dump_pre_spatial;
  unfold lit_var_c in *;
  pose proof (Z.div_mod x 2 ltac:(lia));
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)); lia.

Ltac msat_lit_removable_retval_var_bounds retval retval_7 stack_now M0 lrm_n Hv Hw Hlo Hhi :=
  bind_fact ( retval = lit_var_c retval_7 ) as Hv;
  bind_fact ( retval_7 = tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) ) as Hw;
  bind_fact ( 0 <= lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) ) as
      Hlo;
  bind_fact ( lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) < lrm_n )
      as Hhi;
  assert (Hretval_nonneg : 0 <= retval) by (rewrite Hv, Hw; exact Hlo);
  assert (Hretval_bound : retval < lrm_n) by (rewrite Hv, Hw; exact Hhi);
  (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).

Ltac msat_lit_removable_lits_pointer_even cn Mm cc lrn cw :=
  let Hdb_bin := fresh "Hdb_bin" in
  let Hdb := fresh "Hdb" in
  let Hptr_wf := fresh "Hptr_wf" in
  let Hpos := fresh "Hpos" in
  let Heven := fresh "Heven" in
  let Hrem := fresh "Hrem" in
  match goal with
  | Hready : analysis_cancel_ready ?n0 ?F0 ?A0 ?K0 ?M1 ?focus0 |- _ =>
      pose proof
        (analysis_cancel_ready_db_binary__lit_removable
          n0 F0 A0 K0 M1 focus0 Hready) as Hdb_bin
  end;
  destruct Hdb_bin as [Hdb _];
  prop_apply_p
    (clause_db_pair_remainder_ptr_wf__lit_removable
      cn (ms_prob Mm) (ms_learnt Mm) cc lrn cw Hdb);
  Intros_p Hptr_wf;
  destruct Hptr_wf as [Hpos Heven];
  assert (Hrem : Z.rem cc 2 = 0)
    by (apply Z.rem_divide; [lia |];
        apply Z.mod_divide; [lia | exact Heven]);
  unfold clause_lits_pointer;
  (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).

Ltac msat_analyze_scan_count_bound :=
  (LLM_pre_process ltac:(lia || nia || int_auto));
  match goal with
  | H : analyze_clause_scan_inv _ _ _ _ _ ?M _ _ _ _ _ _ _ _ _ ?Sc ?Rc ?ls _ ?c
    |- _ => msat_analyze_bound_scan_count_by_tagged H c Sc Rc M ls
  end.

Lemma msat_analyze_cancel_ready_core :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z),
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\
    Zlength (mt_lim (ms_core M)) <= n /\
    0 <= ms_root_level M /\
    Zlength (mt_trail (ms_core M)) = ms_qtail M /\
    ms_binary M <> 0 /\
    db_wf n (msolver_db M) /\
    (Zlength (ms_orderpos M) = ms_size M ->
     Zlength (ms_activity M) = ms_size M ->
     Zlength (ms_tags M) = ms_size M ->
     Zlength (ms_stats M) = 11 ->
     solver_shape M).
Proof.
  intros n F A_arr K M focus H_analysis_cancel_ready.
  pose proof H_analysis_cancel_ready as Hready.
  destruct Hready as [Mbase [Hcancel [Hequiv _]]].
  destruct Hcancel as [[_ Hinv] _].
  assert (Hshape_base : solver_shape Mbase).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_shape Hinv).
    - exact (msa_shape Hinv).
  }
  assert (Htrail_base : mtrail_wf n (ms_core Mbase)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_trail_wf Hinv).
    - exact (msa_trail_wf Hinv).
  }
  assert (Hlim_base : Zlength (mt_lim (ms_core Mbase)) <= n).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_level_bound Hinv).
    - exact (msa_level_bound Hinv).
  }
  assert (Hdb_base : db_wf n (msolver_db Mbase)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_db_wf Hinv).
    - exact (msa_db_wf Hinv).
  }
  assert (Hqtail_eq : ms_qtail M = ms_qtail Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hcore_eq : ms_core M = ms_core Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hroot_eq : ms_root_level M = ms_root_level Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hbinary_eq : ms_binary M = ms_binary Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hprob_eq : ms_prob M = ms_prob Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hlearnt_eq : ms_learnt M = ms_learnt Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Htrail : mtrail_wf n (ms_core M)).
  { rewrite Hcore_eq. exact Htrail_base. }
  assert (Hlim : Zlength (mt_lim (ms_core M)) <= n).
  { rewrite Hcore_eq. exact Hlim_base. }
  assert (Hroot_nonnegative : 0 <= ms_root_level M).
  {
    assert (0 <= ms_root_level Mbase)
      by (unfold solver_shape in Hshape_base; tauto).
    rewrite Hroot_eq. assumption.
  }
  assert (Htrail_length :
    Zlength (mt_trail (ms_core M)) = ms_qtail M).
  {
    assert (Zlength (mt_trail (ms_core Mbase)) = ms_qtail Mbase)
      by (unfold solver_shape in Hshape_base; tauto).
    rewrite Hcore_eq, Hqtail_eq. assumption.
  }
  assert (Hbinary_nonzero : ms_binary M <> 0).
  {
    assert (ms_binary Mbase <> 0)
      by (unfold solver_shape in Hshape_base; tauto).
    rewrite Hbinary_eq. assumption.
  }
  assert (Hdb : db_wf n (msolver_db M)).
  {
    unfold msolver_db in *.
    rewrite Hprob_eq, Hlearnt_eq.
    exact Hdb_base.
  }
  split; [exact Htrail |].
  split; [exact Hlim |].
  split; [exact Hroot_nonnegative |].
  split; [exact Htrail_length |].
  split; [exact Hbinary_nonzero |].
  split; [exact Hdb |].
  intros Horder_shape Hactivity_shape Htags_shape Hstats_shape.
  unfold solver_shape in Hshape_base |- *.
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason &
     Eprob & Elearnt & Ebinary &
     Ebinarylits & Ewm & Emodel &
     Ecladecay & Eseed & Ependingq & Epending & Esimpassigns &
     Esimpprops).
  rewrite Horder_shape, Hactivity_shape, Htags_shape, Hstats_shape,
    Esize, Ecap, Eqtail, Ecore, Eroot, Ewords, Ebinary,
    Ebinarylits, Ewm, Ependingq, Epending.
  tauto.
Qed.

Lemma msat_analyze_e7_pending_split :
  forall (n : Z) (F : cnf) (M : msolver) (x cnt : Z)
         (S0 R0 : list Z) (learnt0 : clause),
    analyze_inv F (msolver_view n M) S0 R0 learnt0 ->
    In x S0 ->
    cnt + 1 = Zlength S0 ->
    cnt = Zlength (zremove x S0) /\
    Permutation (analyze_tags S0 R0 learnt0)
                (analyze_tags (zremove x S0) (x :: R0) learnt0).
Proof.
  intros n F M x cnt S0 R0 learnt0 Hinv HinS Hcnt.
  assert (HndS0 : NoDup S0).
  {
    pose proof Hinv as Hinv0_fields.
    unfold analyze_inv in Hinv0_fields.
    destruct Hinv0_fields as (_ & Hndtags0 & _).
    unfold analyze_tags in Hndtags0.
    eapply NoDup_app_remove_r. exact Hndtags0.
  }
  pose proof (zremove_split x) as Hremove.
  destruct (Hremove S0 HndS0 HinS)
    as (before & after & HS0 & HremoveS0).
  assert (Hlenremove : cnt = Zlength (zremove x S0)).
  {
    rewrite HremoveS0, Zlength_app.
    rewrite HS0, !Zlength_app, Zlength_cons in Hcnt. lia.
  }
  refine (conj Hlenremove _).
  unfold analyze_tags.
  rewrite HremoveS0, HS0.
  clear HS0 HremoveS0.
  induction before as [|a before IH].
  - cbn. exact (Permutation_middle after
      (R0 ++ map literal_var learnt0) x).
  - cbn. constructor. exact IH.
Qed.

Lemma msat_analyze_e7_ready_semantics :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z),
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\
    stable_view (msolver_view n M) /\
    trail_implied F (ms_core M) /\
    (forall y b,
       assignment (msolver_view n M) y = Some b ->
       level_of (msolver_view n M) y = Some 0 ->
       entails_clause F (satisfying_literal y b :: nil)).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof Hready as Hready_copy.
  unfold analysis_cancel_ready in Hready_copy.
  destruct Hready_copy as
    (Mentry & Hcancel & Hequiv & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  unfold propagation_cancel_ready in Hcancel.
  destruct Hcancel as
    (Hweak & Hprop & Hfocuswf & Hprocessed & Hentryfocus & Hfrontier &
     Hentryheap & Hentrycovers & Hentryearliest).
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as (Hcaproot & Hweak).
  assert (Hsem_entry :
    mtrail_wf n (ms_core Mentry) /\
    stable_view (msolver_view n Mentry) /\
    trail_implied F (ms_core Mentry)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (conj (msw_trail_wf Hweak)
        (conj (msw_stable Hweak) (msw_trail_impl Hweak))).
    - exact (conj (msa_trail_wf Hweak)
        (conj (msa_stable Hweak) (msa_trail_impl Hweak))).
  }
  destruct Hsem_entry as (Htrailwf_entry & Hstable_entry & Htrailimpl_entry).
  pose proof Hequiv as Hequiv_fields.
  unfold analysis_core_equiv in Hequiv_fields.
  destruct Hequiv_fields as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason & Eprob &
     Elearnt & Erest).
  assert (Hview : msolver_view n M = msolver_view n Mentry).
  {
    unfold msolver_view, view_of, msolver_clauses, msolver_db.
    rewrite Ecore, Ereason, Eprob, Elearnt.
    reflexivity.
  }
  assert (Htrailwf : mtrail_wf n (ms_core M)).
  { rewrite Ecore. exact Htrailwf_entry. }
  assert (Hstable : stable_view (msolver_view n M)).
  { rewrite Hview. exact Hstable_entry. }
  assert (Htrailimpl : trail_implied F (ms_core M)).
  { rewrite Ecore. exact Htrailimpl_entry. }
  destruct Hstable as (Hgrounded & Hclosed).
  assert (Hrootunit :
    forall y b,
      assignment (msolver_view n M) y = Some b ->
      level_of (msolver_view n M) y = Some 0 ->
      entails_clause F (satisfying_literal y b :: nil)).
  {
    intros y b Hass Hlev0.
    destruct (Hgrounded y b Hass) as
      (d & r & Hlevd & Hrank & Hreason_origin).
    assert (Hd : d = 0) by congruence. subst d.
    change (trail_pos (ms_core M) y = Some r) in Hrank.
    pose proof (trail_pos_bound (ms_core M) y r Hrank) as Hrbound.
    assert (Hri :
      0 <= Z.of_nat r < Zlength (mt_trail (ms_core M))) by lia.
    pose proof (trail_pos_var (ms_core M) y r Hrank) as Hvar.
    unfold trail_var in Hvar.
    pose proof (Forall_Znth_elim _ _ _ 0 (Z.of_nat r)
      (mtw_trail_lits Htrailwf) Hri) as Hlwf.
    pose proof (lit_var_c_in_range n
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) Hlwf)
      as Hvrange.
    pose proof (Forall_Znth_elim _ _ _ 0 (Z.of_nat r)
      (mtw_trail_true Htrailwf) Hri) as Htrue.
    cbn beta in Htrue.
    rewrite Hvar in Htrue.
    change (mt_pv (ms_core M) y = Some b) in Hass.
    rewrite mt_pv_nonneg in Hass by lia.
    rewrite Htrue, lbool_val_lit_sig in Hass.
    inversion Hass. subst b.
    change
      (option_map
         (fun k => level_of_index (ms_core M) (Z.of_nat k))
         (trail_pos (ms_core M) y) = Some 0) in Hlev0.
    rewrite Hrank in Hlev0. cbn in Hlev0.
    assert (Hlevelindex :
      level_of_index (ms_core M) (Z.of_nat r) = 0) by congruence.
    pose proof (Htrailimpl (Z.of_nat r)
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)
      Hri eq_refl) as Hent.
    rewrite Hlevelindex in Hent.
    unfold decisions_upto, ztake, cnf_with_units in Hent. cbn in Hent.
    rewrite app_nil_r in Hent.
    rewrite lit_denote_satisfying, Hvar in Hent.
    exact Hent.
  }
  exact (conj Htrailwf
    (conj (conj Hgrounded Hclosed) (conj Htrailimpl Hrootunit))).
Qed.

(* The resolvent of a two-literal tagged reason, in both tag states.  Both of
   its literals are at the current level, so nothing is added to [learnt]; the
   selected variable is always already tagged and leaves the pending set, while
   the side variable joins it exactly when it was not tagged yet. *)
Lemma msat_analyze_e7_resolve_sets :
  forall (n : Z) (M : msolver) (c x : Z) (C : clause)
         (S0 R0 : list Z) (learnt0 : clause),
    C = lit_denote (trail_lit_of (ms_core M) x) ::
        literal_neg (lit_denote (tag_lit c)) :: nil ->
    0 <= x ->
    level_of (msolver_view n M) x =
      Some (current_level (msolver_view n M)) ->
    level_of (msolver_view n M) (lit_var_c (tag_lit c)) =
      Some (current_level (msolver_view n M)) ->
    In x S0 ->
    resolve_learnt (msolver_view n M) C S0 R0 learnt0 = learnt0 /\
    (zmem (lit_var_c (tag_lit c)) (analyze_tags S0 R0 learnt0) = false ->
     resolve_S (msolver_view n M) x C S0 R0 learnt0 =
       zremove x S0 ++ (lit_var_c (tag_lit c) :: nil)) /\
    (zmem (lit_var_c (tag_lit c)) (analyze_tags S0 R0 learnt0) = true ->
     resolve_S (msolver_view n M) x C S0 R0 learnt0 = zremove x S0).
Proof.
  intros n M c x C S0 R0 learnt0 HC Hx Hlevx Hlevq HinS.
  assert (Hxseen : zmem x (analyze_tags S0 R0 learnt0) = true).
  {
    apply zmem_true_iff. unfold analyze_tags.
    rewrite !in_app_iff. tauto.
  }
  assert (Hxcurrent :
    at_current_level_b (msolver_view n M)
      (lit_denote (trail_lit_of (ms_core M) x)) = true).
  {
    apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite lit_var_c_denote, trail_lit_of_var by lia.
    exact Hlevx.
  }
  assert (Hqcurrent :
    at_current_level_b (msolver_view n M)
      (literal_neg (lit_denote (tag_lit c))) = true).
  {
    apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite literal_var_neg, lit_var_c_denote.
    exact Hlevq.
  }
  assert (Hxbelow :
    below_current_b (msolver_view n M)
      (lit_denote (trail_lit_of (ms_core M) x)) = false).
  {
    destruct (below_current_b (msolver_view n M)
      (lit_denote (trail_lit_of (ms_core M) x))) eqn:Hb;
      [|reflexivity].
    apply below_current_b_true_iff in Hb.
    destruct Hb as (d & Hd & Hdrange).
    rewrite lit_var_c_denote, trail_lit_of_var in Hd by lia.
    assert (Hdcur : d = current_level (msolver_view n M)) by congruence.
    subst d. lia.
  }
  assert (Hqbelow :
    below_current_b (msolver_view n M)
      (literal_neg (lit_denote (tag_lit c))) = false).
  {
    destruct (below_current_b (msolver_view n M)
      (literal_neg (lit_denote (tag_lit c)))) eqn:Hb;
      [|reflexivity].
    apply below_current_b_true_iff in Hb.
    destruct Hb as (d & Hd & Hdrange).
    rewrite literal_var_neg, lit_var_c_denote in Hd.
    assert (Hdcur : d = current_level (msolver_view n M)) by congruence.
    subst d. lia.
  }
  refine (conj _ (conj _ _)).
  - unfold resolve_learnt, resolve_new_lits. rewrite HC.
    cbn [filter].
    rewrite Hxbelow, Hqbelow. cbn. rewrite app_nil_r. reflexivity.
  - intros Hqnotseen.
    unfold resolve_S, resolve_new_S. rewrite HC.
    cbn [map filter].
    rewrite Hxcurrent, Hqcurrent. cbn.
    rewrite lit_var_c_denote, trail_lit_of_var by lia.
    rewrite literal_var_neg, lit_var_c_denote.
    rewrite Hxseen, Hqnotseen. cbn. reflexivity.
  - intros Hqseen.
    unfold resolve_S, resolve_new_S. rewrite HC.
    cbn [map filter].
    rewrite Hxcurrent, Hqcurrent. cbn.
    rewrite lit_var_c_denote, trail_lit_of_var by lia.
    rewrite literal_var_neg, lit_var_c_denote.
    rewrite Hxseen, Hqseen. cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma msat_analyze_e7_scan_index_nonzero :
  forall (n : Z) (M Mnext : msolver) (ind : Z)
         (S R : list Z) (learnt : clause),
    ms_core Mnext = ms_core M ->
    analysis_tags_exact n (ms_tags Mnext) (ms_tagged Mnext) ->
    Permutation (ms_tagged Mnext) (analyze_tags S R learnt) ->
    (exists y, In y S) ->
    (forall y, In y S -> exists r,
       assignment_rank (msolver_view n M) y = Some r /\
       Z.of_nat r <= ind) ->
    0 <= ind ->
    Znth (lit_var_c (Znth ind (mt_trail (ms_core Mnext)) 0))
      (ms_tags Mnext) 0 = 0 -> 0 < ind.
Proof.
  intros n M Mnext ind S R learnt Hcore Htags Hperm HexS Hranks Hind Hzero.
  destruct (Z.eq_dec ind 0) as [Hzind | Hzind]; [|lia].
  subst ind.
  pose proof Htags as Htags_fields.
  unfold analysis_tags_exact in Htags_fields.
  destruct Htags_fields as
    (Htagslen & Htaggednd & Htaggedrange & Htagcells & Htagiff).
  destruct HexS as (y & Hy).
  destruct (Hranks y Hy) as (r & Hyrank & Hyrle).
  assert (Hr0 : r = 0%nat) by lia. subst r.
  change (trail_pos (ms_core M) y = Some 0%nat) in Hyrank.
  pose proof (trail_pos_var (ms_core M) y 0%nat Hyrank) as Hyvar.
  cbn in Hyvar. unfold trail_var in Hyvar.
  assert (Hytags : In y (analyze_tags S R learnt)).
  { unfold analyze_tags. apply in_or_app. left. exact Hy. }
  assert (Hyphysical : In y (ms_tagged Mnext)).
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hytags.
  }
  rewrite Forall_forall in Htaggedrange.
  pose proof (Htaggedrange y Hyphysical) as Hyrange.
  pose proof (proj2 (Htagiff y Hyrange) Hyphysical) as Hyone.
  rewrite Hcore, Hyvar in Hzero.
  congruence.
Qed.

(* The shared decoded clause identifies its selected variable through the
   head literal. *)
Lemma msat_analyze_e7_select_bridge :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver)
         (focus c ind cnt p x : Z) (C : clause) (words S0 R0 : list Z)
         (learnt0 : clause),
    analyze_resolution_loop_inv n F A_arr K M focus AnalyzeSelected
      c C words cnt ind p ->
    reason_target_wf n M x c C ->
    is_tag c = msat_true ->
    In x S0 ->
    cnt + 1 = Zlength S0 ->
    analyze_inv F (msolver_view n M) S0 R0 learnt0 ->
    Permutation (ms_tagged M) (analyze_tags S0 R0 learnt0) ->
    solver_shape M ->
    mtrail_wf n (ms_core M) ->
    stable_view (msolver_view n M) ->
    (forall y b,
       assignment (msolver_view n M) y = Some b ->
       level_of (msolver_view n M) y = Some 0 ->
       entails_clause F (satisfying_literal y b :: nil)) ->
    C = lit_denote (trail_lit_of (ms_core M) x) ::
        literal_neg (lit_denote (tag_lit c)) :: nil /\
    (forall s, In s S0 -> s <> x -> rank_lt (msolver_view n M) s x) /\
    assignment_rank (msolver_view n M) x = Some (Z.to_nat (ind + 1)) /\
    reason_valid (msolver_view n M) x C /\
    entails_clause F C /\
    NoDup (map literal_var C) /\
    analyze_inv F (msolver_view n M)
      (resolve_S (msolver_view n M) x C S0 R0 learnt0) (x :: R0)
      (resolve_learnt (msolver_view n M) C S0 R0 learnt0) /\
    (forall y, In y S0 -> y <> x -> exists r,
       assignment_rank (msolver_view n M) y = Some r /\
       Z.of_nat r <= ind) /\
    (forall y, In y (x :: R0) -> exists r,
       assignment_rank (msolver_view n M) y = Some r /\
       ind < Z.of_nat r) /\
    analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
    0 <= ind < ms_qtail M /\
    1 <= Zlength words <= n /\
    ms_root_level M < Zlength (mt_lim (ms_core M)) /\
    0 <= lit_var_c (Znth ind (mt_trail (ms_core M)) 0) < n /\
    0 <= x < n /\
    lit_var_c (tag_lit c) <> x.
Proof.
  intros n F A_arr K M focus c ind cnt p x C words S0 R0 learnt0
    Hloop Htargetx Htag HinS Hcnt Hinv Hperm Hshape Htrailwf Hstable
    Hrootunit.
  destruct Hstable as (Hgrounded & Hclosed).
  unfold analyze_resolution_loop_inv in Hloop. cbn in Hloop.
  destruct Hloop as
    (Hready & Hind & Hwords & Hroot & Htags &
     Sa & Ra & La & xa & Hpne & Hxa & Hina & Htrail & Hrankxa &
     Hordera & Hlita & Hcnta & Hcntposa & Hca & HreasA & HtargetA &
     HfocusA & HvalidA & HentA & HCwfA & HCndA & HinvA & HwordsA &
     HpermA).
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as
    (Hsizecur & Hmatch & Hbinary).
  assert (Htagged_source : forall v,
    reason_target_wf n M v c C ->
    0 <= v < n /\ c = Znth v (ms_reason_words M) 0 /\
    C = lit_denote (trail_lit_of (ms_core M) v) ::
        literal_neg (lit_denote (tag_lit c)) :: nil).
  { intros v Htarget.
    unfold reason_target_wf in Htarget.
    destruct Htarget as (Hrange & Hword & Hnonzero & Hreason & Hkind).
    destruct Hkind as [(Htagged & Hpositive & Hlitwf) |
                      (co & Hnotag & Hnotbinary & Hin & Hdenote)].
    - assert (Hvn : 0 <= v < n) by lia.
      pose proof (Hmatch v Hvn) as Hcodec.
      rewrite <- Hword in Hcodec.
      pose proof (reason_word_ok_tag (ms_core M) v (msolver_db M) c
        (ms_reason_of M v) Hpositive Htag Hcodec) as Hclause.
      rewrite Hreason in Hclause.
      split; [exact Hvn |]. split; [exact Hword | congruence].
    - rewrite Htag in Hnotag. discriminate. }
  destruct (Htagged_source xa HtargetA) as (HrangeAn & HwordA & HCshapeA).
  destruct (Htagged_source x Htargetx) as (HrangeXn & HwordX & HCshapeX).
  assert (Hhead :
    lit_denote (trail_lit_of (ms_core M) xa) =
    lit_denote (trail_lit_of (ms_core M) x)) by congruence.
  pose proof (f_equal literal_var Hhead) as Howner.
  rewrite !lit_var_c_denote in Howner.
  rewrite !trail_lit_of_var in Howner by lia.
  subst xa.
  assert (HpermAS :
    Permutation (analyze_tags Sa Ra La) (analyze_tags S0 R0 learnt0)).
  {
    eapply Permutation_trans.
    - apply Permutation_sym. exact HpermA.
    - exact Hperm.
  }
  assert (HlenAS : Zlength Sa = Zlength S0) by lia.
  pose proof
    (analyze_inv_rank_partition_unique__analyze
      F (msolver_view n M) Sa Ra La S0 R0 learnt0
      HinvA Hinv HpermAS HlenAS) as HmembersAS.
  assert (Horder0 :
    forall s, In s S0 -> s <> x ->
      rank_lt (msolver_view n M) s x).
  {
    intros s Hs Hne.
    rewrite <- Howner.
    apply Hordera.
    - apply (proj2 (HmembersAS s)). exact Hs.
    - rewrite Howner. exact Hne.
  }
  rewrite Howner in HvalidA, HreasA, Hrankxa.
  pose proof HvalidA as Hvalid_fields.
  destruct Hvalid_fields as
    (bx & dx & rx & Hassx & Hlevx & Hrankx & Hsatx & Hsidesx).
  assert (Hreason_view :
    reason_of (msolver_view n M) x = Some C).
  {
    change (trail_pos (ms_core M) x = Some rx) in Hrankx.
    change
      ((match trail_pos (ms_core M) x with
        | Some _ => ms_reason_of M x
        | None => None
        end) = Some C).
    rewrite Hrankx. exact HreasA.
  }
  assert (HinvNew :
    analyze_inv F (msolver_view n M)
      (resolve_S (msolver_view n M) x C S0 R0 learnt0)
      (x :: R0)
      (resolve_learnt (msolver_view n M) C S0 R0 learnt0)).
  {
    eapply analyze_resolve_step;
      [exact Hclosed | exact Hrootunit | exact Hinv | exact HinS |
       exact Hreason_view | exact HvalidA | exact HentA | exact HCndA |
       exact Horder0].
  }
  assert (HpendS :
    forall y, In y S0 -> y <> x -> exists r,
      assignment_rank (msolver_view n M) y = Some r /\
      Z.of_nat r <= ind).
  {
    intros y HyS Hyx.
    destruct (Horder0 y HyS Hyx) as (ry & rx' & Hry & Hrx' & Hlt).
    change (trail_pos (ms_core M) x = Some rx') in Hrx'.
    rewrite Hrankxa in Hrx'. inversion Hrx'. subst rx'.
    exists ry. split; [exact Hry |].
    apply Nat2Z.inj_lt in Hlt.
    rewrite Z2Nat.id in Hlt by lia. lia.
  }
  pose proof Hinv as Hinv0_rank_fields.
  unfold analyze_inv in Hinv0_rank_fields.
  destruct Hinv0_rank_fields as
    (_ & _ & _ & _ & _ & HrankR0 & _).
  rewrite Forall_forall in HrankR0.
  assert (HresolvedRanks :
    forall y, In y (x :: R0) -> exists r,
      assignment_rank (msolver_view n M) y = Some r /\
      ind < Z.of_nat r).
  {
    intros y Hy. destruct Hy as [Hy | Hy].
    - subst y. exists (Z.to_nat (ind + 1)). split.
      + exact Hrankxa.
      + rewrite Z2Nat.id by lia. lia.
    - specialize (HrankR0 y Hy x HinS).
      destruct HrankR0 as (rx' & ry & Hrx' & Hry & Hlt).
      change (trail_pos (ms_core M) x = Some rx') in Hrx'.
      rewrite Hrankxa in Hrx'. inversion Hrx'. subst rx'.
      exists ry. split; [exact Hry |].
      apply Nat2Z.inj_lt in Hlt.
      rewrite Z2Nat.id in Hlt by lia. lia.
  }
  assert (Hqtrail :
    Zlength (mt_trail (ms_core M)) = ms_qtail M).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hidx :
    0 <= ind < Zlength (mt_trail (ms_core M))) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 ind
    (mtw_trail_lits Htrailwf) Hidx) as Hindlitwf.
  pose proof (lit_var_c_in_range n
    (Znth ind (mt_trail (ms_core M)) 0) Hindlitwf) as Hindvarrange.
  assert (Htagword :
    is_tag (Znth x (ms_reason_words M) 0) = true).
  { rewrite <- HwordX. exact Htag. }
  assert (HxrangeM : 0 <= x < ms_size M) by lia.
  destruct (Hbinary x HxrangeM Htagword) as
    (Hqwf & Hqlevel_same & Hqneq_word).
  assert (Hqneq : lit_var_c (tag_lit c) <> x).
  { rewrite HwordX. exact Hqneq_word. }
  exact (conj HCshapeX (conj Horder0 (conj Hrankxa (conj HvalidA
    (conj HentA (conj HCndA (conj HinvNew (conj HpendS
    (conj HresolvedRanks (conj Htags (conj Hind (conj Hwords
    (conj Hroot (conj Hindvarrange (conj HrangeXn Hqneq))))))))))))))).
Qed.

Ltac msat_analyze_e7_semantic_facts n F A_arr K M focus c x C phase
    words cnt ind p S0 R0 learnt :=
  bind_fact ( reason_target_wf n M x c C ) as H_reason_target;
  bind_fact ( analysis_cancel_ready n F A_arr K M focus )
    as H_cancel_ready;
  bind_fact ( is_tag c = msat_true ) as H_is_tag;
  bind_fact ( 0 <= lit_var_c (tag_lit c) ) as H_tag_lo;
  bind_fact ( lit_var_c (tag_lit c) < n ) as H_tag_hi;
  bind_fact ( level_of (msolver_view n M) (lit_var_c (tag_lit c)) =
    Some (current_level (msolver_view n M)) ) as H_tag_level;
  bind_fact ( analyze_resolution_loop_inv n F A_arr K M
    focus phase c C words cnt ind p ) as H_loop_inv;
  bind_fact ( phase = AnalyzeSelected ) as H_phase;
  bind_fact ( In x S0 ) as H_x_in_S0;
  bind_fact ( cnt + 1 = Zlength S0 ) as H_cnt_len;
  bind_fact ( level_of (msolver_view n M) x =
    Some (current_level (msolver_view n M)) ) as H_x_level;
  bind_fact ( c = Znth x (ms_reason_words M) 0 ) as H_reason_word;
  bind_fact ( analyze_inv F (msolver_view n M) S0 R0 learnt )
    as H_analyze_inv;
  bind_fact ( lits_denote (tl words) = learnt ) as H_learnt_eq;
  bind_fact ( Permutation (ms_tagged M) (analyze_tags S0 R0 learnt) )
    as H_tagged_perm;
  bind_fact ( solver_shape M ) as H_shape;
  bind_fact ( ms_size M = n ) as H_size.

(* The rank of the tagged side variable.  It is the one literal of the reason
   clause other than the selected variable's own, so [reason_valid] bounds its
   trail position strictly below the selected variable's, which the loop
   invariant pins at [ind + 1]. *)
Lemma msat_analyze_e7_side_rank :
  forall (n : Z) (M : msolver) (c x ind : Z) (C : clause),
    C = lit_denote (trail_lit_of (ms_core M) x) ::
        literal_neg (lit_denote (tag_lit c)) :: nil ->
    reason_valid (msolver_view n M) x C ->
    assignment_rank (msolver_view n M) x = Some (Z.to_nat (ind + 1)) ->
    0 <= ind ->
    lit_var_c (tag_lit c) <> x ->
    exists rq,
      assignment_rank (msolver_view n M) (lit_var_c (tag_lit c)) = Some rq /\
      Z.of_nat rq <= ind.
Proof.
  intros n M c x ind C HC Hvalid Hrank_sel Hind Hqneq.
  destruct Hvalid as
    (bx & dx & rx & Hassx & Hlevx & Hrankx & Hsatx & Hsidesx).
  assert (HqinC : In (literal_neg (lit_denote (tag_lit c))) C).
  { rewrite HC. cbn. tauto. }
  assert (Hqvarneq :
    literal_var (literal_neg (lit_denote (tag_lit c))) <> x).
  {
    rewrite literal_var_neg, lit_var_c_denote.
    exact Hqneq.
  }
  destruct (Hsidesx _ HqinC Hqvarneq) as
    (_ & dq & rq & Hlevq & Hrankq & Hdq & Hrqlt).
  rewrite literal_var_neg, lit_var_c_denote in Hrankq.
  exists rq. split; [exact Hrankq |].
  rewrite Hrank_sel in Hrankx. inversion Hrankx. subst rx.
  apply Nat2Z.inj_lt in Hrqlt.
  rewrite Z2Nat.id in Hrqlt by lia. lia.
Qed.

(* The state after the C code tags the side variable, bumps the heap and copies
   the activity arrays.  The step touches only heuristic and scratch fields, so
   the whole cancel-ready package, the shape, the seed shadow and both core
   equivalences survive it; the ghost tag list gains exactly [q] at the end,
   which is where the resolvent's new pending variable sits. *)
Lemma msat_analyze_e7_tag_state :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M0 M Mtag : msolver)
         (focus q x : Z) (activity' : list fp64)
         (orderpos' heap' S0 R0 : list Z) (learnt0 : clause)
         (var_inc' : fp64),
    Mtag = analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
             (ms_tagged M ++ (q :: nil)) activity' orderpos'
             heap' var_inc' ->
    analysis_cancel_ready n F A_arr K M focus ->
    analysis_tags_exact n (ms_tags M) (ms_tagged M) ->
    0 <= q < n ->
    Znth q (ms_tags M) 0 = 0 ->
    Permutation (ms_tagged M) (analyze_tags S0 R0 learnt0) ->
    Permutation (analyze_tags S0 R0 learnt0)
                (analyze_tags (zremove x S0) (x :: R0) learnt0) ->
    order_heap_wf n heap' orderpos' ->
    Permutation (ms_order M) heap' ->
    solver_shape M ->
    ms_size M = n ->
    Zlength activity' = n ->
    Zlength orderpos' = n ->
    analysis_core_equiv M0 M ->
    msolver_seed_shadow M ->
    zmem q (analyze_tags S0 R0 learnt0) = false /\
    analysis_tags_exact n (ms_tags Mtag) (ms_tagged Mtag) /\
    Permutation (ms_tagged Mtag)
      (analyze_tags (zremove x S0 ++ (q :: nil)) (x :: R0) learnt0) /\
    analysis_cancel_ready n F A_arr K Mtag focus /\
    solver_shape Mtag /\
    n = ms_size Mtag /\
    analysis_core_equiv M0 Mtag /\
    analysis_core_equiv M Mtag /\
    msolver_seed_shadow Mtag /\
    ms_core Mtag = ms_core M /\
    msolver_view n Mtag = msolver_view n M /\
    ms_root_level Mtag = ms_root_level M /\
    ms_qtail Mtag = ms_qtail M.
Proof.
  intros n F A_arr K M0 M Mtag focus q x activity' orderpos' heap'
    S0 R0 learnt0 var_inc' HMtag Hready Htags Hqrange Hqcell0 Hperm
    Hperm_move Hheap Horder Hshape Hsize Hact Hpos Hcore0 Hseed.
  subst Mtag.
  pose proof Hready as Hready_copy.
  unfold analysis_cancel_ready in Hready_copy.
  destruct Hready_copy as
    (Mentry & Hcancel_full & Hequiv & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  pose proof Htags as Htags_fields.
  unfold analysis_tags_exact in Htags_fields.
  destruct Htags_fields as
    (Htagslen & Htaggednd & Htaggedrange & Htagcells & Htagiff).
  assert (Hqnotin_tagged : ~ In q (ms_tagged M)).
  {
    intro Hin.
    pose proof (proj2 (Htagiff q Hqrange) Hin) as Hone.
    congruence.
  }
  assert (Hqnotseen : zmem q (analyze_tags S0 R0 learnt0) = false).
  {
    apply zmem_false_iff. intro Hin.
    apply Hqnotin_tagged.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
  }
  assert (HtagsNew :
    analysis_tags_exact n
      (replace_Znth q 1 (ms_tags M))
      (ms_tagged M ++ (q :: nil))).
  {
    unfold analysis_tags_exact.
    refine (conj _ _).
    { rewrite Zlength_replace_Znth. exact Htagslen. }
    refine (conj _ _).
    { apply NoDup_snoc; assumption. }
    refine (conj _ _).
    { apply Forall_app. split; [exact Htaggedrange |].
      constructor; [exact Hqrange | constructor]. }
    refine (conj _ _).
    { apply Forall_replace_Znth; [exact Htagcells |].
      right. reflexivity. }
    intros v Hv.
    destruct (Z.eq_dec v q) as [-> | Hneq].
    - rewrite Znth_replace_Znth_Same by (rewrite Htagslen; exact Hqrange).
      split; intros _.
      + apply in_or_app. right. left. reflexivity.
      + reflexivity.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Htagslen; try lia; congruence).
      rewrite (Htagiff v Hv), in_app_iff. cbn.
      intuition congruence.
  }
  assert (Hperm_base :
    Permutation (ms_tagged M)
      (analyze_tags (zremove x S0) (x :: R0) learnt0)).
  { eapply Permutation_trans; [exact Hperm | exact Hperm_move]. }
  assert (HpermNew :
    Permutation (ms_tagged M ++ (q :: nil))
      (analyze_tags (zremove x S0 ++ (q :: nil))
        (x :: R0) learnt0)).
  {
    eapply Permutation_trans.
    - apply Permutation_app_tail. exact Hperm_base.
    - unfold analyze_tags.
      exact (Permutation_rotate_snoc (zremove x S0)
        ((x :: R0) ++ map literal_var learnt0) q).
  }
  assert (HheapNow :
    heap_wf n {| mh_heap := heap'; mh_orderpos := orderpos' |}).
  { exact Hheap. }
  assert (HheapIncl : incl (ms_order M) heap').
  {
    intros v Hin.
    eapply Permutation_in; [exact Horder | exact Hin].
  }
  assert (HcoversNow :
    heap_covers n {| mh_heap := heap'; mh_orderpos := orderpos' |}
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M))).
  {
    unfold heap_covers in Hcovers |- *.
    intros v Hv Hmissing.
    apply Hcovers; [exact Hv |].
    eapply heap_wf_incl_missing_mono;
      [exact Hheapwf | exact HheapNow | exact HheapIncl | exact Hv |
       exact Hmissing].
  }
  assert (HreadyTag :
    analysis_cancel_ready n F A_arr K
      (analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
         (ms_tagged M ++ (q :: nil)) activity' orderpos'
         heap' var_inc') focus).
  {
    unfold analysis_cancel_ready.
    exists Mentry.
    refine (conj _ _); [exact Hcancel_full |].
    refine (conj _ _).
    { apply analysis_core_equiv_analyze_tag_step. exact Hequiv. }
    refine (conj _ _).
    { rewrite msolver_heap_analyze_tag_step. exact HheapNow. }
    refine (conj _ _).
    { cbn. exact HcoversNow. }
    refine (conj _ _).
    { unfold current_reasonless_earliest in *. cbn in *. exact Hearliest. }
    refine (conj _ _).
    { cbn. exact Hfocuslev. }
    cbn. exact Hclainc.
  }
  assert (HshapeTag :
    solver_shape
      (analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
         (ms_tagged M ++ (q :: nil)) activity' orderpos'
         heap' var_inc')).
  {
    eapply solver_shape_analyze_tag_step; [exact Hshape | | |].
    - rewrite Hsize, Zlength_replace_Znth. exact Htagslen.
    - rewrite Hsize. exact Hact.
    - rewrite Hsize. exact Hpos.
  }
  assert (HseedTag :
    msolver_seed_shadow
      (analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
         (ms_tagged M ++ (q :: nil)) activity' orderpos'
         heap' var_inc')).
  {
    apply (proj2 (msolver_seed_shadow_analyze_tag_step
      M (replace_Znth q 1 (ms_tags M))
      (ms_tagged M ++ q :: nil) activity'
      orderpos' heap' var_inc')).
    exact Hseed.
  }
  refine (conj Hqnotseen (conj HtagsNew (conj HpermNew (conj HreadyTag (conj
    HshapeTag (conj (eq_sym Hsize) (conj _ (conj _ (conj HseedTag (conj
    eq_refl (conj _ (conj eq_refl (eq_refl))))))))))))).
  - apply analysis_core_equiv_analyze_tag_step. exact Hcore0.
  - apply analysis_core_equiv_analyze_tag_step_self.
  - apply msolver_view_analyze_tag_step.
Qed.

Lemma msat_analyze_e7_tag_already_seen :
  forall (n : Z) (M : msolver) (c q : Z)
         (S0 R0 : list Z) (learnt0 : clause),
    analysis_tags_exact n (ms_tags M) (ms_tagged M) ->
    Permutation (ms_tagged M) (analyze_tags S0 R0 learnt0) ->
    q = lit_var_c (tag_lit c) ->
    0 <= lit_var_c (tag_lit c) ->
    lit_var_c (tag_lit c) < n ->
    Znth q (ms_tags M) 0 <> 0 ->
    zmem (lit_var_c (tag_lit c)) (analyze_tags S0 R0 learnt0) = true.
Proof.
  intros n M c q S0 R0 learnt0 Htags Hperm Hq Hqlo Hqhi Hnz.
  pose proof Htags as Htags_fields.
  unfold analysis_tags_exact in Htags_fields.
  destruct Htags_fields as
    (Htagslen & Htaggednd & Htaggedrange & Htagcells & Htagiff).
  assert (Hqcell : Znth (lit_var_c (tag_lit c)) (ms_tags M) 0 = 1).
  {
    assert (Hqidx :
      0 <= lit_var_c (tag_lit c) < Zlength (ms_tags M)) by lia.
    pose proof (Forall_Znth_elim _ _ _ 0 (lit_var_c (tag_lit c))
      Htagcells Hqidx) as Hcell.
    cbn beta in Hcell.
    rewrite <- Hq in Hcell.
    destruct Hcell as [Hz | Ho].
    - exfalso. apply Hnz. exact Hz.
    - rewrite <- Hq. exact Ho.
  }
  apply zmem_true_iff.
  eapply Permutation_in; [exact Hperm |].
  apply (proj1 (Htagiff _ (conj Hqlo Hqhi))).
  exact Hqcell.
Qed.

Tactic Notation "msat_analyze_scan_entry"
    ident(mact) ident(ph) ident(ccur) ident(cw2) ident(lrn2)
    ident(opos) ident(aptr) :=
  match goal with
  | Hret : _ = clause_lits_addr ?cc,
    Hloop : analyze_resolution_loop_inv ?nn ?ff ?aa ?kk mact ?foc ph ?cc ccur ?w2 ?cn ?idx ?pp |- _ =>
    assert (Hphase : ph = AnalyzeInitial) by
      (destruct ph; [ reflexivity | ];
       unfold analyze_resolution_loop_inv in Hloop;
       cbn in Hloop;
       decompose [and ex] Hloop; lia);
    subst ph;
    subst ccur;
    assert (Hcore : analysis_core_equiv mact mact) by
      (unfold analysis_core_equiv; repeat split; reflexivity);
    assert (Hscan :
      analyze_clause_scan_inv nn ff aa kk mact mact foc AnalyzeInitial
        (lits_denote cw2) 0 idx
        (@nil Z) (@nil Z) (@nil literal) (-1)
        (@nil Z) (@nil Z) (@nil literal) w2 cn) by
      (unfold analyze_clause_scan_inv;
       unfold analyze_resolution_loop_inv in Hloop;
       cbn in Hloop;
       destruct Hloop as (Hready & Hind0 & Hwords & Hroot & Htags & Hinit);
       destruct Hinit as (Hp & Hcnt & Hindtail & Hconf & Hptr & Htagged & Hlearnt);
       pose proof Hconf as Hconf_all;
       destruct Hconf as (Hent & Hfalse & HCwf & HCnd & Hex);
       refine (conj Hready _);
       refine (conj Hcore _);
       refine (conj Hind0 _);
       refine (conj Hroot _);
       refine (conj HCwf _);
       refine (conj HCnd _);
       refine (conj _ _);
       [ pose proof (Zlength_nonneg (lits_denote cw2)); lia | ];
       refine (conj _ _);
       [ rewrite Hcnt; reflexivity | ];
       refine (conj Hwords _);
       refine (conj Hlearnt _);
       refine (conj Htags _);
       refine (conj _ _);
       [ rewrite Htagged; simpl; constructor | ];
       cbn;
       repeat split; try assumption; simpl; try lia; try reflexivity);
    assert (Hhdr : clause_hdr_word lrn2 (Zlength cw2) / 2 = Zlength cw2) by
      (apply clause_hdr_word_div2; apply Zlength_nonneg);
    Exists aptr opos (@nil Z) (@nil Z) (@nil literal) (-1)
           (@nil Z) (@nil Z) (@nil literal) w2 mact;
    split_pure_spatial;
    [ rewrite Hret; msat_cancel_sound; change (emp |-- emp); cancel
    | split_pures; dump_pre_spatial;
      first
        [ exact Hcore
        | exact Hscan
        | assumption
        | reflexivity
        | unfold clause_lits_pointer; assumption
        | rewrite zdiv_equiv;
          [ exact Hhdr
          | unfold clause_hdr_word; destruct lrn2;
            pose proof (Zlength_nonneg cw2); lia
          | lia ]
        | unfold analyze_resolution_loop_inv in Hloop; cbn in Hloop; lia
        | apply Zlength_nonneg ] ]
  end.

Tactic Notation "msat_analyze_resolve"
    ident(mact) ident(ph) ident(ccur) ident(cw2) ident(lrn2)
    ident(opos) ident(aptr) :=
  match goal with
  | Hret : _ = clause_lits_addr ?cc,
    Hloop : analyze_resolution_loop_inv ?nn ?ff ?aa ?kk mact ?foc ph ?cc ccur ?w2 ?cn ?idx ?pp
    |- _ =>
    Right;
    assert (Hphase : ph = AnalyzeSelected) by
      (destruct ph;
       [ unfold analyze_resolution_loop_inv in Hloop; cbn in Hloop; tauto
       | reflexivity ]);
    subst ph; subst ccur;
    pose proof Hloop as Hstep;
    unfold analyze_resolution_loop_inv in Hstep; cbn in Hstep;
    destruct Hstep as
      (Hready & Hind & Hwords & Hroot & Htags &
       S0 & R0 & learnt0 & x & Hp & Hx & Hinx & Htrail & Hrankx &
       Horder & Hlit & Hcnt & Hcntpos & Hc & Hreason & Htarget & Hfocus &
       Hrv & Hent & HwfC & HnodupC & Hinv & Hlearnt & Hperm);
    assert (HndS0 : NoDup S0) by
      (pose proof Hinv as Hinv';
       unfold analyze_inv in Hinv';
       destruct Hinv' as (_ & Hndtags & _);
       unfold analyze_tags in Hndtags;
       eapply NoDup_app_remove_r; exact Hndtags);
    pose proof (zremove_split x) as Hremove;
    destruct (Hremove S0 HndS0 Hinx) as (before & after & HS0 & HremoveS0);
    assert (Hlenremove : cn = Zlength (zremove x S0)) by
      (rewrite HremoveS0, Zlength_app;
       rewrite HS0, !Zlength_app, Zlength_cons in Hcnt; lia);
    assert (Hperm_move :
      Permutation (analyze_tags S0 R0 learnt0)
                  (analyze_tags (zremove x S0) (x :: R0) learnt0)) by
      (unfold analyze_tags;
       rewrite HremoveS0, HS0;
       clear HS0 HremoveS0;
       induction before as [|a before IH];
       [ cbn; exact (Permutation_middle after (R0 ++ map literal_var learnt0) x)
       | cbn; constructor; exact IH ]);
    assert (HClen : 1 <= Zlength (lits_denote cw2)) by
      (unfold reason_valid in Hrv;
       destruct Hrv as (b & d & rx & Hass & Hlev & Hrank & Hsat & Hside);
       destruct (In_Znth_ex literal (lits_denote cw2)
         (satisfying_literal x b) (satisfying_literal x b) Hsat) as (i & Hi & Hnth);
       lia);
    assert (Htailone :
      skipn (Pos.to_nat 1)
        (firstn (Pos.to_nat 1) (lits_denote cw2)) = (@nil literal)) by
      (cbn; apply skipn_all2; rewrite length_firstn; lia);
    assert (Hscan :
      analyze_clause_scan_inv nn ff aa kk mact mact foc AnalyzeSelected
        (lits_denote cw2) 1 idx S0 R0 learnt0 x
        (zremove x S0) (x :: R0) learnt0 w2 cn) by
      (unfold analyze_clause_scan_inv; cbn;
       split; [exact Hready |];
       split; [ unfold analysis_core_equiv; repeat split; reflexivity |];
       split; [exact Hind |];
       split; [exact Hroot |];
       split; [exact HwfC |];
       split; [exact HnodupC |];
       split; [lia |];
       split; [exact Hlenremove |];
       split; [exact Hwords |];
       split; [exact Hlearnt |];
       split; [exact Htags |];
       split; [ eapply Permutation_trans; [exact Hperm | exact Hperm_move] |];
       split; [exact Hcntpos |];
       split; [lia |];
       split; [exact Hinx |];
       split; [exact Hrankx |];
       split; [exact Horder |];
       split; [exact Hinv |];
       split; [exact Hreason |];
       split; [exact Hrv |];
       split; [exact Hent |];
       split;
       [ unfold resolve_S, resolve_new_S; rewrite Htailone; cbn;
         rewrite app_nil_r; reflexivity |];
       split; [reflexivity |];
       unfold resolve_learnt, resolve_new_lits; rewrite Htailone; cbn;
       rewrite app_nil_r; reflexivity);
    Exists aptr opos
      S0 R0 learnt0 x (zremove x S0) (x :: R0) learnt0 w2 mact;
    Intros;
    split_pure_spatial;
    [ rewrite Hret; msat_cancel_sound; change (emp |-- emp); cancel
    | split_pures; dump_pre_spatial; try solve [auto | lia] ];
    [ unfold analysis_core_equiv; repeat split; reflexivity
    | rewrite zdiv_equiv;
      [ apply clause_hdr_word_div2; apply Zlength_nonneg
      | unfold clause_hdr_word; destruct lrn2;
        pose proof (Zlength_nonneg cw2); lia
      | lia ]
    | rewrite lits_denote_length in HClen; exact HClen ]
  end.

Lemma ms_analyze_tag_step_cancel_ready :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z)
         (tags tagged : list Z) (activity : list fp64)
         (orderpos order : list Z) (var_inc : fp64),
    analysis_cancel_ready n F A_arr K M focus ->
    order_heap_wf n order orderpos ->
    (forall u : Z, 0 <= u < n -> Znth u orderpos (-1) = -1 ->
       Znth u (ms_orderpos M) (-1) = -1) ->
    analysis_cancel_ready n F A_arr K
      (analyze_tag_step_msolver M tags tagged activity orderpos
         order var_inc) focus.
Proof.
  intros n F A_arr K M focus tags tagged activity orderpos order
    var_inc Hready Hheap Hpos.
  destruct Hready as
    [Mentry [Hprop [Hequiv [Hwf [Hcovers [Hearliest [Hfocus Hinc]]]]]]].
  exists Mentry. split; [exact Hprop|].
  split.
  - apply analysis_core_equiv_analyze_tag_step. exact Hequiv.
  - split.
    + rewrite msolver_heap_analyze_tag_step.
      unfold order_heap_wf in Hheap. exact Hheap.
    + split.
      * rewrite msolver_heap_analyze_tag_step.
        apply (heap_covers_weaken_heap n (msolver_heap M)
          {| mh_heap := order; mh_orderpos := orderpos |}
          (mt_assigns (ms_core M)) (mt_trail (ms_core M))
          (mt_qhead (ms_core M)) Hcovers).
        intros u Hu Hm1. apply Hpos; assumption.
      * split; [exact Hearliest|].
        split; [exact Hfocus|exact Hinc].
Qed.

Tactic Notation "msat_analyze_start_step_tag" ident(q) constr(v) constr(n)
    constr(Ma) constr(C) constr(idx) constr(w) constr(Sc) constr(Lc)
    ident(HC) ident(Hjhi) ident(HS) ident(HL) ident(Hat) ident(Hbelow) ident(Eqv) :=
  assert (Hprefix : sublist 0 (idx + 1) C =
      sublist 0 idx C ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc w C 0 idx
          HC ltac:(lia) ltac:(lia) Hjhi));
  assert (HSnext : Sc ++ (v :: nil) =
      analyze_start_S (msolver_view n Ma) (sublist 0 (idx + 1) C))
    by (rewrite HS; unfold analyze_start_S;
        rewrite Hprefix, filter_app, map_app; cbn [filter map];
        rewrite Hat; cbn [filter map]; rewrite Eqv; reflexivity);
  assert (HLnext : Lc =
      analyze_start_learnt (msolver_view n Ma) (sublist 0 (idx + 1) C))
    by (rewrite HL; unfold analyze_start_learnt;
        rewrite Hprefix, filter_app; cbn [filter]; rewrite Hbelow;
        cbn [filter]; rewrite app_nil_r; reflexivity).

Tactic Notation "msat_analyze_tag_step_frame" ident(Mnext) constr(Mscan)
    constr(v) constr(act) constr(opos) constr(ord) constr(vinc)
    constr(c) constr(isl) constr(words) :=
  assert (Hrem : analysis_clause_remainder Mnext c isl words =
      analysis_clause_remainder Mscan c isl words) by reflexivity;
  rewrite Hrem;
  unfold Mnext;
  rewrite solver_analyze_frame_analyze_tag_step;
  rewrite solver_analyze_inert_at_tag_step;
  pose proof (analyze_tag_step_msolver_proj Mscan
    (replace_Znth v 1 (ms_tags Mscan)) (ms_tagged Mscan ++ (v :: nil))
    act opos ord vinc) as Hproj;
  cbv zeta in Hproj;
  destruct Hproj as (Etags & Etagged & Eactivity & Eorderpos &
      Eorder & Evarinc & Esize & Ecap & Eqtail & Ecore & Ereasonwords &
      Ereasonof & Estack & Estats & Eclainc);
  assert (Elearnt : ms_learnt (analyze_tag_step_msolver Mscan
      (replace_Znth v 1 (ms_tags Mscan)) (ms_tagged Mscan ++ (v :: nil))
      act opos ord vinc) = ms_learnt Mscan) by reflexivity;
  try rewrite Etags; try rewrite Etagged;
  try rewrite Eactivity; try rewrite Eorderpos; try rewrite Eorder;
  try rewrite Evarinc; try rewrite Esize; try rewrite Ecap;
  try rewrite Eqtail; try rewrite Ecore; try rewrite Ereasonwords;
  try rewrite Ereasonof; try rewrite Estack;
  try rewrite Estats; try rewrite Eclainc;
  try rewrite Elearnt.

Lemma ms_analyze_notin_initial_resolved :
  forall (v x : Z) (S0 R0 Sc Rc : list Z) (L0 Lc : clause),
    ~ In v (analyze_tags Sc Rc Lc) ->
    Sc = zremove x S0 -> Rc = x :: R0 -> Lc = L0 ->
    ~ In v (analyze_tags S0 R0 L0).
Proof.
  intros v x S0 R0 Sc Rc L0 Lc Hnotcur HS HR HL Hin. apply Hnotcur.
  unfold analyze_tags in *. rewrite !in_app_iff in *.
  destruct Hin as [HinS|[HinR|HinL]].
  - destruct (Z.eq_dec v x) as [->|Hne].
    + right. left. rewrite HR. simpl. tauto.
    + left. rewrite HS. apply In_zremove_iff. tauto.
  - right. left. rewrite HR. simpl. tauto.
  - right. right. rewrite <- HL in HinL. exact HinL.
Qed.

Lemma ms_sublist_one_one_nil : forall (l : clause), sublist 1 1 l = nil.
Proof.
  intros l. unfold sublist. change (skipn 1 (firstn 1 l) = nil).
  destruct l; reflexivity.
Qed.

Tactic Notation "msat_analyze_tag_step_open" ident(v) ident(Mnext)
    constr(idx) constr(w) constr(act)
    constr(opos) constr(ord) constr(vinc) ident(Hready) ident(Hheap)
    ident(Hu) ident(Htags) :=
  lazymatch type of Hready with
  | analysis_cancel_ready ?n ?F ?A_arr ?K ?Mscan ?focus =>
  set (v := lit_var_c (Znth (idx - 0) w 0));
  set (Mnext := analyze_tag_step_msolver Mscan
    (replace_Znth v 1 (ms_tags Mscan))
    (ms_tagged Mscan ++ (v :: nil)) act opos ord vinc);
  assert (Hreadynew : analysis_cancel_ready n F A_arr K Mnext focus)
    by (unfold Mnext; apply ms_analyze_tag_step_cancel_ready;
        [exact Hready | exact Hheap | exact Hu]);
  assert (Htagsnew : analysis_tags_exact n (replace_Znth v 1 (ms_tags Mscan))
      (ms_tagged Mscan ++ (v :: nil)))
    by (apply ms_analysis_tags_exact_snoc;
        [exact Htags | unfold v; lia | unfold v in *; lia])
  end.

(* A variable absent from the RESOLVED tag sets is absent from the INITIAL ones,
   in the general scan position: the resolved [S] drops only the pivot [x] and
   keeps every other initial candidate, the resolved trail only prepends [x],
   and the resolved learnt list only extends the initial one. *)
Lemma msat_analyze_e12_notin_initial :
  forall (a : cdcl_view) (C : clause) (j : Z) (x v : Z)
         (S0 R0 Sc Rc : list Z) (L0 Lc : clause),
    ~ In v (analyze_tags Sc Rc Lc) ->
    v <> x ->
    Sc = resolve_S a x (sublist 1 j C) S0 R0 L0 ->
    Rc = x :: R0 ->
    Lc = resolve_learnt a (sublist 1 j C) S0 R0 L0 ->
    zmem v (analyze_tags S0 R0 L0) = false.
Proof.
  intros a C j x v S0 R0 Sc Rc L0 Lc Hnot Hne HS HR HL.
  apply zmem_false_iff. intro Hin. apply Hnot.
  unfold analyze_tags in Hin |- *.
  rewrite !in_app_iff in Hin |- *.
  destruct Hin as [HinS | [HinR | HinL]].
  - left. rewrite HS. unfold resolve_S.
    apply in_or_app. left. apply In_zremove_iff. split; assumption.
  - right. left. rewrite HR. right. exact HinR.
  - right. right. rewrite HL. unfold resolve_learnt.
    rewrite map_app. apply in_or_app. left. exact HinL.
Qed.

Lemma msat_analyze_e12_resolve_step_tag :
  forall (a : cdcl_view) (C : clause) (j : Z) (l : literal) (v x : Z)
         (S0 R0 Sc : list Z) (L0 Lc : clause),
    literal_var l = v ->
    sublist 1 (j + 1) C = sublist 1 j C ++ (l :: nil) ->
    at_current_level_b a l = true ->
    below_current_b a l = false ->
    zmem v (analyze_tags S0 R0 L0) = false ->
    Sc = resolve_S a x (sublist 1 j C) S0 R0 L0 ->
    Lc = resolve_learnt a (sublist 1 j C) S0 R0 L0 ->
    Sc ++ (v :: nil) = resolve_S a x (sublist 1 (j + 1) C) S0 R0 L0 /\
    Lc = resolve_learnt a (sublist 1 (j + 1) C) S0 R0 L0.
Proof.
  intros a C j l v x S0 R0 Sc L0 Lc Ev Hsub Hat Hbelow Hmem HS HL.
  split.
  - symmetry. unfold resolve_S, resolve_new_S in HS |- *.
    rewrite Hsub, filter_app, map_app, filter_app.
    cbn [filter map]. rewrite Hat. cbn [filter map negb].
    rewrite Ev. rewrite Hmem. cbn [filter map negb].
    rewrite app_assoc. rewrite <- HS. reflexivity.
  - symmetry. unfold resolve_learnt, resolve_new_lits in HL |- *.
    rewrite Hsub, filter_app. cbn [filter].
    rewrite Hbelow. cbn [filter negb andb]. rewrite app_nil_r.
    exact (eq_sym HL).
Qed.

Lemma msat_analyze_e12_scan_lit_current :
  forall (n : Z) (M : msolver) (C : clause) (l : literal) (v x : Z),
    reason_valid (msolver_view n M) x C ->
    In l C ->
    literal_var l = v ->
    v <> x ->
    mtrail_wf n (ms_core M) ->
    Znth v (mt_levels (ms_core M)) 0 = Zlength (mt_lim (ms_core M)) ->
    at_current_level_b (msolver_view n M) l = true /\
    below_current_b (msolver_view n M) l = false.
Proof.
  intros n M C l v x Hvalid Hin Ev Hne Htrailwf Hraw. subst v.
  destruct Hvalid as (bx & dx & rx & Hassx & Hlevx & Hrankx & Hsatx & Hsides).
  destruct (Hsides l Hin Hne) as
    (Hlfalse & dq & rq & Hlevq & Hrankq & Hdq & Hrq).
  assert (Hpos : trail_pos (ms_core M) (literal_var l) = Some rq)
    by exact Hrankq.
  assert (Hlevel : level_of (msolver_view n M) (literal_var l) =
    Some (current_level (msolver_view n M))).
  {
    pose proof (trail_pos_bound (ms_core M) (literal_var l) rq Hpos) as Hrqb.
    pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
    rewrite (trail_pos_var (ms_core M) (literal_var l) rq Hpos) in Hagree.
    change
      (option_map
        (fun k => level_of_index (ms_core M) (Z.of_nat k))
        (trail_pos (ms_core M) (literal_var l)) =
       Some (Zlength (mt_lim (ms_core M)))).
    rewrite Hpos. cbn. rewrite <- Hagree. f_equal. exact Hraw.
  }
  split.
  - apply (proj2 (at_current_level_b_true_iff _ _)). exact Hlevel.
  - destruct (below_current_b (msolver_view n M) l) eqn:Hb; [|reflexivity].
    apply below_current_b_true_iff in Hb.
    destruct Hb as (d & Hd & Hdrange).
    assert (Hdcur : d = current_level (msolver_view n M)) by congruence.
    subst d. lia.
Qed.

(* The tag step keeps [analysis_cancel_ready] when the fresh order heap is
   presented as a PERMUTATION of the old one (the exit that copies the heap
   rather than the one that only rewrites order positions): a permutation is an
   inclusion, and the missing-variable coverage of the old heap transports along
   an inclusion between two well-formed heaps. *)
Lemma msat_analyze_e12_tag_ready_perm :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z)
         (tags tagged : list Z) (activity : list fp64)
         (orderpos order : list Z) (var_inc : fp64),
    analysis_cancel_ready n F A_arr K M focus ->
    order_heap_wf n order orderpos ->
    Permutation (ms_order M) order ->
    analysis_cancel_ready n F A_arr K
      (analyze_tag_step_msolver M tags tagged activity orderpos
         order var_inc) focus.
Proof.
  intros n F A_arr K M focus tags tagged activity orderpos order
    var_inc Hready Hheap Hperm.
  destruct Hready as
    (Mentry & Hcancel_full & HequivEntry & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  assert (HheapNow :
    heap_wf n {| mh_heap := order; mh_orderpos := orderpos |})
    by exact Hheap.
  assert (HheapIncl : incl (ms_order M) order).
  { intros u Hin. eapply Permutation_in; [exact Hperm | exact Hin]. }
  assert (HcoversNow :
    heap_covers n {| mh_heap := order; mh_orderpos := orderpos |}
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M))).
  {
    unfold heap_covers in Hcovers |- *.
    intros u Hu Hmissing.
    apply Hcovers; [exact Hu |].
    eapply heap_wf_incl_missing_mono;
      [exact Hheapwf | exact HheapNow | exact HheapIncl | exact Hu |
       exact Hmissing].
  }
  unfold analysis_cancel_ready.
  exists Mentry.
  refine (conj Hcancel_full _).
  refine (conj _ _).
  { apply analysis_core_equiv_analyze_tag_step. exact HequivEntry. }
  refine (conj _ _).
  { rewrite msolver_heap_analyze_tag_step. exact HheapNow. }
  refine (conj _ _).
  { cbn. exact HcoversNow. }
  refine (conj _ _).
  { unfold current_reasonless_earliest in *. cbn in *. exact Hearliest. }
  refine (conj _ _).
  { cbn. exact Hfocuslev. }
  cbn. exact Hclainc.
Qed.

Lemma ms_analyze_scan_initial_pack :
  forall {n : Z} {F : cnf} {A_arr : list literal}
         {K : solver_propagation_context} {M0 M : msolver} {focus : Z}
         {phase : analyze_resolution_phase} {C : clause} {j ind : Z}
         {S0 R0 : list Z} {learnt0 : clause} {x : Z} {S R : list Z}
         {learnt : clause} {words : list Z} {cnt : Z},
    phase = AnalyzeInitial ->
    analyze_clause_scan_inv n F A_arr K M0 M focus phase C j ind S0 R0 learnt0
      x S R learnt words cnt ->
    propagation_conflict_cert n F M0 C /\
    S = analyze_start_S (msolver_view n M0) (sublist 0 j C) /\
    learnt = analyze_start_learnt (msolver_view n M0) (sublist 0 j C).
Proof.
  intros * Hphase Hinv. unfold analyze_clause_scan_inv in Hinv.
  rewrite Hphase in Hinv. cbn in Hinv. tauto.
Qed.

Lemma ms_analyze_tags_perm_snoc_l :
  forall (tagged S R : list Z) (L : clause) (l : literal),
    Permutation tagged (analyze_tags S R L) ->
    Permutation (tagged ++ (literal_var l :: nil))
      (analyze_tags S R (L ++ (l :: nil))).
Proof.
  intros tagged S R L l Hpermold.
  eapply Permutation_trans.
  - apply Permutation_app_tail. exact Hpermold.
  - unfold analyze_tags. rewrite map_app. cbn [map].
    rewrite !app_assoc. reflexivity.
Qed.

Tactic Notation "msat_analyze_initial_level_readback" ident(v) constr(n)
    constr(Ma) constr(Mscan) constr(rq) ident(Hrank) ident(Htrailwf) ident(Eview)
    ident(Hvar_pos) ident(Hpositive) ident(Hvar_level) ident(Hcurrent) ident(Hdifferent) :=
  assert (Hrqb : Z.of_nat rq < Zlength (mt_trail (ms_core Mscan)))
    by (apply (trail_pos_bound (ms_core Mscan) v rq Hrank));
  pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree;
  rewrite (trail_pos_var (ms_core Mscan) v rq Hrank) in Hagree;
  set (dq := level_of_index (ms_core Mscan) (Z.of_nat rq));
  assert (Hdqpos : 0 < dq)
    by (unfold dq; fold v in Hvar_pos; rewrite Hvar_pos in Hpositive;
        replace (v - 0) with v in Hpositive by lia; lia);
  assert (Hdqne : dq <> Zlength (mt_lim (ms_core Mscan)))
    by (unfold dq; fold v in Hvar_level;
        rewrite Hvar_level, Hcurrent in Hdifferent;
        replace (v - 0) with v in Hdifferent by lia; lia);
  assert (Hdqlt : dq < Zlength (mt_lim (ms_core Mscan)))
    by (pose proof (prop_level_processed_level_le (ms_core Mscan) (Z.of_nat rq)); lia);
  assert (Hlevq : level_of (msolver_view n Ma) v = Some dq)
    by (rewrite Eview; unfold msolver_view, view_of;
        cbn [level_of]; rewrite Hrank; reflexivity).

Tactic Notation "msat_analyze_offlevel_flags" constr(n) constr(Ma)
    constr(q) constr(dq) ident(Hlev) ident(Hne) ident(Eq) ident(Ev) :=
  assert (Hat : at_current_level_b (msolver_view n Ma) (lit_denote q) = false)
    by (unfold at_current_level_b; rewrite Eq, Hlev;
        rewrite Ev, msolver_view_current_level;
        apply Z.eqb_neq; exact Hne);
  assert (Hbelow : below_current_b (msolver_view n Ma) (lit_denote q) = true)
    by (apply (proj2 (below_current_b_true_iff _ _));
        exists dq; rewrite Eq; split; [exact Hlev|];
        rewrite Ev, msolver_view_current_level; lia).

Tactic Notation "msat_analyze_scan_inv_word" ident(Mnext) ident(phase)
    constr(HC) constr(Hwl) constr(Hws) constr(HS) constr(HL) :=
  unfold analyze_clause_scan_inv in *;
  subst phase;
  unfold Mnext, analyze_tag_step_msolver, msolver_analysis_update, msolver_view in *;
  cbn -[Z.add Z.sub Z.mul Z.div Z.modulo] in *;
  intuition (try lia; try assumption);
  try (rewrite HC; rewrite lits_denote_length; lia);
  try exact Hwl;
  try exact Hws;
  try exact HS;
  try exact HL.

Tactic Notation "msat_analyze_start_step_word" ident(q) constr(n)
    constr(Ma) constr(C) constr(idx) constr(w) constr(Sc) constr(Lc)
    ident(HC) ident(Hjhi) ident(HS) ident(HL) ident(Hlv) ident(Hbl) :=
  assert (Hprefix : sublist 0 (idx + 1) C =
      sublist 0 idx C ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc w C 0 idx
          HC ltac:(lia) ltac:(lia) Hjhi));
  assert (HSnext : Sc =
      analyze_start_S (msolver_view n Ma) (sublist 0 (idx + 1) C))
    by (rewrite HS; unfold analyze_start_S;
        rewrite Hprefix, filter_app, map_app; cbn [filter map];
        rewrite Hlv; cbn [filter map]; rewrite app_nil_r; reflexivity);
  assert (HLnext : Lc ++ (lit_denote q :: nil) =
      analyze_start_learnt (msolver_view n Ma) (sublist 0 (idx + 1) C))
    by (rewrite HL; unfold analyze_start_learnt;
        rewrite Hprefix, filter_app; cbn [filter]; rewrite Hbl;
        cbn [filter]; reflexivity).

(* Room for one more learnt word.  The AnalyzeInitial start-learnt set of any
   prefix of a conflicting clause [C] holds literals of pairwise distinct
   variables, all strictly below the current decision level, so the current
   level's own literal [lcur] of [C] is not among them; the [n] variables of
   the solver therefore leave room for that one extra slot. *)
Lemma ms_analyze_start_learnt_room :
  forall (n k : Z) (a : cdcl_view) (C : clause) (lcur : literal),
    Forall (literal_wf n) C ->
    NoDup (map literal_var C) ->
    In lcur C ->
    level_of a (literal_var lcur) = Some (current_level a) ->
    1 + Zlength (analyze_start_learnt a (sublist 0 k C)) <= n.
Proof.
  intros n k a C lcur HwfC HndC Hlcur Hlevcur.
  set (L := analyze_start_learnt a (sublist 0 k C)).
  pose proof (msat_analyze_start_learnt_incl a k C) as HinLC.
  assert (HndL : NoDup (map literal_var L)).
  { unfold L, analyze_start_learnt.
    apply NoDup_map_filter. unfold sublist. cbn.
    pose proof HndC as Hndpre.
    rewrite <- (firstn_skipn (Z.to_nat k) C) in Hndpre.
    rewrite map_app in Hndpre.
    eapply NoDup_app_remove_r. exact Hndpre. }
  assert (HnotcurL : ~ In (literal_var lcur) (map literal_var L)).
  { intro Hin. apply in_map_iff in Hin.
    destruct Hin as [l [Hel Hl]].
    unfold L, analyze_start_learnt in Hl.
    apply filter_In in Hl. destruct Hl as [_ Hbelow_l].
    apply (proj1 (below_current_b_true_iff _ _)) in Hbelow_l.
    destruct Hbelow_l as [dl [Hlevl [_ Hdllt]]].
    rewrite <- Hel, Hlevl in Hlevcur.
    injection Hlevcur as Ecur. lia. }
  rewrite Forall_forall in HwfC.
  assert (Hn0 : 0 <= n).
  { pose proof (HwfC lcur Hlcur) as Hw.
    unfold literal_wf, var_in_range in Hw. lia. }
  pose proof (msat_cons_map_literal_var_bounded n C L lcur HwfC Hlcur HinLC)
    as HboundedL.
  pose proof (NoDup_Z_bounded_length
    (literal_var lcur :: map literal_var L) n Hn0
    ltac:(constructor; [exact HnotcurL|exact HndL]) HboundedL) as Hcard.
  cbn [Datatypes.length] in Hcard. rewrite length_map in Hcard.
  rewrite Nat2Z.inj_succ, <- Zlength_correct in Hcard. lia.
Qed.

Lemma ms_learnt_words_len :
  forall (words : list Z) (L : clause),
    1 <= Zlength words -> lits_denote (tl words) = L ->
    Zlength words = 1 + Zlength L.
Proof.
  intros words L Hlow Hden.
  destruct words as [|w ws].
  - cbn in Hlow. lia.
  - cbn [tl] in Hden.
    pose proof (f_equal (@Zlength literal) Hden) as Hz.
    rewrite lits_denote_length in Hz.
    rewrite Zlength_cons. lia.
Qed.

Lemma ms_learnt_words_snoc :
  forall (words : list Z) (L : clause) (w : Z),
    1 <= Zlength words -> lits_denote (tl words) = L ->
    lits_denote (tl (words ++ (w :: nil))) = L ++ (lit_denote w :: nil).
Proof.
  intros words L w Hlow Hden.
  destruct words as [|x ws].
  - cbn in Hlow. lia.
  - cbn [tl] in Hden. cbn [app tl].
    rewrite lits_denote_app. cbn [lits_denote map].
    rewrite Hden. reflexivity.
Qed.

Tactic Notation "msat_analyze_resolve_step_word" ident(q) constr(n)
    constr(Ma) constr(C) constr(idx) constr(w) constr(x) constr(S0)
    constr(R0) constr(L0) constr(Sc) constr(Lc) ident(HC) ident(Hjhi)
    ident(HS) ident(HL) ident(Hlv) ident(Hbl) ident(Heqv) ident(Hmem) :=
  assert (Hprefix : sublist 1 (idx + 1) C =
      sublist 1 idx C ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc w C 1 idx
          HC ltac:(lia) ltac:(lia) Hjhi));
  assert (HSnext : Sc = resolve_S (msolver_view n Ma) x
      (sublist 1 (idx + 1) C) S0 R0 L0)
    by (unfold resolve_S, resolve_new_S in *;
        rewrite Hprefix, filter_app, map_app, filter_app;
        cbn [filter map]; rewrite Hlv; cbn [filter];
        rewrite HS; repeat rewrite app_assoc;
        rewrite app_nil_r; reflexivity);
  assert (HLnext : Lc ++ (lit_denote q :: nil) =
      resolve_learnt (msolver_view n Ma) (sublist 1 (idx + 1) C) S0 R0 L0)
    by (unfold resolve_learnt, resolve_new_lits in *;
        rewrite Hprefix, filter_app; cbn [filter]; rewrite Hbl;
        cbn [filter]; rewrite Heqv, Hmem; cbn [negb andb];
        rewrite HL; repeat rewrite app_assoc; reflexivity).

Tactic Notation "msat_analyze_scan_level_transport" constr(v) constr(Mscan)
    constr(rq) constr(Hlevq) constr(Hrankq) constr(Eqv) constr(Eview)
    constr(Htrailwf) :=
  pose proof Hlevq as Hlevq0; rewrite Eqv in Hlevq0;
  pose proof Hlevq as Hlevqscan; pose proof Hrankq as Hrankqscan;
  rewrite Eqv, Eview in Hlevqscan, Hrankqscan;
  unfold msolver_view, view_of in Hlevqscan, Hrankqscan;
  cbn [level_of assignment_rank] in Hlevqscan, Hrankqscan;
  rewrite Hrankqscan in Hlevqscan;
  cbn in Hlevqscan; injection Hlevqscan as Edq;
  pose proof (trail_pos_bound (ms_core Mscan) v rq Hrankqscan) as Hrqb;
  pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree;
  rewrite (trail_pos_var (ms_core Mscan) v rq Hrankqscan) in Hagree.

(* ---- shared pure steps of the solver_analyze clause-scan VC family ---- *)
Lemma ms_analyze_tags_len :
  forall (tagged S R : list Z) (L : clause),
    Permutation tagged (analyze_tags S R L) ->
    Zlength tagged = Zlength S + Zlength R + Zlength L.
Proof.
  intros tagged S R L Hperm.
  pose proof (Zlength_perm_eq _ _ _ Hperm) as Hz.
  unfold analyze_tags in Hz. rewrite !Zlength_app in Hz.
  assert (Hm : Zlength (map literal_var L) = Zlength L).
  { rewrite !Zlength_correct. rewrite length_map. reflexivity. }
  rewrite Hm in Hz. lia.
Qed.

Tactic Notation "msat_analyze_scan_words_grow" constr(n) constr(q)
    constr(Mscan) constr(wl) constr(Sc) constr(Rc) constr(R0) constr(Lc)
    ident(Hperm) ident(HR) :=
  assert (Hwordlenold : Zlength wl = 1 + Zlength Lc)
    by (apply ms_learnt_words_len; assumption);
  assert (Htaglen : Zlength (ms_tagged Mscan) =
      Zlength Sc + Zlength Rc + Zlength Lc)
    by (apply ms_analyze_tags_len; exact Hperm);
  assert (Hwordlennew : 1 <= Zlength (wl ++ (q :: nil)) <= n)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil;
        rewrite HR, Zlength_cons in Htaglen;
        pose proof (Zlength_nonneg Sc);
        pose proof (Zlength_nonneg R0);
        pose proof (Zlength_nonneg Lc); lia);
  assert (Hwordsnext : lits_denote (tl (wl ++ (q :: nil))) =
      Lc ++ (lit_denote q :: nil))
    by (apply ms_learnt_words_snoc; assumption).

Tactic Notation "msat_analyze_selected_level_bounds" ident(v) constr(Mscan)
    constr(rq) constr(dq) ident(Hvar_pos) ident(Hpositive)
    ident(Hvar_level) ident(Hcurrent) ident(Hdifferent) ident(Edq) ident(Hagree) :=
  assert (Hdqpos : 0 < dq)
    by (fold v in Hvar_pos; rewrite Hvar_pos in Hpositive;
        replace (v - 0) with v in Hpositive by lia;
        rewrite Edq in Hagree; lia);
  assert (Hdqne : dq <> Zlength (mt_lim (ms_core Mscan)))
    by (fold v in Hvar_level; rewrite Hvar_level, Hcurrent in Hdifferent;
        replace (v - 0) with v in Hdifferent by lia;
        rewrite Edq in Hagree; lia);
  assert (Hdqlt : dq < Zlength (mt_lim (ms_core Mscan)))
    by (let Hupper := fresh "Hlevel_upper" in
        pose proof (prop_level_processed_level_le
          (ms_core Mscan) (Z.of_nat rq)) as Hupper;
        rewrite Edq in Hupper; lia).

Tactic Notation "msat_analyze_scan_unchanged_close" ident(phase)
    constr(HC) constr(HS) constr(HL) :=
  unfold analyze_clause_scan_inv in *;
  subst phase;
  cbn -[Z.add Z.sub Z.mul Z.div Z.modulo] in *;
  intuition (try lia; try assumption);
  (try (rewrite HC; rewrite lits_denote_length; lia);
   try exact HS;
   try exact HL).

Ltac msat_analyze_scan_stop_facts j Ccur clause_words2 anz_n Mscan_2 K Mact :=
  let Hequiv := fresh "Hequiv" in
  let Hfalse := fresh "Hfalse" in
  let k := fresh "k" in
  let Hpos := fresh "Hpos" in
  let Hdypos := fresh "Hdypos" in
  (  assert (Hrootnonneg : 0 <= ms_root_level Mscan_2) by
    (let Hready := fresh "Hready" in
     match goal with
     | Hready0 : analysis_cancel_ready _ _ _ _ ?Ms _
       |- 0 <= ms_root_level ?Ms =>
         pose proof Hready0 as Hready
     end;
     destruct Hready as [Mready [Hcancel [Hequiv _]]];
     destruct Hcancel as [Hweak _]; destruct Hweak as [_ Hinv];
     assert (Hrootready : 0 <= ms_root_level Mready) by
       (destruct K;
        [pose proof (msw_shape Hinv)
        |pose proof (msa_shape Hinv)];
        match goal with
        | Hshape0 : solver_shape _ |- _ => unfold solver_shape in Hshape0
        end; tauto);
     unfold analysis_core_equiv in Hequiv;
     destruct Hequiv as [_ [_ [_ [_ [Eroot _]]]]];
     rewrite Eroot; exact Hrootready);
  assert (Hwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption);
  assert (HqIn : In (Znth j Ccur (Pos 0)) Ccur) by
    (apply Znth_In; lia);
  assert (Hqnth :
    Znth j Ccur (Pos 0) = lit_denote (Znth j clause_words2 0)) by
    (match goal with
     | HCwords : ?C = lits_denote ?words
       |- Znth ?idx ?C (Pos 0) = lit_denote (Znth ?idx ?words 0) =>
         rewrite HCwords; unfold lits_denote; apply Znth_map; lia
     end);
  match goal with
  | Hequiv0 : analysis_core_equiv ?Ma ?Ms,
    Hcert0 : propagation_conflict_cert _ _ ?Ma _ |- _ =>
      pose proof Hequiv0 as Hequiv;
      destruct Hcert0 as [_ [Hfalse _]]
  end;
  unfold analysis_core_equiv in Hequiv;
  destruct Hequiv as [_ [_ [_ [Ecore _]]]];
  rewrite <- Ecore in Hfalse;
  assert (Hqnonneg :
    0 <= literal_var (Znth j Ccur (Pos 0))) by
    (match goal with
     | HwfC : Forall (literal_wf ?nv) ?C,
       Hin : In (Znth ?idx ?C (Pos 0)) ?C |- _ =>
         rewrite Forall_forall in HwfC;
         pose proof (HwfC _ Hin) as Hlitwf;
         unfold literal_wf, var_in_range in Hlitwf; lia
     end);
  assert (Hqfalse :
    eval_partial_literal (assignment (msolver_view anz_n Mscan_2))
      (Znth j Ccur (Pos 0)) = Some false) by
    (rewrite msolver_view_assignment;
     pose proof (Hfalse _ HqIn) as Hqfalse_raw;
     unfold eval_partial_literal in Hqfalse_raw |- *;
     rewrite mt_pv_nonneg by exact Hqnonneg;
     unfold assigns_pv, assigns_val in Hqfalse_raw;
     exact Hqfalse_raw);
  destruct (eval_partial_false_shape _ _ Hqfalse) as
    [b [Hqassign Hqshape]];
  rewrite msolver_view_assignment in Hqassign;
  destruct (trail_pos (ms_core Mscan_2)
    (literal_var (Znth j Ccur (Pos 0)))) as [k|] eqn:Hpos;
  try (match goal with
    | Hpos0 : trail_pos ?t ?v = None,
      Hwf0 : mtrail_wf ?nv ?t,
      Hassign0 : mt_pv ?t ?v = Some ?b |- _ =>
        exfalso;
        pose proof (proj2 (view_unassigned_iff nv t v Hwf0) Hpos0)
          as Hunassigned;
        congruence
    end);
  assert (Hqlevel :
    level_of (msolver_view anz_n Mscan_2)
      (literal_var (Znth j Ccur (Pos 0))) =
      Some (level_of_index (ms_core Mscan_2) (Z.of_nat k))) by
    (cbn [msolver_view view_of level_of]; rewrite Hpos; reflexivity);
  assert (Hqcell :
    Znth (literal_var (Znth j Ccur (Pos 0)))
      (mt_levels (ms_core Mscan_2)) 0 =
      level_of_index (ms_core Mscan_2) (Z.of_nat k)) by
    (rewrite <- (trail_pos_var _ _ _ Hpos);
     apply (mtw_levels_agree Hwf);
     split; [lia|exact (trail_pos_bound _ _ _ Hpos)]);
  assert (Hqraw :
    Znth (literal_var (Znth j Ccur (Pos 0)))
      (mt_levels (ms_core Mscan_2)) 0 <= 0) by
    (rewrite Hqnth, lit_var_c_denote;
     match goal with
     | Hraw0 : Znth (?rv - 0) ?levels 0 <= 0,
       Heq0 : ?rv = lit_var_c ?word
       |- Znth (lit_var_c ?word) ?levels 0 <= 0 =>
         rewrite <- Heq0;
         replace rv with (rv - 0) by lia;
         exact Hraw0
     end);
  rewrite Hqcell in Hqraw;
  assert (Hat : at_current_level_b (msolver_view anz_n Mact)
    (Znth j Ccur (Pos 0)) = false) by
    (unfold at_current_level_b;
     cbn [msolver_view view_of level_of current_level];
     rewrite <- Ecore, Hpos; cbn [option_map];
     apply Z.eqb_neq; lia);
  assert (Hbelow : below_current_b (msolver_view anz_n Mact)
    (Znth j Ccur (Pos 0)) = false) by
    (unfold below_current_b;
     cbn [msolver_view view_of level_of current_level];
     rewrite <- Ecore, Hpos; cbn [option_map];
     destruct (Z.ltb 0
       (level_of_index (ms_core Mscan_2) (Z.of_nat k))) eqn:Hdypos;
     [apply Z.ltb_lt in Hdypos; lia|reflexivity]);
  assert (Hprefix :
    sublist 0 (j + 1) Ccur =
      sublist 0 j Ccur ++ (Znth j Ccur (Pos 0) :: nil)) by
    (rewrite (sublist_split 0 (j + 1) j Ccur) by lia;
     f_equal; apply sublist_single; lia);
  change (firstn (Z.to_nat (j + 1)) Ccur =
    firstn (Z.to_nat j) Ccur ++ (Znth j Ccur (Pos 0) :: nil)) in Hprefix).

Ltac msat_analyze_scan_stop_head phase j Ccur clause_words2 :=
  unfold analyze_clause_scan_inv in *;
  subst phase;
  cbn in *;
  replace (j - 0) with j in * by lia;
  assert (HClen : Zlength Ccur = Zlength clause_words2)
    by (match goal with
    | HCwords : Ccur = lits_denote clause_words2 |- _ =>
        rewrite HCwords, lits_denote_length
    end; reflexivity);
  intuition (try lia; try congruence).

Ltac msat_analyze_scan_stop opos act S0 R0 learnt0 x Sscan Rscan learnt
    words M phase j Ccur cw anz K Mact :=
  Left;
  Exists act opos S0 R0 learnt0 x Sscan Rscan learnt words M;
  Intros;
  split_pure_spatial;
  [ msat_cancel_sound; change (emp |-- emp); cancel
  | split_pures; dump_pre_spatial; try solve [auto | lia] ];
  msat_analyze_scan_stop_head phase j Ccur cw;
  msat_analyze_scan_stop_facts j Ccur cw anz M K Mact;
  [ unfold analyze_start_S in *;
    match goal with
    | Hp : firstn _ _ = firstn _ _ ++ _ |- _ => rewrite Hp in *
    end;
    rewrite filter_app in *; cbn [filter];
    match goal with
    | Ha : at_current_level_b _ _ = false |- _ => rewrite Ha in *
    end;
    cbn in *; rewrite app_nil_r in *; congruence
  | unfold analyze_start_learnt in *;
    match goal with
    | Hp : firstn _ _ = firstn _ _ ++ _ |- _ => rewrite Hp in *
    end;
    rewrite filter_app in *; cbn [filter];
    match goal with
    | Hb : below_current_b _ _ = false |- _ => rewrite Hb in *
    end;
    cbn in *; rewrite app_nil_r in *; congruence ].

Lemma msat_analysis_equiv_transport :
  forall n M M',
    analysis_core_equiv M M' ->
    ms_core M' = ms_core M /\
    ms_reason_of M' = ms_reason_of M /\
    msolver_view n M = msolver_view n M'.
Proof.
  intros n M M' Hequiv.
  pose proof (analysis_core_equiv_view__analyze n M M' Hequiv)
    as Eview.
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as [_ [_ [_ [Ecore [_ [_ [Ereason _]]]]]]].
  split; [exact Ecore|].
  split; [exact Ereason|].
  symmetry. exact Eview.
Qed.

Lemma msat_analysis_ready_scan_facts :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\
    stable_view (msolver_view n M) /\
    trail_implied F (ms_core M) /\
    ms_qtail M = Zlength (mt_trail (ms_core M)) /\
    (forall v b,
       assignment (msolver_view n M) v = Some b ->
       level_of (msolver_view n M) v = Some 0 ->
       entails_clause F (satisfying_literal v b :: nil)).
Proof.
  intros n F A_arr K M focus Hready.
  destruct (analysis_cancel_ready_weak_facts__analyze
    n F A_arr K M focus Hready) as (_ & _ & _ & Hwf & _ & _ & Htrailimpl).
  pose proof (analysis_cancel_ready_qtail_eq__analyze
    n F A_arr K M focus Hready) as Hqtail.
  assert (Hstable : stable_view (msolver_view n M)).
  { destruct Hready as [M0 [Hcancel [Hequiv _]]].
    destruct Hcancel as [Hweak _]. destruct Hweak as [_ Hinv].
    rewrite (analysis_core_equiv_view__analyze n M0 M Hequiv).
    destruct K; [exact (msw_stable Hinv)|exact (msa_stable Hinv)]. }
  split; [exact Hwf|].
  split; [exact Hstable|].
  split; [exact Htrailimpl|].
  split; [symmetry; exact Hqtail|].
  intros v b Hass Hlev.
  destruct Hstable as [Hgrounded _].
  destruct (Hgrounded v b Hass) as [d [r [Hd [Hr _]]]].
  assert (d = 0) by congruence. subst d.
  cbn [msolver_view view_of assignment_rank] in Hr.
  assert (Hrbound :
    0 <= Z.of_nat r < Zlength (mt_trail (ms_core M))).
  { split; [lia|exact (trail_pos_bound _ _ _ Hr)]. }
  pose proof (trail_pos_var _ _ _ Hr) as Hvar.
  assert (Hcell :
    Znth v (mt_assigns (ms_core M)) 0 =
    lit_sig (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)).
  { rewrite <- Hvar.
    exact (Forall_Znth_elim _ _ _ 0 _ (mtw_trail_true Hwf) Hrbound). }
  assert (Hvnonneg : 0 <= v).
  { pose proof (Forall_Znth_elim _ _ _ 0 (Z.of_nat r)
      (mtw_trail_lits Hwf) Hrbound) as Hlit.
    pose proof (lit_var_c_in_range n
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) Hlit) as Hvrange.
    change (0 <= trail_var (ms_core M) (Z.of_nat r) < n) in Hvrange.
    rewrite Hvar in Hvrange. lia. }
  assert (Hbpol :
    b = lit_pol (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)).
  { cbn [msolver_view view_of assignment] in Hass.
    rewrite mt_pv_nonneg in Hass by exact Hvnonneg.
    rewrite Hcell, lbool_val_lit_sig in Hass. congruence. }
  specialize (Htrailimpl (Z.of_nat r)
    (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)
    Hrbound eq_refl).
  cbn [msolver_view view_of level_of] in Hlev.
  rewrite Hr in Hlev. cbn [option_map] in Hlev.
  injection Hlev as Hzero.
  rewrite Hzero in Htrailimpl.
  unfold decisions_upto, ztake in Htrailimpl. cbn in Htrailimpl.
  assert (Hvarc : lit_var_c
    (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) = v) by exact Hvar.
  rewrite lit_denote_satisfying, Hvarc, <- Hbpol in Htrailimpl.
  unfold cnf_with_units in Htrailimpl. cbn in Htrailimpl.
  rewrite app_nil_r in Htrailimpl.
  exact Htrailimpl.
Qed.

Lemma msat_trail_lit_var_range :
  forall n M idx,
    mtrail_wf n (ms_core M) ->
    0 <= idx < Zlength (mt_trail (ms_core M)) ->
    0 <= lit_var_c (Znth idx (mt_trail (ms_core M)) 0) < n.
Proof.
  intros n M idx Hwf Hidx.
  apply lit_var_c_in_range.
  exact (Forall_Znth_elim _ _ _ 0 idx (mtw_trail_lits Hwf) Hidx).
Qed.

Lemma msat_analysis_reason_head_var :
  forall n F A_arr K M focus x Ccur,
    analysis_cancel_ready n F A_arr K M focus ->
    0 <= x < n ->
    ms_reason_of M x = Some Ccur ->
    literal_var (Znth 0 Ccur (Pos 0)) = x.
Proof.
  intros n F A_arr K M focus x Ccur Hready Hxrange Hreason_M.
  destruct Hready as [Mready [Hcancel [Hequiv _]]].
  destruct Hcancel as [Hweak _]. destruct Hweak as [_ Hinv].
  assert (Hsize : n = ms_size Mready) by
    (destruct K; [exact (msw_size Hinv)|exact (msa_size Hinv)]).
  assert (Hmatch : reasons_match n (ms_core Mready) (msolver_db Mready)
    (ms_reason_words Mready) (ms_reason_of Mready)) by
    (destruct K;
     [exact (msw_reasons_mem Hinv)|exact (msa_reasons_mem Hinv)]).
  assert (Hhead : reason_head_ok Mready) by
    (destruct K;
     [exact (msw_reason_head Hinv)|exact (msa_reason_head Hinv)]).
  assert (Hdbwf : db_wf n (msolver_db Mready)) by
    (destruct K; [exact (msw_db_wf Hinv)|exact (msa_db_wf Hinv)]).
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    [_ [_ [_ [_ [_ [_ [Ereason _]]]]]]].
  assert (Hreason : ms_reason_of Mready x = Some Ccur).
  { rewrite <- Ereason. exact Hreason_M. }
  specialize (Hmatch x Hxrange).
  remember (Znth x (ms_reason_words Mready) 0) as w eqn:Hw.
  assert (Hwneq : w <> 0).
  { intro Hw0.
    unfold reason_word_ok in Hmatch.
    rewrite Hw0 in Hmatch. cbn in Hmatch. congruence. }
  assert (Hwzero : Z.eqb w 0 = false) by
    (apply Z.eqb_neq; exact Hwneq).
  destruct (is_tag w) eqn:Htag.
  - unfold reason_word_ok in Hmatch. rewrite Hwzero, Htag in Hmatch.
    destruct Hmatch as [_ Hshape]. rewrite Hreason in Hshape.
    inversion Hshape. cbn.
    rewrite lit_var_c_denote, trail_lit_of_var; lia.
  - unfold reason_word_ok in Hmatch. rewrite Hwzero, Htag in Hmatch.
    destruct Hmatch as [_ [co [Hin Hshape]]].
    rewrite Hreason in Hshape. inversion Hshape; subst Ccur.
    assert (Hxsize : 0 <= x < ms_size Mready) by lia.
    specialize (Hhead x co Hxsize).
    rewrite <- Hw in Hhead.
    specialize (Hhead Htag Hwneq Hin).
    pose proof (db_wf_obj n (msolver_db Mready) w co Hdbwf Hin) as Hobj.
    unfold obj_wf in Hobj. destruct Hobj as [Hlen _].
    unfold denote_obj, lits_denote.
    rewrite (Znth_map Z literal lit_denote (co_lits co) 0 0 (Pos 0)) by lia.
    rewrite lit_var_c_denote.
    exact Hhead.
Qed.

Lemma msat_analyze_scan_rank_split :
  forall F a S0 R0 learnt0 Sscan Rscan learnt_scan x ind,
    0 <= ind ->
    analyze_inv F a Sscan Rscan learnt_scan ->
    analyze_inv F a S0 R0 learnt0 ->
    Rscan = x :: R0 ->
    In x S0 ->
    assignment_rank a x = Some (Z.to_nat (ind + 1)) ->
    (forall y, In y Sscan ->
       exists r, assignment_rank a y = Some r /\ Z.of_nat r <= ind) /\
    (forall y, In y Rscan ->
       exists r, assignment_rank a y = Some r /\ ind < Z.of_nat r).
Proof.
  intros F a S0 R0 learnt0 Sscan Rscan learnt_scan x ind
    Hind Hinvscan Hinv0 HRscan HinS Hrankx.
  split.
  - intros y Hy.
    pose proof Hinvscan as Htmp.
    destruct Htmp as [_ [_ [_ [_ [_ [HrankR _]]]]]].
    rewrite Forall_forall in HrankR.
    specialize (HrankR x ltac:(rewrite HRscan; left; reflexivity) y Hy).
    destruct HrankR as [ry [rx [Hry [Hrx Hlt]]]].
    rewrite Hrankx in Hrx. injection Hrx as <-.
    exists ry. split; [exact Hry|].
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by lia. lia.
  - intros y Hy. rewrite HRscan in Hy. cbn in Hy.
    destruct Hy as [<-|Hy].
    + exists (Z.to_nat (ind + 1)). split; [exact Hrankx|].
      rewrite Z2Nat.id by lia. lia.
    + pose proof Hinv0 as Htmp.
      destruct Htmp as [_ [_ [_ [_ [_ [HrankR _]]]]]].
      rewrite Forall_forall in HrankR.
      specialize (HrankR y Hy x HinS).
      destruct HrankR as [rx [ry [Hrx [Hry Hlt]]]].
      rewrite Hrankx in Hrx. injection Hrx as <-.
      exists ry. split; [exact Hry|].
      apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by lia. lia.
Qed.

Lemma msat_clause_head_tail :
  forall Ccur j,
    0 < j ->
    j = Zlength Ccur ->
    Ccur = Znth 0 Ccur (Pos 0) :: tl Ccur /\
    skipn (Pos.to_nat 1) (firstn (Z.to_nat j) Ccur) = tl Ccur.
Proof.
  intros Ccur j Hjpos Hjfull.
  assert (HCcons : Ccur = Znth 0 Ccur (Pos 0) :: tl Ccur).
  { destruct Ccur as [|q qs]; [cbn in Hjfull; lia|reflexivity]. }
  split; [exact HCcons|].
  assert (Hprefixall : firstn (Z.to_nat j) Ccur = Ccur).
  { rewrite Hjfull, Zlength_correct, Nat2Z.id. apply firstn_all. }
  rewrite Hprefixall. cbn [Pos.to_nat]. destruct Ccur; reflexivity.
Qed.

Lemma msat_resolve_head_drop :
  forall a x Ccur S0 R0 learnt0,
    Ccur = Znth 0 Ccur (Pos 0) :: tl Ccur ->
    literal_var (Znth 0 Ccur (Pos 0)) = x ->
    In x S0 ->
    resolve_S a x Ccur S0 R0 learnt0 =
      resolve_S a x (tl Ccur) S0 R0 learnt0 /\
    resolve_learnt a Ccur S0 R0 learnt0 =
      resolve_learnt a (tl Ccur) S0 R0 learnt0.
Proof.
  intros a x Ccur S0 R0 learnt0 HCcons Hheadvar HinS.
  assert (Htagx : zmem x (analyze_tags S0 R0 learnt0) = true).
  { apply zmem_true_iff. unfold analyze_tags.
    apply in_or_app. left. exact HinS. }
  split.
  - unfold resolve_S, resolve_new_S.
    rewrite HCcons at 1. cbn [filter map].
    destruct (at_current_level_b a (Znth 0 Ccur (Pos 0))); cbn [filter map].
    + rewrite Hheadvar, Htagx. cbn. reflexivity.
    + reflexivity.
  - unfold resolve_learnt, resolve_new_lits.
    rewrite HCcons at 1. cbn [filter].
    rewrite Hheadvar, Htagx, andb_false_r. cbn. reflexivity.
Qed.

Lemma msat_trail_pos_var_range :
  forall n M x k,
    mtrail_wf n (ms_core M) ->
    0 <= k ->
    trail_pos (ms_core M) x = Some (Z.to_nat k) ->
    0 <= x < n.
Proof.
  intros n M x k Hwf Hk Hpos.
  assert (Hidx : 0 <= k < Zlength (mt_trail (ms_core M))).
  { split; [lia|].
    pose proof (trail_pos_bound _ _ _ Hpos) as Hb.
    rewrite Z2Nat.id in Hb by lia. exact Hb. }
  pose proof (msat_trail_lit_var_range n M k Hwf Hidx) as Hrange.
  pose proof (trail_pos_var _ _ _ Hpos) as Hvar.
  rewrite Z2Nat.id in Hvar by lia.
  change (lit_var_c (Znth k (mt_trail (ms_core M)) 0) = x) in Hvar.
  rewrite Hvar in Hrange. exact Hrange.
Qed.


Ltac msat_analyze_reason_target_lit_bound :=
  (LLM_pre_process ltac:(lia || int_auto));
  match goal with
  | Hrtw : reason_target_wf _ _ _ ?cc _,
    Htag : is_tag ?cc = msat_true |- _ =>
      unfold reason_target_wf in Hrtw;
      destruct Hrtw as [_ [_ [_ [_ Hshape]]]];
      destruct Hshape as [[_ [_ Hlit]] | [co [Hnot_tag _]]];
      [ unfold lit_wf_c in Hlit; (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]); lia
      | rewrite Htag in Hnot_tag; discriminate ]
  end.

Ltac msat_analyze_cancel_heap_tail :=
  dump_pre_spatial;
  try lia;
  try match goal with
        Hshape : solver_shape ?M |- _ =>
          unfold solver_shape in Hshape; intuition congruence
      end;
  match goal with
  | Hready : analysis_cancel_ready ?anz_n _ _ _ ?M _ |- _ =>
      destruct Hready as [? [? [? [Hheap _]]]];
      unfold order_heap_wf, msolver_heap; cbn;
      try match goal with
            Hsize : ms_size M = anz_n |- _ => rewrite Hsize
          end;
      exact Hheap
  end.

Lemma ms_analyze_db_triple_positive :
  forall prob learnt b lits,
    clause_db_rep prob
    ** clause_db_rep learnt
    ** binary_scratch_rep b lits
    |-- “ Forall (fun e => 0 < fst e) prob
          /\ Forall (fun e => 0 < fst e) learnt
          /\ 0 < b ”.
Proof.
  intros prob learnt b lits.
  prop_apply_p (clause_db_rep_positive__analyze prob).
  Intros_p H1.
  prop_apply_p (clause_db_rep_positive__analyze learnt).
  Intros_p H2.
  prop_apply_p (binary_scratch_positive b lits).
  Intros_p H3.
  dump_pre_spatial. tauto.
Qed.

Ltac msat_analyze_word_range_context n j cw :=
  assert (Hlit : lit_wf_c n (Znth (j - 0) cw 0));
  [ apply (Forall_Znth_elim _ _ _ 0 (j - 0)); [assumption | lia]
  | unfold lit_wf_c in Hlit; msat_manual_entailer_with ltac:(lia) ].

Tactic Notation "msat_analyze_clause_word_range" ident(n_v) ident(j_v)
    ident(cw) constr(k) :=
  msat_analyze_stage_clause_word_range_at_fixed_index n_v k cw;
  msat_analyze_word_range_context n_v j_v cw.

Ltac msat_analyze_learnt_lit_range_tail hf nn cw jj :=
  dump_pre_spatial;
  pose proof
    (Forall_Znth_elim Z (lit_wf_c nn) cw 0 (jj - 0) hf ltac:(lia)) as Hwf;
  unfold lit_wf_c in Hwf;
  lia.

Tactic Notation "msat_analyze_clause_word_int_range_via_wf"
    ident(j) ident(cw) ident(Hlit) :=
  msat_split_after_llm; dump_pre_spatial;
  msat_analyze_close_clause_word_int_range j cw Hlit.

Ltac msat_analyze_learnt_offset_congruence :=
  msat_split_after_llm;
  dump_pre_spatial;
  rewrite Z.sub_0_r in *;
  congruence.

Tactic Notation "msat_analyze_trail_lit"
    ident(Hready) constr(i) ident(Hi) "as" ident(Hlit) :=
  lazymatch type of Hready with
  | analysis_cancel_ready ?n ?F ?A ?K ?M ?focus =>
    let Hwf := fresh "Htrailwf" in
    pose proof (analysis_cancel_ready_trail_wf__analyze
      n F A K M focus Hready) as Hwf;
    pose proof (Forall_Znth_elim _ _ _ 0 i (mtw_trail_lits Hwf) Hi) as Hlit;
    clear Hwf
  end.

Lemma msat_analyze_minimize_scan_assigned :
  forall (n : Z) (F : cnf) (M : msolver)
         (original kept removed words T : list Z) (i j : Z),
    analyze_clause_cert n F M original ->
    analyze_minimize_loop_inv n M original kept removed words T i j ->
    incl (map lit_var_c words) (map lit_var_c (mt_trail (ms_core M))) ->
    0 <= i -> i < Zlength words ->
    assigned_below_current (msolver_view n M) (lit_var_c (Znth (i - 0) words 0)).
Proof.
  intros n F M original kept removed words T i j Hcert0 Hinv H_incl Hi0 Hi1.
  unfold analyze_minimize_loop_inv in Hinv; simpl in Hinv.
  unfold analyze_clause_cert, uip_exit_cert in Hcert0.
  destruct Hinv as [Hj Htmp].
  destruct Htmp as [Hji Htmp].
  destruct Htmp as [HiLen Htmp].
  destruct Htmp as [Hlen Htmp].
  destruct Htmp as [Hhead Htmp].
  destruct Htmp as [Horig Htmp].
  destruct Htmp as [Hwords Htmp].
  destruct Htmp as [Hkept Htmp].
  destruct Htmp as [Hremoved Htmp].
  destruct Htmp as [Hsuffix Htmp].
  destruct Htmp as [Htags Htmp].
  destruct Htmp as [Hperm Htmp].
  destruct Htmp as [Hwitness Htmp].
  destruct Htmp as [Hscope Htmp].
  destruct Htmp as [HremovedT Htmp].
  destruct Htmp as [HallT Hprefix].
  destruct Hcert0 as [Hcert Hroot].
  destruct Hcert as [Hsound HcertRest].
  destruct HcertRest as [Hnodup Hexists].
  destruct Hexists as [uh [ur [Hule [Hul Hrest]]]].
  set (w := Znth (i - 0) words 0).
  assert (Hsub : In w (sublist i (Zlength original) original)).
  { assert (Hsub0 : In w (sublist i (Zlength words) words)).
    { unfold w. replace (i - 0) with i by lia.
      pose proof (Znth_In Z (sublist i (Zlength words) words) 0 0) as H0.
      rewrite (Znth_sublist 0 i 0 (Zlength words) words) in H0 by lia.
      apply H0. rewrite Zlength_sublist by lia. lia. }
    rewrite Hlen in Hsub0. rewrite Hsuffix in Hsub0. exact Hsub0. }
  assert (HlitPending : In (lit_denote w)
    (lits_denote (sublist i (Zlength original) original))).
  { apply lits_denote_in. exact Hsub. }
  assert (HlitTail : In (lit_denote w) (lits_denote (tl original))).
  { eapply Permutation_in; [exact (Permutation_sym Hperm)|].
    apply in_or_app. right. apply in_or_app. right. exact HlitPending. }
  destruct original as [|wh wt].
  - simpl in HlitTail. contradiction.
  - simpl in Hule, HlitTail.
    inversion Hule; subst.
    rewrite Forall_forall in Hrest.
    destruct (Hrest _ HlitTail) as [d [Hd Hlt]].
    rewrite lit_var_c_denote in Hd.
    assert (Htrail : In (lit_var_c w)
      (map lit_var_c (mt_trail (ms_core M)))).
    { apply H_incl. apply in_map. apply Znth_In. lia. }
    destruct (find_var_pos_in _ _ Htrail) as [r Hr].
    unfold assigned_below_current.
    exists d. exists r.
    split; [exact Hd | split; [exact Hr | exact Hlt]].
Qed.

Ltac msat_analyze_clause_ptr_even :=
  match goal with
  | He : Z.even _ = true |- _ => apply clause_ptr_mod2; exact He
  end.

Tactic Notation "msat_analyze_clause_db_side" ident(cc) ident(Mc) constr(other_db) :=
  let cco := fresh "co" in
  let cpre := fresh "pre" in
  let cpost := fresh "post" in
  ( Intros cco cpre cpost;
    match goal with
    | Hd : _ = _ ++ _ :: _ /\ _ /\ _ |- _ =>
        destruct Hd as [Hdecomp [Hlits Htag]];
        rewrite Hdecomp;
        sep_apply_r_atomic (clause_db_rep_app_intro cpre ((cc, cco) :: cpost));
        rewrite clause_db_rep_cons;
        unfold MiniSatClause.rep;
        cbn [fst snd]; rewrite Htag, Hlits;
        split_pure_spatial;
        [ cancel (clause_db_rep cpost); cancel
        | split_pures; dump_pre_spatial; repeat split;
          [ apply Zlength_nonneg | lia | msat_analyze_clause_ptr_even ] ]
    end ).

(* Only the binary arm differs
   between the callers, so it is the single tactic argument. *)
Tactic Notation "msat_analyze_focus_clause_db" ident(cc) ident(Mc) tactic3(binary_arm) :=
  let htag := fresh "H_is_tag" in
  ( bind_fact ( is_tag cc = msat_false ) as htag;
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]);
    assert (Heven : Z.even cc = true)
      by (rewrite <- Z.negb_odd;
          unfold is_tag, msat_false in htag;
          rewrite htag; reflexivity);
    unfold analysis_clause_remainder;
    Split;
    [ binary_arm
    | Intros_p Hreal;
      unfold clause_db_pair_remainder;
      Split;
      [ msat_analyze_clause_db_side cc Mc (ms_learnt Mc)
      | msat_analyze_clause_db_side cc Mc (ms_prob Mc) ] ] ).

(* The pointer bound is the
   one fact the VC gets from the frame rather than from the databases. *)
Lemma analysis_focus_clause_db_close :
  forall anz_n Mdone c is_learnt2 clause_words2 lits,
    db_wf anz_n (msolver_db Mdone) ->
    solver_shape Mdone ->
    0 <= ms_binary Mdone ->
    clause_lits_pointer c lits ->
    clause_hdr_addr c # Int |-> clause_hdr_word is_learnt2
        (Zlength clause_words2) **
    activity_state c is_learnt2 (Zlength clause_words2) **
    IntArray.seg lits 0 (Zlength clause_words2) clause_words2 **
    analysis_clause_remainder Mdone c is_learnt2 clause_words2
    |-- clause_db_rep (ms_prob Mdone) **
        clause_db_rep (ms_learnt Mdone) **
        binary_scratch_rep (ms_binary Mdone) (ms_binary_lits Mdone).
Proof.
  intros anz_n Mdone c is_learnt2 clause_words2 lits Hdb Hshape Hbinary_nonneg
    H_clause_lits_pointer.
    unfold clause_lits_pointer in H_clause_lits_pointer. subst lits.
    unfold analysis_clause_remainder.
    Split.
    - Intros_p Hbinary.
      destruct Hbinary as [Hc [Htag [Hwords_binary Hinitialized]]].
      subst c is_learnt2 clause_words2.
      rewrite (binary_scratch_initialized _ _ Hinitialized).
      unfold MiniSatClause.rep.
      split_pure_spatial.
      + cancel (clause_db_rep (ms_prob Mdone)).
        cancel.
      + dump_pre_spatial.
        repeat split.
        * apply Zlength_nonneg.
        * pose proof (solver_shape_binary_nonnull Mdone Hshape). lia.
        * apply clause_ptr_mod2. unfold solver_shape in Hshape. tauto.
    - Intros_p Hreal.
      unfold clause_db_pair_remainder.
      Split.
      + Intros co pre post.
        destruct H as [Hdecomp [Hwords_co Htag]].
        assert (Hin : In (c, co) (msolver_db Mdone)).
        { unfold msolver_db. rewrite Hdecomp.
          apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
        assert (Hpos : 0 < c) by (eapply db_wf_ptr_pos; eauto).
        assert (Heven : Z.even c = true) by (eapply db_wf_even; eauto).
        rewrite Hdecomp.
        sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
        rewrite clause_db_rep_cons.
        unfold MiniSatClause.rep.
        cbn [fst snd]. rewrite Htag, Hwords_co.
        split_pure_spatial.
        * cancel (clause_db_rep pre).
          cancel.
        * dump_pre_spatial.
          repeat split.
          -- apply Zlength_nonneg.
          -- exact Hpos.
          -- apply clause_ptr_mod2. exact Heven.
      + Intros co pre post.
        destruct H as [Hdecomp [Hwords_co Htag]].
        assert (Hin : In (c, co) (msolver_db Mdone)).
        { unfold msolver_db. rewrite Hdecomp.
          apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
        assert (Hpos : 0 < c) by (eapply db_wf_ptr_pos; eauto).
        assert (Heven : Z.even c = true) by (eapply db_wf_even; eauto).
        rewrite Hdecomp.
        sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
        rewrite clause_db_rep_cons.
        unfold MiniSatClause.rep.
        cbn [fst snd]. rewrite Htag, Hwords_co.
        split_pure_spatial.
        * cancel (clause_db_rep pre).
          cancel.
        * dump_pre_spatial.
          repeat split.
          -- apply Zlength_nonneg.
          -- exact Hpos.
          -- apply clause_ptr_mod2. exact Heven.
Qed.

Lemma analyze_backward_scan_shape_db :
  forall anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt ind Sdone Rdone
    learnt_done,
    analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt
      ind Sdone Rdone learnt_done ->
    Zlength (ms_stats Mdone) = 11 ->
    Zlength (ms_activity Mdone) = anz_n ->
    solver_shape Mdone /\ db_wf anz_n (msolver_db Mdone).
Proof.
  intros anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt ind Sdone Rdone
    learnt_done Hscan Hstats Hactivity.
  unfold analyze_backward_scan_inv in Hscan.
  destruct Hscan as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Hlits_done
    [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  split.
  {
    destruct Hready as
      (Mbase & Hcancel & Hequiv & Hheap & Hcovers & Hreasonless & Hfocus & Hcla).
    destruct Hcancel as [[Hpending Hweak] Hcancel_rest].
    destruct K as [A_inst | A_proc]; cbn in Hweak.
    - pose proof (msw_size Hweak) as Hsize.
      pose proof (msw_shape Hweak) as Hshape0.
      unfold analysis_core_equiv in Hequiv;
        unfold solver_shape in Hshape0 |- *;
        unfold heap_wf, msolver_heap in Hheap; cbn in Hheap;
        unfold analysis_tags_exact in Htags;
        intuition (try congruence; try lia).
    - pose proof (msa_size Hweak) as Hsize.
      pose proof (msa_shape Hweak) as Hshape0.
      unfold analysis_core_equiv in Hequiv;
        unfold solver_shape in Hshape0 |- *;
        unfold heap_wf, msolver_heap in Hheap; cbn in Hheap;
        unfold analysis_tags_exact in Htags;
        intuition (try congruence; try lia).
  }
  {
    destruct Hready as [Mbase [Hcancel [Hequiv _]]].
    destruct Hcancel as [Hweak0 _].
    destruct Hweak0 as [_ Hinv].
    assert (Hdb0 : db_wf anz_n (msolver_db Mbase)).
    { destruct K; cbn in Hinv.
      - exact (msw_db_wf Hinv).
      - exact (msa_db_wf Hinv). }
    unfold analysis_core_equiv in Hequiv.
    destruct Hequiv as
      (_ & _ & _ & _ & _ & _ & _ & Hprob & Hlearnt & _).
    unfold msolver_db in *. rewrite Hprob, Hlearnt. exact Hdb0.
  }
Qed.

Lemma analyze_stats_frame_close :
  forall s Mdone,
    stats_analyze_frame &(s # "solver_t" ->ₛ "stats")
        (ms_stats Mdone) **
    &(s # "solver_t" ->ₛ "stats" .ₛ "max_literals") # UInt64
      |-> Znth 9 (ms_stats Mdone) 0 **
    &(s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") # UInt64
      |-> Znth 10 (ms_stats Mdone) 0
    |-- stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mdone).
Proof.
  intros s Mdone.
    unfold stats_analyze_frame, stats_rep.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
    csimpl.
    msat_manual_entailer_with ltac:(lia).
Qed.

(* Traverse both
   separating-conjunction branches; use reflexivity at leaves because the
   goal uses Syntax.sepcon rather than this file's notation. *)
Ltac msat_sep_replace_atom_with_emp atom P :=
  lazymatch P with
  | context C [atom] =>
      let R := context C [emp] in constr:(R)
  end.

(* Writing the two literal-statistics slots that [solver_analyze] updates: slot 9
   (max_literals) and slot 10 (tot_literals) of an eleven-slot statistics list. *)
Lemma stats_pair_update_slots :
  forall (stats : list Z) (max_lits tot_lits : Z),
    Zlength stats = 11 ->
    (forall k, 0 <= k < 9 ->
       Znth k (replace_Znth 9 max_lits (replace_Znth 10 tot_lits stats)) 0 =
       Znth k stats 0) /\
    Znth 9 (replace_Znth 9 max_lits (replace_Znth 10 tot_lits stats)) 0 =
      max_lits /\
    Znth 10 (replace_Znth 9 max_lits (replace_Znth 10 tot_lits stats)) 0 =
      tot_lits.
Proof.
  intros stats max_lits tot_lits Hlen.
  split; [| split].
  - intros k Hk.
    rewrite (Znth_replace_Znth_Diff 0
      (replace_Znth 10 tot_lits stats) 9 k max_lits)
      by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite (Znth_replace_Znth_Diff 0 stats 10 k tot_lits)
      by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - rewrite (Znth_replace_Znth_Same 0
      (replace_Znth 10 tot_lits stats) 9 max_lits)
      by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - rewrite (Znth_replace_Znth_Diff 0
      (replace_Znth 10 tot_lits stats) 9 10 max_lits)
      by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite (Znth_replace_Znth_Same 0 stats 10 tot_lits)
      by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
Qed.

(* [analysis_tags_exact] with an EMPTY tagged vector forces every tag word to
   0: the iff turns a set bit into membership in [nil], and the [Forall] bounds
   every entry to {0,1}. *)
Lemma analysis_tags_exact_nil_zero :
  forall (n : Z) (tags : list Z),
    analysis_tags_exact n tags nil -> tags = repeat_Z 0 n.
Proof.
  intros n tags Hexact.
  unfold analysis_tags_exact in Hexact.
  destruct Hexact as [Htags_len [_ [_ [Hbits Hiff]]]].
  apply (list_eq_nth Z tags (repeat_Z 0 n) 0).
  - unfold repeat_Z. rewrite repeat_length.
    rewrite Zlength_correct in Htags_len.
    rewrite <- Htags_len, Nat2Z.id. reflexivity.
  - intros k Hk.
    unfold repeat_Z. rewrite nth_repeat.
    assert (Hin : In (nth k tags 0) tags)
      by (apply nth_In; exact Hk).
    rewrite Forall_forall in Hbits.
    specialize (Hbits _ Hin).
    destruct Hbits as [Hz | Hz]; [exact Hz|].
    exfalso.
    assert (Hkrange : 0 <= Z.of_nat k < n).
    { rewrite Zlength_correct in Htags_len.
      apply Nat2Z.inj_lt in Hk. lia. }
    assert (Hone : Znth (Z.of_nat k) tags 0 = 1).
    { unfold Znth.
      replace (Z.to_nat (Z.of_nat k)) with k by lia.
      exact Hz. }
    apply (proj1 (Hiff (Z.of_nat k) Hkrange)) in Hone.
    contradiction.
Qed.

Ltac msat_scalar_side_conditions :=
  first [ solve [msat_manual_entailer_with ltac:(int_auto || lia || tauto)]
        | solve [(Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto || lia || tauto)] ..])]
        | solve [dump_pre_spatial; lia] ].

Ltac msat_clause_new_side_conditions :=
  rewrite ?IntArray.undef_seg_empty;
  replace (0 - 0) with 0 in * by reflexivity;
  replace (1 - 0) with 1 in * by reflexivity;
  try match goal with H : solver_shape ?m |- _ =>
    assert (Hsmall : 2 * ms_size m <= 2147483647)
      by (unfold solver_shape in H; tauto)
  end;
  try match goal with H : Forall (lit_wf_c ?nn) ?words |- _ =>
    pose proof (Forall_lit_wf_Znth nn words 0 H ltac:(lia)) as Hlit0;
    pose proof (Forall_lit_wf_Znth nn words 1 H ltac:(lia)) as Hlit1;
    pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0;
    pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1;
    unfold lit_wf_c in Hlit0, Hlit1, Hneg0, Hneg1
  end;
  try match goal with
  | |- context[IntArray.missing_i ?x ?idx ?lo ?hi ?words] =>
      sep_apply (IntArray.seg_split_to_missing_i x lo idx hi words 0 ltac:(lia))
  end;
  first [ solve [msat_manual_entailer_with ltac:(lia || tauto ||
            (unfold clause_new_stage_ready_root; tauto))]
        | solve [(Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia || tauto ||
            (unfold clause_new_stage_ready_root; tauto))] ..])]
        | solve [msat_entailer_with ltac:(lia || tauto ||
            (unfold clause_new_stage_ready_root; tauto))]
        | solve [dump_pre_spatial; lia] ].

Ltac msat_clause_new_safety :=
  rewrite ?sizeof_int in *;
  replace (0 - 0) with 0 in * by reflexivity;
  replace (1 - 0) with 1 in * by reflexivity;
  try match goal with |- context[signed_last_nbits ?x 32] =>
    pose proof (signed_Lastnbits_range x 32 ltac:(lia)) as Hbits;
    change (-2147483648 <= signed_last_nbits x 32 < 2147483648) in Hbits
  end;
  first [ solve [dump_pre_spatial; lia]
        | solve [(Intros; split_pures; dump_pre_spatial; solve [auto | (first
            [solve [int_auto] | solve [lia] | solve [nia] | solve [tauto]])])]
        | solve [int_auto]
        | solve [nia] ].

Lemma msat_binary_reason_current_level :
  forall n F A_arr K M focus x c Ccur,
    analysis_cancel_ready n F A_arr K M focus ->
    reason_target_wf n M x c Ccur ->
    level_of (msolver_view n M) x = Some (current_level (msolver_view n M)) ->
    is_tag c = msat_true ->
    0 <= lit_var_c (tag_lit c) < n /\
    level_of (msolver_view n M) (lit_var_c (tag_lit c)) =
      Some (current_level (msolver_view n M)).
Proof.
  intros n F A_arr K M focus x c Ccur Hready Htarget Hlevel Htagged.
  unfold msat_true in Htagged.
  destruct Htarget as
    [Hxrange [Hword [Hnonzero [Hreason Htarget]]]].
  destruct Htarget as
    [[Htag [Hpositive Hqwf]] |
     [co [Hnottag [Hnotbin [Hin HC]]]]].
  2: { rewrite Htagged in Hnottag. discriminate. }
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
  assert (Hxn : 0 <= x < n) by lia.
  assert (Htagword :
    is_tag (Znth x (ms_reason_words M) 0) = true).
  { rewrite <- Hword. exact Htag. }
  destruct (Hbinary x Hxrange Htagword) as
    [Hqwf' [Hsame Hneq]].
  rewrite <- Hword in Hsame, Hneq.
  assert (Hqrange : 0 <= lit_var_c (tag_lit c) < n).
  { apply lit_var_c_in_range. exact Hqwf. }
  pose proof (Hmatch x Hxn) as Hok.
  rewrite <- Hword in Hok.
  pose proof (reason_word_ok_tag
    (ms_core M) x (msolver_db M) c (ms_reason_of M x)
    Hpositive Htag Hok) as HCshape.
  rewrite Hreason in HCshape. inversion HCshape as [HCeq].
  subst Ccur.
  pose proof Hready as Hreadycopy.
  destruct Hreadycopy as [M0 [Hcancel [Hequiv Hrest]]].
  destruct Hcancel as [[Hpending Hweak] Hcancelrest].
  assert (Hinvpair :
    mtrail_wf n (ms_core M0) /\
    stable_view (msolver_view n M0)).
  { destruct K as [A_inst | A_proc]; cbn in Hweak.
    - split; [exact (msw_trail_wf Hweak) | exact (msw_stable Hweak)].
    - split; [exact (msa_trail_wf Hweak) | exact (msa_stable Hweak)]. }
  destruct Hinvpair as [Hwf0 Hstable0].
  destruct Hequiv as
    [Esize [_ [_ [Ecore [_ [Ewords [Ereason [Eprob [Elearnt Erest]]]]]]]]].
  assert (Hwf : mtrail_wf n (ms_core M)).
  { rewrite Ecore. exact Hwf0. }
  assert (Hview : msolver_view n M = msolver_view n M0).
  { unfold msolver_view, msolver_clauses, msolver_db.
    rewrite Ecore, Ereason, Eprob, Elearnt. reflexivity. }
  assert (Hstable : stable_view (msolver_view n M)).
  { rewrite Hview. exact Hstable0. }
  pose proof Hlevel as Hlevelx.
  unfold msolver_view, view_of in Hlevelx.
  cbn in Hlevelx.
  destruct (trail_pos (ms_core M) x) as [kx|] eqn:Hposx;
    cbn in Hlevelx; [|discriminate].
  inversion Hlevelx as [Hidxx].
  destruct (assignment (msolver_view n M) x) as [b|] eqn:Hassign.
  2: {
    change (mt_pv (ms_core M) x = None) in Hassign.
    apply (proj1 (view_unassigned_iff n (ms_core M) x Hwf)) in Hassign.
    rewrite Hposx in Hassign. discriminate. }
  destruct Hstable as [Hground Hclosed].
  destruct (Hground x b Hassign) as
    [d [rx [Hld [Hrank Hreason_valid]]]].
  destruct Hreason_valid as
    [Hnone | [C' [Hreason' Hvalid]]].
  { unfold msolver_view, view_of in Hnone. cbn in Hnone.
    rewrite Hposx in Hnone. cbn in Hnone.
    rewrite Hreason in Hnone. discriminate. }
  unfold msolver_view, view_of in Hreason'. cbn in Hreason'.
  rewrite Hposx in Hreason'. cbn in Hreason'.
  rewrite Hreason in Hreason'. inversion Hreason'. subst C'.
  destruct Hvalid as
    [b' [d' [rx' [Hassign' [Hlevel' [Hrank' [Hhead Hothers]]]]]]].
  specialize (Hothers
    (literal_neg (lit_denote (tag_lit c)))
    ltac:(simpl; tauto) ltac:(rewrite literal_var_neg, lit_var_c_denote;
      exact Hneq)).
  destruct Hothers as [Heval [dq [rq [Hlevelq [Hrankq Horder]]]]].
  pose proof Hlevelq as Hlevelq_idx.
  rewrite literal_var_neg, lit_var_c_denote in Hlevelq_idx.
  unfold msolver_view, view_of in Hlevelq_idx.
  cbn in Hlevelq_idx.
  destruct (trail_pos (ms_core M) (lit_var_c (tag_lit c)))
    as [kq|] eqn:Hposq; cbn in Hlevelq_idx; [|discriminate].
  inversion Hlevelq_idx as [Hidxq].
  assert (Hxarray :
    Znth x (mt_levels (ms_core M)) 0 =
      Zlength (mt_lim (ms_core M))).
  { rewrite <- (trail_pos_var (ms_core M) x kx Hposx).
    rewrite (mtw_levels_agree Hwf (Z.of_nat kx)).
    - exact Hidxx.
    - split; [lia|]. eapply trail_pos_bound. exact Hposx. }
  assert (Hqarray :
    Znth (lit_var_c (tag_lit c)) (mt_levels (ms_core M)) 0 = dq).
  { rewrite <- (trail_pos_var
      (ms_core M) (lit_var_c (tag_lit c)) kq Hposq).
    rewrite (mtw_levels_agree Hwf (Z.of_nat kq)).
    - exact Hidxq.
    - split; [lia|]. eapply trail_pos_bound. exact Hposq. }
  assert (Hdq : dq = Zlength (mt_lim (ms_core M))) by lia.
  rewrite Hdq in Hlevelq.
  rewrite literal_var_neg, lit_var_c_denote in Hlevelq.
  split; [exact Hqrange | exact Hlevelq].
Qed.

(** ** Propagation, simplify, reducedb and search closers for the cap-free vector shape
    ([Vecp.rep_ptr]; capacities stay hidden). *)

(* MISC family: cap-free ports of stale automation definitions. *)

Ltac msat_search_safety_qtail_gap :=
  (LLM_pre_process ltac:(lia || nia || int_auto));
  match goal with
  | |- context [Vecp.rep_ptr ?v ?p ?l] =>
      sep_apply (Vecp.rep_ptr_bounds v p l); Intros
  end;
  match goal with
  | H : msolver_inv _ _ _ _ _ |- _ => msat_search_bound_learnts_qtail_gap H
  end.

Ltac msat_simplify_keep_db_close words i j cls co pre post :=
  let Hclose := fresh "Hclose" in
  assert (Hclose :
      clause_db_rep pre ** clause_db_rep post **
      clause_hdr_addr (Znth i words 0) # Int |->
        clause_hdr_word (co_learnt co) (Zlength (co_lits co)) **
      activity_state (Znth i words 0) (co_learnt co) (Zlength (co_lits co)) **
      IntArray.seg (clause_lits_addr (Znth i words 0)) 0
        (Zlength (co_lits co)) (co_lits co)
    |-- clause_db_rep (pre ++ (Znth i words 0, co) :: post)) by
    (sep_apply_r_atomic (clause_db_rep_app_intro pre
      ((Znth i words 0, co) :: post));
     simpl; unfold MiniSatClause.rep;
     split_pure_spatial;
     [ cancel (clause_db_rep pre); cancel (clause_db_rep post); cancel
     | dump_pre_spatial; pose proof (Zlength_nonneg (co_lits co)); lia ]);
  unfold solver_simplify_db_rest_at; sep_apply Hclose; cancel.

Ltac msat_reducedb_remove_current nn FF AA AI MM ww ii jj ss lp :=
  let Hinv := fresh "Hinv" in
  let Hcomp := fresh "Hcomp" in
  let Hi := fresh "Hi" in
  let wm := fresh "wm" in
  let st := fresh "st" in
  let Hremove0 := fresh "Hremove0" in
  let Hstats := fresh "Hstats" in
  let Hreasons := fresh "Hreasons" in
  let Hunlocked := fresh "Hunlocked" in
  let co := fresh "co" in
  let pre := fresh "pre" in
  let post := fresh "post" in
  let Hbad := fresh "Hbad" in
  let Hlearn := fresh "Hlearn" in
  let Hlits := fresh "Hlits" in
  let Hlearnt := fresh "Hlearnt" in
  let cc := fresh "c" in
  let Hfresh := fresh "Hfresh" in
  let Hremove := fresh "Hremove" in
  let Mnext := fresh "Mnext" in
  let Hentry := fresh "Hentry" in
  let Hbase_next := fresh "Hbase_next" in
  let Hcapacity := fresh "Hcapacity" in
  let Hinvnext := fresh "Hinvnext" in
  let Hstep := fresh "Hstep" in
  let Hcompnext := fresh "Hcompnext" in
  let Hlearnnext := fresh "Hlearnnext" in
  match goal with
  | _ : vec_buf_ok ?cp ?lr |- _ =>
      sep_apply (Vecp.rep_ptr_intro &(ss # "solver_t" ->ₛ "learnts") lr ww cp _ _ _ eq_refl eq_refl eq_refl);
      [ | pose proof (Zlength_nonneg ww); first [lia | vec_buf_solve] .. ]
  end;
  bind_fact (msolver_inv nn FF AA AI MM) as Hinv;
  bind_fact (db_compaction_inv MM ww ii jj) as Hcomp;
  bind_fact (ii < Zlength ww) as Hi;
  unfold clause_remove_post at 1;
  Intros wm st;
  match goal with
  | Hpost : clause_remove_result _ _ _ wm /\ _ |- _ =>
      destruct Hpost as [Hremove0 [Hstats [Hreasons Hunlocked]]]
  end;
  unfold clause_db_pair_remainder at 1;
  Split;
  [ Intros co pre post; match goal with
    | Hdb : db_nil = pre ++ (Znth (ii - 0) ww 0, co) :: post /\ _ |- _ =>
        destruct Hdb as [Hbad _]
    end;
    destruct pre; simpl in Hbad; discriminate
  | Intros co pre post; match goal with
    | Hdb : ms_learnt MM = pre ++ (Znth (ii - 0) ww 0, co) :: post /\ _ |- _ =>
        destruct Hdb as [Hlearn [Hlits Hlearnt]]
    end;
    set (cc := Znth (ii - 0) ww 0);
    assert (Hfresh : ~ In cc (map fst pre)) by
      (eapply db_wf_learnt_split_fresh__reducedb;
       [exact (msi_db_wf Hinv) | exact Hlearn]);
    assert (Hremove : clause_remove_result cc (co_lits co) (ms_wm MM) wm) by
      (unfold cc; rewrite Hlits; exact Hremove0);
    set (Mnext := msolver_remove_clause MM true cc wm st);
    match goal with
    | Hbase : minisat_base_watch_completed ?entry ->
        minisat_base_watch_completed MM |- _ =>
      assert (Hbase_next : minisat_base_watch_completed entry ->
          minisat_base_watch_completed Mnext) by
        (intro Hentry; unfold Mnext;
         apply minisat_base_watch_completed_remove_clause__api_reentry;
         exact (Hbase Hentry))
    end;
    assert (Hcapacity : ms_cap Mnext = ms_cap MM) by reflexivity;
    assert (Hinvnext : msolver_inv nn FF AA AI Mnext) by
      (unfold Mnext; eapply msolver_inv_remove_learnt__reducedb; eassumption);
    assert (Hstep : db_compaction_step MM cc Mnext) by
      (unfold Mnext, db_compaction_step; split;
       [right; exists wm, st; reflexivity | split; reflexivity]);
    assert (Hcompnext : db_compaction_inv Mnext ww (ii + 1) jj) by
      (unfold Mnext, cc;
       eapply db_compaction_inv_remove_current__reducedb;
       [exact (msi_weak Hinv) | exact Hcomp | exact Hi |
        replace (ii - 0) with ii by lia; reflexivity]);
    assert (Hlearnnext : ms_learnt Mnext = pre ++ post) by
      (unfold Mnext;
       exact (msolver_remove_learnt_split_proj__reducedb
         MM cc co pre post wm st Hlearn Hfresh));
    Exists ww Mnext;
    cancel;
    rewrite Hlearnnext;
    sep_apply (clause_db_rep_app_intro pre post);
    unfold Mnext, cc;
    rewrite (solver_db_mutation_frame_at_remove_learnt__reducedb
      ss MM lp (Znth (ii - 0) ww 0) wm st);
    unfold msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update;
    cbn;
    unfold db_nil, solver_wlists_handle, PtrArray.seg;
    eval_ptr_size;
    msat_manual_entailer_with ltac:(int_auto) ].

(* RS family: real-satisfied scan step (propagate, watched literal already true).
   The step lemma is the normal-case VC itself: the opened watch vector of the
   scan is folded back into [Vecp.rep_ptr]; the conclusion is the first
   (non-[scan_begin]) disjunct of the real_satisfied VCs. *)
Lemma propagation_scan_real_satisfied_step__shared_propagate_normal :
forall (s_pre: Z) (wlists_entry: Z) (levels_entry: Z) (assigns_entry: Z) (M0: msolver)
  (K: solver_propagation_context) (A_arr: (@list literal)) (F: cnf) (n: Z) (begin: Z) (ws: Z)
  (confl: Z) (p: Z) (Mscan: msolver) (watch_memory: (@list Z)) (logical_words: (@list Z))
  (scan_wm: (@list (@list Z))) (retained: (@list Z))
  (moved: (@list Z)) (rest: (@list Z)) (garbage: (@list Z)) (ii: Z) (jj: Z) (prop_count: Z)
  (simp_count: Z) (rsn_scan: Z) (trl_scan: Z) (Mentry: msolver) (source_words: (@list Z)) (cap: Z)
  (scan_current: Z) (clause_contents: (@list Z)) (garbage_route: (@list Z)) (memory_route: (@list Z))
  (watch0: Z) (prob_route: dbmap) (learnt_route: dbmap) (Mroute: msolver)
  (retained_route: (@list Z)) (rest_route: (@list Z)),
  (db_pair_lits_update (ms_prob (Mscan)) (ms_learnt (Mscan)) scan_current clause_contents (propagation_normalized_clause (watch0) ((lit_neg_c (p))) (clause_contents)) prob_route learnt_route ) ->
  (propagation_real_satisfied_transition n F A_arr K Mscan p prob_route learnt_route retained_route rest_route Mroute ) ->
  (minisat_propagation_reuse_scan M0 Mroute p 0 rest_route ) ->
  (propagation_scan_keep_step source_words retained moved rest watch_memory ii jj scan_current retained_route rest_route garbage_route memory_route ) ->
  (confl = 0) ->
  (ii < (Zlength (source_words))) ->
  (vec_buf_ok cap begin ) ->
  (cap <= INT_MAX) ->
  ((Zlength (watch_memory)) <= cap) ->
  ((mt_qhead ((ms_core (M0)))) < (ms_qtail (M0))) ->
  (solver_shape Mscan ) ->
  (msolver_seed_shadow Mscan ) ->
  (propagation_caller_frame M0 Mscan ) ->
  (propagation_scan_frontier Mentry Mscan p ) ->
  (logical_words = (app (retained) (rest))) ->
  ((ms_wm (Mscan)) = (replace_Znth (p) (logical_words) (scan_wm))) ->
  (0 <= p) -> (p < (2 * n )) ->
  (ws = (Vecp.slot (wlists_entry) (p))) ->
  ((Zlength (watch_memory)) = (Zlength (source_words))) ->
  (0 <= jj) -> (jj <= ii) -> (0 <= ii) ->
  (simp_count = (ms_simpdb_props (Mscan))) ->
  (prop_count = (stats_propagations ((ms_stats (Mscan))))) ->
  (0 <= (Zlength (source_words))) ->
  ((Zlength (source_words)) <= INT_MAX) ->
  (clause_db_rep prob_route )
  **  (clause_db_rep learnt_route )
  **  (PtrArray.full begin (Zlength (source_words)) (replace_Znth (jj) (scan_current) (watch_memory)) )
  **  (CharArray.seg assigns_entry 0 (ms_size (Mscan)) (mt_assigns ((ms_core (Mscan)))) )
  **  (PtrArray.undef_seg begin (Zlength (watch_memory)) cap )
  **  (Vecp.header ws begin (Zlength (watch_memory)) cap )
  **  (solver_wlists_handle s_pre wlists_entry )
  **  (VecpArray.missing_i wlists_entry p 0 (2 * n ) scan_wm )
  **  (solver_char_tail assigns_entry (ms_size (Mscan)) (ms_cap (Mscan)) )
  **  ((&((s_pre)  # "solver_t" ->ₛ "reasons")) # Ptr  |-> rsn_scan)
  **  ((&((s_pre)  # "solver_t" ->ₛ "levels")) # Ptr  |-> levels_entry)
  **  ((&((s_pre)  # "solver_t" ->ₛ "trail")) # Ptr  |-> trl_scan)
  **  (PtrArray.seg rsn_scan 0 (ms_size (Mscan)) (ms_reason_words (Mscan)) )
  **  (solver_ptr_tail rsn_scan (ms_size (Mscan)) (ms_cap (Mscan)) )
  **  (IntArray.seg levels_entry 0 (ms_size (Mscan)) (mt_levels ((ms_core (Mscan)))) )
  **  (solver_int_tail levels_entry (ms_size (Mscan)) (ms_cap (Mscan)) )
  **  (IntArray.seg trl_scan 0 (ms_qtail (Mscan)) (mt_trail ((ms_core (Mscan)))) )
  **  (solver_int_tail trl_scan (ms_qtail (Mscan)) (ms_cap (Mscan)) )
  **  (Veci.rep &((s_pre)  # "solver_t" ->ₛ "trail_lim") (mt_lim ((ms_core (Mscan)))) )
  **  ((&((s_pre)  # "solver_t" ->ₛ "qhead")) # Int  |-> (mt_qhead ((ms_core (Mscan)))))
  **  ((&((s_pre)  # "solver_t" ->ₛ "qtail")) # Int  |-> (ms_qtail (Mscan)))
  **  ((&((s_pre)  # "solver_t" ->ₛ "simpdb_props")) # Int  |-> simp_count)
  **  ((&((s_pre)  # "solver_t" ->ₛ "assigns")) # Ptr  |-> assigns_entry)
  **  ((&((s_pre)  # "solver_t" ->ₛ "binary")) # Ptr  |-> (ms_binary (Mscan)))
  **  (solver_binary_rep Mscan )
  **  ((&((s_pre)  # "solver_t" ->ₛ "stats" .ₛ "propagations")) # UInt64  |-> prop_count)
  **  ((&((s_pre)  # "solver_t" ->ₛ "stats" .ₛ "inspects")) # UInt64  |-> (stats_inspects ((ms_stats (Mscan)))))
  **  (solver_propagate_frame s_pre Mscan )
  **  ((( &( "l_Undef" ) )) # Char  |-> 0)
  **  ((( &( "true" ) )) # Int  |-> 1)
|--
  EX (trl_next: Z)  (rsn_next: Z)  (prop_count_next: Z)  (simp_count_next: Z)  (next_wm: (@list (@list Z)))  (logical_next: (@list Z))  (source_words_next: (@list Z))  (moved_next: (@list Z))  (garbage_next: (@list Z))  (memory_next: (@list Z))  (ii_next: Z)  (jj_next: Z)  (retained_next: (@list Z))  (rest_next: (@list Z))  (Mentry_next: msolver)  (Mnext: msolver)  (lvl_next: Z) ,
  “ (lvl_next = levels_entry) ” 
  &&  “ ((mt_qhead ((ms_core (M0)))) < (ms_qtail (M0))) ” 
  &&  “ (solver_shape Mnext ) ” 
  &&  “ (msolver_seed_shadow Mnext ) ” 
  &&  “ (propagation_caller_frame M0 Mnext ) ” 
  &&  “ (propagation_scan_frontier Mentry_next Mnext p ) ” 
  &&  “ (solver_propagation_scan_semantics n F A_arr K Mnext p confl retained_next rest_next ) ” 
  &&  “ (minisat_propagation_reuse_scan M0 Mnext p confl rest_next ) ” 
  &&  “ (propagation_watch_scan_physical source_words_next retained_next moved_next rest_next garbage_next memory_next ii_next jj_next ) ” 
  &&  “ (logical_next = (app (retained_next) (rest_next))) ” 
  &&  “ ((ms_wm (Mnext)) = (replace_Znth (p) (logical_next) (next_wm))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < (2 * n )) ” 
  &&  “ (ws = (Vecp.slot (wlists_entry) (p))) ” 
  &&  “ ((begin + ((Zlength (source_words)) * sizeof(PTR))) = (begin + ((Zlength (source_words_next)) * sizeof(PTR)))) ” 
  &&  “ ((Zlength (memory_next)) = (Zlength (source_words_next))) ” 
  &&  “ ((begin + ((ii + 1 ) * sizeof(PTR))) = (begin + (ii_next * sizeof(PTR)))) ” 
  &&  “ ((begin + ((jj + 1 ) * sizeof(PTR))) = (begin + (jj_next * sizeof(PTR)))) ” 
  &&  “ (0 <= jj_next) ” 
  &&  “ (jj_next <= ii_next) ” 
  &&  “ (0 <= ii_next) ” 
  &&  “ (ii_next <= (Zlength (source_words_next))) ” 
  &&  “ (ii_next <> 0) ” 
  &&  “ (simp_count_next = (ms_simpdb_props (Mnext))) ” 
  &&  “ (prop_count_next = (stats_propagations ((ms_stats (Mnext))))) ” 
  &&  “ (0 <= (Zlength (source_words_next))) ” 
  &&  “ ((Zlength (source_words_next)) <= INT_MAX) ”
  &&  (Vecp.rep_ptr ws begin memory_next )
  **  (solver_wlists_handle s_pre wlists_entry )
  **  (VecpArray.missing_i wlists_entry p 0 (2 * n ) next_wm )
  **  (clause_db_rep (ms_prob (Mnext)) )
  **  (clause_db_rep (ms_learnt (Mnext)) )
  **  ((&((s_pre)  # "solver_t" ->ₛ "reasons")) # Ptr  |-> rsn_next)
  **  ((&((s_pre)  # "solver_t" ->ₛ "levels")) # Ptr  |-> lvl_next)
  **  ((&((s_pre)  # "solver_t" ->ₛ "trail")) # Ptr  |-> trl_next)
  **  (CharArray.seg assigns_entry 0 (ms_size (Mnext)) (mt_assigns ((ms_core (Mnext)))) )
  **  (solver_char_tail assigns_entry (ms_size (Mnext)) (ms_cap (Mnext)) )
  **  ((&((s_pre)  # "solver_t" ->ₛ "qhead")) # Int  |-> (mt_qhead ((ms_core (Mnext)))))
  **  (solver_propagation_scan_core_at s_pre Mnext assigns_entry rsn_next lvl_next trl_next simp_count_next prop_count_next )
  **  ((( &( "l_Undef" ) )) # Char  |-> 0)
  **  ((( &( "true" ) )) # Int  |-> 1).
Proof.
  intros until rest_route.
  intros Hupd Htr Hreuse Hkeep Hconfl Hii Hbuf Hcap Hwcap Hqhead Hshape Hseed Hcaller
    Hfrontier Hlogical_words Hwm Hp_lo Hp_hi Hws Hwm_len Hjj0 Hjj Hii0 Hsimp Hprop Hsrc0 Hsrc_max.
  destruct Htr as [HMroute Hsem].
  destruct Hkeep as [Hrest [Hretained [Hmemory Hphysical]]].
  set (satisfied_memory := replace_Znth jj scan_current watch_memory).
  assert (Hphysical_sat : propagation_watch_scan_physical source_words
      retained_route moved rest_route garbage_route satisfied_memory (ii + 1) (jj + 1)).
  { subst satisfied_memory. rewrite <- Hmemory. exact Hphysical. }
  assert (Hmemory_length : Zlength satisfied_memory = Zlength source_words)
    by (unfold propagation_watch_scan_physical in Hphysical_sat; tauto).
  assert (Hlogical : logical_words = retained_route ++ rest_route)
    by (rewrite Hlogical_words, Hretained, Hrest, <- app_assoc; reflexivity).
  assert (Hframe : solver_propagate_frame s_pre Mroute = solver_propagate_frame s_pre Mscan).
  { destruct (db_pair_lits_update_words__propagate _ _ _ _ _ _ _ Hupd)
      as [Hprob_words Hlearnt_words].
    rewrite HMroute.
    unfold msolver_propagation_db_wmap_update, msolver_propagation_overlay,
      msolver_propagation_update, solver_propagate_frame.
    cbn. rewrite Hprob_words, Hlearnt_words. reflexivity. }
  subst confl.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) satisfied_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin satisfied_memory cap (Zlength watch_memory)
    (Zlength source_words) (Zlength watch_memory)); [ | first [lia | assumption] .. ].
  Exists trl_scan rsn_scan prop_count simp_count scan_wm
    logical_words source_words moved garbage_route satisfied_memory
    (ii + 1) (jj + 1) retained_route rest_route Mentry.
  Exists Mroute levels_entry.
  split_pure_spatial.
  - unfold solver_propagation_scan_core_at.
    rewrite Hframe, HMroute.
    unfold solver_binary_rep, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update.
    cbn -[ptr_size_Z Znth Vecp.rep_ptr]. unfold PtrArray.seg, stats_propagate_scan.
    cbn -[ptr_size_Z Znth Vecp.rep_ptr].
    cancel (clause_db_rep prob_route).
    cancel.
    exact (stats_propagate_scan_refold__propagate s_pre prop_count (ms_stats Mscan)).
  - split_pures; dump_pre_spatial.
    all: first
      [ assumption | reflexivity | lia
      | rewrite HMroute;
        cbn [msolver_propagation_db_wmap_update msolver_propagation_overlay
          msolver_propagation_update];
        first [ assumption | reflexivity | lia | unfold solver_shape in *; assumption ] ].
Qed.

(* Closes a real_satisfied VC (either disjunct order) after
   [LLM_pre_process]: instantiate the step lemma by the VC's own names,
   discharge its premises from the context, and pick whichever disjunct the
   conclusion is. *)
Ltac msat_real_satisfied_dispatch :=
  let s_pre := ident:(s_pre) in
  let wlists_entry := ident:(wlists_entry) in
  let levels_entry := ident:(levels_entry) in
  let assigns_entry := ident:(assigns_entry) in
  let M0 := ident:(M0) in
  let K := ident:(K) in
  let A_arr := ident:(A_arr) in
  let F := ident:(F) in
  let n := ident:(n) in
  let begin := ident:(begin) in
  let ws := ident:(ws) in
  let confl := ident:(confl) in
  let p := ident:(p) in
  let Mscan := ident:(Mscan) in
  let watch_memory := ident:(watch_memory) in
  let logical_words := ident:(logical_words) in
  let scan_wm := ident:(scan_wm) in
  let retained := ident:(retained) in
  let moved := ident:(moved) in
  let rest := ident:(rest) in
  let garbage := ident:(garbage) in
  let ii := ident:(ii) in
  let jj := ident:(jj) in
  let prop_count := ident:(prop_count) in
  let simp_count := ident:(simp_count) in
  let rsn_scan := ident:(rsn_scan) in
  let trl_scan := ident:(trl_scan) in
  let Mentry := ident:(Mentry) in
  let source_words := ident:(source_words) in
  let cap := ident:(cap) in
  let scan_current := ident:(scan_current) in
  let clause_contents := ident:(clause_contents) in
  let garbage_route := ident:(garbage_route) in
  let memory_route := ident:(memory_route) in
  let watch0 := ident:(watch0) in
  let prob_route := ident:(prob_route) in
  let learnt_route := ident:(learnt_route) in
  let Mroute := ident:(Mroute) in
  let retained_route := ident:(retained_route) in
  let rest_route := ident:(rest_route) in
  let Hstep := fresh "Hstep" in
  pose proof (propagation_scan_real_satisfied_step__shared_propagate_normal
    s_pre wlists_entry levels_entry assigns_entry M0 K A_arr F n begin ws confl p Mscan
    watch_memory logical_words scan_wm retained moved rest garbage ii jj
    prop_count simp_count rsn_scan trl_scan Mentry source_words cap scan_current
    clause_contents garbage_route memory_route watch0 prob_route learnt_route Mroute
    retained_route rest_route) as Hstep;
  repeat lazymatch type of Hstep with
  | ?P -> _ =>
      let Hp := fresh "Hstep_arg" in
      assert (Hp : P) by first [assumption | reflexivity | lia];
      specialize (Hstep Hp); clear Hp
  end;
  unfold stats_propagations, stats_inspects in Hstep |- *;
  sep_apply Hstep; clear Hstep;
  (* the step's conclusion is the disjunct WITHOUT [msolver_propagation_scan_begin];
     select it syntactically (unifying against the other arm is very slow) *)
  lazymatch goal with
  | |- _ |-- ?A || _ =>
      lazymatch A with
      | context [msolver_propagation_scan_begin _ _ _] => apply derivable1_orp_intros2
      | _ => apply derivable1_orp_intros1
      end
  end.

(* Family BK: binary-keep / unit-conflict-copy / scan-finish closers, cap-free. *)

(* Length side conditions of a watch-vector fold: unfold the [replace_Znth]
   writes the memory went through, then arithmetic or buffer validity. *)
Ltac msat_bk_len :=
  repeat match goal with
  | |- context [Zlength (replace_Znth _ _ _)] => rewrite Zlength_replace_Znth
  | H : ?x = replace_Znth _ _ _ |- context [Zlength ?x] => is_var x; rewrite H
  end;
  first [reflexivity | lia | vec_buf_solve].

(* Fold the opened vector (header, full array, undef tail) back into [Vecp.rep_ptr]. *)
Ltac msat_bk_vecp_fold :=
  lazymatch goal with
  | |- context [PtrArray.full ?b ?n ?m] =>
    lazymatch goal with
    | |- context [Vecp.header ?v b ?k ?c] =>
        sep_apply_l_atomic (PtrArray.full_to_seg b n m);
        sep_apply (Vecp.rep_ptr_intro v b m c k n k); [ | msat_bk_len .. ]
    end
  end.

Ltac msat_propagate_unit_conflict_copy_close jj :=
  match goal with
  | Hc : ?watch_memory = ?raw_prefix ++ ?scan_current :: ?raw_suffix,
    Hd : Zlength ?raw_prefix = ?ii,
    He : ?candidate_post_memory = ?watch_memory |- _ =>
      Exists (replace_Znth jj scan_current candidate_post_memory)
        (jj + 1) (ii + 1);
      split_pure_spatial;
      [ sep_apply (store_ptr_undef_store_ptr (&("k")));
        sep_apply (store_ptr_undef_store_ptr (&("stop")));
        sep_apply (store_char_undef_store_char (&("sig")));
        msat_bk_vecp_fold; cancel
      | split_pures; dump_pre_spatial;
        solve
          [ auto
          | lia
          | congruence
          | rewrite Zlength_replace_Znth; lia
          | exists nil, raw_suffix;
            split; [exact Hc|];
            split; [exact Hd|];
            split; [lia|];
            split; [simpl; reflexivity|];
            split; [rewrite Zlength_nil; lia|];
            split; [rewrite Zlength_nil; lia|];
            split;
            [ rewrite He; simpl; reflexivity
            | rewrite He, Zlength_replace_Znth; reflexivity ] ] ]
  end.

Tactic Notation "msat_binary_keep_new_exists"
    ident(trl_v) ident(rsn_v) ident(lvl_v) ident(hmroute) ident(hsem2)
    ident(hbinary) ident(hframe) ident(htagged) ident(hwm) ident(hfrontier) :=
  match goal with
  | Hp1 : wlist_scan_inv ?sw ?rr ?mv ?rt, Hp2 : ?mr = ?rr ++ ?gr ++ ?rt,
    Hp3 : Zlength ?rr = ?jn, Hp4 : Zlength (?rr ++ ?gr) = ?iN |- _ =>
      match type of hwm with
      | ms_wm _ = replace_Znth _ _ ?wfull =>
          match type of hmroute with
          | ?Mr = _ =>
              match type of hfrontier with
              | propagation_scan_frontier ?Me _ _ =>
                  Exists trl_v rsn_v (Znth 2 (ms_stats Mr) 0)
                    (ms_simpdb_props Mr) wfull
                    (rr ++ rt) sw mv gr mr iN jn rr rt Me;
                  Exists Mr lvl_v
              end
          end
      end
  end;
  rewrite hmroute in hsem2;
  match type of hmroute with
  | ?Mr = _ =>
      match goal with
      | Hreuse : minisat_propagation_reuse_scan _ Mr _ _ _ |- _ =>
          rewrite hmroute in Hreuse
      end
  end;
  unfold solver_propagation_scan_core_at, stats_propagate_scan;
  rewrite hbinary, hframe;
  rewrite hmroute;
  unfold msolver_propagation_overlay, msolver_propagation_update, mt_enqueue, mt_push;
  cbn;
  rewrite htagged;
  split_pure_spatial;
  [ cancel (&( "l_Undef") # Char |-> 0); cancel
  | split_pures; dump_pre_spatial; try solve [auto | lia] ].

Tactic Notation "msat_binary_keep_open"
    ident(qtail_v) ident(assigns_v) ident(levels_v) ident(reasons_v)
    ident(trail_v) ident(rsn_v) ident(trl_v) :=
  match goal with
  | H : propagation_binary_keep_transition _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold propagation_binary_keep_transition in H;
      destruct H as [HMroute Hsem]
  end;
  match goal with
  | H : propagation_scan_keep_step _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold propagation_scan_keep_step in H;
      destruct H as [Hrest [Hretained [Hmemory Hphysical]]]
  end;
  Left;
  unfold enqueue_post_at at 1;
  Intros qtail_v assigns_v levels_v reasons_v trail_v;
  unfold enqueue_state_at at 1;
  Intros rsn_v trl_v;
  match goal with
  | H : enqueue_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold enqueue_transition in H;
      destruct H as [Hsame | [Hconflict | Hnew]]
  end.

Tactic Notation "msat_binary_keep_same_close"
    ident(trl_v) ident(rsn_v) ident(lvl_v) ident(htagged) ident(hsimp)
    ident(hprop) ident(hwm) ident(hlogical) ident(hfrontier) :=
  match goal with
  | Hp1 : wlist_scan_inv ?sw ?rr ?mv ?rt, Hp2 : ?mr = ?rr ++ ?gr ++ ?rt,
    Hp3 : Zlength ?rr = ?jn, Hp4 : Zlength (?rr ++ ?gr) = ?iN |- _ =>
      match type of hwm with
      | ms_wm ?M = replace_Znth _ _ ?wfull =>
          match type of hfrontier with
          | propagation_scan_frontier ?Me _ _ =>
              Exists trl_v rsn_v (Znth 2 (ms_stats M) 0)
                (ms_simpdb_props M) wfull (rr ++ rt) sw
                mv gr mr iN jn rr rt Me;
              Exists M lvl_v
          end
      end
  end;
  unfold solver_propagation_scan_core_at, stats_propagate_scan;
  rewrite htagged;
  rewrite <- hsimp, <- hprop;
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  lazymatch goal with
  | |- _ |-- “ _ ” =>
      apply dump_spatial_left; simpl_entail_with ltac:(lia)
  | |- _ |-- _ => msat_cancel_sound; try reflexivity
  end;
  try lia;
  try assumption;
  try (unfold propagation_watch_scan_physical;
    repeat split; assumption);
  try (cancel; unfold Znth; cbn; csimpl; lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel);
  try (rewrite hwm, hlogical; reflexivity).

Ltac msat_propagate_binary_keep :=
  msat_split_after_llm;
  msat_binary_keep_bind_facts;
  msat_bk_vecp_fold;
  msat_binary_keep_open qtail' assigns' levels' reasons' trail' rsn trl;
  [ msat_binary_keep_same_head Hsame HMroute Mroute assigns' levels'
      reasons' trail' qtail';
    msat_binary_keep_route_memory H_tagged_enqueue_success_memory
      H_tagged_memory Hmemory H_logical_words Hrest Hretained;
    msat_binary_keep_route_bounds Hphysical ii jj garbage_route confl
      H_solver_propagation_scan_semantics Hrest;
    msat_binary_keep_same_close trl rsn levels_entry Htagged_memory
      H_simp_count H_prop_count H_ms_wm Hlogical_route
      H_propagation_scan_frontier
  | msat_binary_keep_conflict Hconflict
  | msat_binary_keep_new_head Hnew HMroute assigns' levels' reasons'
      trail' qtail';
    msat_binary_keep_route_memory H_tagged_enqueue_success_memory
      H_tagged_memory Hmemory H_logical_words Hrest Hretained;
    msat_binary_keep_route_bounds Hphysical ii jj garbage_route confl
      H_solver_propagation_scan_semantics Hrest;
    msat_binary_keep_new_facts H_enqueue_input Hzero
      H_solver_propagation_scan_semantics;
    msat_binary_keep_new_overlay HMroute H_solver_shape Hpending_zero
      H_msolver_seed_shadow H_propagation_caller_frame;
    msat_binary_keep_new_route_eqs K Hrest
      H_solver_propagation_scan_semantics H_solver_shape HMroute Heq
      scan_current p s_pre;
    msat_binary_keep_new_frontier Hroute_enqueue
      H_propagation_scan_frontier Htrail_wf Heq;
    msat_binary_keep_new_exists trl rsn levels_entry HMroute Hsem
      Hbinary_route Hframe_route Htagged_memory H_ms_wm
      H_propagation_scan_frontier;
    msat_binary_keep_new_side H_ms_wm Hlogical_route HMroute
      Hfrontier_route Hshape_route Hseed_route Hcaller_route;
    msat_binary_keep_new_stats levels_entry rsn Hroute_enqueue
      H_simp_count H_prop_count s_pre
  ].

Lemma propagation_scan_finish_step__shared_solver_propagate_normal :
  forall (s_pre: Z) (levels_entry: Z) (assigns_entry: Z) (M0: msolver) (K:
    solver_propagation_context) (A_arr: (@list literal)) (F: cnf) (n: Z) (i: Z) (endvar: Z) (p:
    Z) (confl: Z) (ws: Z) (begin: Z) (j: Z) (Mscan: msolver) (watch_memory: (@list Z))
    (logical_words: (@list Z)) (scan_wm: (@list (@list Z))) (retained: (@list
    Z)) (moved: (@list Z)) (rest: (@list Z)) (garbage: (@list Z)) (ii: Z) (jj: Z) (prop_count:
    Z) (simp_count: Z) (rsn_scan: Z) (trl_scan: Z) (wl: Z) (Mentry: msolver) (source_words:
    (@list Z)) (retval: Z) (retval_2: Z)
    (Hwritten_prefix_length : ((Zlength ((sublist (0) ((((begin + (jj * sizeof(PTR))) - retval_2
      ) ÷ sizeof(PTR) )) (watch_memory)))) = (((begin + (jj * sizeof(PTR))) - retval_2 ) ÷
      sizeof(PTR) )))
    (Hgetter_alias : (retval_2 = retval))
    (Hretained_index : ((((begin + (jj * sizeof(PTR))) - begin ) ÷ sizeof(PTR) ) = jj))
    (Hgetter_base : (retval = begin))
    (Hshape : (solver_shape Mscan ))
    (Hseed : (msolver_seed_shadow Mscan ))
    (Hcaller : (propagation_caller_frame M0 Mscan ))
    (Hfrontier : (propagation_scan_frontier Mentry Mscan p ))
    (Hscan_finished : (solver_propagation_scan_semantics n F A_arr K Mscan p confl retained
      (@nil Z) ))
    (Hreuse_scan : minisat_propagation_reuse_scan M0 Mscan p confl nil)
    (Hphysical_finished : (propagation_watch_scan_physical source_words retained moved (@nil Z)
      garbage watch_memory ii jj ))
    (Hscan_index_at_end : (ii = (Zlength (source_words))))
    (Hretained_length : (jj = (Zlength (retained))))
    (Hwatch_map_finished : ((ms_wm (Mscan)) = (replace_Znth (p) (retained) (scan_wm))))
    (Hp_lo : (0 <= p))
    (Hp_hi : (p < (2 * n )))
    (Hwatch_slot : (ws = (Vecp.slot (wl) (p))))
    (Hscan_pointer_at_end : ((begin + (ii * sizeof(PTR))) = (begin + ((Zlength (source_words)) *
      sizeof(PTR)))))
    (Hscan_pointer_ge_end : (i >= endvar))
    (Hscan_open : (solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ))
    (Hphysical_open : (propagation_watch_scan_physical source_words retained moved rest garbage
      watch_memory ii jj ))
    (Hlogical_words : (logical_words = (app (retained) (rest))))
    (Hwatch_map_open : ((ms_wm (Mscan)) = (replace_Znth (p) (logical_words) (scan_wm))))
    (Hend_pointer : (endvar = (begin + ((Zlength (source_words)) * sizeof(PTR)))))
    (Hmemory_source_length : ((Zlength (watch_memory)) = (Zlength (source_words))))
    (Hscan_pointer : (i = (begin + (ii * sizeof(PTR)))))
    (Hretain_pointer : (j = (begin + (jj * sizeof(PTR)))))
    (Hretain_index_nonnegative : (0 <= jj))
    (Hretain_index_le_scan : (jj <= ii))
    (Hscan_index_nonnegative : (0 <= ii))
    (Hscan_index_bound : (ii <= (Zlength (source_words))))
    (Hsimp_count : (simp_count = (ms_simpdb_props (Mscan))))
    (Hprop_count : (prop_count = (stats_propagations ((ms_stats (Mscan))))))
    (Hsource_max : ((Zlength (source_words)) <= INT_MAX)),
  (Vecp.rep_ptr ws begin (sublist (0) ((((begin + (jj * sizeof(PTR))) - retval_2 ) ÷ sizeof(PTR) ))
    (watch_memory)) )
  **  ((( &( "j" ) )) # Ptr  |-> (begin + (jj * sizeof(PTR))))
  **  ((( &( "begin" ) )) # Ptr  |-> begin)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
  **  ((( &( "endvar" ) )) # Ptr  |-> (begin + ((Zlength (source_words)) * sizeof(PTR))))
  **  ((( &( "i" ) )) # Ptr  |-> (begin + (ii * sizeof(PTR))))
  **  (solver_wlists_handle s_pre wl )
  **  (VecpArray.missing_i wl p 0 (2 * n ) scan_wm )
  **  (clause_db_rep (ms_prob (Mscan)) )
  **  (clause_db_rep (ms_learnt (Mscan)) )
  **  (CharArray.seg assigns_entry 0 (ms_size (Mscan)) (mt_assigns ((ms_core (Mscan)))) )
  **  (solver_char_tail assigns_entry (ms_size (Mscan)) (ms_cap (Mscan)) )
  **  ((&((s_pre)  # "solver_t" ->ₛ "reasons")) # Ptr  |-> rsn_scan)
  **  ((&((s_pre)  # "solver_t" ->ₛ "levels")) # Ptr  |-> levels_entry)
  **  ((&((s_pre)  # "solver_t" ->ₛ "trail")) # Ptr  |-> trl_scan)
  **  (PtrArray.seg rsn_scan 0 (ms_size (Mscan)) (ms_reason_words (Mscan)) )
  **  (solver_ptr_tail rsn_scan (ms_size (Mscan)) (ms_cap (Mscan)) )
  **  (IntArray.seg levels_entry 0 (ms_size (Mscan)) (mt_levels ((ms_core (Mscan)))) )
  **  (solver_int_tail levels_entry (ms_size (Mscan)) (ms_cap (Mscan)) )
  **  (IntArray.seg trl_scan 0 (ms_qtail (Mscan)) (mt_trail ((ms_core (Mscan)))) )
  **  (solver_int_tail trl_scan (ms_qtail (Mscan)) (ms_cap (Mscan)) )
  **  (Veci.rep &((s_pre)  # "solver_t" ->ₛ "trail_lim") (mt_lim ((ms_core (Mscan)))) )
  **  ((&((s_pre)  # "solver_t" ->ₛ "qhead")) # Int  |-> (mt_qhead ((ms_core (Mscan)))))
  **  ((&((s_pre)  # "solver_t" ->ₛ "qtail")) # Int  |-> (ms_qtail (Mscan)))
  **  ((&((s_pre)  # "solver_t" ->ₛ "simpdb_props")) # Int  |-> simp_count)
  **  ((&((s_pre)  # "solver_t" ->ₛ "assigns")) # Ptr  |-> assigns_entry)
  **  ((&((s_pre)  # "solver_t" ->ₛ "binary")) # Ptr  |-> (ms_binary (Mscan)))
  **  (solver_binary_rep Mscan )
  **  ((&((s_pre)  # "solver_t" ->ₛ "stats" .ₛ "propagations")) # UInt64  |-> prop_count)
  **  ((&((s_pre)  # "solver_t" ->ₛ "stats" .ₛ "inspects")) # UInt64  |-> (unsigned_last_nbits (((stats_inspects
  ((ms_stats (Mscan)))) + (unsigned_last_nbits ((((begin + (jj * sizeof(PTR))) - retval ) ÷ sizeof(PTR)
    )) (64)) )) (64)))
  **  (solver_propagate_frame s_pre Mscan )

|--
  (EX (trl_finish: Z)  (rsn_finish: Z)  (Mfinish: msolver)  (lvl_finish: Z) ,
  propagation_scan_finish_arm_normal (confl <> 0)
    (propagation_scan_conflict_finalize n F A_arr K M0 Mscan p confl jj retained Mfinish )
    trl_finish rsn_finish Mfinish lvl_finish levels_entry n F A_arr K M0 confl jj
    watch_memory retained scan_wm p
    0 s_pre wl assigns_entry)
  ||
  (EX (trl_finish: Z)  (rsn_finish: Z)  (Mfinish: msolver)  (lvl_finish: Z) ,
  propagation_scan_finish_arm_normal (confl = 0)
    (propagation_scan_live_finalize n F A_arr K M0 Mscan p jj retained Mfinish)
    trl_finish rsn_finish Mfinish lvl_finish levels_entry n F A_arr K M0 confl jj
    watch_memory retained scan_wm p
    0 s_pre wl assigns_entry).
Proof.
  unfold propagation_scan_finish_arm_normal.
  aggressive_pre_process.
  assert (Hfocus_level : confl <> 0 ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan)))).
  { intro Hnonzero.
    destruct Hscan_finished as [[Hzero Hlive]|[Hconflict [Hempty [Hready Hcert]]]].
    - contradiction.
    - unfold propagation_cancel_ready in Hready. tauto. }
  pose proof (minisat_propagation_reuse_scan_finish__api_reentry
    n M0 Mscan p confl jj Hreuse_scan Hfocus_level) as Hreuse_finish.
  pose proof (Zlength_nonneg watch_memory) as Hmemory_length_nonnegative.
  pose proof (Zlength_nonneg source_words) as Hsource_length_nonnegative.
  subst retval_2. subst retval. subst ws.
  assert (Hprefix : sublist 0 jj watch_memory = retained).
  { unfold propagation_watch_scan_physical in Hphysical_finished.
    destruct Hphysical_finished as [_ [Hmemory [Hretained _]]].
    rewrite Hmemory, app_nil_r, <- Hretained.
    rewrite sublist_app_exact1. reflexivity. }
  assert (Hshape_finish : solver_shape
    (msolver_propagation_scan_finish Mscan jj)).
  { apply solver_shape_scan_finish__propagate. exact Hshape. }
  assert (Hseed_finish : msolver_seed_shadow
    (msolver_propagation_scan_finish Mscan jj)).
  { change (msolver_seed_shadow Mscan). exact Hseed. }
  assert (Hloop_finish : solver_propagation_loop_inv n F A_arr K M0
    (msolver_propagation_scan_finish Mscan jj) confl).
  { eapply solver_propagation_scan_finish_loop__propagate;
      [exact Hcaller | exact Hscan_finished]. }
  assert (Hwm : Zlength (replace_Znth p retained scan_wm) =
    2 * ms_size Mscan).
  { pose proof Hshape as Hshape_wm.
    unfold solver_shape in Hshape_wm. rewrite <- Hwatch_map_finished. tauto. }
  rewrite Zlength_replace_Znth in Hwm.
  assert (Hdelta : 0 <= jj < 2 ^ 64) by lia.
  assert (Hqtail_size : ms_qtail Mscan <= ms_size Mscan).
  { eapply propagation_scan_semantics_qtail_size__propagate.
    exact Hscan_finished. }
  pose proof Hshape_finish as Hsf. unfold solver_shape in Hsf.
  destruct (Z.eq_dec confl 0) as [Hconfl | Hconfl]; [Right | Left];
  Exists trl_scan rsn_scan (msolver_propagation_scan_finish Mscan jj)
    levels_entry;
  (split_pure_spatial;
  [ rewrite Hretained_index, Hprefix;
    sep_apply (Vecp.rep_ptr_rep (Vecp.slot wl p) begin retained);
    prop_apply_p (VecpArray.missing_i_Zlength wl p 0 (2 * n) scan_wm); Intros;
    replace (2 * n) with (2 * ms_size Mscan) by lia;
    sep_apply (missing_i_merge_to_wlists_rep
      wl (ms_size Mscan) p scan_wm retained ltac:(lia));
    sep_apply (solver_propagate_frame_scan_finish__propagate
      s_pre Mscan jj Hshape);
    rewrite scan_finish_stats2__propagate by exact Hshape;
    rewrite scan_finish_stats3__propagate by assumption;
    rewrite solver_binary_rep_scan_finish__propagate;
    unfold solver_wlists_handle, PtrArray.seg;
    unfold msolver_propagation_scan_finish, msolver_propagation_overlay, msolver_propagation_update;
    cbn; rewrite Hsimp_count, Hprop_count, Hwatch_map_finished;
    cancel;
    repeat sep_apply store_ptr_undef_store_ptr; cancel
  | split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia; try tauto;
    first
      [ unfold propagation_scan_live_finalize;
        split; [reflexivity|]; rewrite <- Hconfl; split; assumption
      | unfold propagation_scan_conflict_finalize;
        split; [exact Hconfl|]; split; [reflexivity|]; split; assumption ] ]).
Qed.

(* Close a scan-finish VC (the two [solver_propagate_entail_wit_28_*]) from
   [Hfinish], an instance of the lemma above: discharge its premises, then
   move the two-arm conclusion to the VC's postcondition. *)
Ltac msat_propagate_finish_normal_close Hfinish :=
  repeat lazymatch type of Hfinish with
  | ?P -> _ =>
      let Hp := fresh "Hfinish_arg" in
      assert (Hp : P) by (first [assumption | reflexivity | congruence]);
      specialize (Hfinish Hp); clear Hp
  end;
  lazymatch goal with
  | |- _ |-- ?T =>
      lazymatch type of Hfinish with
      | _ |-- ?R =>
          let Hcut := fresh "Hcut" in
          assert (Hcut : R ** (((( &( "l_Undef" ) )) # Char |-> 0) **
            ((( &( "true" ) )) # Int |-> 1)) |-- T);
          [ Split; [Left | Right];
            let a := fresh "trl" in let b := fresh "rsn" in
            let c := fresh "Mfinish" in let d := fresh "lvl" in
            Intros a b c d; unfold propagation_scan_finish_arm_normal; Intros;
            Exists a b c d; msat_manual_entailer_with lia
          | sep_apply_r_atomic Hcut; sep_apply_r_atomic Hfinish;
            msat_manual_entailer_with lia ]
      end
  end.


Lemma solver_reason_levels_join__analyze :
  forall s M rsn lvl trl tgs wl,
    solver_shape M ->
    (&(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn) **
    (PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
     (solver_ptr_tail rsn (ms_size M) (ms_cap M) **
      ((&(s # "solver_t" ->ₛ "levels") # Ptr |-> lvl) **
       (IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
        (solver_int_tail lvl (ms_size M) (ms_cap M) **
         solver_reason_levels_frame_at s M trl tgs wl)))))
    |-- solver_rep_analyze_at s M rsn lvl trl tgs wl.
Proof.
  intros s M rsn lvl trl tgs wl Hshape.
  unfold solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_rep_analyze_at, solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_scalars_rep, solver_vecs_rep,
    clause_new_scalars_frame.
  Intros act asg opos.
  Exists act asg opos.
  msat_entailer_with ltac:(first [assumption | lia]).
Qed.

Lemma propagation_scan_enqueue_input__propagate :
  forall n F A_arr K Mscan p retained rest l,
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    lit_wf_c n l ->
    enqueue_input (ms_size Mscan) l (ms_qtail Mscan)
      (mt_assigns (ms_core Mscan)) (mt_levels (ms_core Mscan))
      (ms_reason_words Mscan) (mt_trail (ms_core Mscan)).
Proof.
  intros n F A_arr K Mscan p retained rest l Hsem Hwf.
  assert (Hweak : solver_propagation_weak n F A_arr K Mscan).
  { destruct Hsem as [[_ [Hweak _]] | [Hconfl _]].
    - exact Hweak.
    - contradiction. }
  destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mscan Hweak)
    as [Hnsize [Hshape [_ [_ Htrailwf]]]].
  subst n.
  assert (Hcells : Forall (fun x => -1 <= x <= 1) (mt_assigns (ms_core Mscan))).
  { eapply Forall_impl; [| exact (mtw_cells Htrailwf)].
    intros x Hx. unfold lbool_cell in Hx. lia. }
  assert (Hroom : Znth (lit_var_c l)
    (mt_assigns (ms_core Mscan)) 0 = 0 -> ms_qtail Mscan < ms_size Mscan).
  { intro Hzero.
    pose proof (mtrail_unassigned_room (ms_size Mscan) (ms_core Mscan)
      (lit_var_c l) Htrailwf
      (lit_var_c_in_range _ _ Hwf) Hzero) as Hroom.
    unfold solver_shape in Hshape. lia. }
  pose proof (mtw_trail_bound Htrailwf) as Hbound.
  unfold enqueue_input, solver_shape in *.
  repeat split; try assumption; try lia.
  all: unfold lit_wf_c in Hwf; lia.
Qed.
