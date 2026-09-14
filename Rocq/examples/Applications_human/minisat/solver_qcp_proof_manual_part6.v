(* ============================================================
   solver_qcp_proof_manual_part6.v

   Manual proof obligations for the C functions:
   assume, lit_var, order_select, order_unassigned, order_update,
   solver_analyze, solver_canceluntil, solver_lit_removable,
   solver_progress, solver_propagate, solver_record,
   solver_search, solver_solve, veci_*, vecp_*.

   Lemmas are grouped by C function below, each group preceded by
   a "===== <function> <kind> wits (N proofs) =====" banner; within
   a group, wits appear in lexicographic order of the wit name, so
   [wit_10_1] precedes [wit_2_1].

   See solver_qcp_proof_manual.v for the nine-part split rationale,
   the parallel-build independence rule, and the stub convention
   ("exact proof_of_<keeper>" only ever cites a keeper earlier in
   this same file).
   ============================================================ *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_goal.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_common.
Local Open Scope sac.


(* ------------------------------------------------------------------------ *)
(* Part-local tactics.  Each one is the body of a group of proofs in this    *)
(* file that were byte-identical (or identical up to the names they pass);   *)
(* every name a body cites has to be a formal argument, because Ltac         *)
(* resolves a body identifier at DEFINITION time -- only the names this      *)
(* body itself introduces with [intros] resolve without being passed in.     *)
(* ------------------------------------------------------------------------ *)

(* The length side condition of a watched-list scan step: the physical scan
   invariant is the only fact needed, and the candidate memory is the store
   whose defining equation has to be substituted first.  Six sites. *)
Tactic Notation "msat_propagate_scan_length_close_p6" ident(sw) ident(ret)
    ident(mv) ident(rst) ident(gb) ident(wm) ident(ii_v) ident(jj_v)
    ident(hscan) ident(cpm) :=
  right; intros;
  bind_fact ( propagation_watch_scan_physical sw ret mv rst gb wm ii_v jj_v ) as hscan;
  unfold propagation_watch_scan_physical in hscan;
  destruct hscan as [_ [_ [_ [_ Hlength]]]];
  subst cpm;
  entailer_with ltac:(lia).

(* The decision-variable bound pair on the leaf branches of the search
   selection.  The [_pair] sibling of this closer is reached from
   proof_common's [msat_search_decision_var_bounds_pure].  Eight sites. *)
Tactic Notation "msat_search_selection_leaves_p6" ident(n_v) ident(f_v)
    ident(arr_v) ident(inst_v) ident(rv) ident(msel) ident(hsel) :=
  Unfold;
  left; intros;
  bind_fact ( solver_search_selection_state n_v f_v arr_v inst_v rv msel ) as hsel;
  msat_search_close_decision_var_bounds_leaves hsel rv.

(* The [ms_size Mselected = n] side condition once the model is ready.
   Five sites. *)
Tactic Notation "msat_search_model_ready_size_p6" ident(n_v) ident(f_v)
    ident(arr_v) ident(inst_v) ident(msel) ident(hready) :=
  Unfold;
  left; intros;
  bind_fact ( solver_search_model_ready n_v f_v arr_v inst_v msel ) as hready;
  msat_search_close_model_ready_size_eq hready msel n_v.

(* The header-word range obligation of [solver_lit_removable]: the entailer
   leaves the arithmetic, which follows by case analysis on the learnt flag.
   Three sites. *)
Tactic Notation "msat_lit_removable_hdr_bound_p6" ident(learnt_v)
    ident(words_v) ident(hhdr) :=
  Unfold;
  right; intros;
  bind_fact ( clause_hdr_word learnt_v (Zlength words_v) <= 2147483647 ) as hhdr;
  entailer_with ltac:(lia);
  unfold clause_hdr_word in hhdr;
  destruct learnt_v; lia.

(* The literal-range obligation on a word of the learnt clause: [k] is the
   fixed index (0 or 1) whose [lit_wf_c] bound is staged into the context
   first, [j_v] is the loop index the entailer still has to discharge, [cw]
   the clause word list and [n_v] the variable count.  Seven sites. *)
Tactic Notation "msat_analyze_clause_word_range_p6" ident(n_v) ident(j_v)
    ident(cw) constr(k) :=
  Unfold; right; intros;
  msat_analyze_stage_clause_word_range_at_fixed_index n_v k cw;
  msat_analyze_close_clause_word_range_via_entailer n_v j_v cw.

(* The return entailment of [veci_reserve] / [vecp_reserve]: the two proofs
   differ only in the vector element type.  Two sites. *)
Tactic Notation "msat_reserve_return_close_p6" ident(cap_v) :=
  aggressive_pre_process;
    try (subst cap_v);
    entailer_with ltac:(lia).

(* The return entailment of [veci_push] / [vecp_push]: the appended element
   lengthens the vector by exactly one.  Two sites. *)
Ltac msat_push_return_close_p6 :=
  aggressive_pre_process;
  rewrite Zlength_app, Zlength_cons, Zlength_nil;
  entailer_with ltac:(lia).

(* The tagged-vector capacity bounds of [solver_lit_removable], which live
   under the leading [veci_rep_at] of the precondition.  Two sites. *)
Ltac msat_lit_removable_tagged_bounds_p6 :=
  Unfold;
  left; intros;
  unfold veci_rep_at at 1; Intros_p Htagged_bounds;
  split_pures;
  dump_pre_spatial; lia.

(* The safety obligations of [solver_canceluntil]: every one of them is an
   arithmetic consequence of the solver shape invariant.  Two sites. *)
Tactic Notation "msat_canceluntil_shape_close_p6" ident(m_v) ident(hshape) :=
  aggressive_pre_process;
  bind_fact ( solver_shape m_v ) as hshape;
  dump_pre_spatial; unfold solver_shape in hshape; intuition lia.

(* The two disjunct choices of an [order_select] entailment whose conclusion
   is an [||]: [transitivity] onto the arm, then the matching intro rule. *)
Ltac msat_order_select_orp_left_p6 :=
  lazymatch goal with
  | |- ?P |-- ?T =>
      lazymatch T with
      | ?Q || ?R => transitivity Q; [| apply derivable1_orp_intros1]
      end
  end.

(* The right-arm counterpart of [msat_order_select_orp_left_p6]. *)
Ltac msat_order_select_orp_right_p6 :=
  lazymatch goal with
  | |- ?P |-- ?T =>
      lazymatch T with
      | ?Q || ?R => transitivity R; [| apply derivable1_orp_intros2]
      end
  end.

(* Opener shared by the [order_select] sift-descent entailments: it names the
   22 loop binders (every [order_select_entail_wit_*] carries the same ones,
   under the names used here) and commits to the outer left arm. *)
Ltac msat_order_select_cursor_open_p6 :=
  Unfold;
  intros s_pre activity_ptr assigns_ptr orderpos_ptr order_cap qhead activity0
    trail0 assigns0 heap0 n order_ptr child size next x i sift_heap_before
    sift_heap_now sift_orderpos_now sift_seed_value_now sift_seed_shadow_now;
  intros;
  msat_order_select_orp_left_p6.

(* The six int-range side conditions of the sift cursors; [h1] .. [h6] are the
   names given to the ranges so that the [change] steps can normalise them
   into the INT_MIN/INT_MAX spelling [lia] is given. *)
Tactic Notation "msat_order_select_cursor_ranges_p6" ident(s_v) ident(cap_v)
    ident(heap_v) ident(n_v) ident(size_v) ident(next_v) ident(x_v)
    ident(h1) ident(h2) ident(h3) ident(h4) ident(h5) ident(h6) :=
  poly_store_unfold; Rename pre_process_pure;
  prop_rewrite (store_int_range
    (&(s_v # "solver_t" ->ₛ "order" .ₛ "cap")) cap_v);
  Intros_p h1;
  prop_rewrite (store_int_range
    (&(s_v # "solver_t" ->ₛ "order" .ₛ "size")) (Zlength heap_v));
  Intros_p h2;
  prop_rewrite (store_int_range (&(s_v # "solver_t" ->ₛ "size")) n_v);
  Intros_p h3;
  prop_rewrite (store_int_range (&("size")) size_v);
  Intros_p h4;
  prop_rewrite (store_int_range (&("next")) next_v);
  Intros_p h5;
  prop_rewrite (store_int_range (&("x")) x_v);
  Intros_p h6;
  entailer_with ltac:(lia);
  change (INT_MIN <= cap_v <= INT_MAX) in h1;
  change (INT_MIN <= Zlength heap_v <= INT_MAX) in h2;
  change (INT_MIN <= n_v <= INT_MAX) in h3;
  change (INT_MIN <= size_v <= INT_MAX) in h4;
  change (INT_MIN <= next_v <= INT_MAX) in h5;
  change (INT_MIN <= x_v <= INT_MAX) in h6;
  try lia;
  try (rewrite Znth_replace_Znth_Same by lia; lia).

(* The capacity/room obligations a sift step leaves once the heap slot has
   been written: the sift invariant bounds the heap length by [n], and the
   two property rewrites recover the vector's own capacity facts.  Four sites. *)
Tactic Notation "msat_order_select_sift_capacity_p6" ident(s_v) ident(optr)
    ident(cap_v) ident(n_v) ident(next_v) ident(x_v) ident(i_v)
    ident(heap0_v) ident(before_v) ident(now_v) ident(pos_v)
    ident(assigns_v) ident(trail_v) ident(qhead_v)
    ident(hinv) ident(hcap) ident(hroom) :=
  Rename pre_process_pure;
  bind_fact ( order_select_sift_inv n_v next_v x_v i_v heap0_v before_v now_v pos_v
    assigns_v trail_v qhead_v ) as hinv;
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
  prop_rewrite (store_int_range
    (&((s_v) # "solver_t" ->ₛ "order" .ₛ "cap")) cap_v);
  Intros_p hcap;
  prop_rewrite (IntArray.undef_seg_valid
    optr (Zlength now_v) cap_v);
  Intros_p hroom;
  msat_manual_entailer_with ltac:(int_auto).

(* The wide sibling step of [msat_order_select_sift_promote_p6]: when the goal
   still carries both child activity cells, their four range facts and their
   distinctness are bound and the pair is refolded into the double-array
   predicate.  Split out only to keep the promote tactic under the line cap. *)
Tactic Notation "msat_order_select_sift_siblings_p6"
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
    (double_array_missing2_refold__vecp_remove act_ptr
      (Znth child_v heap_v 0) (Znth (child_v + 1) heap_v 0)
      n_v act0 (conj hz2 hz3) (conj hz4 hz5) hz6).

(* The sift step that promotes the hole into the loop invariant.  [chld] says
   whether the goal still spells the child index as [child - 0]; [wide] says
   whether the two sibling activity cells have to be refolded, which is the
   only other difference between the four members.  Four sites. *)
Tactic Notation "msat_order_select_sift_promote_p6" ident(hz) ident(hinv)
    ident(hp) ident(op) constr(chld) constr(wide)
    ident(hz2) ident(hz3) ident(hz4) ident(hz5) ident(hz6) :=
  Unfold;
  left;
  intros s_pre activity_ptr assigns_ptr orderpos_ptr order_cap qhead activity0
    trail0 assigns0 heap0 n order_ptr child size next x i sift_heap_before
    sift_heap_now sift_orderpos_now sift_seed_value_now sift_seed_shadow_now;
  intros;
  poly_store_unfold; Rename pre_process_pure;
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
      msat_order_select_sift_siblings_p6 activity_ptr activity0 n child
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
  prop_apply (store_int_range
    (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap);
  Intros_p Hcap_range;
  prop_apply (IntArray.undef_seg_valid
    order_ptr (Zlength sift_heap_now) order_cap);
  Intros_p Hcap_room;
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n op);
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength sift_heap_now) hp);
  Exists sift_seed_shadow_now sift_seed_value_now hp op;
  rewrite <- Hheaplen;
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr;
  entailer_with ltac:(lia);
  csimpl; entailer_with ltac:(lia).


(* Writing the two literal-statistics slots that [solver_analyze] updates: slot 9
   (max_literals) and slot 10 (tot_literals) of an eleven-slot statistics list.
   The three equations say the two written slots read back and every slot below
   them is untouched; the [solver_analyze] stats wits need all three. *)
Lemma stats_pair_update_slots_p6 :
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
   every entry to {0,1}.  Lifted verbatim out of
   [solver_analyze_which_implies_wit_39], where it was an inline 24-line
   induction inside a 177-line proof. *)
Lemma analysis_tags_exact_nil_zero_p6 :
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


(* Re-writing a run of words back over the very cells it was read from leaves the
   watch memory unchanged: [binary_watch_write] at [|prefix| + 1] over [copied]
   rewrites exactly the [copied] segment of [prefix ++ current :: copied ++
   suffix].  The binary-watch copy step needs it on both no-op arms. *)
Lemma binary_watch_write_identity_p6 :
  forall (prefix : list Z) (current : Z) (copied suffix : list Z),
    binary_watch_write (Zlength prefix + 1) copied
      (prefix ++ (current :: (copied ++ suffix))) =
    prefix ++ (current :: (copied ++ suffix)).
Proof.
  intros prefix current copied0.
  revert prefix current.
  induction copied0 as [|a copied0 IH]; intros prefix current suffix.
  - simpl. reflexivity.
  - simpl.
    set (L := prefix ++ (current :: (a :: (copied0 ++ suffix)))).
    assert (Hnth :
      Znth (Zlength prefix + 1) L 0 = a).
    { unfold L. rewrite app_Znth2 by lia.
      replace (Zlength prefix + 1 - Zlength prefix) with 1 by lia.
      simpl. reflexivity. }
    assert (Hrep :
      replace_Znth (Zlength prefix + 1) a L = L).
    { eapply eq_trans.
      - apply (f_equal (fun y : Z =>
          replace_Znth (Zlength prefix + 1) y L)).
        symmetry. exact Hnth.
      - apply replace_Znth_Znth. }
    change (binary_watch_write (Zlength prefix + 1 + 1) copied0
      (replace_Znth (Zlength prefix + 1) a L) = L).
    rewrite Hrep.
    replace (Zlength prefix + 1 + 1) with
      (Zlength (prefix +:: current) + 1) by
      (rewrite Zlength_app_cons; lia).
    unfold L.
    assert (Happend :
      prefix ++ (current :: (a :: (copied0 ++ suffix))) =
      (prefix +:: current) ++ (a :: (copied0 ++ suffix))).
    { change (prefix ++ ((current :: nil) ++ (a :: (copied0 ++ suffix))) =
        (prefix ++ (current :: nil)) ++ (a :: (copied0 ++ suffix))).
      apply app_assoc. }
    rewrite Happend.
    apply (IH (prefix +:: current) a suffix).
Qed.


(* [binary_watch_write dst ws base] stores [ws] into the cells at [dst ..
   dst + |ws|), so any index at or past the end of that run still reads [base].
   The binary-watch copy step needs it to read the source cell out of the
   pre-write memory. *)
Lemma binary_watch_write_read_after_p6 :
  forall (base : list Z) (write_dst : Z) (writes : list Z) (index : Z),
    0 <= write_dst ->
    write_dst + Zlength writes <= index ->
    index < Zlength base ->
    Znth index (binary_watch_write write_dst writes base) 0 =
    Znth index base 0.
Proof.
  intros base write_dst writes.
  revert base write_dst.
  induction writes as [|a writes IH];
    intros base write_dst index Hwrite_dst Hafter Hindex.
  - simpl. reflexivity.
  - simpl.
    assert (Hwrite_dst' : 0 <= write_dst + 1) by lia.
    assert (Hafter' : write_dst + 1 + Zlength writes <= index).
    { rewrite Zlength_cons in Hafter. lia. }
    assert (Hindex' :
      index < Zlength (replace_Znth write_dst a base)).
    { rewrite Zlength_replace_Znth. exact Hindex. }
    pose proof (Zlength_nonneg writes) as Hwrites_nonneg.
    assert (Hwrite_bound : 0 <= write_dst < Zlength base) by lia.
    assert (Hindex_bound : 0 <= index < Zlength base) by lia.
    assert (Hwrite_index : write_dst <> index) by lia.
    rewrite (IH (replace_Znth write_dst a base) (write_dst + 1)
      index Hwrite_dst' Hafter' Hindex').
    rewrite (Znth_replace_Znth_Diff 0 base write_dst index a
      Hwrite_bound Hindex_bound Hwrite_index).
    reflexivity.
Qed.

(* A half-open slice extended by the cell at its upper bound is the slice one
   longer.  Both copy cursors of the binary-watch step close a range this way. *)
Lemma sublist_snoc_p6 :
  forall (l : list Z) (lo hi : Z),
    0 <= lo <= hi ->
    hi < Zlength l ->
    sublist lo hi l +:: Znth hi l 0 = sublist lo (hi + 1) l.
Proof.
  intros l lo hi Hlo Hhi.
  change (sublist lo hi l ++ (Znth hi l 0 :: nil) = sublist lo (hi + 1) l).
  rewrite (sublist_split lo (hi + 1) hi l) by lia.
  f_equal.
  symmetry. apply sublist_single.
  lia.
Qed.

(* Storing into a cell of the low prefix splits the array into the three slices
   the copy step's array merges address separately: below [dst + 1], between
   [dst + 1] and [src + 1], and from [src + 1] to the end. *)
Lemma replace_Znth_prefix_split_p6 :
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


(* ---------------------------------------------------------------------- *)
(* The four solver_propagate_entail_wit_22_*_binary_keep obligations differ  *)
(* only in PreH24 (jj < ii vs jj = ii), so `exact` cannot share them, but    *)
(* their proofs were four byte-identical 323-line copies.  The script below  *)
(* is that text, split into the small documented steps of the argument: the  *)
(* generated facts are bound by shape, the enqueue transition is opened, and *)
(* each of its three arms is closed by its own tactic.  Every fact a step    *)
(* introduces and a later step reads is a formal argument, because Ltac      *)
(* resolves a body identifier at DEFINITION time; everything a step can read *)
(* off a hypothesis it already holds is matched instead of passed.           *)
(* ---------------------------------------------------------------------- *)

(* Binds the twelve generated facts of this obligation by their STATEMENT
   shape instead of by their PreH number.  The two [replace_Znth] equations
   and the [logical_words] equation are matched jointly with the fact that
   pins their free list, which is what makes each of them unambiguous.  Runs
   before any [destruct]: opening the transition fact would put a second
   [solver_propagation_scan_semantics] in the context. *)
Ltac msat_binary_keep_bind_facts_p6 :=
  match goal with
  | Ha : _ = replace_Znth _ (Znth _ ?tm _) ?tm, Hb : ?tm = replace_Znth _ _ _ |- _ =>
      rename Ha into H_tagged_enqueue_success_memory;
      rename Hb into H_tagged_memory
  end;
  match goal with
  | Hw : ms_wm _ = _ ++ ?lw :: _, Hl : ?lw = _ ++ _ |- _ =>
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

(* Opens the obligation: both structural transitions are unfolded and
   destructed under fixed names, the left disjunct of the post-condition is
   selected, the enqueue post-state's existentials are introduced, and the
   enqueue transition is split into its assigned / conflicting / fresh arms.
   The seven introduced names are arguments so that the wrapper can hand the
   same names to the arm tactics below. *)
Tactic Notation "msat_binary_keep_open_p6"
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

(* The assigned arm: the literal already carries its own sign, so the
   enqueue test is false and the route solver collapses to the scan solver.
   The tested expression is read off the [Znth ... = lit_sig ...] conjunct
   rather than respelled. *)
Tactic Notation "msat_binary_keep_same_head_p6"
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

(* Shared by the assigned and the fresh arm: the written watch memory is the
   route memory (the write at [ii] puts back what [ii] already held), and the
   logical word list splits at the scanned literal.  Both statements are read
   off the hypotheses, so no list has to be named. *)
Tactic Notation "msat_binary_keep_route_memory_p6"
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

(* Shared by the assigned and the fresh arm: opens the physical scan
   invariant of the route state and derives the four index bounds and the
   [confl = 0] fact that the closing entailer needs.  [Hii0] is the only one
   that still reads a generated equation, and it is located by its right-hand
   side [ii]. *)
Tactic Notation "msat_binary_keep_route_bounds_p6"
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

(* Closes the assigned arm: the twenty existential witnesses are read off the
   physical scan invariant, the watch-capacity split and the watch-list slot
   equation, so only the four names introduced by the opener are passed in. *)
Tactic Notation "msat_binary_keep_same_close_p6"
    ident(trl_v) ident(rsn_v) ident(lvl_v) ident(htagged) ident(hsimp)
    ident(hprop) ident(hwm) ident(hlogical) ident(hfrontier) :=
  match goal with
  | Hp1 : wlist_scan_inv ?sw ?rr ?mv ?rt, Hp2 : ?mr = ?rr ++ ?gr ++ ?rt,
    Hp3 : Zlength ?rr = ?jn, Hp4 : Zlength (?rr ++ ?gr) = ?iN |- _ =>
      match type of hwm with
      | ms_wm ?M = ?wpre ++ _ :: ?wpost =>
          match type of hfrontier with
          | propagation_scan_frontier ?Me _ _ =>
              match goal with
              | Hc : ms_wcaps _ = ?cp ++ ?wc :: ?cq,
                Hv : _ = vecp_slot ?wl _ |- _ =>
                  Exists trl_v rsn_v (Znth 2 (ms_stats M) 0)
                    (ms_simpdb_props M) cp wc cq wpre wpost (rr ++ rt) sw
                    mv gr mr iN jn rr rt Me;
                  Exists M lvl_v
              end
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
  try (set_String_name; sepcon_assoc_change; sepcon_cancel;
    subst_all_strings; unfold Znth; cbn; csimpl; intros m Hm; exact Hm);
  try (rewrite hwm, hlogical; reflexivity).

(* The conflicting arm is vacuous here: the transition returns 0 while the
   call site already established that the return value is 1. *)
Tactic Notation "msat_binary_keep_conflict_p6" ident(hconflict) :=
  destruct hconflict as [_ [_ [Hret _]]];
  lia.

(* The fresh arm: the literal was unassigned, so the enqueue test is true and
   the route solver is the overlay of a successful enqueue.  The tested
   expression is read off the [Znth ... = 0] conjunct rather than respelled. *)
Tactic Notation "msat_binary_keep_new_head_p6"
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

(* Two facts the fresh arm needs about the pre-state: the queue has room for
   one more literal (the enqueue contract's own implication, discharged by the
   unassigned test), and the root propagation counter is already zero.  Both
   statements are read off the hypotheses that carry them. *)
Tactic Notation "msat_binary_keep_new_facts_p6"
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

(* The three msolver invariants transported to the route state: shape, seed
   shadow and caller frame all survive the enqueue overlay.  The route state
   is read off its defining equation and the caller's model off the frame
   fact, so neither has to be named. *)
Tactic Notation "msat_binary_keep_new_overlay_p6"
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
            Hqtail_range & Hwm_len & Hwcaps_len & Hbinary_lits_len &
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

(* The four equations that let the closing entailer rewrite the route state:
   its trail is well formed and has the queue's length, it is the folded
   enqueue-success overlay, and both the binary representation and the
   propagate frame are unchanged by that overlay. *)
Tactic Notation "msat_binary_keep_new_route_eqs_p6"
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

(* The queue frontier survives a successful enqueue: [qhead] is unchanged,
   the recorded literal is still the one at the entry head, the trail only
   grew at the end, and the rollback carrier is transported by the shared
   lemma.  Every name comes from the two hypotheses this step already holds. *)
Tactic Notation "msat_binary_keep_new_frontier_p6"
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

(* Instantiates the post-state of the fresh arm.  Same twenty witnesses as
   the assigned arm, but around the route solver, and the two representation
   equations are rewritten before the entailer runs. *)
Tactic Notation "msat_binary_keep_new_exists_p6"
    ident(trl_v) ident(rsn_v) ident(lvl_v) ident(hmroute) ident(hsem2)
    ident(hbinary) ident(hframe) ident(htagged) ident(hwm) ident(hfrontier) :=
  match goal with
  | Hp1 : wlist_scan_inv ?sw ?rr ?mv ?rt, Hp2 : ?mr = ?rr ++ ?gr ++ ?rt,
    Hp3 : Zlength ?rr = ?jn, Hp4 : Zlength (?rr ++ ?gr) = ?iN |- _ =>
      match type of hwm with
      | ms_wm _ = ?wpre ++ _ :: ?wpost =>
          match type of hmroute with
          | ?Mr = _ =>
              match type of hfrontier with
              | propagation_scan_frontier ?Me _ _ =>
                  match goal with
                  | Hc : ms_wcaps _ = ?cp ++ ?wc :: ?cq,
                    Hv : _ = vecp_slot ?wl _ |- _ =>
                      Exists trl_v rsn_v (Znth 2 (ms_stats Mr) 0)
                        (ms_simpdb_props Mr) cp wc cq wpre wpost
                        (rr ++ rt) sw mv gr mr iN jn rr rt Me;
                      Exists Mr lvl_v
                  end
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
  entailer_with lia.

(* The pure and small spatial side goals the entailer leaves on the fresh
   arm.  Each transported invariant is offered both folded and unfolded
   because the entailer states some of them about the overlay expression and
   some about the route state itself. *)
Tactic Notation "msat_binary_keep_new_side_p6"
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
   shared alias lemma.  The scanned literal and the reason tag are read off
   the folded enqueue equation. *)
Tactic Notation "msat_binary_keep_new_stats_p6"
    ident(lvl_v) ident(rsn_v) ident(hroute_enq) ident(hsimp) ident(hprop)
    ident(s_v) :=
  match type of hroute_enq with
  | _ = msolver_propagation_enqueue_success ?M ?tl ?tp _ =>
      unfold CharArray.seg, IntArray.seg, PtrArray.seg, Znth;
      cbn;
      rewrite (logic_equiv_sepcon_swap
        (store_array_rec
        (fun (x : addr) (lo a : Z) =>
        (x + lo * sizeof ( INT )) # Int |-> a)
        lvl_v 0 (ms_size M)
        (replace_Znth (lit_var_c tl)
        (Zlength (mt_lim (ms_core M)))
        (mt_levels (ms_core M))))
        (store_array_rec
        (fun (x : addr) (lo a : Z) => (x + lo * ptr_size_Z) # Ptr |-> a)
        rsn_v 0 (ms_size M)
        (replace_Znth (lit_var_c tl)
        tp (ms_reason_words M))) _)
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
  set_String_name;
  intros m Hm;
  exact Hm.

(* The four [binary_keep] members of [solver_propagate] open with the same
   [aggressive_pre_process] and then run the steps above in order; the
   bracketed dispatch is the three arms of the enqueue transition.  Four
   sites. *)
Ltac msat_propagate_binary_keep_p6 :=
  aggressive_pre_process;
  msat_binary_keep_bind_facts_p6;
  msat_binary_keep_open_p6 qtail' assigns' levels' reasons' trail' rsn trl;
  [ msat_binary_keep_same_head_p6 Hsame HMroute Mroute assigns' levels'
      reasons' trail' qtail';
    msat_binary_keep_route_memory_p6 H_tagged_enqueue_success_memory
      H_tagged_memory Hmemory H_logical_words Hrest Hretained;
    msat_binary_keep_route_bounds_p6 Hphysical ii jj garbage_route confl
      H_solver_propagation_scan_semantics Hrest;
    msat_binary_keep_same_close_p6 trl rsn levels_entry Htagged_memory
      H_simp_count H_prop_count H_ms_wm Hlogical_route
      H_propagation_scan_frontier
  | msat_binary_keep_conflict_p6 Hconflict
  | msat_binary_keep_new_head_p6 Hnew HMroute assigns' levels' reasons'
      trail' qtail';
    msat_binary_keep_route_memory_p6 H_tagged_enqueue_success_memory
      H_tagged_memory Hmemory H_logical_words Hrest Hretained;
    msat_binary_keep_route_bounds_p6 Hphysical ii jj garbage_route confl
      H_solver_propagation_scan_semantics Hrest;
    msat_binary_keep_new_facts_p6 H_enqueue_input Hzero
      H_solver_propagation_scan_semantics;
    msat_binary_keep_new_overlay_p6 HMroute H_solver_shape Hpending_zero
      H_msolver_seed_shadow H_propagation_caller_frame;
    msat_binary_keep_new_route_eqs_p6 K Hrest
      H_solver_propagation_scan_semantics H_solver_shape HMroute Heq
      scan_current p s_pre;
    msat_binary_keep_new_frontier_p6 Hroute_enqueue
      H_propagation_scan_frontier Htrail_wf Heq;
    msat_binary_keep_new_exists_p6 trl rsn levels_entry HMroute Hsem
      Hbinary_route Hframe_route Htagged_memory H_ms_wm
      H_propagation_scan_frontier;
    msat_binary_keep_new_side_p6 H_ms_wm Hlogical_route HMroute
      Hfrontier_route Hshape_route Hseed_route Hcaller_route;
    msat_binary_keep_new_stats_p6 levels_entry rsn Hroute_enqueue
      H_simp_count H_prop_count s_pre
  ].

(* ===== assume which_implies wits (2 proofs) ===== *)
Lemma proof_of_assume_which_implies_wit_1 : assume_which_implies_wit_1.
Proof.
  Unfold.
  right.
  intros.
  unfold enqueue_state_at.
  Intros rsn trl.
  Exists trl rsn.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_assume_which_implies_wit_2 : assume_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  replace (lit_var_c l0 - 0) with (lit_var_c l0) by lia.
  reflexivity.
Qed.

(* ===== lit_var return wits (2 proofs) ===== *)
Lemma proof_of_lit_var_return_wit_1_original : lit_var_return_wit_1_original.
Proof.
  aggressive_pre_process;
    unfold lit_var_c;
    rewrite Z.shiftr_div_pow2 by lia;
    change (2 ^ 1) with 2;
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_lit_var_return_wit_3_bounded_index : lit_var_return_wit_3_bounded_index.
Proof.
  Unfold.
  right; intros.
  unfold lit_var_c in *.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  assert (Hlo : 0 <= l_pre / 2) by (apply Z.div_pos; lia).
  assert (Hhi : l_pre / 2 < lv_bound_n_bounded_index)
    by (apply Z.div_lt_upper_bound; lia).
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== order_select entail wits (22 proofs) ===== *)
Lemma proof_of_order_select_entail_wit_2_1 : order_select_entail_wit_2_1.
Proof.
  Unfold.
  right; intros; poly_store_unfold; Rename pre_process_pure.
  subst retval_3.
  (* goal.v binds this arm's seed shadow as [z2] (the sibling arm names it
       [seed_shadow]); that is the witness the [Exists] below needs. *)
  assert (Hfp : fp64_eq (Z_to_fp64 z2) (Z_to_fp64 z2)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  Exists z2.
  replace (Zlength assigns0) with n by lia.
  unfold order_select_loop_inv.
  entailer_with lia.
  unfold incl. auto.
Qed.

Lemma proof_of_order_select_entail_wit_2_2 : order_select_entail_wit_2_2.
Proof.
  Unfold.
  right; intros; poly_store_unfold; Rename pre_process_pure.
  subst retval.
  assert (Hfp : fp64_eq (Z_to_fp64 seed_shadow) (Z_to_fp64 seed_shadow)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  Exists seed_shadow.
  replace (Zlength assigns0) with n by lia.
  unfold order_select_loop_inv.
  entailer_with ltac:(lia).
  unfold incl. auto.
Qed.

Lemma proof_of_order_select_entail_wit_2_3 : order_select_entail_wit_2_3.
Proof.
  Unfold.
  right; intros; poly_store_unfold; Rename pre_process_pure.
  subst retval_2.
  assert (Hfp : fp64_eq (Z_to_fp64 z2) (Z_to_fp64 z2)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  Exists z2.
  replace (Zlength assigns0) with n by lia.
  unfold order_select_loop_inv.
  entailer_with ltac:(lia).
  unfold incl. auto.
Qed.

Lemma proof_of_order_select_entail_wit_4 : order_select_entail_wit_4.
Proof.
  Unfold.
  left; intros; poly_store_unfold; Rename pre_process_pure.
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  pose proof
    (order_select_loop_inv_cell_range__order_select
       n heap0 heap_now orderpos_now assigns0 trail0 qhead 0 H_order_select_loop_inv
       ltac:(lia)) as Hroot_range.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_select_entail_wit_7 : order_select_entail_wit_7.
Proof.
  Unfold.
  left; intros; poly_store_unfold; Rename pre_process_pure.
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  pose proof
    (order_select_loop_inv_cell_range__order_select
       n heap0 heap_now orderpos_now assigns0 trail0 qhead
       (retval_2 - 1) H_order_select_loop_inv ltac:(lia)) as Hlast_range.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_select_entail_wit_8 : order_select_entail_wit_8.
Proof.
  Unfold.
  left; intros; poly_store_unfold; Rename pre_process_pure.
  entailer_with ltac:(lia);
    replace (retval_2 - 1 - 0) with (retval_2 - 1) by lia;
    assumption.
Qed.

Lemma proof_of_order_select_entail_wit_9 : order_select_entail_wit_9.
Proof.
  Unfold.
  intros.
  poly_store_unfold; Rename pre_process_pure.
  bind_fact ( Zlength (sublist 0 (retval - 1) heap_now) = retval - 1 ) as H_Zlength.
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr 0 n activity0).
  Intros_p Hactivity_len.
  assert (Hn : 0 < n) by lia.
  assert (Hsift :
    order_select_sift_inv n (Znth 0 heap_now 0)
      (Znth (retval - 1) heap_now 0) 0 heap0 heap_now
      (sublist 0 (retval - 1) heap_now)
      (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now)
      assigns0 trail0 qhead).
  { eapply order_select_sift_inv_init__order_select.
    - exact H_order_select_loop_inv.
    - lia.
    - lia.
    - rewrite (Znth_indep heap_now 0 0 (-1)) by lia. reflexivity.
    - rewrite (Znth_indep heap_now (retval - 1) 0 (-1)) by lia.
      reflexivity. }
  destruct (Z_le_gt_dec (retval - 1) 1) as [Hsmall | Hmore].
  - assert (Hsize : retval - 1 = 1) by lia.
    assert (Hone : Znth 1 (sublist 0 (retval - 1) heap_now) 0 = 0).
    { apply Znth_zero_past_end__order_select. rewrite H_Zlength. lia. }
    assert (Htwo : Znth 2 (sublist 0 (retval - 1) heap_now) 0 = 0).
    { apply Znth_zero_past_end__order_select. rewrite H_Zlength. lia. }
    msat_order_select_orp_left_p6.
    msat_order_select_orp_left_p6.
    Exists seed_shadow_now seed_value_now heap_now
      (sublist 0 (retval - 1) heap_now)
      (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
    replace (0 - 0) with 0 by lia.
    replace (retval - 1 - 0) with (retval - 1) by lia.
    entailer_with ltac:(int_auto);
      replace (1 + 1) with 2 by lia;
      rewrite Htwo;
      lia.
  - destruct (Z_le_gt_dec (retval - 1) 2) as [Htwo_children | Hlarge].
    + assert (Hsize : retval - 1 = 2) by lia.
      assert (Hchild_range :
        0 <= Znth 1 (sublist 0 (retval - 1) heap_now) 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - lia. }
      assert (Hpast : Znth 2 (sublist 0 (retval - 1) heap_now) 0 = 0).
      { apply Znth_zero_past_end__order_select. rewrite H_Zlength. lia. }
      msat_order_select_orp_left_p6.
      msat_order_select_orp_right_p6.
      Exists seed_shadow_now seed_value_now heap_now
        (sublist 0 (retval - 1) heap_now)
        (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
      entailer_with ltac:(int_auto).
      sep_apply_l_atomic
        (DoubleArray.seg_split_to_missing_i activity_ptr 0
          (Znth 1 (sublist 0 (retval - 1) heap_now) 0) n activity0
          msat_fp64_zero).
      * dump_pre_spatial. exact Hchild_range.
      * unfold StoreDoubleAsElement.storeA, double_Znth, IntArray.full.
        replace (1 - 0) with 1 by lia.
        replace (0 - 0) with 0 by lia.
        entailer_with ltac:(int_auto).
      * replace (0 - 0) with 0 by lia.
        replace (retval - 1 - 0) with (retval - 1) by lia.
        exact Hsift.
    + assert (Hchild1_range :
        0 <= Znth 1 (sublist 0 (retval - 1) heap_now) 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - lia. }
      assert (Hchild2_range :
        0 <= Znth 2 (sublist 0 (retval - 1) heap_now) 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - lia. }
      assert (Hchildren_neq :
        Znth 1 (sublist 0 (retval - 1) heap_now) 0 <>
        Znth 2 (sublist 0 (retval - 1) heap_now) 0).
      { eapply order_select_sift_inv_cells_neq__order_select.
        - exact Hsift.
        - rewrite H_Zlength. lia.
        - rewrite H_Zlength. lia.
        - lia.
        - lia.
        - lia. }
      msat_order_select_orp_right_p6.
      Exists seed_shadow_now seed_value_now heap_now
        (sublist 0 (retval - 1) heap_now)
        (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
      entailer_with ltac:(int_auto).
      sep_apply
        (double_array_seg_split_to_missing2__order_select activity_ptr
          (Znth 1 (sublist 0 (retval - 1) heap_now) 0)
          (Znth 2 (sublist 0 (retval - 1) heap_now) 0)
          n activity0 Hchild1_range Hchild2_range Hchildren_neq).
      * unfold IntArray.full.
        replace (0 - 0) with 0 by lia.
        replace (1 - 0) with 1 by lia.
        replace (1 + 1 - 0) with 2 by lia.
        replace
          (Znth 1 (sublist 0 (retval - 1) heap_now) 0 - 0)
          with (Znth 1 (sublist 0 (retval - 1) heap_now) 0) by lia.
        replace
          (Znth 2 (sublist 0 (retval - 1) heap_now) 0 - 0)
          with (Znth 2 (sublist 0 (retval - 1) heap_now) 0) by lia.
        entailer_with ltac:(int_auto).
      * replace (0 - 0) with 0 by lia.
        replace (retval - 1 - 0) with (retval - 1) by lia.
        exact Hsift.
Qed.

Lemma proof_of_order_select_entail_wit_10_1 : order_select_entail_wit_10_1.
Proof.
  msat_order_select_cursor_open_p6. msat_order_select_orp_left_p6.
  msat_order_select_cursor_ranges_p6 s_pre order_cap sift_heap_now n size next x
    Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
Qed.

Lemma proof_of_order_select_entail_wit_10_2 : order_select_entail_wit_10_2.
Proof.
  msat_order_select_cursor_open_p6. msat_order_select_orp_right_p6.
  msat_order_select_cursor_ranges_p6 s_pre order_cap sift_heap_now n size next x
    Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
Qed.

Lemma proof_of_order_select_entail_wit_10_3 : order_select_entail_wit_10_3.
Proof.
  Unfold.
  intros.
  msat_order_select_orp_right_p6.
  poly_store_unfold; Rename pre_process_pure.
  prop_rewrite (store_int_range
    (&(s_pre # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap).
  Intros.
  prop_rewrite (store_int_range
    (&(s_pre # "solver_t" ->ₛ "order" .ₛ "size"))
    (Zlength sift_heap_now)).
  Intros.
  prop_rewrite (store_int_range (&(s_pre # "solver_t" ->ₛ "size")) n).
  Intros.
  prop_rewrite (store_int_range (&("size")) size_2).
  Intros.
  prop_rewrite (store_int_range (&("next")) next_2).
  Intros.
  prop_rewrite (store_int_range (&("x")) x_2).
  Intros.
  entailer_with ltac:(lia);
    change (INT_MIN <= order_cap <= INT_MAX) in H;
    change (INT_MIN <= Zlength sift_heap_now <= INT_MAX) in H0;
    change (INT_MIN <= n <= INT_MAX) in H1;
    change (INT_MIN <= size_2 <= INT_MAX) in H2;
    change (INT_MIN <= next_2 <= INT_MAX) in H3;
    change (INT_MIN <= x_2 <= INT_MAX) in H4;
    try lia;
    try (rewrite Znth_replace_Znth_Same by lia; lia).
Qed.

(* The sift arms use the same index/readback normalizations at two loci.
   Keep goal-only rewriting separate from rewriting the whole context. *)
Local Ltac msat_order_select_offsets_all_p6 leftidx rightidx heap :=
  replace (leftidx - 0) with leftidx in * by lia;
  replace (rightidx - 0) with rightidx in * by lia;
  replace (Znth leftidx heap 0 - 0) with (Znth leftidx heap 0) in * by lia;
  replace (Znth rightidx heap 0 - 0) with (Znth rightidx heap 0) in * by lia.

Local Ltac msat_order_select_offsets_goal_p6 leftidx rightidx heap :=
  replace (leftidx - 0) with leftidx by lia;
  replace (rightidx - 0) with rightidx by lia;
  replace (Znth leftidx heap 0 - 0) with (Znth leftidx heap 0) by lia;
  replace (Znth rightidx heap 0 - 0) with (Znth rightidx heap 0) by lia.

Lemma proof_of_order_select_entail_wit_11_1 : order_select_entail_wit_11_1.
Proof.
  Unfold.
  intros.
  poly_store_unfold; Rename pre_process_pure.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before_2 sift_heap_now_2 sift_orderpos_now_2 assigns0
      trail0 qhead ) as H_order_select_sift_inv.
  bind_fact ( Zlength sift_heap_now_2 = size ) as H_Zlength.
  bind_fact ( 0 <= Znth (child - 0) sift_heap_now_2 0 ) as H_Znth.
  bind_fact ( Znth (child - 0) sift_heap_now_2 0 < n ) as H_Znth_2.
  bind_fact ( 0 <= Znth (child + 1 - 0) sift_heap_now_2 0 ) as H_Znth_3.
  bind_fact ( Znth (child + 1 - 0) sift_heap_now_2 0 < n ) as H_Znth_4.
  bind_fact ( Znth (child - 0) sift_heap_now_2 0 <> Znth (child + 1 - 0) sift_heap_now_2 0 ) as H_Znth_5.
  msat_order_select_offsets_all_p6 child (child + 1) sift_heap_now_2.
  set (heap' :=
    replace_Znth i (Znth child sift_heap_now_2 0) sift_heap_now_2).
  set (orderpos' := replace_Znth (Znth i heap' 0) i sift_orderpos_now_2).
  assert (Hmoved : Znth i heap' 0 = Znth child sift_heap_now_2 0).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hsift :
    order_select_sift_inv n next x child heap0 sift_heap_before_2
      heap' orderpos' assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved.
    apply order_select_sift_inv_step__order_select.
    - exact H_order_select_sift_inv.
    - lia.
    - lia. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now_2).
  { subst heap'. rewrite Zlength_replace_Znth. reflexivity. }
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n orderpos').
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength sift_heap_now_2) heap').
  sep_apply
    (double_array_missing2_refold__vecp_remove activity_ptr
      (Znth child sift_heap_now_2 0)
      (Znth (child + 1) sift_heap_now_2 0)
      n activity0 (conj H_Znth H_Znth_2) (conj H_Znth_3 H_Znth_4) H_Znth_5).
  msat_order_select_offsets_all_p6 (2 * child + 1) (2 * child + 1 + 1) heap'.
  destruct (Z_le_gt_dec size (2 * child + 1)) as [Hnone | Hleft].
  - assert (Hleft_past : Znth (2 * child + 1) heap' 0 = 0).
    { apply Znth_zero_past_end__order_select.
      rewrite Hheaplen, H_Zlength. lia. }
    assert (Hright_past : Znth ((2 * child + 1) + 1) heap' 0 = 0).
    { apply Znth_zero_past_end__order_select.
      rewrite Hheaplen, H_Zlength. lia. }
    msat_order_select_orp_left_p6.
    msat_order_select_orp_left_p6.
    Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
      heap' orderpos'.
    rewrite <- Hheaplen.
    entailer_with ltac:(lia);
      rewrite ?Hleft_past, ?Hright_past;
      lia.
  - destruct (Z_le_gt_dec size ((2 * child + 1) + 1))
      as [Honly_left | Hboth].
    + assert (Hleft_range :
        0 <= Znth (2 * child + 1) heap' 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia. }
      assert (Hright_past : Znth ((2 * child + 1) + 1) heap' 0 = 0).
      { apply Znth_zero_past_end__order_select.
        subst heap'. rewrite Zlength_replace_Znth. lia. }
      msat_order_select_orp_left_p6.
      msat_order_select_orp_right_p6.
      Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
        heap' orderpos'.
      rewrite <- Hheaplen.
      msat_order_select_offsets_goal_p6 (2 * child + 1) (2 * child + 1 + 1) heap'.
      entailer_with ltac:(lia).
      sep_apply_l_atomic
        (DoubleArray.seg_split_to_missing_i activity_ptr 0
          (Znth (2 * child + 1) heap' 0) n activity0 msat_fp64_zero).
      * dump_pre_spatial. exact Hleft_range.
      * unfold StoreDoubleAsElement.storeA, double_Znth.
        replace (Znth (2 * child + 1) heap' 0 - 0)
          with (Znth (2 * child + 1) heap' 0) by lia.
        entailer_with ltac:(lia).
    + assert (Hleft_range :
        0 <= Znth (2 * child + 1) heap' 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia. }
      assert (Hright_range :
        0 <= Znth ((2 * child + 1) + 1) heap' 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia. }
      assert (Hchildren_neq :
        Znth (2 * child + 1) heap' 0 <>
        Znth ((2 * child + 1) + 1) heap' 0).
      { eapply order_select_sift_inv_cells_neq__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia.
        - lia.
        - lia. }
      msat_order_select_orp_right_p6.
      Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
        heap' orderpos'.
      rewrite <- Hheaplen.
      msat_order_select_offsets_goal_p6 (2 * child + 1) (2 * child + 1 + 1) heap'.
      entailer_with ltac:(lia).
      sep_apply
        (double_array_seg_split_to_missing2__order_select activity_ptr
          (Znth (2 * child + 1) heap' 0)
          (Znth ((2 * child + 1) + 1) heap' 0)
          n activity0 Hleft_range Hright_range Hchildren_neq).
      unfold double_Znth.
      replace (Znth (2 * child + 1) heap' 0 - 0)
        with (Znth (2 * child + 1) heap' 0) by lia.
      replace (Znth (2 * child + 1 + 1) heap' 0 - 0)
        with (Znth (2 * child + 1 + 1) heap' 0) by lia.
      msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_select_entail_wit_11_2 : order_select_entail_wit_11_2.
Proof.
  Unfold.
  intros.
  poly_store_unfold; Rename pre_process_pure.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before_2 sift_heap_now_2 sift_orderpos_now_2 assigns0
      trail0 qhead ) as H_order_select_sift_inv.
  bind_fact ( Zlength sift_heap_now_2 = size ) as H_Zlength.
  bind_fact ( 0 <= Znth (child - 0) sift_heap_now_2 0 ) as H_Znth.
  bind_fact ( Znth (child - 0) sift_heap_now_2 0 < n ) as H_Znth_2.
  bind_fact ( 0 <= Znth (child + 1 - 0) sift_heap_now_2 0 ) as H_Znth_3.
  bind_fact ( Znth (child + 1 - 0) sift_heap_now_2 0 < n ) as H_Znth_4.
  bind_fact ( Znth (child - 0) sift_heap_now_2 0 <> Znth (child + 1 - 0) sift_heap_now_2 0 ) as H_Znth_5.
  msat_order_select_offsets_all_p6 child (child + 1) sift_heap_now_2.
  set (heap' :=
    replace_Znth i (Znth (child + 1) sift_heap_now_2 0) sift_heap_now_2).
  set (orderpos' := replace_Znth (Znth i heap' 0) i sift_orderpos_now_2).
  assert (Hmoved : Znth i heap' 0 = Znth (child + 1) sift_heap_now_2 0).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hsift :
    order_select_sift_inv n next x (child + 1) heap0 sift_heap_before_2
      heap' orderpos' assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved.
    apply order_select_sift_inv_step__order_select.
    - exact H_order_select_sift_inv.
    - lia.
    - lia. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now_2).
  { subst heap'. rewrite Zlength_replace_Znth. reflexivity. }
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n orderpos').
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength sift_heap_now_2) heap').
  sep_apply
    (double_array_missing2_refold__vecp_remove activity_ptr
      (Znth child sift_heap_now_2 0)
      (Znth (child + 1) sift_heap_now_2 0)
      n activity0 (conj H_Znth H_Znth_2) (conj H_Znth_3 H_Znth_4) H_Znth_5).
  msat_order_select_offsets_all_p6 (2 * (child + 1) + 1) (2 * (child + 1) + 1 + 1) heap'.
  destruct (Z_le_gt_dec size (2 * (child + 1) + 1)) as [Hnone | Hleft].
  - assert (Hleft_past : Znth (2 * (child + 1) + 1) heap' 0 = 0).
    { apply Znth_zero_past_end__order_select.
      rewrite Hheaplen, H_Zlength. lia. }
    assert (Hright_past :
      Znth ((2 * (child + 1) + 1) + 1) heap' 0 = 0).
    { apply Znth_zero_past_end__order_select.
      rewrite Hheaplen, H_Zlength. lia. }
    msat_order_select_orp_left_p6.
    msat_order_select_orp_left_p6.
    Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
      heap' orderpos'.
    rewrite <- Hheaplen.
    entailer_with ltac:(lia);
      rewrite ?Hleft_past, ?Hright_past;
      lia.
  - destruct (Z_le_gt_dec size ((2 * (child + 1) + 1) + 1))
      as [Honly_left | Hboth].
    + assert (Hleft_range :
        0 <= Znth (2 * (child + 1) + 1) heap' 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia. }
      assert (Hright_past :
        Znth ((2 * (child + 1) + 1) + 1) heap' 0 = 0).
      { apply Znth_zero_past_end__order_select.
        subst heap'. rewrite Zlength_replace_Znth. lia. }
      msat_order_select_orp_left_p6.
      msat_order_select_orp_right_p6.
      Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
        heap' orderpos'.
      rewrite <- Hheaplen.
      msat_order_select_offsets_goal_p6 (2 * (child + 1) + 1) (2 * (child + 1) + 1 + 1) heap'.
      entailer_with ltac:(lia).
      sep_apply_l_atomic
        (DoubleArray.seg_split_to_missing_i activity_ptr 0
          (Znth (2 * (child + 1) + 1) heap' 0) n activity0
          msat_fp64_zero).
      * dump_pre_spatial. exact Hleft_range.
      * unfold StoreDoubleAsElement.storeA, double_Znth.
        replace (Znth (2 * (child + 1) + 1) heap' 0 - 0)
          with (Znth (2 * (child + 1) + 1) heap' 0) by lia.
        entailer_with ltac:(lia).
    + assert (Hleft_range :
        0 <= Znth (2 * (child + 1) + 1) heap' 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia. }
      assert (Hright_range :
        0 <= Znth ((2 * (child + 1) + 1) + 1) heap' 0 < n).
      { eapply order_select_sift_inv_cell_range__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia. }
      assert (Hchildren_neq :
        Znth (2 * (child + 1) + 1) heap' 0 <>
        Znth ((2 * (child + 1) + 1) + 1) heap' 0).
      { eapply order_select_sift_inv_cells_neq__order_select.
        - exact Hsift.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - subst heap'. rewrite Zlength_replace_Znth. lia.
        - lia.
        - lia.
        - lia. }
      msat_order_select_orp_right_p6.
      Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
        heap' orderpos'.
      rewrite <- Hheaplen.
      msat_order_select_offsets_goal_p6 (2 * (child + 1) + 1) (2 * (child + 1) + 1 + 1) heap'.
      entailer_with ltac:(lia).
      sep_apply
        (double_array_seg_split_to_missing2__order_select activity_ptr
          (Znth (2 * (child + 1) + 1) heap' 0)
          (Znth ((2 * (child + 1) + 1) + 1) heap' 0)
          n activity0 Hleft_range Hright_range Hchildren_neq).
      unfold double_Znth.
      replace (Znth (2 * (child + 1) + 1) heap' 0 - 0)
        with (Znth (2 * (child + 1) + 1) heap' 0) by lia.
      replace (Znth (2 * (child + 1) + 1 + 1) heap' 0 - 0)
        with (Znth (2 * (child + 1) + 1 + 1) heap' 0) by lia.
      msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_select_entail_wit_11_3 : order_select_entail_wit_11_3.
Proof.
  Unfold.
  left; intros; poly_store_unfold; Rename pre_process_pure.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before_2 sift_heap_now_2 sift_orderpos_now_2 assigns0
      trail0 qhead ) as H_order_select_sift_inv.
  set (heap' := replace_Znth i (Znth (child - 0) sift_heap_now_2 0)
    sift_heap_now_2).
  set (orderpos' := replace_Znth (Znth i heap' 0) i
    sift_orderpos_now_2).
  assert (Hmoved : Znth i heap' 0 = Znth child sift_heap_now_2 0).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia.
    replace (child - 0) with child by lia. reflexivity. }
  assert (Hsift : order_select_sift_inv n next x child heap0
    sift_heap_before_2 heap' orderpos' assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved. subst heap'.
    replace (child - 0) with child by lia.
    apply order_select_sift_inv_step__order_select.
    - exact H_order_select_sift_inv.
    - lia.
    - lia. }
  assert (Hleft_past : Znth (2 * child + 1) heap' 0 = 0).
  { apply Znth_zero_past_end__order_select.
    subst heap'. rewrite Zlength_replace_Znth. lia. }
  assert (Hright_past : Znth (2 * child + 1 + 1) heap' 0 = 0).
  { apply Znth_zero_past_end__order_select.
    subst heap'. rewrite Zlength_replace_Znth. lia. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now_2).
  { subst heap'. rewrite Zlength_replace_Znth. reflexivity. }
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n orderpos').
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength sift_heap_now_2) heap').
  Exists sift_seed_shadow_now_2 sift_seed_value_now_2 sift_heap_before_2
    heap' orderpos'.
  rewrite <- Hheaplen.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_select_entail_wit_12_1 : order_select_entail_wit_12_1.
Proof.
  Unfold. intros. Left. Left. Left. poly_store_unfold.
  msat_order_select_sift_capacity_p6 s_pre order_ptr order_cap n next x i heap0
    sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0 qhead
    H_sift Hcap Hroom.
Qed.

Lemma proof_of_order_select_entail_wit_12_2 : order_select_entail_wit_12_2.
Proof.
  Unfold. intros. Left. Left. Right. poly_store_unfold.
  msat_order_select_sift_capacity_p6 s_pre order_ptr order_cap n next_2 x_2 i_2 heap0
    sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0 qhead
    H_sift Hcap Hroom.
Qed.

Lemma proof_of_order_select_entail_wit_12_3 : order_select_entail_wit_12_3.
Proof.
  Unfold. intros. Left. Right.
  msat_order_select_sift_capacity_p6 s_pre order_ptr order_cap n next_2 x_2 i_2 heap0
    sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0 qhead
    H_sift Hcap Hroom.
Qed.

Lemma proof_of_order_select_entail_wit_12_4 : order_select_entail_wit_12_4.
Proof.
  Unfold. intros. Right. poly_store_unfold.
  msat_order_select_sift_capacity_p6 s_pre order_ptr order_cap n next_3 x_3 i_3 heap0
    sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0 qhead
    H_sift Hcap Hroom.
Qed.

Lemma proof_of_order_select_entail_wit_13_1 : order_select_entail_wit_13_1.
Proof.
  msat_order_select_sift_promote_p6 H_Znth H_sift heap' orderpos' false false
    H_Znth_2 H_Znth_3 H_Znth_4 H_Znth_5 H_Znth_6.
Qed.

Lemma proof_of_order_select_entail_wit_13_2 : order_select_entail_wit_13_2.
Proof.
  msat_order_select_sift_promote_p6 H_Znth H_sift heap' orderpos' true true
    H_Znth_2 H_Znth_3 H_Znth_4 H_Znth_5 H_Znth_6.
Qed.

Lemma proof_of_order_select_entail_wit_13_3 : order_select_entail_wit_13_3.
Proof.
  msat_order_select_sift_promote_p6 H_Znth H_sift heap' orderpos' true true
    H_Znth_2 H_Znth_3 H_Znth_4 H_Znth_5 H_Znth_6.
Qed.

Lemma proof_of_order_select_entail_wit_13_4 : order_select_entail_wit_13_4.
Proof.
  msat_order_select_sift_promote_p6 H_Znth H_sift heap' orderpos' true false
    H_Znth_2 H_Znth_3 H_Znth_4 H_Znth_5 H_Znth_6.
Qed.

Lemma proof_of_order_select_entail_wit_13_5 : order_select_entail_wit_13_5.
Proof.
  Unfold.
  left; intros; poly_store_unfold; Rename pre_process_pure.
  bind_fact ( Znth (Znth (0 - 0) heap_now_2 0 - 0) assigns0 0 <> 0 ) as H_Znth.
  bind_fact ( order_select_loop_inv n heap0 heap_now_2 orderpos_now_2 assigns0 trail0 qhead ) as
      H_order_select_loop_inv.
  replace (0 - 0) with 0 in * by lia.
  replace (Znth 0 heap_now_2 0 - 0)
    with (Znth 0 heap_now_2 0) in * by lia.
  assert (Hone : Zlength heap_now_2 = 1) by lia.
  assert (Hloop : order_select_loop_inv n heap0 (@nil Z)
    (replace_Znth (Znth 0 heap_now_2 (-1)) (-1) orderpos_now_2)
    assigns0 trail0 qhead).
  { apply order_select_loop_pop_assigned_empty__order_select.
    - exact H_order_select_loop_inv.
    - exact Hone.
    - rewrite (Znth_indep heap_now_2 0 (-1) 0) by lia.
      exact H_Znth. }
  prop_apply (store_int_range
    (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap).
  Intros_p Hcap_range.
  prop_apply (IntArray.undef_seg_valid order_ptr
    (Zlength (sublist 0 (retval_2 - 1) heap_now_2)) order_cap).
  Intros_p Hcap_room.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth (Znth 0 heap_now_2 0) (-1) orderpos_now_2)).
  rewrite (Znth_indep heap_now_2 0 0 (-1)) by lia.
  Exists seed_shadow_now_2 seed_value_now_2 (@nil Z)
    (replace_Znth (Znth 0 heap_now_2 (-1)) (-1) orderpos_now_2).
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  rewrite Zsublist_nil by lia.
  entailer_with ltac:(lia);
    try rewrite Zlength_nil;
    csimpl; entailer_with ltac:(lia).
Qed.

(* ===== order_select return wits (2 proofs) ===== *)
Lemma proof_of_order_select_return_wit_1 : order_select_return_wit_1.
Proof.
  Unfold.
  left; intros; poly_store_unfold; Rename pre_process_pure.
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  assert (Hempty : heap_now = @nil Z).
  { apply Zlength_nil_inv. lia. }
  subst heap_now.
  prop_apply (store_int_range
    (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap).
  Intros_p Hcap_range.
  prop_apply (IntArray.undef_seg_valid order_ptr 0 order_cap).
  Intros_p Hcap_room.
  Exists seed_shadow_now seed_value_now (@nil Z) orderpos_now.
  unfold veci_rep, veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  pose proof (order_select_loop_empty_post__order_select
    n heap0 orderpos_now assigns0 trail0 qhead H_order_select_loop_inv) as Hpost.
  Exists order_ptr.
  entailer_with ltac:(lia).
  csimpl. msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_order_select_return_wit_2 : order_select_return_wit_2.
Proof.
  Unfold.
  left; intros; poly_store_unfold; Rename pre_process_pure.
  bind_fact ( Znth (next - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0
      qhead ) as H_order_select_sift_inv.
  replace (next - 0) with next in * by lia.
  set (heap' := replace_Znth i x sift_heap_now).
  set (orderpos' := replace_Znth (Znth i heap' 0) i sift_orderpos_now).
  assert (Hmoved : Znth i heap' 0 = x).
  { subst heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hpost : order_select_post n next heap0 heap' orderpos'
    assigns0 trail0 qhead).
  { subst orderpos'. rewrite Hmoved.
    eapply order_select_sift_close_unassigned_post__order_select
      with (before := sift_heap_before).
    - exact H_order_select_sift_inv.
    - exact H_Znth. }
  assert (Hheaplen : Zlength heap' = Zlength sift_heap_now).
  { subst heap'. rewrite Zlength_replace_Znth. reflexivity. }
  prop_apply (store_int_range
    (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap).
  Intros_p Hcap_range.
  prop_apply (IntArray.undef_seg_valid
    order_ptr (Zlength sift_heap_now) order_cap).
  Intros_p Hcap_room.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n orderpos').
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength sift_heap_now) heap').
  Exists sift_seed_shadow_now sift_seed_value_now heap' orderpos'.
  unfold veci_rep, veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists order_ptr.
  rewrite <- Hheaplen.
  entailer_with ltac:(lia).
  csimpl. msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== order_unassigned return wits (2 proofs) ===== *)
Lemma proof_of_order_unassigned_return_wit_1 : order_unassigned_return_wit_1.
Proof.
  (* Same re-spelling as act_var_bump_return_wit_1: order_update_post's first
     argument is now [Zlength activity0] (the remaining length equation supplies the rewrite).  Match the
     new spelling, rewrite back to [n] in BOTH the hypothesis and the goal, then
     the original script is unchanged. *)
  Unfold; left; intros.
  bind_fact ( order_update_post (Zlength activity0) v_pre (heap0 +:: v_pre) (replace_Znth v_pre (Zlength heap0)
      orderpos0) heap1_2 orderpos1_2 ) as H_order_update_post.
  bind_fact ( Zlength activity0 = n ) as H_Zlength_act.
  rewrite H_Zlength_act in H_order_update_post.
  (* the SPATIAL atoms moved too -- IntArray.seg/DoubleArray.seg are now keyed on
     [Zlength activity0] rather than [n], so the entailer cannot cancel them
     against the RHS until the goal is normalised as well. *)
  rewrite H_Zlength_act.
  bind_fact ( Zlength (heap0 +:: v_pre) <= cap_prime ) as H_Zlength.
  bind_fact ( Znth (v_pre - 0) orderpos0 0 = -1 ) as H_Znth.
  bind_fact ( order_unassigned_pre n v_pre order_cap heap0 orderpos0 ) as H_order_unassigned_pre.
  assert (Hvpos : 0 <= v_pre < Zlength orderpos0).
  { pose proof (heap_wf_orderpos_length n
      {| mh_heap := heap0; mh_orderpos := orderpos0 |}
      (proj1 H_order_unassigned_pre)) as E.
    cbn [mh_orderpos] in E. lia. }
  assert (Hmissing : Znth v_pre orderpos0 (-1) = -1).
  { replace (v_pre - 0) with v_pre in H_Znth by lia.
    rewrite (Znth_indep orderpos0 v_pre (-1) 0) by exact Hvpos.
    exact H_Znth. }
  assert (Hpost : order_unassigned_post n v_pre order_cap heap0 orderpos0
                    cap_prime heap1_2 orderpos1_2).
  { eapply order_unassigned_post_after_update__vecp_remove.
    - exact H_order_unassigned_pre.
    - exact Hmissing.
    - lia.
    - exact H_Zlength.
    - exact H_order_update_post. }
  Exists cap_prime heap1_2 orderpos1_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_unassigned_return_wit_2 : order_unassigned_return_wit_2.
Proof.
  Unfold; left; intros.
  msat_order_unassigned_noop_return order_ptr.
Qed.

(* ===== order_update entail wits (5 proofs) ===== *)
Lemma proof_of_order_update_entail_wit_1 : order_update_entail_wit_1.
Proof.
  aggressive_pre_process;
    bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre;
    bind_fact ( 0 <= Znth v_pre orderpos0 (-1) ) as H_Znth;
    bind_fact ( Znth v_pre orderpos0 (-1) < Zlength heap0 ) as H_Znth_2;
    unfold order_update_pre, order_heap_wf, heap_wf in H_order_update_pre;
    cbn in H_order_update_pre;
    destruct H_order_update_pre as ((Hlen & _) & _);
    replace (v_pre - 0) with v_pre by lia;
    rewrite (Znth_indep orderpos0 v_pre 0 (-1)) by lia.
  - exact H_Znth_2.
  - exact H_Znth.
Qed.

Lemma proof_of_order_update_entail_wit_2 : order_update_entail_wit_2.
Proof.
  aggressive_pre_process.
  all: (bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre);
    (bind_fact ( 0 <= Znth (Znth v_pre orderpos0 (-1)) heap0 0 ) as H_Znth);
    (bind_fact ( Znth (Znth v_pre orderpos0 (-1)) heap0 0 < n ) as H_Znth_2);
    (unfold order_update_pre, order_heap_wf, heap_wf in H_order_update_pre);
    (cbn in H_order_update_pre);
    (destruct H_order_update_pre as ((Hlen & _) & _));
    (replace (v_pre - 0) with v_pre by lia);
    (rewrite (Znth_indep orderpos0 v_pre 0 (-1)) by lia);
    (replace (Znth v_pre orderpos0 (-1) - 0)
         with (Znth v_pre orderpos0 (-1)) by lia).
  - exact H_Znth_2.
  - exact H_Znth.
Qed.

Lemma proof_of_order_update_entail_wit_3 : order_update_entail_wit_3.
Proof.
  aggressive_pre_process.
  (* Recover the activity length required by the RHS from its owned array
     segment; the spatial atom supplies this fact. *)
  prop_apply (DoubleArray.seg_Zlength activity_ptr 0 n activity0).
  Intros_p Hactlen.
  bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre.
  bind_fact ( 0 <= Znth (Znth v_pre orderpos0 (-1)) heap0 0 ) as H_Znth.
  bind_fact ( Znth (Znth v_pre orderpos0 (-1)) heap0 0 < n ) as H_Znth_2.
  pose proof H_order_update_pre as Hpre.
  unfold order_update_pre, order_heap_wf, heap_wf in Hpre.
  cbn in Hpre.
  destruct Hpre as ((Hoplen & _) & _).
  replace (v_pre - 0) with v_pre in * by lia.
  assert (Hiind : Znth v_pre orderpos0 0 = Znth v_pre orderpos0 (-1)).
  { apply Znth_indep. lia. }
  rewrite Hiind in *.
  replace (Znth v_pre orderpos0 (-1) - 0)
    with (Znth v_pre orderpos0 (-1)) in * by lia.
  assert (Hxind :
    Znth (Znth v_pre orderpos0 (-1)) heap0 0 =
    Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)).
  { apply Znth_indep. lia. }
  rewrite Hxind in *.
  pose proof (order_update_loop_inv_init n v_pre
    (Znth v_pre orderpos0 (-1))
    (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
    heap0 orderpos0 H_order_update_pre eq_refl eq_refl) as Hinit.
  destruct Hinit as (Hirange & Hxv & Hinv).
  destruct (Z.eq_dec (Znth v_pre orderpos0 (-1)) 0) as [Hi0|Hi0].
  - assert (Hparent0 :
      (Znth v_pre orderpos0 (-1) - 1) ÷ 2 = 0).
    { rewrite Hi0. reflexivity. }
    assert (Hzeroind : Znth 0 heap0 0 = Znth 0 heap0 (-1)).
    { apply Znth_indep. rewrite Hi0 in Hirange. lia. }
    assert (Hzero_lo : 0 <= Znth 0 heap0 (-1)).
    { replace (Znth 0 heap0 (-1))
        with (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)).
      - exact H_Znth.
      - rewrite Hi0. reflexivity. }
    assert (Hzero_hi : Znth 0 heap0 (-1) < n).
    { replace (Znth 0 heap0 (-1))
        with (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)).
      - exact H_Znth_2.
      - rewrite Hi0. reflexivity. }
    Left. subst retval.
    Exists heap0 orderpos0.
    entailer_with ltac:(lia);
      try rewrite Hparent0;
      try replace (0 - 0) with 0 by lia;
      try rewrite Hzeroind;
      try lia;
      try exact Hzero_lo;
      try exact Hzero_hi;
      try exact H_Znth;
      try exact H_Znth_2.
  - assert (Hparent_lo :
      0 <= (Znth v_pre orderpos0 (-1) - 1) ÷ 2).
    { rewrite zdiv_equiv by lia. apply Z.div_pos; lia. }
    assert (Hparent_lt_i :
      (Znth v_pre orderpos0 (-1) - 1) ÷ 2 <
      Znth v_pre orderpos0 (-1)).
    { rewrite zdiv_equiv by lia. apply Z.div_lt_upper_bound; lia. }
    pose proof Hinv as Hinv_copy.
    unfold order_update_loop_inv in Hinv_copy.
    destruct Hinv_copy as (_ & _ & Hhole).
    assert (Hparent_range :
      0 <= Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1) < n).
    { apply (order_heap_one_hole_cell_range n heap0
        (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
        (Znth v_pre orderpos0 (-1)) heap0 orderpos0
        ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) Hhole); lia. }
    assert (Hparent_ind :
      Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 0 =
      Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1)).
    { apply Znth_indep. lia. }
    assert (Hx_ne_parent :
      Znth (Znth v_pre orderpos0 (-1)) heap0 (-1) <>
      Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1)).
    { apply (order_heap_one_hole_x_neq_cell__vecp_remove n heap0
        (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
        (Znth v_pre orderpos0 (-1)) heap0 orderpos0
        ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) Hhole); lia. }
    Right. subst retval.
    Exists heap0 orderpos0.
    entailer_with ltac:(lia);
      try replace
        ((Znth v_pre orderpos0 (-1) - 1) ÷ 2 - 0)
        with ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) by lia;
      try rewrite Hparent_ind;
      try lia;
      try exact Hparent_range;
      try exact Hx_ne_parent.
    sep_apply (double_array_seg_split_to_missing2__order_select
      activity_ptr
      (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1))
      (Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1))
      n activity0 (conj H_Znth H_Znth_2) Hparent_range Hx_ne_parent).
    replace (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1) - 0)
      with (Znth (Znth v_pre orderpos0 (-1)) heap0 (-1)) by lia.
    replace (Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1) - 0)
      with (Znth ((Znth v_pre orderpos0 (-1) - 1) ÷ 2) heap0 (-1)) by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_update_entail_wit_4 : order_update_entail_wit_4.
Proof.
  aggressive_pre_process;
    bind_fact ( parent = (i - 1) ÷ 2 ) as H_parent;
    bind_fact ( 0 <= Znth (parent - 0) heap_now 0 ) as H_Znth;
    bind_fact ( Znth (parent - 0) heap_now 0 < n ) as H_Znth_2;
    try rewrite Znth_replace_Znth_Same by lia;
    try lia;
    rewrite <- H_parent.
  - exact H_Znth_2.
  - exact H_Znth.
Qed.

Lemma proof_of_order_update_entail_wit_5 : order_update_entail_wit_5.
Proof.
  Unfold.
  (* Introduce the complete telescope, then select the two facts this proof
     uses by their statements so changes to the With binders preserve the
     intended hypotheses. *)
  intros.
  assert (Hparent_def : parent = (i - 1) ÷ 2) by assumption.
  assert (Hactivity_len : Zlength activity0 = n) by assumption.
  replace (x - 0) with x in * by lia.
  replace (parent - 0) with parent in * by lia.
  replace (Znth parent heap_now_2 0 - 0)
    with (Znth parent heap_now_2 0) in * by lia.
  set (y := Znth parent heap_now_2 0).
  set (heap' := replace_Znth i y heap_now_2).
  set (pos' := replace_Znth y i orderpos_now_2).
  assert (Hparent_lt : parent < i).
  { rewrite Hparent_def. apply Z.quot_lt_upper_bound; lia. }
  assert (Hparent_ne : parent <> i) by lia.
  assert (Hstep : order_update_loop_inv n v_pre heap0 x parent heap' pos').
  { subst heap' pos' y.
    apply order_update_loop_inv_step__vecp_remove; try assumption; lia. }
  assert (Hlen' : Zlength heap' = Zlength heap_now_2).
  { unfold heap'. apply Zlength_replace_Znth. }
  assert (Hy : 0 <= y < n) by (unfold y; lia).
  assert (Hxy : x <> y) by (unfold y; lia).
  assert (Hxrange : 0 <= x < n) by lia.
  assert (Hati : Znth i heap' 0 = y).
  { unfold heap'. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hposarr :
    replace_Znth
      (Znth i (replace_Znth i (Znth parent heap_now_2 0) heap_now_2) 0)
      i orderpos_now_2 = pos').
  { unfold pos', y. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hheaparr :
    replace_Znth i (Znth parent heap_now_2 0) heap_now_2 = heap')
    by reflexivity.
  fold heap'.
  rewrite Hati.
  fold pos'.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n pos').
  sep_apply_l_atomic
    (IntArray.full_to_seg order_ptr (Zlength heap_now_2) heap').
  sep_apply_l_atomic (double_array_missing2_refold__vecp_remove
    activity_ptr x y n activity0 Hxrange Hy Hxy).
  set (gp := (parent - 1) ÷ 2).
  replace (gp - 0) with gp in * by lia.
  destruct (Z.eq_dec parent 0) as [Hparent_zero|Hparent_nonzero].
  - assert (Hgp0 : gp = 0)
      by (unfold gp; rewrite Hparent_zero; reflexivity).
    assert (Hlookup0 : Znth 0 heap' 0 = y).
    { unfold heap'.
      rewrite (Znth_replace_Znth_Diff 0 heap_now_2 i 0 y) by lia.
      unfold y. now rewrite Hparent_zero. }
    Left. Exists heap' pos'.
    rewrite Hlen'.
    entailer_with ltac:(lia); try rewrite Hgp0; try rewrite Hlookup0; try lia.
  - assert (Hgp_lo : 0 <= gp).
    { unfold gp. rewrite zdiv_equiv by lia. apply Z.div_pos; lia. }
    assert (Hgp_lt : gp < parent).
    { unfold gp. rewrite zdiv_equiv by lia.
      apply Z.div_lt_upper_bound; lia. }
    assert (Hgp_idx : 0 <= gp < Zlength heap').
    { rewrite Hlen'. lia. }
    pose proof Hstep as Hstep'.
    unfold order_update_loop_inv in Hstep'.
    destruct Hstep' as (_ & _ & Hhole).
    assert (Hgpvalm1 : 0 <= Znth gp heap' (-1) < n).
    { apply (order_heap_one_hole_cell_range
        n heap0 x parent heap' pos' gp Hhole); lia. }
    assert (Hgpind : Znth gp heap' 0 = Znth gp heap' (-1)).
    { apply Znth_indep. exact Hgp_idx. }
    assert (Hgpval0 : 0 <= Znth gp heap' 0 < n).
    { rewrite Hgpind. exact Hgpvalm1. }
    assert (Hxgp0 : x <> Znth gp heap' 0).
    { rewrite Hgpind.
      apply (order_heap_one_hole_saved_neq_cell__vecp_remove
        n heap0 x parent heap' pos' gp Hhole); lia. }
    sep_apply_l_atomic (double_array_missing2_focus__vecp_remove
      activity_ptr x (Znth gp heap' 0) n activity0
      Hactivity_len Hxrange Hgpval0 Hxgp0).
    Right. Exists heap' pos'.
    rewrite Hlen'.
    replace (Znth gp heap' 0 - 0) with (Znth gp heap' 0) by lia.
    entailer_with ltac:(lia); try lia.
Qed.

(* ===== order_update return wits (2 proofs) ===== *)
Lemma proof_of_order_update_return_wit_1 : order_update_return_wit_1.
Proof.
  Unfold; left; intros.
  bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre.
  bind_fact ( order_update_loop_inv n v_pre heap0 x i heap_now orderpos_now ) as H_order_update_loop_inv.
  pose proof (order_update_close_post__vecp_remove
    n v_pre heap0 orderpos0 x i heap_now orderpos_now H_order_update_pre H_order_update_loop_inv) as Hpost.
  prop_apply (store_int_range
    (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap).
  Intros_p Hcap_range.
  prop_apply (IntArray.undef_seg_valid
    order_ptr (Zlength heap_now) order_cap).
  Intros_p Hcap_room.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth x i orderpos_now)).
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength heap_now) (replace_Znth i x heap_now)).
  Exists (replace_Znth i x heap_now) (replace_Znth x i orderpos_now).
  unfold veci_rep, veci_rep_at,
    veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists order_ptr.
  rewrite Zlength_replace_Znth.
  entailer_with ltac:(int_auto).
  csimpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_update_return_wit_2 : order_update_return_wit_2.
Proof.
  Unfold; left; intros.
  bind_fact ( order_update_pre n v_pre heap0 orderpos0 ) as H_order_update_pre.
  bind_fact ( order_update_loop_inv n v_pre heap0 x i heap_now orderpos_now ) as H_order_update_loop_inv.
  bind_fact ( 0 <= x ) as H_x.
  bind_fact ( x < n ) as H_x_2.
  bind_fact ( 0 <= Znth (parent - 0) heap_now 0 ) as H_Znth.
  bind_fact ( Znth (parent - 0) heap_now 0 < n ) as H_Znth_2.
  bind_fact ( x <> Znth (parent - 0) heap_now 0 ) as H_x_3.
  replace (x - 0) with x in * by lia.
  replace (parent - 0) with parent in * by lia.
  replace (Znth parent heap_now 0 - 0)
    with (Znth parent heap_now 0) in * by lia.
  pose proof (order_update_close_post__vecp_remove
    n v_pre heap0 orderpos0 x i heap_now orderpos_now H_order_update_pre H_order_update_loop_inv) as Hpost.
  prop_apply (store_int_range
    (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap).
  Intros_p Hcap_range.
  prop_apply (IntArray.undef_seg_valid
    order_ptr (Zlength heap_now) order_cap).
  Intros_p Hcap_room.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth x i orderpos_now)).
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength heap_now) (replace_Znth i x heap_now)).
  sep_apply_l_atomic (double_array_missing2_refold__vecp_remove
    activity_ptr x (Znth parent heap_now 0) n activity0
    (conj H_x H_x_2) (conj H_Znth H_Znth_2) H_x_3).
  Exists (replace_Znth i x heap_now) (replace_Znth x i orderpos_now).
  unfold veci_rep, veci_rep_at,
    veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists order_ptr.
  rewrite Zlength_replace_Znth.
  entailer_with ltac:(int_auto).
  csimpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== order_update which_implies wits (1 proofs) ===== *)
Lemma proof_of_order_update_which_implies_wit_1 : order_update_which_implies_wit_1.
Proof.
  Unfold; left; intros.
  bind_fact ( order_update_pre n v heap0 orderpos0 ) as H_order_update_pre.
  pose proof H_order_update_pre as Hpre.
  unfold order_update_pre, order_heap_wf in Hpre.
  destruct Hpre as (Hwf & Hv & Hpresent).
  destruct (heap_wf_lookup n
    {| mh_heap := heap0; mh_orderpos := orderpos0 |}
    v Hwf Hv Hpresent) as [Hidx Hback].
  assert (Hback0 : Znth (Znth v orderpos0 (-1)) heap0 0 = v).
  { rewrite (Znth_indep heap0 (Znth v orderpos0 (-1)) 0 (-1))
      by exact Hidx.
    exact Hback. }
  assert (Hval0 : 0 <= Znth (Znth v orderpos0 (-1)) heap0 0 < n).
  { rewrite Hback0. exact Hv. }
  msat_manual_entailer_with ltac:(int_auto).
Qed.

(* ===== solver_analyze partial_solve wits (12 proofs) ===== *)
Lemma proof_of_solver_analyze_partial_solve_wit_59_learnt_pure : solver_analyze_partial_solve_wit_59_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_59_learnt_pure, solver_analyze_open_at.
  msat_analyze_clause_word_range_p6 anz_n j clause_words2 1.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_60_learnt_pure : solver_analyze_partial_solve_wit_60_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_60_learnt_pure, solver_analyze_open_at.
  msat_analyze_clause_word_range_p6 anz_n j clause_words2 1.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_62_learnt_pure : solver_analyze_partial_solve_wit_62_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_62_learnt_pure, solver_analyze_open_at.
  Unfold; right; intros.
  msat_analyze_close_clause_word_range_via_entailer anz_n j clause_words2.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_63_learnt_pure : solver_analyze_partial_solve_wit_63_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_63_learnt_pure, solver_analyze_open_at.
  Unfold; right; intros.
  msat_analyze_close_clause_word_range_via_entailer anz_n j clause_words2.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_65_learnt_pure : solver_analyze_partial_solve_wit_65_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_65_learnt_pure, solver_analyze_open_at.
  msat_analyze_clause_word_range_p6 anz_n j clause_words2 0.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_66_learnt_pure : solver_analyze_partial_solve_wit_66_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_66_learnt_pure, solver_analyze_open_at.
  msat_analyze_clause_word_range_p6 anz_n j clause_words2 0.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_72_learnt_pure : solver_analyze_partial_solve_wit_72_learnt_pure.
Proof.
  Unfold; right; intros.
  msat_analyze_close_clause_word_range_via_entailer anz_n j clause_words2.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_73_learnt_pure : solver_analyze_partial_solve_wit_73_learnt_pure.
Proof.
  msat_analyze_clause_word_range_p6 anz_n j clause_words2 1.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_74_learnt_pure : solver_analyze_partial_solve_wit_74_learnt_pure.
Proof.
  Unfold; right; intros.
  msat_analyze_close_clause_word_range_via_entailer anz_n j clause_words2.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_75_learnt_pure : solver_analyze_partial_solve_wit_75_learnt_pure.
Proof.
  msat_analyze_clause_word_range_p6 anz_n j clause_words2 0.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_80_learnt_pure : solver_analyze_partial_solve_wit_80_learnt_pure.
Proof.
  msat_analyze_clause_word_range_p6 anz_n j clause_words2 0.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_81_learnt_pure : solver_analyze_partial_solve_wit_81_learnt_pure.
Proof.
  Unfold; right; intros.
  msat_analyze_close_clause_word_range_via_entailer anz_n j clause_words2.
Qed.

(* ===== solver_analyze which_implies wits (11 proofs) ===== *)
Lemma proof_of_solver_analyze_which_implies_wit_29 : solver_analyze_which_implies_wit_29.
Proof.
  Unfold.
  right.
  intros focus K A_arr F n Mresolution words_before p PreH1.
  bind_fact ( analyze_resolution_exit n F A_arr K Mresolution focus p words_before ) as H_analyze_resolution_exit.
  unfold analyze_resolution_exit in H_analyze_resolution_exit.
  destruct H_analyze_resolution_exit as (_ & Hlen & _).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_30 : solver_analyze_which_implies_wit_30.
Proof.
  Unfold.
  right.
  intros words_before cap_before q p PreH1 PreH2 PreH3.
  assert (Hr : 0 <= 0 < Zlength words_before) by lia.
  pose proof (IntArray.missing_i_merge_to_seg q 0 0
    (Zlength words_before) (lit_neg_c p) words_before Hr) as Hmerge.
  generalize Hmerge.
  clear Hmerge.
  replace (q + 0 * sizeof(INT)) with q by lia.
  intros Hmerge.
  sep_apply Hmerge.
  rewrite Zlength_replace_Znth.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_31 : solver_analyze_which_implies_wit_31.
Proof.
  Unfold.
  right.
  intros anz_wl n Mresolution cap_before words_uip tags trail levels reasons
    s lits learnt PreH1 PreH2.
  subst n.
  assert (Htagged :
    veci_rep &((s) # "solver_t" ->ₛ "tagged")
      (ms_tagged Mresolution) (ms_tagged_cap Mresolution) |--
    “ 0 <= Zlength (ms_tagged Mresolution) <= ms_tagged_cap Mresolution /\
      0 < ms_tagged_cap Mresolution <= INT_MAX ” &&
    veci_rep &((s) # "solver_t" ->ₛ "tagged")
      (ms_tagged Mresolution) (ms_tagged_cap Mresolution)).
  { unfold veci_rep. Intros backing. Exists backing.
    unfold veci_rep_at. entailer_with lia. }
  assert (Hstack :
    veci_rep &((s) # "solver_t" ->ₛ "stack")
      (ms_stack Mresolution) (ms_stack_cap Mresolution) |--
    “ 0 <= Zlength (ms_stack Mresolution) <= ms_stack_cap Mresolution /\
      0 < ms_stack_cap Mresolution <= INT_MAX ” &&
    veci_rep &((s) # "solver_t" ->ₛ "stack")
      (ms_stack Mresolution) (ms_stack_cap Mresolution)).
  { unfold veci_rep. Intros backing. Exists backing.
    unfold veci_rep_at. entailer_with lia. }
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at, solver_vecs_rep,
    solver_ptrs_rep, solver_var_arrays_rep.
  Intros act asg opos.
  sep_apply peel_scalars_size.
  sep_apply Htagged.
  sep_apply Hstack.
  Exists act asg opos.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_32 : solver_analyze_which_implies_wit_32.
Proof.
  Unfold.
  right.
  intros n words_uip i PreH1 PreH2 PreH3.
  bind_fact ( Forall (lit_wf_c n) words_uip ) as H_Forall.
  bind_fact ( 0 <= i ) as H_i.
  bind_fact ( i < Zlength words_uip ) as H_i_2.
  pose proof (Forall_Znth_elim Z (lit_wf_c n) words_uip 0 i
    H_Forall (conj H_i H_i_2)) as Hlit.
  pose proof (lit_var_c_in_range n (Znth i words_uip 0) Hlit) as Hrange.
  replace (i - 0) with i by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_33 : solver_analyze_which_implies_wit_33.
Proof.
  aggressive_pre_process.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mmin anz_focus ) as H_analysis_cancel_ready.
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mmin anz_focus H_analysis_cancel_ready) as [Hsize _].
  subst anz_n.
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at, solver_vecs_rep,
    solver_ptrs_rep, solver_var_arrays_rep.
  Intros act asg opos.
  sep_apply peel_scalars_size.
  Exists act asg opos.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_34 : solver_analyze_which_implies_wit_34.
Proof.
  Unfold.
  right.
  intros n words_min i PreH1 PreH2 PreH3.
  bind_fact ( Forall (lit_wf_c n) words_min ) as H_Forall.
  bind_fact ( 0 <= i ) as H_i.
  bind_fact ( i < Zlength words_min ) as H_i_2.
  pose proof (Forall_Znth_elim Z (lit_wf_c n) words_min 0 i
    H_Forall (conj H_i H_i_2)) as Hlit.
  pose proof (lit_var_c_in_range n (Znth i words_min 0) Hlit) as Hrange.
  replace (i - 0) with i by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_36 : solver_analyze_which_implies_wit_36.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( msolver_seed_shadow Mmin_done ) as H_msolver_seed_shadow.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mmin_done anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mmin_done) (ms_tagged Mmin_done) ) as H_analysis_tags_exact.
  bind_fact ( analyze_clause_cert anz_n anz_F Mmin_done words_uip ) as H_analyze_clause_cert.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_done words_uip kept_done removed_done words_done T_done i j ) as
      H_analyze_minimize_loop_inv.
  set (stats_upd := replace_Znth 9 max_lits
    (replace_Znth 10 tot_lits (ms_stats Mmin_done))).
  set (Mstats_upd := msolver_with_cla_inc_stats Mmin_done
    (ms_cla_inc Mmin_done) stats_upd).
  assert (Hcore : analysis_core_equiv M0 Mstats_upd).
  { subst Mstats_upd. unfold analysis_core_equiv,
      msolver_with_cla_inc_stats in *.
    cbn in *. tauto. }
  assert (Hseed : msolver_seed_shadow Mstats_upd).
  { subst Mstats_upd. unfold msolver_seed_shadow,
      msolver_with_cla_inc_stats. cbn. exact H_msolver_seed_shadow. }
  assert (Hcancel : analysis_cancel_ready anz_n anz_F anz_A_arr K Mstats_upd anz_focus).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analysis_cancel_ready. }
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mstats_upd)
      (ms_tagged Mstats_upd)).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analysis_tags_exact. }
  assert (Hcert : analyze_clause_cert anz_n anz_F Mstats_upd words_uip).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analyze_clause_cert. }
  assert (Hloop : analyze_minimize_loop_inv anz_n Mstats_upd words_uip
      kept_done removed_done words_done T_done i j).
  { subst Mstats_upd. cbn [msolver_with_cla_inc_stats]. exact H_analyze_minimize_loop_inv. }
  Exists Mstats_upd.
  entailer_with ltac:(lia).
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_literal_stats_frame_at.
  entailer_with ltac:(lia).
  Intros act asg opos.
  entailer_with ltac:(lia).
  assert (Hstats_len : Zlength (ms_stats Mmin_done) = 11).
  { unfold solver_shape in H; tauto. }
  assert (Hznth : forall k, 0 <= k < 9 ->
    Znth k stats_upd 0 = Znth k (ms_stats Mmin_done) 0).
  { unfold stats_upd.
    exact (proj1 (stats_pair_update_slots_p6 (ms_stats Mmin_done)
      max_lits tot_lits Hstats_len)). }
  cancel.
  Exists act asg opos.
  entailer_with ltac:(lia).
  2: {
    assert (Hlen_upd : Zlength stats_upd = 11).
    { unfold stats_upd. rewrite !Zlength_replace_Znth.
      exact Hstats_len. }
    unfold solver_shape in H |- *.
    cbn in *.
    rewrite Hlen_upd.
    tauto. }
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
  cbn.
  assert (Hsc : solver_scalars_rep s Mstats_upd =
      solver_scalars_rep s Mmin_done).
  { unfold solver_scalars_rep, Mstats_upd,
      msolver_with_cla_inc_stats. cbn. reflexivity. }
  rewrite Hsc.
  cancel.
  assert (Hfp : solver_fp_rep s Mstats_upd =
      solver_fp_rep s Mmin_done).
  { unfold solver_fp_rep, Mstats_upd,
      msolver_with_cla_inc_stats. cbn. reflexivity. }
  rewrite Hfp.
  cancel.
  assert (Hvec : solver_vecs_rep s Mstats_upd =
      solver_vecs_rep s Mmin_done).
  { unfold solver_vecs_rep, Mstats_upd,
      msolver_with_cla_inc_stats. cbn. reflexivity. }
  rewrite Hvec.
  cancel.
  set (P8 :=
    &(s # "solver_t" ->ₛ "wlists") # Ptr |-> anz_wl **
    &(s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    &(s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &(s # "solver_t" ->ₛ "reasons") # Ptr |-> reasons **
    &(s # "solver_t" ->ₛ "trail") # Ptr |-> trail **
    &(s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary Mmin_done **
    &(s # "solver_t" ->ₛ "tags") # Ptr |-> tags).
  set (A0tail :=
    PtrArray.seg reasons 0 (ms_size Mmin_done)
      (ms_reason_words Mmin_done) **
    PtrArray.undef_seg reasons (ms_size Mmin_done) (ms_cap Mmin_done) **
    CharArray.seg tags 0 (ms_size Mmin_done) (ms_tags Mmin_done) **
    CharArray.undef_seg tags (ms_size Mmin_done) (ms_cap Mmin_done)).
  set (A0 :=
    DoubleArray.seg act 0 (ms_size Mmin_done) (ms_activity Mmin_done) **
    DoubleArray.undef_seg act (ms_size Mmin_done) (ms_cap Mmin_done) **
    CharArray.seg asg 0 (ms_size Mmin_done)
      (mt_assigns (ms_core Mmin_done)) **
    CharArray.undef_seg asg (ms_size Mmin_done) (ms_cap Mmin_done) **
    IntArray.seg opos 0 (ms_size Mmin_done) (ms_orderpos Mmin_done) **
    IntArray.undef_seg opos (ms_size Mmin_done) (ms_cap Mmin_done) **
    A0tail).
  set (L0 :=
    &(s # "solver_t" ->ₛ "levels") # Ptr |-> levels **
    IntArray.seg levels 0 (ms_size Mmin_done)
      (mt_levels (ms_core Mmin_done)) **
    IntArray.undef_seg levels (ms_size Mmin_done) (ms_cap Mmin_done)).
  assert (Htrail : solver_trail_array_rep Mstats_upd trail =
      solver_trail_array_rep Mmin_done trail).
  { unfold solver_trail_array_rep, Mstats_upd,
      msolver_with_cla_inc_stats. cbn. reflexivity. }
  assert (Hmax_slot : Znth 9 stats_upd 0 = max_lits).
  { unfold stats_upd.
    exact (proj1 (proj2 (stats_pair_update_slots_p6 (ms_stats Mmin_done)
      max_lits tot_lits Hstats_len))). }
  assert (Htot_slot : Znth 10 stats_upd 0 = tot_lits).
  { unfold stats_upd.
    exact (proj2 (proj2 (stats_pair_update_slots_p6 (ms_stats Mmin_done)
      max_lits tot_lits Hstats_len))). }
  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hmax_addr :
      &(s # "solver_t" ->ₛ "stats" .ₛ "max_literals") =
      &(stats_ptr # "stats_t" ->ₛ "max_literals"))
    by (unfold stats_ptr; csimpl; reflexivity).
  assert (Htot_addr :
      &(s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") =
      &(stats_ptr # "stats_t" ->ₛ "tot_literals"))
    by (unfold stats_ptr; csimpl; reflexivity).
  unfold stats_rep, stats_analyze_frame, stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals.
  rewrite !Hznth by lia.
  rewrite Hmax_slot, Htot_slot.
  unfold stats_upd. rewrite !Zlength_replace_Znth.
  sepcon_assoc_change.
  repeat sepcon_cancel.
  sepcon_assoc_change.
  rewrite Htrail.
  rewrite Hmax_addr, Htot_addr.
  unfold P8, A0, A0tail, L0, solver_ptrs_rep,
    solver_var_arrays_rep.
  unfold DoubleArray.seg, IntArray.seg, PtrArray.seg, CharArray.seg.
  unfold StoreDoubleAsElement.storeA, StoreIntAsElement.storeA,
    StorePtrAsElement.storeA, StoreCharAsElement.storeA.
  unfold store_double.
  unfold bits_of_double_value.
  cbn.
  sepcon_assoc_change.
  repeat sepcon_cancel.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_37 : solver_analyze_which_implies_wit_37.
Proof.
  aggressive_pre_process.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mstats anz_focus ) as H_analysis_cancel_ready.
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mstats anz_focus H_analysis_cancel_ready) as [Hsize _].
  subst anz_n.
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_reason_levels_frame_at, solver_tags_tagged_frame_at,
    solver_removable_frame_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_vecs_rep, solver_ptrs_rep,
    solver_var_arrays_rep.
  Intros act asg opos.
  sep_apply peel_scalars_size.
  unfold veci_rep at 1.
  Intros tagged_ptr.
  Exists tagged_ptr act asg opos.
  unfold veci_rep_at at 1.
  entailer_with ltac:(lia).
  unfold veci_rep_at.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_39 : solver_analyze_which_implies_wit_39.
Proof.
  Unfold.
  right.
  intros anz_wl anz_focus M K anz_A_arr anz_F anz_n Mstats
    words_compact tags_final tagged_list tagged_p tagged_cap_final
    s tags trail levels reasons; intros.
  try rename anz_n into n.
  try rename anz_F into F.
  try rename anz_A_arr into A_arr.
  try rename anz_focus into focus.
  bind_fact ( analysis_core_equiv M Mstats ) as H_analysis_core_equiv.
  bind_fact ( msolver_seed_shadow Mstats ) as H_msolver_seed_shadow.
  bind_fact ( analysis_cancel_ready n F A_arr K Mstats focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert n F Mstats words_compact ) as H_analyze_clause_cert.
  bind_fact ( Zlength tagged_list = 0 ) as H_Zlength.
  bind_fact ( analysis_tags_exact n tags_final tagged_list ) as H_analysis_tags_exact.
  assert (Htagged_nil : tagged_list = nil).
  { destruct tagged_list as [|a rest]; [reflexivity|].
    rewrite Zlength_cons in H_Zlength.
    pose proof (Zlength_nonneg rest). lia. }
  subst tagged_list.
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K Mstats focus H_analysis_cancel_ready) as [Hsize _].
  assert (Htags_zero : tags_final = repeat_Z 0 n)
    by exact (analysis_tags_exact_nil_zero_p6 n tags_final
                H_analysis_tags_exact).
  unfold analysis_tags_exact in H_analysis_tags_exact.
  destruct H_analysis_tags_exact as
    [Htags_len [Hnodup [Hrange [Hbits Hiff]]]].
  assert (Hn_nonneg : 0 <= n).
  { rewrite <- Htags_len. apply Zlength_nonneg. }
  assert (Hframe_lengths_keep :
    solver_tags_tagged_frame_at s Mstats reasons levels trail anz_wl |--
      “ Zlength (ms_activity Mstats) = ms_size Mstats /\
        Zlength (ms_orderpos Mstats) = ms_size Mstats /\
        Zlength (ms_stats Mstats) = 11 ” &&
      solver_tags_tagged_frame_at s Mstats reasons levels trail anz_wl).
  { unfold solver_tags_tagged_frame_at at 1.
    sep_apply
      (solver_removable_frame_lengths_keep__lit_removable
        s Mstats trail anz_wl).
    Intros_p Hframe_lengths.
    destruct Hframe_lengths as
      (Hactivity_len & Horder_len & Hstats_len).
    unfold solver_tags_tagged_frame_at.
    entailer_with ltac:(lia). }
  sep_apply Hframe_lengths_keep.
  Intros_p Hframe_lengths.
  destruct Hframe_lengths as
    (Hactivity_len & Horder_len & Hstats_len).
  pose proof H_analysis_cancel_ready as Hready.
  unfold analysis_cancel_ready in Hready.
  destruct Hready as
    [Mbase [Hprop [Hequiv [Hheap [Hcovers [Hcurrent [Hfocus Hcla]]]]]]].
  unfold propagation_cancel_ready in Hprop.
  destruct Hprop as [Hweak _].
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as [_ Hweak].
  assert (Hshape_base : solver_shape Mbase).
  { destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (msw_shape Hweak).
    - exact (msa_shape Hweak). }
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason &
     Eprob & Elearnt & Eprobcap & Elearntcap & Ebinary & Ebinarylits &
     Ewm & Ewcaps & Elimcap & Emodel & Emodelcap & Ecladecay & Eseed &
     Ependingq & Epending & Esimpassigns & Esimpprops).
  set (Mclear := msolver_scratch_update Mstats tags_final nil
    tagged_cap_final (ms_stack Mstats) (ms_stack_cap Mstats)).
  assert (Htags_size : Zlength tags_final = ms_size Mstats).
  { rewrite Htags_len. exact Hsize. }
  assert (Hshape : solver_shape Mclear).
  { unfold solver_shape in Hshape_base.
    rewrite <- Esize, <- Ecap, <- Eqtail, <- Ecore, <- Eroot,
      <- Ewords, <- Ebinary, <- Ebinarylits, <- Ewm, <- Ewcaps,
      <- Ependingq, <- Epending in Hshape_base.
    destruct Hshape_base as
      (Hsrange & Hcapmax & Htwice & Hassigns & Hlevels_len &
       Hreasons_len & Horder_old & Hactivity_old & Htags_old &
       Htrail_len & Hqhead_range & Hpending_range & Hpending_flag &
       Hpending_case & Hqtail_range & Hwm_len & Hwcaps_len &
       Hbinary_lits_len & Hstats_old & Hroot_nonneg &
       Hbinary_nonzero & Hbinary_even).
    subst Mclear.
    unfold solver_shape, msolver_scratch_update, msolver_analysis_update. cbn.
    (* Every conjunct is already a hypothesis: the four scratch-updated lengths
       come from the heap above, the rest straight from [Hshape_base]. *)
    repeat split; tauto. }
  assert (Hcore : analysis_core_equiv M Mclear).
  { subst Mclear.
    change (analysis_core_equiv M Mstats).
    exact H_analysis_core_equiv. }
  assert (Hseed : msolver_seed_shadow Mclear).
  { subst Mclear.
    change (msolver_seed_shadow Mstats).
    exact H_msolver_seed_shadow. }
  assert (Hcancel : analysis_cancel_ready n F A_arr K Mclear focus).
  { subst Mclear.
    change (analysis_cancel_ready n F A_arr K Mstats focus).
    exact H_analysis_cancel_ready. }
  assert (Hcert : analyze_clause_cert n F Mclear words_compact).
  { subst Mclear.
    change (analyze_clause_cert n F Mstats words_compact).
    exact H_analyze_clause_cert. }
  Exists Mclear.
  entailer_with ltac:(lia).
  unfold solver_rep_analyze_at, solver_rep_at,
      solver_tags_tagged_frame_at, solver_removable_frame_at,
      solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
      solver_trail_array_rep, solver_scalars_rep, solver_vecs_rep,
      solver_ptrs_rep, solver_var_arrays_rep, clause_new_scalars_frame.
  Intros act asg opos.
  sep_apply (veci_rep_at_rep &((s) # "solver_t" ->ₛ "tagged")
    tagged_p nil tagged_cap_final).
  Exists act asg opos.
  subst Mclear. unfold msolver_scratch_update, msolver_analysis_update. cbn.
  entailer_with ltac:(lia).
  rewrite Hsize.
  unfold solver_fp_rep, DoubleArray.seg, IntArray.seg,
    PtrArray.seg, CharArray.seg.
  cbn.
  sepcon_assoc_change.
  repeat sepcon_cancel.
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_40 : solver_analyze_which_implies_wit_40.
Proof.
  aggressive_pre_process;
    bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mclear anz_focus ) as H_analysis_cancel_ready.
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mclear anz_focus H_analysis_cancel_ready) as [Hsize _].
  subst anz_n.
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at, solver_vecs_rep,
    solver_ptrs_rep, solver_var_arrays_rep.
  Intros act asg opos.
  sep_apply peel_scalars_size.
  Exists act asg opos.
  entailer_with ltac:(lia).
  all: unfold solver_rep_analyze_at, solver_rep_at;
    Intros act' asg' opos';
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_41 : solver_analyze_which_implies_wit_41.
Proof.
  Unfold.
  right.
  intros n words_compact PreH1 PreH2.
  bind_fact ( Forall (lit_wf_c n) words_compact ) as H_Forall.
  pose proof (Forall_Znth_elim Z (lit_wf_c n) words_compact 0 1
    H_Forall ltac:(lia)) as Hlit.
  pose proof (lit_var_c_in_range n (Znth 1 words_compact 0) Hlit) as Hrange.
  replace (1 - 0) with 1 by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_canceluntil entail wits (6 proofs) ===== *)
Lemma proof_of_solver_canceluntil_entail_wit_1 : solver_canceluntil_entail_wit_1.
Proof.
  aggressive_pre_process.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  unfold solver_cancel_post.
  Left.
  apply derivable1s_coq_prop_andp_r.
  2: { lia. }
  unfold solver_cancel_owned.
  apply derivable1s_coq_prop_andp_r.
  2: { exact H_solver_shape. }
  unfold solver_cancel_frame.
  Intros tgs.
  Exists activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
    solver_trail_array_rep, solver_cancel_undef_tail.
  entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_entail_wit_2 : solver_canceluntil_entail_wit_2.
Proof.
  unfold solver_canceluntil_entail_wit_2, solver_cancel_open_at.
  left; intros.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  assert (Hlevel : 0 <= level_pre < Zlength (mt_lim (ms_core M0))) by lia.
  pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level_pre
    H_mtrail_wf Hlevel) as Hbound.
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  assert (Hslice : sublist (ms_qtail M0 - 1 + 1) (ms_qtail M0)
    (mt_trail (ms_core M0)) = (@nil Z)).
  { replace (ms_qtail M0 - 1 + 1) with (ms_qtail M0) by lia.
    unfold sublist; apply skipn_all2; rewrite length_firstn; lia. }
  assert (Hinv : cancel_clear_loop_inv M0 level_pre (ms_qtail M0 - 1)
    (mt_assigns (ms_core M0)) (ms_reason_words M0)).
  { unfold cancel_clear_loop_inv.
    repeat split; try lia; rewrite Hslice; reflexivity. }
  Exists (mt_assigns (ms_core M0)) (ms_reason_words M0).
  split_pure_spatial.
  - set_String_name; sepcon_assoc_change; sepcon_cancel; subst_all_strings.
    unfold veci_rep; Exists p; unfold veci_rep_at.
    entailer_with ltac:(lia).
    unfold veci_size_addr, veci_cap_addr, veci_ptr_addr; csimpl.
    entailer_with ltac:(lia).
  - split_pures; dump_pre_spatial; try assumption.
    replace (level_pre - 0) with level_pre by lia; reflexivity.
Qed.

Lemma proof_of_solver_canceluntil_entail_wit_3 : solver_canceluntil_entail_wit_3.
Proof.
  unfold solver_canceluntil_entail_wit_3, solver_cancel_open_at.
  aggressive_pre_process.
  bind_fact ( retval = lit_var_c (Znth (c - 0) (mt_trail (ms_core M0)) 0) ) as H_retval.
  bind_fact ( cancel_clear_loop_inv M0 level_pre c assigns_now_2 reasons_now_2 ) as H_cancel_clear_loop_inv.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  replace (c - 0) with c in H_retval by lia.
  subst retval.
  unfold cancel_clear_loop_inv in H_cancel_clear_loop_inv.
  destruct H_cancel_clear_loop_inv as (Hlevel & Hc & Hass & Hreason).
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hinv : cancel_clear_loop_inv M0 level_pre (c - 1)
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 assigns_now_2)
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 reasons_now_2)).
  { unfold cancel_clear_loop_inv.
    repeat split; try lia.
    - rewrite Hass.
      replace (c - 1 + 1) with c by lia.
      apply clear_vars_sublist_step__assume; lia.
    - rewrite Hreason.
      replace (c - 1 + 1) with c by lia.
      apply clear_vars_sublist_step__assume; lia. }
  Exists
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 assigns_now_2)
    (replace_Znth (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) 0 reasons_now_2).
  (* Do not reintroduce `replace (sizeof (PTR)) with 4 by reflexivity` here: the
          PtrArray lemmas are stated with `ptr_size_Z`, so pinning the literal 32-bit
          width PREVENTS the match below instead of enabling it. *)
  (* arch port A04: the goal carries the unfolded Arch alias while PtrArray's
     lemmas are stated with the derived [ptr_size_Z]; fold the alias back to
     that derived name so sep_apply_l_atomic matches syntactically. *)
  try change (sizeof (PTR)) with ptr_size_Z. fold_arch.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full reasons_ptr
      (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) (ms_size M0) 0
      reasons_now_2).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic
      (CharArray.missing_i_merge_to_full assigns_ptr
        (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) (ms_size M0) 0
        assigns_now_2).
    + dump_pre_spatial. lia.
    + msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_canceluntil_entail_wit_4 : solver_canceluntil_entail_wit_4.
Proof.
  unfold solver_canceluntil_entail_wit_4, solver_cancel_open_at.
  Unfold.
  left. intros.
  aggressive_pre_process.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( heap_wf (ms_size M0) (msolver_heap M0) ) as H_heap_wf.
  bind_fact ( cancel_bound_ready M0 level_pre ) as H_cancel_bound_ready.
  bind_fact ( cancel_clear_loop_inv M0 level_pre c assigns_now_2 reasons_now_2 ) as H_cancel_clear_loop_inv.
  unfold veci_rep at 2.
  Intros order_data_ptr.
  unfold veci_rep_at at 1.
  Intros.
  destruct H as (Horderlen & Hordercap).
  unfold cancel_clear_loop_inv in H_cancel_clear_loop_inv.
  destruct H_cancel_clear_loop_inv as (Hlevel & Hc & Hass & Hreason).
  assert (Hcb : c = Znth level_pre (mt_lim (ms_core M0)) 0 - 1) by lia.
  pose proof H_cancel_bound_ready as Hready.
  unfold cancel_bound_ready in H_cancel_bound_ready.
  destruct H_cancel_bound_ready as [Hout | Hbound]; [lia|].
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  (* The trail-length equation is the only conjunct of [solver_shape] this proof
     names; bind it by its statement, not by the position the bulk destruct below
     happens to mint. *)
  assert (Htrail_len : Zlength (mt_trail (ms_core M0)) = ms_qtail M0) by tauto.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hinv : cancel_reinsert_loop_inv M0 level_pre
    (mt_qhead (ms_core M0) - 1) (ms_order_cap M0)
    assigns_now_2 reasons_now_2 (ms_order M0) (ms_orderpos M0)).
  { unfold cancel_reinsert_loop_inv.
    split.
    - rewrite Hass, Hcb.
      replace (Znth level_pre (mt_lim (ms_core M0)) 0 - 1 + 1)
        with (Znth level_pre (mt_lim (ms_core M0)) 0) by lia.
      rewrite <- Htrail_len, sublist_to_zdrop__assume. reflexivity.
    - split.
      + rewrite Hreason, Hcb.
        replace (Znth level_pre (mt_lim (ms_core M0)) 0 - 1 + 1)
          with (Znth level_pre (mt_lim (ms_core M0)) 0) by lia.
        rewrite <- Htrail_len, sublist_to_zdrop__assume. reflexivity.
      + split; [lia|].
        split; [lia|].
        split; [lia|].
        split; [lia|].
        split; [lia|].
        split.
        * change (heap_wf (ms_size M0) (msolver_heap M0)). exact H_heap_wf.
        * split; [apply incl_refl|].
          replace (mt_qhead (ms_core M0) - 1 + 1)
            with (mt_qhead (ms_core M0)) by lia.
          apply cancel_reinserted_init. }
  Exists (ms_order_cap M0) assigns_now_2 reasons_now_2
    (ms_order M0) (ms_orderpos M0).
  entailer_with ltac:(lia).
  unfold veci_rep. Exists order_data_ptr. unfold veci_rep_at. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_entail_wit_5 : solver_canceluntil_entail_wit_5.
Proof.
  unfold solver_canceluntil_entail_wit_5, solver_cancel_open_at.
  aggressive_pre_process.
  bind_fact ( order_unassigned_post (ms_size M0) retval order_cap_now_2 order_now_2 orderpos_now_2 order_cap1 heap1
      orderpos1 ) as H_order_unassigned_post.
  bind_fact ( retval = lit_var_c (Znth (c - 0) (mt_trail (ms_core M0)) 0) ) as H_retval.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( 0 <= lit_var_c (Znth c (mt_trail (ms_core M0)) 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth c (mt_trail (ms_core M0)) 0) < ms_size M0 ) as H_lit_var_c_2.
  bind_fact ( cancel_reinsert_loop_inv M0 level_pre c order_cap_now_2 assigns_now_2 reasons_now_2 order_now_2
      orderpos_now_2 ) as H_cancel_reinsert_loop_inv.
  replace (c - 0) with c in H_retval by lia. subst retval.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  destruct H_cancel_reinsert_loop_inv as
    (Hassigns & Hreasons & Hlevel & Hcrange & Hcap & Hcappos & Hlen &
     Hwf & Horig & Hreinserted).
  pose proof (order_unassigned_post_members__assume
    (ms_size M0) (lit_var_c (Znth c (mt_trail (ms_core M0)) 0))
    order_cap_now_2 order_now_2 orderpos_now_2 order_cap1 heap1 orderpos1
    H_order_unassigned_post Hwf (conj H_lit_var_c H_lit_var_c_2)) as Hmembers.
  destruct Hmembers as (Hincl & Hhit).
  unfold order_unassigned_post in H_order_unassigned_post.
  destruct H_order_unassigned_post as (Hwfnew & Hcaps & Hlennew & Hcases).
  change (heap_wf (ms_size M0) (heap_of_lists heap1 orderpos1)) in Hwfnew.
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hreinserted' :
    cancel_reinserted (heap_of_lists heap1 orderpos1)
      (mt_trail (ms_core M0)) c (mt_qhead (ms_core M0))).
  { intros i Hi.
    destruct (Z.eq_dec i c) as [->|Hne]; [exact Hhit|].
    assert (Hvrange :
      0 <= lit_var_c (Znth i (mt_trail (ms_core M0)) 0) < ms_size M0).
    { apply trail_var_range with (t := ms_core M0); [exact H_mtrail_wf|].
      apply in_map. apply Znth_In. lia. }
    apply (proj1 (heap_wf_in_iff (ms_size M0)
      (heap_of_lists heap1 orderpos1)
      (lit_var_c (Znth i (mt_trail (ms_core M0)) 0)) Hwfnew Hvrange)).
    apply Hincl.
    apply (proj2 (heap_wf_in_iff (ms_size M0)
      (heap_of_lists order_now_2 orderpos_now_2)
      (lit_var_c (Znth i (mt_trail (ms_core M0)) 0)) Hwf Hvrange)).
    apply Hreinserted. lia. }
  Exists order_cap1 assigns_now_2 reasons_now_2 heap1 orderpos1.
  entailer_with ltac:(lia).
  unfold cancel_reinsert_loop_inv.
  split; [exact Hassigns|].
  split; [exact Hreasons|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [exact Hwfnew|].
  split.
  - intros x Hx. apply Hincl. apply Horig. exact Hx.
  - replace (c - 1 + 1) with c by lia. exact Hreinserted'.
Qed.

Lemma proof_of_solver_canceluntil_entail_wit_6 : solver_canceluntil_entail_wit_6.
Proof.
  aggressive_pre_process.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( bound = Znth level_pre (mt_lim (ms_core M0)) 0 ) as H_bound.
  bind_fact ( cancel_reinsert_loop_inv M0 level_pre c order_cap_now assigns_now reasons_now order_now orderpos_now )
      as H_cancel_reinsert_loop_inv.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  destruct H_cancel_reinsert_loop_inv as
    (Hassigns & Hreasons & Hlevel & Hcrange & Hcap & Hcappos & Hlen &
     Hwf & Hincl & Hreinserted).
  assert (Hcb : c = bound - 1) by (rewrite H_bound in *; lia).
  assert (Hreinserted' :
    cancel_reinserted (heap_of_lists order_now orderpos_now)
      (mt_trail (ms_core M0)) bound (mt_qhead (ms_core M0))).
  { replace bound with (c + 1) by lia. exact Hreinserted. }
  assert (Hbound_qtail : 0 <= bound <= ms_qtail M0).
  { assert (Htraillen0 :
      Zlength (mt_trail (ms_core M0)) = ms_qtail M0)
      by (unfold solver_shape in H_solver_shape; tauto).
    pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level_pre
      H_mtrail_wf Hlevel) as Hr. rewrite <- H_bound in Hr. lia. }
  assert (Hqtail_cap : ms_qtail M0 <= ms_cap M0)
    by (unfold solver_shape in H_solver_shape; tauto).
  unfold solver_cancel_post.
  right.
  exists orderpos_now, order_now, order_cap_now.
  split.
  - assert (Hreinserted_goal :
      cancel_reinserted (heap_of_lists order_now orderpos_now)
        (mt_trail (ms_core M0))
        (Znth level_pre (mt_lim (ms_core M0)) 0)
        (mt_qhead (ms_core M0))).
    { rewrite <- H_bound. exact Hreinserted'. }
    exact (conj Hlevel
      (conj Hcap (conj Hwf (conj Hincl Hreinserted_goal)))).
  - unfold solver_cancel_owned.
    split.
    + destruct Hlevel as [Hlevel0 HlevelLt].
      pose proof H_solver_shape as Hshape.
      unfold solver_shape in Hshape.
      destruct Hshape as
        (Hsrange & Hcapmax & Htwice & Hassignlen & Hlevelslen &
         Hreasonlen & Horderposoriglen & Hactivitylen & Htagslen &
         Htraillen & Hqrange & Hpendingrange & Hflag & Hpending &
         Hqtailrange & Hwmlen & Hwcapslen & Hbinarylen & Hstatslen &
         Hroot & Hbinarynz & Hbinaryeven).
      pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level_pre
        H_mtrail_wf (conj Hlevel0 HlevelLt)) as Hboundrange.
      pose proof (heap_wf_orderpos_length (ms_size M0)
        (heap_of_lists order_now orderpos_now) Hwf) as Horderposlen.
      assert (Hflag0 : ms_capacity_root_propagation_pending M0 = 0).
      { destruct Hflag as [Hf|Hf]; [exact Hf|].
        exfalso. specialize (Hpending Hf). lia. }
      unfold solver_shape, msolver_cancel_project, msolver_core_heap_update.
      cbn [mt_cancel].
      simpl.
      repeat split; try lia; try assumption;
        try (rewrite Zlength_clear_vars; assumption);
        try (rewrite Zlength_ztake by lia; lia);
        try (rewrite Hflag0; auto).
    + match type of H with
      | ?P m =>
        assert (HP : P |-- (EX act asg opos rsn trl tgs : Z,
          solver_nonlevel_rep_at s_pre
            (msolver_cancel_project M0 level_pre orderpos_now order_now
              order_cap_now (ms_root_level M0)) wl act asg opos rsn trl tgs))
      end.
      * unfold solver_cancel_undef_tail.
        sep_apply_l_atomic
          (IntArray.seg_split_to_seg trail_ptr 0 bound (ms_qtail M0)
            (mt_trail (ms_core M0))).
        -- dump_pre_spatial. lia.
        -- sep_apply_l_atomic
             (IntArray.seg_to_undef_seg trail_ptr bound (ms_qtail M0)
               (sublist (bound - 0) (ms_qtail M0 - 0)
                 (mt_trail (ms_core M0)))).
           sep_apply_l_atomic
             (IntArray.undef_seg_merge_to_undef_seg trail_ptr bound
               (ms_qtail M0) (ms_cap M0)).
           ++ dump_pre_spatial. lia.
           ++ unfold solver_cancel_frame.
              Intros tgs.
              Exists activity_ptr assigns_ptr orderpos_ptr reasons_ptr
                trail_ptr tgs.
              unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep,
                solver_vecs_rep, solver_trail_array_rep,
                msolver_cancel_project, msolver_core_heap_update.
              cbn [mt_cancel].
              simpl.
              rewrite Hassigns, Hreasons, H_bound.
              rewrite !sublist_zero_ztake__assume.
              entailer_with ltac:(lia).
              sep_apply_l_atomic
                (solver_fp_rep_cancel_project__assume s_pre M0
                  level_pre orderpos_now order_now order_cap_now
                  (ms_root_level M0)).
              unfold veci_rep.
              Exists p.
              unfold veci_rep_at.
              rewrite Zlength_ztake by lia.
              entailer_with ltac:(lia).
              unfold veci_size_addr, veci_cap_addr, veci_ptr_addr.
              csimpl.
              rewrite !Zlength_ztake by lia.
              unfold solver_fp_rep, msolver_cancel_project,
                msolver_core_heap_update.
              simpl.
              entailer_with ltac:(lia).
              replace (Znth level_pre (mt_lim (ms_core M0)) 0 - 0)
                with (Znth level_pre (mt_lim (ms_core M0)) 0) by lia.
              change (ztake level_pre (mt_lim (ms_core M0)))
                with (sublist 0 level_pre (mt_lim (ms_core M0))).
              cancel.
              all: try (rewrite Zlength_ztake by lia); lia.
      * exact (HP m H).
Qed.

(* ===== solver_canceluntil partial_solve wits ===== *)


Lemma proof_of_solver_canceluntil_partial_solve_wit_7_pure : solver_canceluntil_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process;
    replace (c - 0) with c by lia; msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_canceluntil safety wits (2 proofs) ===== *)
Lemma proof_of_solver_canceluntil_safety_wit_1 : solver_canceluntil_safety_wit_1.
Proof.
  msat_canceluntil_shape_close_p6 M0 H_shape.
Qed.

Lemma proof_of_solver_canceluntil_safety_wit_6 : solver_canceluntil_safety_wit_6.
Proof.
  msat_canceluntil_shape_close_p6 M0 H_shape.
Qed.

(* ===== solver_lit_removable entail wits (2 proofs) ===== *)
Lemma proof_of_solver_lit_removable_entail_wit_1 : solver_lit_removable_entail_wit_1.
Proof.
  Unfold.
  right. intros.
  bind_fact ( 0 <= minl_pre ) as H_minl_pre.
  bind_fact ( minl_pre <= 4294967295 ) as H_minl_pre_2.
  bind_fact ( assigned_below_current (msolver_view lrm_n M0) (lit_var_c l_pre) ) as H_assigned_below_current.
  bind_fact ( reason_target_wf lrm_n M0 (lit_var_c l_pre) (Znth (lit_var_c l_pre) (ms_reason_words M0) 0) Croot ) as
      H_reason_target_wf.
  bind_fact ( analysis_tags_exact lrm_n (ms_tags M0) (ms_tagged M0) ) as H_analysis_tags_exact.
  bind_fact ( In (lit_var_c l_pre) (map lit_var_c (mt_trail (ms_core M0))) ) as H_In.
  match goal with
  | MS : msolver |- _ =>
      pose proof
        (removable_dfs_loop_init__record
          lrm_n MS l_pre minl_pre Croot H_analysis_tags_exact H_assigned_below_current H_reason_target_wf
          (conj H_minl_pre H_minl_pre_2)) as Hinv
  end.
  Exists (@nil Z).
  subst retval_5 retval_6.
  simpl in *.
  entailer_with ltac:(lia).
  - intros x [<- | []]. exact H_In.
  - rewrite Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_2 : solver_lit_removable_entail_wit_2.
Proof.
  Unfold.
  right. intros. entailer_with lia.
  (* The stack index is spelled through the call result [retval_3] rather than
          through [Zlength stack_now] (a PreH ties them), so only the [- 0] tail is
          left to normalise. *)
  replace (retval_3 - 1 - 0) with (retval_3 - 1) by lia.
  reflexivity.
Qed.

(* ===== solver_lit_removable partial_solve wits ===== *)
Lemma proof_of_solver_lit_removable_partial_solve_wit_46_pure : solver_lit_removable_partial_solve_wit_46_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact ( removable_rollback_inv lrm_n top j (ms_tagged M0) (ms_tags M0) tags_now tagged_now tags_rollback ) as
      H_removable_rollback_inv.
  unfold removable_rollback_inv in H_removable_rollback_inv.
  split_pures;
    pose proof (Zlength_nonneg (ms_tagged M0)); dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_49_pure : solver_lit_removable_partial_solve_wit_49_pure.
Proof.
  Unfold.
  left; intros.
  entailer_with ltac:(lia).
  apply clause_hdr_word_nonneg.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_53_pure : solver_lit_removable_partial_solve_wit_53_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  assert (Hi : 0 <= i < Zlength clause_words) by lia.
  assert (Hin : In (Znth i clause_words 0) clause_words)
    by (apply Znth_In; exact Hi).
  rewrite Forall_forall in H_Forall.
  specialize (H_Forall _ Hin).
  unfold lit_wf_c in H_Forall.
  replace (i - 0) with i by lia.
  entailer_with ltac:(lia); lia.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_58_pure : solver_lit_removable_partial_solve_wit_58_pure.
Proof.
  Unfold.
  left; intros.
  split_pures; dump_pre_spatial;
    replace (retval - 0) with retval in * by lia;
    assumption.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_60_pure : solver_lit_removable_partial_solve_wit_60_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  assert (Hi : 0 <= i < Zlength clause_words) by lia.
  assert (Hin : In (Znth i clause_words 0) clause_words)
    by (apply Znth_In; exact Hi).
  rewrite Forall_forall in H_Forall.
  specialize (H_Forall _ Hin).
  unfold lit_wf_c in H_Forall.
  replace (i - 0) with i by lia.
  entailer_with ltac:(lia); lia.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_61_pure : solver_lit_removable_partial_solve_wit_61_pure.
Proof.
  Unfold.
  left; intros.
  unfold veci_rep at 2; Intros p.
  unfold veci_rep_at at 1; Intros_p Hstack_bounds.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_64_pure : solver_lit_removable_partial_solve_wit_64_pure.
Proof.
  Unfold.
  msat_lit_removable_close_tagged_caps_by_lia.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_70_pure : solver_lit_removable_partial_solve_wit_70_pure.
Proof.
  Unfold.
  left; intros.
  replace (j - 0) with j by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_lit_removable safety wits (5 proofs) ===== *)
Lemma proof_of_solver_lit_removable_safety_wit_25 : solver_lit_removable_safety_wit_25.
Proof.
  Unfold.
  right. intros.
  (* This obligation spells the level index as [retval]; the sibling safety
       obligations spell it [retval - 0].  The posed bound has to match the goal's
       spelling, so there is nothing to normalise here. *)
  match goal with
  | MS : msolver |- _ =>
      pose proof
        (land_31_bounds__record
          (Znth retval (mt_levels (ms_core MS)) 0)) as [Hlo Hhi]
  end.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_lit_removable_safety_wit_43 : solver_lit_removable_safety_wit_43.
Proof.
  Unfold.
  right. intros.
  match goal with
  | MS : msolver |- _ =>
      pose proof
        (land_31_bounds__record
          (Znth (retval - 0) (mt_levels (ms_core MS)) 0)) as [Hlo Hhi]
  end.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_safety_wit_57 : solver_lit_removable_safety_wit_57.
Proof.
  msat_lit_removable_hdr_bound_p6 is_learnt_now clause_words H_hdr.
Qed.

Lemma proof_of_solver_lit_removable_safety_wit_58 : solver_lit_removable_safety_wit_58.
Proof.
  msat_lit_removable_hdr_bound_p6 is_learnt_now clause_words H_hdr.
Qed.

Lemma proof_of_solver_lit_removable_safety_wit_59 : solver_lit_removable_safety_wit_59.
Proof.
  msat_lit_removable_hdr_bound_p6 is_learnt_now clause_words H_hdr.
Qed.


(* ===== solver_progress return witness ===== *)
Lemma proof_of_solver_progress_return_wit_1 : solver_progress_return_wit_1.
Proof.
  Unfold.
  right.
  intros n progress_now i PreH1 PreH2 PreH3.
  unfold msat_fp64_value.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_propagate entail wits (16 proofs) ===== *)
Lemma proof_of_solver_propagate_entail_wit_18_1_unit_conflict_copy :
  solver_propagate_entail_wit_18_1_unit_conflict_copy.
Proof.
  unfold solver_propagate_entail_wit_18_1_unit_conflict_copy.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  bind_fact ( copy_dst_2 = copy_src_2 ) as H_copy_dst_2.
  bind_fact ( i < endvar ) as H_i.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src_2 * sizeof ( PTR ) ) as H_i_2.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_dst_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  Exists (replace_Znth copy_dst_2
    (Znth copy_src_2
      (replace_Znth copy_src_2 (Znth copy_src_2 copy_memory_2 0)
        copy_memory_2) 0)
    (replace_Znth copy_src_2 (Znth copy_src_2 copy_memory_2 0)
      copy_memory_2))
    (copy_dst_2 + 1) (copy_src_2 + 1).
  entailer_with lia;
    try lia.
  (* The copied cell's address is spelled [begin + copy_dst_2 * sizeof(PTR)] against
          a [missing_i] hole indexed by copy_src_2, so the array merge does not fire on
          its own and survives [entailer_with lia] as a remaining goal.  [H_copy_dst_2]
          identifies the two indices; after that the merge is the standard missing_i ->
          full step at copy_src_2, whose index bound is the arch-scaled form of
          [H_endvar] and [H_i_2]. *)
  assert (Hbound : 0 <= copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i_2. unfold_arch. cbn in H_endvar, H_i_2. nia. }
  - rewrite H_copy_dst_2, !replace_Znth_Znth.
    pose proof (PtrArray.missing_i_merge_to_full begin copy_src_2
      (Zlength source_words) (Znth copy_src_2 copy_memory_2 0) copy_memory_2
      Hbound) as Hm.
    rewrite replace_Znth_Znth in Hm.
    change (sizeof (PTR)) with ptr_size_Z. fold_arch. exact Hm.
  - unfold binary_watch_copy_progress in H_binary_watch_copy_progress |- *.
    destruct H_binary_watch_copy_progress as [copied [rest0
      [Hwords [Hkept [Hjj [Hsuffix [Hsrc [Hdst [Hmem Hlen]]]]]]]]].
    destruct rest0 as [|x rest0].
    + exfalso.
      unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
      destruct H_propagation_watch_scan_physical as [_ [_ [_ [_ Hphysical_len]]]].
      subst raw_suffix.
      rewrite Hwords, Zlength_app, Zlength_cons, Hkept in Hphysical_len.
      rewrite <- Hphysical_len in H_endvar.
      rewrite H_endvar, H_i_2, Hsrc in H_i.
      rewrite app_nil_r in H_i, H_endvar, Hphysical_len, Hwords, H_rest.
      assert (Hidx : ii + 1 + Zlength copied = ii + Z.succ (Zlength copied))
        by lia.
      rewrite Hidx in H_i.
      lia.
    + destruct Hjj as [Hjj0 Hjjle].
      assert (Hij : ii = jj) by lia.
      subst jj.
      assert (Hcurrent : Znth ii watch_memory 0 = scan_current).
      { rewrite Hwords.
        rewrite app_Znth2 by (rewrite Hkept; lia).
        rewrite Hkept.
        replace (ii - ii) with 0 by lia.
        simpl. reflexivity. }
      assert (Hreplace_current :
        replace_Znth ii scan_current watch_memory = watch_memory).
      { rewrite <- Hcurrent. apply replace_Znth_Znth. }
      assert (Hcopy_mem : copy_memory_2 = watch_memory).
      { rewrite Hmem, Hreplace_current, Hwords, Hsuffix.
        replace ii with (Zlength raw_prefix) by lia.
        apply binary_watch_write_identity_p6. }
      exists (copied ++ (x :: nil)), rest0.
      repeat split.
      * exact Hwords.
      * exact Hkept.
      * exact Hjj0.
      * exact Hjjle.
      * rewrite Hsuffix.
        change (copied ++ x :: rest0 = (copied ++ (x :: nil)) ++ rest0).
        replace (x :: rest0) with ((x :: nil) ++ rest0) by reflexivity.
        apply app_assoc.
      * rewrite Hsrc.
        rewrite Zlength_app_cons. lia.
      * rewrite Hdst.
        rewrite Zlength_app_cons. lia.
      * rewrite H_copy_dst_2.
        rewrite !replace_Znth_Znth.
        rewrite Hcopy_mem.
        rewrite Hreplace_current, Hwords, Hsuffix.
        replace ii with (Zlength raw_prefix) by lia.
        symmetry.
        assert (Htail : copied ++ x :: rest0 = (copied +:: x) ++ rest0).
        { change (copied ++ ((x :: nil) ++ rest0) =
            (copied ++ (x :: nil)) ++ rest0).
          apply app_assoc. }
        rewrite Htail.
        apply (binary_watch_write_identity_p6
          raw_prefix scan_current (copied +:: x) rest0).
      * rewrite H_copy_dst_2.
        rewrite !replace_Znth_Znth.
        rewrite Hcopy_mem. reflexivity.
  - change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i_2.
    unfold_arch.
    cbn in H_endvar, H_i_2.
    nia.
Qed.

Lemma proof_of_solver_propagate_entail_wit_18_2_unit_conflict_copy :
  solver_propagate_entail_wit_18_2_unit_conflict_copy.
Proof.
  unfold solver_propagate_entail_wit_18_2_unit_conflict_copy.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  bind_fact ( i < endvar ) as H_i.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src_2 * sizeof ( PTR ) ) as H_i_2.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_dst_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  Exists (replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0)
    copy_memory_2) (copy_dst_2 + 1) (copy_src_2 + 1).
  entailer_with ltac:(lia).
  - sep_apply PtrArray.full_to_seg.
    sep_apply (PtrArray.seg_merge_to_seg begin 0 (copy_dst_2 + 1)
      (copy_src_2 + 1)) ; try lia.
    sep_apply (PtrArray.seg_merge_to_full begin 0 (copy_src_2 + 1)
      (Zlength source_words)) ; try lia.
    entailer_with ltac:(lia).
    unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
    destruct H_binary_watch_copy_progress as [copied [rest0
      [Hwords [Hkept [Hjj [Hsuffix [Hsrc [Hdst [Hmem Hlen]]]]]]]]].
    unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
    destruct H_propagation_watch_scan_physical as [_ [_ [_ [_ Hphysical_len]]]].
    assert (Hcopy_length :
      Zlength copy_memory_2 = Zlength source_words) by lia.
    assert (Hdst_length :
      copy_dst_2 + 1 <= Zlength copy_memory_2) by
      (rewrite Hcopy_length; lia).
    assert (Hsrc_length :
      copy_src_2 + 1 <= Zlength copy_memory_2) by
      (rewrite Hcopy_length; lia).
    pose proof (sublist_snoc_p6 copy_memory_2 0 copy_dst_2
      ltac:(lia) ltac:(lia)) as Hprefix.
    pose proof (sublist_snoc_p6 copy_memory_2 (copy_dst_2 + 1) copy_src_2
      ltac:(lia) ltac:(lia)) as Hmid.
    assert (Hvalue :
      Znth (copy_src_2 - (copy_dst_2 + 1))
        (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 +::
          Znth copy_src_2 copy_memory_2 0) 0 =
      Znth copy_src_2 copy_memory_2 0).
    { rewrite Hmid.
      rewrite Znth_sublist by lia.
      replace (copy_src_2 - (copy_dst_2 + 1) +
        (copy_dst_2 + 1)) with copy_src_2 by lia.
      reflexivity. }
    pose proof (replace_Znth_prefix_split_p6 copy_memory_2 copy_dst_2
      copy_src_2 (Zlength source_words) ltac:(lia) ltac:(lia) ltac:(lia)
      (eq_sym Hcopy_length)) as Hreplace.
    rewrite Hvalue, Hprefix, Hmid.
    rewrite <- Hreplace.
    entailer_with ltac:(lia).
    (* The goal already carries the arch constant, so there is nothing for a
              [rewrite sizeof_ptr] to rewrite; only the fold to the derived [ptr_size_Z]
              name the PtrArray lemmas use is needed. *)
    fold_arch.
    cbn.
    replace (begin + 0) with begin by lia.
    replace (Zlength source_words - 0) with (Zlength source_words) by lia.
    entailer_with ltac:(lia).
  (* arch port A05: the Arch pointer-size constant is opaque to micromega
     ("Cannot find witness"), so unfold it for the current arch below
     without naming a specific width. *)
    change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i_2.
    unfold_arch.
    cbn in H_endvar, H_i_2.
    nia.
  - unfold binary_watch_copy_progress in H_binary_watch_copy_progress |- *.
    destruct H_binary_watch_copy_progress as [copied [rest0
      [Hwords [Hkept [Hjj [Hsuffix [Hsrc [Hdst [Hmem Hlen]]]]]]]]].
    destruct rest0 as [|x rest0].
    + exfalso.
      unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
      destruct H_propagation_watch_scan_physical as [_ [_ [_ [_ Hphysical_len]]]].
      subst raw_suffix.
      rewrite Hwords, Zlength_app, Zlength_cons, Hkept in Hphysical_len.
      rewrite <- Hphysical_len in H_endvar.
      rewrite H_endvar, H_i_2, Hsrc in H_i.
      rewrite app_nil_r in H_i, H_endvar, Hphysical_len, Hwords, H_rest.
      assert (Hidx : ii + 1 + Zlength copied =
        ii + Z.succ (Zlength copied)) by lia.
      rewrite Hidx in H_i.
      lia.
    + destruct Hjj as [Hjj0 Hjjle].
      exists (copied ++ (x :: nil)), rest0.
      repeat split.
      * exact Hwords.
      * exact Hkept.
      * exact Hjj0.
      * exact Hjjle.
      * rewrite Hsuffix.
        change (copied ++ x :: rest0 = (copied ++ (x :: nil)) ++ rest0).
        replace (x :: rest0) with ((x :: nil) ++ rest0) by reflexivity.
        apply app_assoc.
      * rewrite Hsrc.
        rewrite Zlength_app_cons. lia.
      * rewrite Hdst.
        rewrite Zlength_app_cons. lia.
      * assert (Hsource_watch : copy_src_2 < Zlength watch_memory).
        { rewrite Hwords, Hsuffix.
          rewrite !Zlength_app.
          rewrite !Zlength_cons.
          pose proof (Zlength_nonneg rest0) as Hrest0_nonneg.
          rewrite Hkept, Hsrc.
          rewrite !Zlength_app.
          rewrite !Zlength_cons.
          lia. }
        assert (Hsource_base_bound :
          copy_src_2 <
            Zlength (replace_Znth jj scan_current watch_memory)).
        { rewrite Zlength_replace_Znth. exact Hsource_watch. }
        assert (Hsource_value :
          Znth copy_src_2 copy_memory_2 0 =
          Znth copy_src_2
            (replace_Znth jj scan_current watch_memory) 0).
        { rewrite Hmem.
          apply binary_watch_write_read_after_p6; lia. }
        assert (Hsource_base :
          Znth copy_src_2
            (replace_Znth jj scan_current watch_memory) 0 = x).
        { pose proof (Zlength_nonneg copied) as Hcopied_nonneg.
          pose proof (Zlength_nonneg raw_prefix) as Hprefix_nonneg.
          assert (Hsrc_nonneg : 0 <= copy_src_2) by
            (rewrite Hsrc, <- Hkept; lia).
          assert (Hjj_bound : 0 <= jj < Zlength watch_memory) by lia.
          assert (Hsrc_bound :
            0 <= copy_src_2 < Zlength watch_memory) by lia.
          assert (Hjj_src : jj <> copy_src_2) by lia.
          rewrite (Znth_replace_Znth_Diff 0 watch_memory jj
            copy_src_2 scan_current Hjj_bound Hsrc_bound Hjj_src).
          rewrite Hwords, Hsuffix.
          rewrite app_Znth2 by (rewrite Hkept; lia).
          rewrite Hkept, Hsrc.
          replace (ii + 1 + Zlength copied - ii) with
            (1 + Zlength copied) by lia.
          rewrite Znth_cons by lia.
          replace (1 + Zlength copied - 1) with
            (Zlength copied) by lia.
          rewrite app_Znth2 by lia.
          replace (Zlength copied - Zlength copied) with 0 by lia.
          simpl. reflexivity. }
        rewrite Hsource_value, Hsource_base, Hmem, Hdst.
        symmetry. apply msat_binary_watch_write_snoc.
      * rewrite Zlength_replace_Znth. exact Hlen.
  - change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i_2.
    unfold_arch.
    cbn in H_endvar, H_i_2.
    nia.
Qed.

Lemma proof_of_solver_propagate_entail_wit_19_unit_conflict : solver_propagate_entail_wit_19_unit_conflict.
Proof.
  unfold solver_propagate_entail_wit_19_unit_conflict.
  unfold stats_propagations, stats_inspects.
  aggressive_pre_process.
  bind_fact ( propagation_unit_conflict_transition n F A_arr K Mscan p scan_current prob_route learnt_route
      retained_route Mroute ) as H_propagation_unit_conflict_transition.
  bind_fact ( propagation_scan_conflict_step source_words retained moved rest copy_memory garbage_route retained_route
      ) as H_propagation_scan_conflict_step.
  bind_fact ( propagation_watch_scan_physical source_words retained_route moved nil garbage_route copy_memory (Zlength
      source_words) (Zlength retained_route) ) as H_propagation_watch_scan_physical.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical_2.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src copy_dst
      copy_memory ) as H_binary_watch_copy_progress.
  unfold propagation_unit_conflict_transition in H_propagation_unit_conflict_transition.
  destruct H_propagation_unit_conflict_transition as [HMroute Hsem].
  unfold propagation_scan_conflict_step in H_propagation_scan_conflict_step.
  destruct H_propagation_scan_conflict_step as [Hretained Hphysical].
  unfold propagation_watch_scan_physical in Hphysical, H_propagation_watch_scan_physical,
      H_propagation_watch_scan_physical_2.
  destruct Hphysical as [Hinv_final
    [Hmemory_final [Hkept_final [Hprefix_final Hmemory_length]]]].
  destruct H_propagation_watch_scan_physical_2 as [Hinv_old
    [Hmemory_old [Hkept_old [Hprefix_old Hmemory_old_length]]]].
  unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
  destruct H_binary_watch_copy_progress as [copied [copy_rest Hcopy]].
  destruct Hcopy as [Hwords [Hkept [Hbounds [Hsuffix
    [Hsrc [Hdst [Hcopy_memory Hcopy_length]]]]]]].
  unfold wlist_scan_inv in Hinv_final, Hinv_old.
  assert (Hsource_final : Zlength source_words =
      Zlength retained_route + Zlength moved).
  { pose proof (Zlength_perm_eq _ _ _ Hinv_final) as Hlen.
    rewrite !Zlength_app in Hlen. cbn in Hlen. lia. }
  assert (Hsource_positive : 0 < Zlength source_words).
  { pose proof (Zlength_perm_eq _ _ _ Hinv_old) as Hlen.
    rewrite H_rest in Hlen.
    rewrite !Zlength_app in Hlen.
    rewrite Zlength_cons in Hlen. cbn in Hlen.
    pose proof (Zlength_nonneg retained).
    pose proof (Zlength_nonneg moved).
    pose proof (Zlength_nonneg raw_suffix). lia. }
  change (sizeof (PTR)) with ptr_size_Z in *.
  (* [sizeof_ptr] yields the Arch constant, which micromega cannot delta-reduce, so
          this cancellation reported "Cannot find witness".  [unfold_arch] reduces it for
          whatever arch is current, naming no width. *)
  unfold_arch.
  assert (Hcopy_src : copy_src = Zlength source_words) by nia.
  assert (Hsource_raw : Zlength source_words =
      ii + 1 + Zlength raw_suffix).
  { rewrite <- Hmemory_old_length, Hwords.
    rewrite !Zlength_app. rewrite Zlength_cons, Hkept. lia. }
  assert (Hcopied_raw : Zlength copied = Zlength raw_suffix) by lia.
  assert (Hretained_length : Zlength retained_route =
      jj + 1 + Zlength raw_suffix).
  { rewrite Hretained, Zlength_app, H_rest, Zlength_cons, Hkept_old.
    lia. }
  assert (Hcopy_dst : copy_dst = Zlength retained_route) by lia.
  assert (Hretained_bound : Zlength retained_route <= Zlength source_words).
  { pose proof (Zlength_nonneg moved). lia. }
  Left.
  Exists trl_route rsn_route (Znth 2 (ms_stats Mroute) 0)
    (ms_simpdb_props Mroute)
    scan_caps_pre scan_wcap scan_caps_post scan_wm_pre scan_wm_post
    (retained ++ rest) source_words moved garbage_route copy_memory
    (Zlength source_words) (Zlength retained_route)
    retained_route (@nil Z) Mentry.
  Exists Mroute levels_entry.
  split_pure_spatial.
  - unfold solver_propagation_scan_core_at.
    rewrite HMroute.
    unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update.
    cbn. unfold PtrArray.seg, stats_propagate_scan.
    set_String_name. sepcon_assoc_change. sepcon_cancel.
    subst_all_strings.
    exact (stats_propagate_scan_refold__propagate
      s_pre (Znth 2 (ms_stats Mscan) 0) (ms_stats Mscan)).
  - split_pures; dump_pre_spatial;
      try exact Hsem; try assumption; try reflexivity; try tauto;
      try (rewrite app_nil_r; congruence); try nia;
      try rewrite HMroute;
      try unfold msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update;
      cbn; try assumption; try reflexivity; try tauto; try nia.
Qed.

Lemma proof_of_solver_propagate_entail_wit_21_1_binary_keep : solver_propagate_entail_wit_21_1_binary_keep.
Proof.
  unfold solver_propagate_entail_wit_21_1_binary_keep.
  unfold stats_propagations, stats_inspects.
  msat_propagate_binary_keep_p6.
Qed.

Lemma proof_of_solver_propagate_entail_wit_21_2_binary_keep : solver_propagate_entail_wit_21_2_binary_keep.
Proof.
  unfold solver_propagate_entail_wit_21_2_binary_keep.
  unfold stats_propagations, stats_inspects.
  msat_propagate_binary_keep_p6.
Qed.

Lemma proof_of_solver_propagate_entail_wit_21_3_binary_keep : solver_propagate_entail_wit_21_3_binary_keep.
Proof.
  unfold solver_propagate_entail_wit_21_3_binary_keep.
  unfold stats_propagations, stats_inspects.
  msat_propagate_binary_keep_p6.
Qed.

Lemma proof_of_solver_propagate_entail_wit_21_4_binary_keep : solver_propagate_entail_wit_21_4_binary_keep.
Proof.
  unfold solver_propagate_entail_wit_21_4_binary_keep.
  unfold stats_propagations, stats_inspects.
  msat_propagate_binary_keep_p6.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_1_real_satisfied : solver_propagate_entail_wit_22_1_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_1_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_2_real_satisfied : solver_propagate_entail_wit_22_2_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_2_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_3_real_satisfied : solver_propagate_entail_wit_22_3_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_3_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_4_real_satisfied : solver_propagate_entail_wit_22_4_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_4_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_5_real_satisfied : solver_propagate_entail_wit_22_5_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_5_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_6_real_satisfied : solver_propagate_entail_wit_22_6_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_6_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_7_real_satisfied : solver_propagate_entail_wit_22_7_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_7_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_8_real_satisfied : solver_propagate_entail_wit_22_8_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_8_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_9_real_satisfied : solver_propagate_entail_wit_22_9_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_9_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

(* ===== solver_propagate partial_solve wits (7 proofs) ===== *)
Lemma proof_of_solver_propagate_partial_solve_wit_440_capacity_same_pure :
  solver_propagate_partial_solve_wit_440_capacity_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_440_capacity_same_pure.
  unfold stats_propagations.
  msat_propagate_scan_length_close_p6 source_words retained moved rest garbage
    watch_memory ii jj H_scan candidate_post_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_441_capacity_move_pure :
  solver_propagate_partial_solve_wit_441_capacity_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_441_capacity_move_pure.
  unfold stats_propagations.
  msat_propagate_scan_length_close_p6 source_words retained moved rest garbage
    watch_memory ii jj H_scan candidate_post_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_471_unit_same_pure :
  solver_propagate_partial_solve_wit_471_unit_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_471_unit_same_pure.
  unfold stats_propagations.
  msat_propagate_scan_length_close_p6 source_words retained moved rest garbage
    watch_memory ii jj H_scan candidate_post_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_472_unit_move_pure :
  solver_propagate_partial_solve_wit_472_unit_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_472_unit_move_pure.
  unfold stats_propagations.
  msat_propagate_scan_length_close_p6 source_words retained moved rest garbage
    watch_memory ii jj H_scan candidate_post_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_473_unit_conflict_copy_pure :
  solver_propagate_partial_solve_wit_473_unit_conflict_copy_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_473_unit_conflict_copy_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src * sizeof ( PTR ) ) as H_i.
  assert (Hlt : copy_src < Zlength source_words).
  { assert (copy_src = Zlength source_words \/ copy_src < Zlength source_words)
      as [Heq | Hlt2] by lia.
    - rewrite Heq in H_i. rewrite <- H_endvar in H_i. lia.
    - exact Hlt2. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_479_unit_same_pure :
  solver_propagate_partial_solve_wit_479_unit_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_479_unit_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_length_close_p6 source_words retained moved rest garbage
    watch_memory ii jj H_scan candidate_post_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_480_unit_move_pure :
  solver_propagate_partial_solve_wit_480_unit_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_480_unit_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_length_close_p6 source_words retained moved rest garbage
    watch_memory ii jj H_scan candidate_post_memory.
Qed.

(* ===== solver_record which_implies wits (1 proofs) ===== *)
Lemma proof_of_solver_record_which_implies_wit_6 : solver_record_which_implies_wit_6.
Proof.
  Unfold.
  right. intros.
  unfold solver_rep_levels_wl_at.
  Intros act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_record_finish_frame_at.
  Exists act asg opos rsn trl tgs.
  unfold solver_fp_rep, solver_vecs_rep, solver_ptrs_rep,
    solver_var_arrays_rep, solver_levels_slice_at,
    stats_rep, stats_record_frame, db_words.
  entailer_with ltac:(lia).
  csimpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_search partial_solve wits (24 proofs) ===== *)
Lemma proof_of_solver_search_partial_solve_wit_197_pure : solver_search_partial_solve_wit_197_pure.
Proof.
  msat_search_model_ready_size_p6 n F A_arr A_inst Mselected H_ready.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_198_pure : solver_search_partial_solve_wit_198_pure.
Proof.
  msat_search_model_ready_size_p6 n F A_arr A_inst Mselected H_ready.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_199_pure : solver_search_partial_solve_wit_199_pure.
Proof.
  msat_search_model_ready_size_p6 n F A_arr A_inst Mselected H_ready.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_200_pure : solver_search_partial_solve_wit_200_pure.
Proof.
  msat_search_model_ready_size_p6 n F A_arr A_inst Mselected H_ready.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_201_pure : solver_search_partial_solve_wit_201_pure.
Proof.
  msat_search_model_ready_size_p6 n F A_arr A_inst Mselected H_ready.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_204_pure : solver_search_partial_solve_wit_204_pure.
Proof.
  Unfold.
  left; intros.
  unfold veci_rep, veci_rep_at.
  Intros model_ptr learnt_ptr.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_partial_solve_wit_211_pure : solver_search_partial_solve_wit_211_pure.
Proof.
  Unfold.
  left; intros.
  unfold veci_rep, veci_rep_at.
  Intros learnt_ptr.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_partial_solve_wit_236_pure : solver_search_partial_solve_wit_236_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_237_pure : solver_search_partial_solve_wit_237_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_238_pure : solver_search_partial_solve_wit_238_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_239_pure : solver_search_partial_solve_wit_239_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_240_pure : solver_search_partial_solve_wit_240_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_241_pure : solver_search_partial_solve_wit_241_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_242_pure : solver_search_partial_solve_wit_242_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_243_pure : solver_search_partial_solve_wit_243_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_244_pure : solver_search_partial_solve_wit_244_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_245_pure : solver_search_partial_solve_wit_245_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_246_pure : solver_search_partial_solve_wit_246_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_247_pure : solver_search_partial_solve_wit_247_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_248_pure : solver_search_partial_solve_wit_248_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_249_pure : solver_search_partial_solve_wit_249_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_250_pure : solver_search_partial_solve_wit_250_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_251_pure : solver_search_partial_solve_wit_251_pure.
Proof.
  msat_search_selection_leaves_p6 n F A_arr A_inst retval Mselected H_sel.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_252_pure : solver_search_partial_solve_wit_252_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

(* ===== solver_solve which_implies wits ===== *)
Lemma proof_of_solver_solve_which_implies_wit_12 : solver_solve_which_implies_wit_12.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur ) as H_msolver_inv_assuming_strong.
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hweak.
  pose proof (msa_trail_wf Hweak) as Hwf.
  pose proof (msa_shape Hweak) as Hshape.
  assert (Hcurrent_wf : lit_wf_c n (Znth k raw 0)).
  { eapply Forall_Znth_elim; eauto. }
  assert (Hvar_range : 0 <= lit_var_c (Znth k raw 0) < n)
    by (apply lit_var_c_in_range; exact Hcurrent_wf).
  assert (Hmissing : ~ In (lit_var_c (Znth k raw 0))
      (map lit_var_c (mt_trail (ms_core Mcur)))).
  { intro Hin.
    apply (proj2 (mtw_assigned_iff Hwf _ Hvar_range)) in Hin.
    contradiction. }
  assert (Htrail_lits :
      Forall (lit_wf_c n)
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil))).
  { apply Forall_app. split; [exact (mtw_trail_lits Hwf)|].
    constructor; [exact Hcurrent_wf|constructor]. }
  assert (Htrail_nodup :
      NoDup (map lit_var_c
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)))).
  { rewrite map_app. simpl. apply NoDup_snoc.
    - exact (mtw_trail_nodup Hwf).
    - exact Hmissing. }
  assert (Htrail_lt : Zlength (mt_trail (ms_core Mcur)) < n).
  { pose proof (msat_map_lit_var_c_in_range n
      (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)) Htrail_lits) as Hall.
    pose proof (NoDup_Z_bounded_length
      (map lit_var_c
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)))
      n (mtw_n_nonneg Hwf) Htrail_nodup Hall) as Hle.
    assert (Hle' : Zlength
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)) <= n).
    { rewrite map_length in Hle. rewrite Zlength_correct. exact Hle. }
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hle'. lia. }
  assert (Hlim_le : Zlength (mt_lim (ms_core Mcur)) <=
      Zlength (mt_trail (ms_core Mcur))).
  { eapply strict_sorted_bounded_length__solve.
    - apply Zlength_nonneg.
    - exact (mtw_lim_sorted Hwf).
    - exact (mtw_lim_range Hwf). }
  assert (Henqueue : enqueue_input n (Znth k raw 0) (ms_qtail Mcur)
      (mt_assigns (ms_core Mcur)) (mt_levels (ms_core Mcur))
      (ms_reason_words Mcur) (mt_trail (ms_core Mcur))).
  { unfold enqueue_input.
    unfold solver_shape in Hshape.
    rewrite <- (msa_size Hweak) in Hshape.
    split; [exact Hcurrent_wf|].
    repeat split; try tauto; try lia.
    pose proof (mtw_cells Hwf) as Hcells. revert Hcells.
    apply Forall_impl. intros x Hx. unfold lbool_cell in Hx.
    destruct Hx as [Hx|[Hx|Hx]]; subst x; lia. }
  unfold assumption_fresh_ready.
  entailer_with ltac:(lia);
    try exact Henqueue;
    try rewrite <- (msa_size Hweak); reflexivity.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_13 : solver_solve_which_implies_wit_13.
Proof.
  Unfold. left; intros.
  rename n_solver_solve_spec into n.
  bind_fact (assumption_fresh_ready n raw k Mcur) as Hready.
  pose proof Hready as Hparts.
  unfold assumption_fresh_ready in Hparts.
  destruct Hparts as (Hsize & Hdrain & Hfresh & Hlim & Henqueue).
  subst n.
  unfold solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  unfold enqueue_state_at, solver_assume_frame_wl,
    solver_enqueue_frame_with_scalars_wl, solver_enqueue_cells_at,
    solver_assume_scalars_frame, solver_enqueue_vecs_frame,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
    solver_trail_array_rep, solver_levels_slice_at.
  Exists rsn trl act opos tgs.
  rewrite Hdrain.
  entailer_with ltac:(lia);
    unfold solver_shape in *; try tauto; try lia.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_14 : solver_solve_which_implies_wit_14.
Proof.
  Unfold. left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  bind_fact ( msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur ) as H_msolver_inv_assuming_strong.
  bind_fact ( assumption_fresh_ready n raw k Mcur ) as H_assumption_fresh_ready.
  bind_fact ( ms_capacity_root_propagation_pending Mcur = 0 ) as H_ms_capacity_root_propagation_pending.
  replace (k - 0) with k by lia.
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hweak.
  pose proof (msa_shape Hweak) as Hshape.
  pose proof H_assumption_fresh_ready as Hready.
  unfold assumption_fresh_ready in Hready.
  destruct Hready as [Hsize [Hdrain [Hfresh [Hlevelroom Henq]]]].
  pose proof Henq as Henq'. unfold enqueue_input in Henq'.
  destruct Henq' as [Hlit [Htwice [Haslen [Hlvlen [Hrslen
    [Htrlen [Hqrange [Hroom Hcells]]]]]]]].
  assert (Hroomcap : ms_qtail Mcur < ms_cap Mcur).
  { specialize (Hroom Hfresh). unfold solver_shape in Hshape. lia. }
  pose proof (assume_post_refold_assigns_levels__solve
    solve_wl s values levels_ptr (Znth k raw 0)
    n (ms_cap Mcur) (ms_qtail Mcur)
    (mt_assigns (ms_core Mcur)) (mt_levels (ms_core Mcur))
    (ms_reason_words Mcur) (mt_trail (ms_core Mcur))
    (mt_lim (ms_core Mcur)) (ms_lim_cap Mcur) Mcur) as Hrefold.
  specialize (Hrefold
    (msa_size Hweak) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    Hshape Hroomcap H_ms_capacity_root_propagation_pending Hdrain Hfresh).
  sep_apply Hrefold.
  Intros lim_cap_next.
  lazymatch goal with
  | Hentry : solver_query_reuse ?entry Mcur |- _ =>
      assert (Hreuse_assume : solver_query_reuse entry
          (msolver_assume Mcur (Znth k raw 0) lim_cap_next))
        by (intro Hpublic;
            exact (minisat_base_watch_completed_assume__api_reentry
              n Mcur (Znth k raw 0) lim_cap_next
              (msa_db_wf Hweak) (msa_trail_wf Hweak) Hlit Hfresh
              (Hentry Hpublic)))
  end.
  Exists lim_cap_next (msolver_assume Mcur (Znth k raw 0) lim_cap_next).
  entailer_with ltac:(lia).
  eapply assumption_fresh_transition_intro__solve; eauto.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_15 : solver_solve_which_implies_wit_15.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( assumption_fresh_transition n F A_arr raw k lim_cap_next Mcur Mdecide ) as H_assumption_fresh_transition.
  unfold assumption_fresh_transition in H_assumption_fresh_transition.
  destruct H_assumption_fresh_transition as (_ & _ & Hinv & Hseed).
  unfold solver_propagate_pre.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_16 : solver_solve_which_implies_wit_16.
Proof.
  Unfold.
  left; intros.
  unfold solver_propagate_post.
  apply derivable1_orp_elim.
  - apply derivable1_orp_elim.
    + Intros Mdone.
      rewrite <- derivable1_orp_intros1.
      rewrite <- derivable1_orp_intros1.
      entailer_with ltac:(lia). Exists Mdone. entailer_with ltac:(lia).
    + Intros Mconf p focus C.
      rewrite <- derivable1_orp_intros1.
      rewrite <- derivable1_orp_intros2.
      entailer_with ltac:(lia). Exists Mconf p focus C. entailer_with ltac:(lia).
  - rewrite <- derivable1_orp_intros2.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_17 : solver_solve_which_implies_wit_17.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename M_solver_solve_spec into M.
  bind_fact (ms_cap Mdecide = ms_cap M) as Hentry_cap.
  bind_fact (solver_query_reuse M Mdecide) as Hentry_reuse.
  assert (Hstatus : propagation_status = 1) by lia.
  subst propagation_status.
  unfold solver_propagate_post.
  Split.
  - Split.
    + Intros Mprop.
      match goal with
      | H : solver_propagation_inv _ _ _ _ _ /\ _ |- _ =>
          destruct H as (Hinv & Hcaller & Hreuse & Hseed & Hdrained)
      end.
      assert (Hcap : ms_cap Mprop = ms_cap M).
      { unfold propagation_caller_frame in Hcaller. intuition congruence. }
      assert (Hquery_reuse : solver_query_reuse M Mprop).
      { intro Hentry. exact ((proj1 Hreuse) (Hentry_reuse Hentry)). }
      pose proof Hinv as Hinv_copy.
      destruct Hinv_copy as (Hpending & Hprop).
      assert (Hstrong : msolver_inv_assuming_strong n F A_arr
        (assumption_prefix raw (k + 1)) Mprop).
      { eapply solver_propagation_drained_assuming_strong; eauto. }
      sep_apply (store_int_undef_store_int &("propagation_status") 1).
      Exists Mprop.
      unfold assumption_propagation_success.
      entailer_with ltac:(lia).
    + Intros Mbad pbad focusbad Cbad. Intros. cancel. exfalso; lia.
  - Intros Mcap. Intros. cancel. exfalso; lia.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_18 : solver_solve_which_implies_wit_18.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( assumption_propagation_success n F A_arr raw (k + 1) Mprop ) as H_assumption_propagation_success.
  unfold assumption_propagation_success in H_assumption_propagation_success.
  destruct H_assumption_propagation_success as (Hstrong & Hdrained & Hpending & Hseed).
  pose proof (msas_weak Hstrong) as Hweak.
  assert (Hsize : ms_size Mprop = n) by
    (pose proof (msa_size Hweak); lia).
  pose proof (msa_shape Hweak) as Hshape.
  subst n.
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_assigns_focus_frame_wl_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  Exists act opos rsn trl tgs.
  entailer_with ltac:(lia);
    unfold solver_shape in Hshape; lia.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_19 : solver_solve_which_implies_wit_19.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename M_solver_solve_spec into M.
  bind_fact (ms_cap Mdecide = ms_cap M) as Hentry_cap.
  bind_fact (solver_query_reuse M Mdecide) as Hentry_reuse.
  assert (Hstatus : propagation_status = 0) by lia.
  subst propagation_status.
  unfold solver_propagate_post.
  Split.
  - Split.
    + Intros Mbad. Intros. cancel. exfalso; lia.
    + Intros Mconf p focus Cconf.
      match goal with
      | H : propagation_cancel_ready _ _ _ _ _ _ /\ _ |- _ =>
          destruct H as (Hready & Hcaller & Hwatch & Hresident & Hseed & Hcert & Hptr)
      end.
      assert (Hcap : ms_cap Mconf = ms_cap M).
      { unfold propagation_caller_frame in Hcaller. intuition congruence. }
      assert (Hquery_watch : solver_query_reuse_guard M ->
        minisat_watch_conflict_ready n Mconf).
      { intro Hentry. exact (Hwatch (Hentry_reuse Hentry)). }
      sep_apply (store_int_undef_store_int &("propagation_status") 0).
      Exists p Cconf focus Mconf.
      entailer_with ltac:(lia).
  - Intros Mcap. Intros. cancel. exfalso; lia.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_20 : solver_solve_which_implies_wit_20.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( propagation_cancel_ready n F A_arr (PropagationAssuming (assumption_prefix raw (k + 1))) Mconf focus )
      as H_propagation_cancel_ready.
  bind_fact ( propagation_conflict_cert n F Mconf Cconf ) as H_propagation_conflict_cert.
  pose proof H_propagation_cancel_ready as Hready.
  unfold propagation_cancel_ready in Hready.
  destruct Hready as (Hweak & Hprop & Hlit & Hprocessed & Hlevel &
    Hfront & Hheap & Hcovers & Hreasonless).
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as (Hpending & Hassuming).
  cbn in Hassuming.
  destruct H_propagation_conflict_cert as (Hentails & Hfalse & Hwf & Hnodup & Hlevelmax).
  assert (Hsize : ms_size Mconf = n) by
    (pose proof (msa_size Hassuming); lia).
  assert (Hunsat : cnf_unsat n (cnf_with_units F A_arr)).
  { eapply assuming_conflict_unsat; eauto. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_21 : solver_solve_which_implies_wit_21.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( propagation_cancel_ready n F A_arr (PropagationAssuming (assumption_prefix raw (k + 1))) Mconf focus )
      as H_propagation_cancel_ready.
  pose proof H_propagation_cancel_ready as Hready.
  unfold propagation_cancel_ready in Hready.
  destruct Hready as (Hpropagation & Hlevel & Hlit & Hprocessed & Hfront &
    Hheapcovers & Hreasonless).
  destruct Hreasonless as (Hheap & Hcovers & Hreasonless).
  unfold solver_propagation_weak in Hpropagation.
  destruct Hpropagation as (Hpending & Hweak).
  cbn in Hweak.
  pose proof (msa_size Hweak) as Hsize.
  assert (Hcancel : cancel_bound_ready Mconf 0).
  { unfold cancel_bound_ready.
    destruct (Z_lt_ge_dec 0 (Zlength (mt_lim (ms_core Mconf)))).
    - right. unfold prop_level in Hlevel.
      apply (Forall_Znth_elim Z
        (fun b => b <= mt_qhead (ms_core Mconf))
        (mt_lim (ms_core Mconf)) 0 0 Hlevel). lia.
    - left. pose proof (Zlength_nonneg (mt_lim (ms_core Mconf))). lia. }
  sep_apply (solver_rep_assigns_levels_cancel_split s Mconf values levels_ptr solve_wl_solver_solve_spec).
  sep_apply (store_ptr_undef_store_ptr &("values") values).
  unfold solver_cancel_pre.
  entailer_with ltac:(lia);
    try exact (msa_shape Hweak);
    try (rewrite <- Hsize; exact (msa_trail_wf Hweak));
    try exact Hcancel;
    try (rewrite <- Hsize; exact Hheap);
    pose proof (Zlength_nonneg (mt_lim (ms_core Mconf))); lia.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_22 : solver_solve_which_implies_wit_22.
Proof.
  Unfold. left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  rename M_solver_solve_spec into M.
  bind_fact (propagation_cancel_ready n F A_arr
    (PropagationAssuming (assumption_prefix raw (k + 1))) Mconf focus) as Hready.
  bind_fact (solver_query_reuse_guard M -> minisat_watch_conflict_ready n Mconf) as Hreuse.
  bind_fact (minisat_resident_false_clause Mconf) as Hfalse.
  bind_fact (msolver_seed_shadow Mconf) as Hseed.
  bind_fact (ms_size Mconf = n) as Hsize.
  unfold solver_cancel_post.
  Split.
  - Intros.
    assert (Hdepth : Zlength (mt_lim (ms_core Mconf)) = 0).
    { pose proof (Zlength_nonneg (mt_lim (ms_core Mconf))). lia. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mconf /\ solver_query_reentry n F Mconf /\ msolver_seed_shadow Mconf).
    { intro Hentry.
      pose proof (solver_propagation_conflict_base_recovery__api_reentry
        n F A_arr (PropagationAssuming (assumption_prefix raw (k + 1)))
        Mconf focus Hready (Hreuse Hentry) Hfalse Hdepth) as Hbase.
      split; [exact Hbase|]. split; [|exact Hseed].
      exact (solver_base_recovery_false_reentry__api_reentry
        n F Mconf Hbase Hfalse). }
    Exists Mconf. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep s Mconf levels_ptr solve_wl).
      entailer_with ltac:(lia).
    + entailer_with ltac:(lia).
  - Intros orderpos order order_cap.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hreinserted).
    set (Mpost := msolver_cancel_project Mconf 0 orderpos order order_cap
      (ms_root_level Mconf)).
    assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mconf))) by lia.
    assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
    { rewrite <- Hsize. exact Hheap. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mpost /\ solver_query_reentry n F Mpost /\ msolver_seed_shadow Mpost).
    { intro Hentry.
      destruct (solver_conflict_cancel_zero_base_recovery__api_reentry
        n F A_arr (PropagationAssuming (assumption_prefix raw (k + 1)))
        Mconf focus orderpos order order_cap Hready (Hreuse Hentry)
        Hseed Hpositive Hcap Hheap_n Hincl Hreinserted)
        as [Hbase [_ Hseed_post]].
      split; [exact Hbase|]. split; [|exact Hseed_post].
      exact (solver_cancel_project_reentry__api_reentry
        n F Mconf orderpos order order_cap (ms_root_level Mconf) Hbase). }
    Exists Mpost. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + unfold Mpost.
      sep_apply (solver_cancel_project_join_rep s Mconf levels_ptr 0
        orderpos order order_cap (ms_root_level Mconf) solve_wl).
      entailer_with ltac:(lia).
    + unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
      cbn. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_26 : solver_solve_which_implies_wit_26.
Proof.
  Unfold. left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact (msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur) as Hstrong.
  pose proof (msas_weak Hstrong) as Hweak.
  pose proof (msa_size Hweak) as Hsize.
  pose proof (msas_prop_level Hstrong) as Hprop.
  assert (Hcancel : cancel_bound_ready Mcur 0).
  { unfold cancel_bound_ready.
    destruct (Z_lt_ge_dec 0 (Zlength (mt_lim (ms_core Mcur)))).
    - right. unfold prop_level in Hprop.
      apply (Forall_Znth_elim Z
        (fun b => b <= mt_qhead (ms_core Mcur))
        (mt_lim (ms_core Mcur)) 0 0 Hprop). lia.
    - left. pose proof (Zlength_nonneg (mt_lim (ms_core Mcur))). lia. }
  assert (Htrail : mtrail_wf (ms_size Mcur) (ms_core Mcur))
    by (rewrite <- Hsize; exact (msa_trail_wf Hweak)).
  assert (Hheap : heap_wf (ms_size Mcur) (msolver_heap Mcur))
    by (rewrite <- Hsize; exact (msa_heap_wf Hweak)).
  subst n.
  unfold solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  sep_apply (store_ptr_undef_store_ptr &("values") values).
  unfold solver_cancel_pre, solver_cancel_owned, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at.
  Exists act values opos rsn trl tgs.
  pose proof (Zlength_nonneg (mt_lim (ms_core Mcur))).
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== veci_push return wits (1 proofs) ===== *)
Lemma proof_of_veci_push_return_wit_1 : veci_push_return_wit_1.
Proof.
  msat_push_return_close_p6.
Qed.

(* ===== veci_reserve entail wits (1 proofs) ===== *)
Lemma proof_of_veci_reserve_entail_wit_1 : veci_reserve_entail_wit_1.
Proof.
  aggressive_pre_process; msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== veci_reserve return wits (2 proofs) ===== *)
Lemma proof_of_veci_reserve_return_wit_1 : veci_reserve_return_wit_1.
Proof.
  msat_reserve_return_close_p6 cap.
Qed.

Lemma proof_of_veci_reserve_return_wit_2 : veci_reserve_return_wit_2.
Proof.
  Unfold.
  right.
  intros cap l p retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  subst cap.
  unfold vector_capacity_exhausted, minisat_max_growable_cap.
  rewrite IntArray.undef_seg_empty.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== veci_resize return wits (1 proofs) ===== *)
Lemma proof_of_veci_resize_return_wit_1 : veci_resize_return_wit_1.
Proof.
  aggressive_pre_process.
  - rewrite Zlength_sublist by lia.
    sep_apply_l_atomic
      (IntArray.seg_split_to_seg p 0 k_pre (Zlength l) l).
    + dump_pre_spatial. lia.
    + replace (k_pre - 0) with k_pre by lia.
      replace (Zlength l - 0) with (Zlength l) by lia.
      sep_apply_l_atomic (IntArray.seg_to_undef_seg p k_pre (Zlength l)
        (sublist k_pre (Zlength l) l)).
      sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_seg
        p k_pre (Zlength l) cap).
      * dump_pre_spatial. lia.
      * entailer_with ltac:(lia).
  - rewrite Zlength_sublist by lia. entailer_with ltac:(lia).
  - rewrite Zlength_sublist by lia. msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== vecp_push return wits (1 proofs) ===== *)
Lemma proof_of_vecp_push_return_wit_1 : vecp_push_return_wit_1.
Proof.
  msat_push_return_close_p6.
Qed.

(* ===== vecp_remove which_implies wits (2 proofs) ===== *)
Lemma proof_of_vecp_remove_which_implies_wit_2 : vecp_remove_which_implies_wit_2.
Proof.
  aggressive_pre_process;
    bind_fact ( vecp_remove_shift_inv e words0 found j words_now ) as H_vecp_remove_shift_inv;
    bind_fact ( j >= Zlength words_now - 1 ) as H_j;
    bind_fact ( j < Zlength words_now ) as H_j_2;
    pose proof
      (vecp_remove_shift_done__vecp_remove
        e words0 found j words_now H_vecp_remove_shift_inv H_j H_j_2)
      as Hdone.
  - destruct Hdone as (_ & _ & Heq). exact Heq.
  - destruct Hdone as (_ & Hlen & _). exact Hlen.
  - destruct Hdone as (Hfound & _). exact Hfound.
Qed.

Lemma proof_of_vecp_remove_which_implies_wit_3 : vecp_remove_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  bind_fact ( v = vecp_slot base index ) as H_v.
  bind_fact ( sublist 0 (Zlength words_now - 1) words_now = vecp_remove_result words0 found ) as H_sublist.
  rewrite H_sublist.
  subst wm. subst caps.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (index - Zlength pre) with 0 by lia.
  unfold replace_Znth. simpl.
  unfold wlists_rep.
  entailer_with ltac:(lia).
  - rewrite H_v.
    sep_apply (wlists_rep_from_insert_at base 0 index pre
      (vecp_remove_result words0 found) post capspre cap capspost
      ltac:(lia) ltac:(lia)).
    entailer_with ltac:(lia).
  - rewrite !Zlength_app, !Zlength_cons in *. lia.
Qed.

(* ===== vecp_reserve entail wits (1 proofs) ===== *)
Lemma proof_of_vecp_reserve_entail_wit_1 : vecp_reserve_entail_wit_1.
Proof.
  aggressive_pre_process; msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== vecp_reserve return wits ===== *)


Lemma proof_of_vecp_reserve_return_wit_2 : vecp_reserve_return_wit_2.
Proof.
  Unfold.
  right.
  intros cap l p retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  subst cap.
  unfold vector_capacity_exhausted, minisat_max_growable_cap.
  rewrite PtrArray.undef_seg_empty.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== vecp_resize return wits (1 proofs) ===== *)
Lemma proof_of_vecp_resize_return_wit_1 : vecp_resize_return_wit_1.
Proof.
  aggressive_pre_process.
  - rewrite Zlength_sublist by lia.
    sep_apply_l_atomic
      (PtrArray.seg_split_to_seg p 0 k_pre (Zlength l) l).
    + dump_pre_spatial. lia.
    + replace (k_pre - 0) with k_pre by lia.
      replace (Zlength l - 0) with (Zlength l) by lia.
      sep_apply_l_atomic (PtrArray.seg_to_undef_seg p k_pre (Zlength l)
        (sublist k_pre (Zlength l) l)).
      sep_apply_l_atomic (PtrArray.undef_seg_merge_to_undef_seg
        p k_pre (Zlength l) cap).
      * dump_pre_spatial. lia.
      * entailer_with ltac:(lia).
  - rewrite Zlength_sublist by lia. entailer_with ltac:(lia).
  - rewrite Zlength_sublist by lia. msat_manual_entailer_with ltac:(lia).
Qed.
