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

(* ============================================================================
   Part 5: manual VC proofs for act_clause_bump, act_clause_decay,
   act_clause_rescale, act_var_bump, act_var_rescale, clause_new, clause_remove,
   order_select, solver_analyze, solver_lit_removable, solver_propagate and
   solver_search. The [proof_of_*] obligations are grouped below by C
   function in that order, with a banner marking each family block.  The shared
   part-local [Ltac]/[Tactic Notation] definitions and helper lemmas for the
   [solver_analyze] clause-scan tag step and the [solver_propagate]
   capacity-copy / unit-conflict-copy families come first, ahead of every
   family block that calls them.  Other obligations of these functions
   belong to the other manual parts or the generated, engine-trusted
   [solver_qcp_proof_auto.v] lane and are out of this file's scope. *)

(* Part-local proof tactics for the groups of VC proofs below that were
   byte-identical before this pass; every member now calls the tactic with its
   own binders.  Note for anyone editing them: a [;] that follows a QCP tactic
   taking a [tactic] argument ([LLM_pre_process], [entailer_with]) has to be
   parenthesised, because that argument is parsed as a whole [ltac_expr] and an
   unguarded [;] is swallowed into it. *)

(* Read the tagged vector's bounds by its model projection.  The fresh heap
   order may place other vectors before it, so select the tagged payload. *)
Ltac msat_analyze_tagged_veci_open_p5 :=
  (LLM_pre_process ltac:(lia));
  match goal with
  | |- context [veci_rep ?v (ms_tagged ?M) (ms_tagged_cap ?M)] =>
      prop_apply_p (veci_rep_bounds__canceluntil_cap
        v (ms_tagged M) (ms_tagged_cap M))
  end;
  Intros_p Hbounds.

(* The [veci_rep_at] obligations of [solver_lit_removable] need nothing beyond
   unfolding the wrapper: every bound they ask for is already a pure fact of the
   precondition, so the entailer closes them outright. *)
Ltac msat_lit_removable_veci_at_close_p5 :=
  Unfold; left; intros; unfold veci_rep_at; entailer_with ltac:(lia).

(* [retval] is the variable of the literal read back from the reason row of the
   top stack entry; both of its bounds come from the two [lit_var_c] facts of
   the precondition, once [retval] is rewritten through its two defining
   equations.  [Hv] .. [Hhi] name the four bound facts at the call site. *)
Ltac msat_lit_removable_retval_var_bounds_p5 retval retval_7 stack_now M0 lrm_n Hv Hw Hlo Hhi :=
  bind_fact ( retval = lit_var_c retval_7 ) as Hv;
  bind_fact ( retval_7 = tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) ) as Hw;
  bind_fact ( 0 <= lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) ) as
      Hlo;
  bind_fact ( lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) < lrm_n )
      as Hhi;
  assert (Hretval_nonneg : 0 <= retval) by (rewrite Hv, Hw; exact Hlo);
  assert (Hretval_bound : retval < lrm_n) by (rewrite Hv, Hw; exact Hhi);
  entailer_with lia.

(* Range of the literal at the compaction index [i]: [Hfa] is the well-formedness
   of the compacted word list, and [2 * n <= INT_MAX] is dug out of the cancel
   invariant [Hcr] -- the solver shape carried by whichever arm of the analysis
   context [K] is in play. *)
Ltac msat_analyze_word_range_from_cancel_p5 n F A_arr K M focus words i Hfa Hcr :=
  bind_fact ( Forall (lit_wf_c n) words ) as Hfa;
  bind_fact ( analysis_cancel_ready n F A_arr K M focus ) as Hcr;
  assert (Hindex : 0 <= i < Zlength words) by lia;
  pose proof (Forall_Znth_elim _ _ _ 0 i Hfa Hindex) as Hlit;
  unfold lit_wf_c in Hlit;
  destruct Hlit as [Hlow Hhigh];
  unfold analysis_cancel_ready in Hcr;
  destruct Hcr as [Mbase [Hprop [Hequiv _]]];
  unfold propagation_cancel_ready in Hprop;
  destruct Hprop as [Hweak _];
  unfold solver_propagation_weak in Hweak;
  destruct Hweak as [_ Hweak];
  assert (Htwo_n : 2 * n <= INT_MAX) by
    (destruct K as [A_inst | A_proc]; cbn in Hweak;
     [ pose proof (msw_shape Hweak) as Hshape;
       pose proof (msw_size Hweak) as Hsize;
       unfold solver_shape in Hshape;
       destruct Hshape as [_ [_ [Htwo [_ [_ [_ [_ [_ [_ [Hlen _]]]]]]]]]];
       rewrite Hsize; exact Htwo
     | pose proof (msa_shape Hweak) as Hshape;
       pose proof (msa_size Hweak) as Hsize;
       unfold solver_shape in Hshape;
       destruct Hshape as [_ [_ [Htwo [_ [_ [_ [_ [_ [_ [Hlen _]]]]]]]]]];
       rewrite Hsize; exact Htwo ]);
  split_pures;
  [ dump_pre_spatial; replace (i - 0) with i by lia; exact Hlow
  | dump_pre_spatial; replace (i - 0) with i by lia; lia ].

(* Close a goal that is a right-nested conjunction whose leaves are precondition
   facts or [eq_refl]: the by-content replacement for the [exact (conj h.. ..)]
   terms the closers below used to spell with positionally named hypotheses. *)
Ltac msat_conj_from_facts_p5 :=
  repeat (lazymatch goal with |- _ /\ _ => split end);
  (assumption || reflexivity).

(* Close the two [order_select] sift-down return obligations (the [child] arm and
   the [child + 1] arm, whose statements differ only in which sibling wins the
   comparison).  Only the five state cells are passed; every other name is
   read off the shape of a precondition fact -- the sift invariant carries the
   eleven heap/trail binders, the two sibling-bound pairs carry [child], the seed
   equation carries the random-seed pair and the activity length carries the
   activity list.  The heap/orderpos arrays are refolded through
   [order_select_sift_close_post__order_select] and the two-slot activity window
   through [double_array_missing2_refold__vecp_remove]. *)
Ltac msat_order_select_sift_close_p5
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
      prop_apply (store_int_range
        (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap);
      Intros_p Hcap_range;
      prop_apply (IntArray.undef_seg_valid
        order_ptr (Zlength sift_heap_now) order_cap);
      Intros_p Hcap_room;
      sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
        (replace_Znth x i sift_orderpos_now));
      sep_apply_l_atomic (IntArray.full_to_seg order_ptr
        (Zlength sift_heap_now) (replace_Znth i x sift_heap_now));
      sep_apply_l_atomic (double_array_missing2_refold__vecp_remove
        activity_ptr (Znth child sift_heap_now 0)
        (Znth (child + 1) sift_heap_now 0) n activity0
        (conj Ha Hb) (conj Hc Hd) He);
      Exists sift_seed_shadow_now sift_seed_value_now
        (replace_Znth i x sift_heap_now) (replace_Znth x i sift_orderpos_now);
      unfold veci_rep, veci_rep_at,
        veci_size_addr, veci_cap_addr, veci_ptr_addr;
      Exists order_ptr;
      rewrite Zlength_replace_Znth;
      (entailer_with ltac:(lia));
      csimpl; entailer_with ltac:(lia)
  end.

(* Re-establish the three watcher cells of a unit-conflict copy step: the two
   pointer slots and the sign byte are handed back as initialised stores. *)
Ltac msat_propagate_unit_conflict_cells_p5 :=
  sep_apply store_ptr_undef_store_ptr;
  sep_apply store_ptr_undef_store_ptr;
  sep_apply store_char_undef_store_char;
  cancel.

(* Close the two [solver_propagate] unit-conflict watcher-copy obligations: the
   copied word is planted at [jj], the frame is re-established from the eight
   precondition facts the [lazymatch] binds by shape, and
   [binary_watch_copy_progress] is discharged with the empty "already copied"
   prefix.  [jj] is the only name passed: it is the copy cursor the right-hand
   side asks for and no precondition mentions it. *)
Ltac msat_propagate_unit_conflict_copy_close_p5 jj :=
  lazymatch goal with
  | Ha : ms_wm ?Mroute = ms_wm ?Mscan,
    Hb : ms_wcaps ?Mroute = ms_wcaps ?Mscan,
    Hg : ms_wm ?Mscan = ?scan_wm_pre ++ ?logical_words :: ?scan_wm_post,
    Hh : ms_wcaps ?Mscan = ?scan_caps_pre ++ ?scan_wcap :: ?scan_caps_post,
    Hf : ?logical_words = ?retained ++ ?rest,
    Hc : ?watch_memory = ?raw_prefix ++ ?scan_current :: ?raw_suffix,
    Hd : Zlength ?raw_prefix = ?ii,
    He : ?candidate_post_memory = ?watch_memory |- _ =>
      Exists (replace_Znth jj scan_current candidate_post_memory)
        (jj + 1) (ii + 1);
      (entailer_with ltac:(lia));
      try cancel;
      try lia;
      (msat_propagate_unit_conflict_cells_p5 || congruence || idtac);
      assert (Hprogress :
        binary_watch_copy_progress watch_memory raw_prefix scan_current
          raw_suffix ii jj (ii + 1) (jj + 1)
          (replace_Znth jj scan_current candidate_post_memory)) by
        (exists nil, raw_suffix;
         split; [exact Hc|];
         split; [exact Hd|];
         split; [lia|];
         split; [simpl; reflexivity|];
         split; [rewrite Zlength_nil; lia|];
         split; [rewrite Zlength_nil; lia|];
         split;
         [ rewrite He; simpl; reflexivity
         | rewrite He, Zlength_replace_Znth; reflexivity ]);
      exact Hprogress
  end.

(* Open the capacity-exhausted watcher-copy goal: split the literal array at the
   candidate slot, plant the copied word at the cursor [jj] and hand the frame to
   the entailer.  [rsn_scan] and [trl_scan] are the reason/trail witnesses the
   right-hand side asks for; every other name is read off a precondition fact. *)
Ltac msat_capacity_copy_open_p5 rsn_scan trl_scan jj :=
  lazymatch goal with
  | Hcand : ?candidate = Znth (?offset - 2)
              (sublist 2 (Zlength ?clause_contents) ?clause_contents) 0,
    Hlits : clause_lits_pointer ?scan_current ?lits,
    Hmem : ?watch_memory = ?raw_prefix ++ ?scan_current :: ?raw_suffix,
    Hkept : Zlength ?raw_prefix = ?ii,
    Hcopy : ?candidate_post_memory = ?watch_memory |- _ =>
      assert (Hoffset : 2 <= offset) by lia;
      sep_apply (IntArray.seg_split_to_missing_i lits 2 offset
        (Zlength clause_contents)
        (replace_Znth (offset - 2) candidate
          (sublist 2 (Zlength clause_contents) clause_contents)) 0); try lia;
      Exists rsn_scan trl_scan
        (replace_Znth jj scan_current candidate_post_memory) (jj + 1) (ii + 1);
      (entailer_with ltac:(lia))
  end.

(* The scan-open and capacity-target residues of the copy step: both are pure
   conjunctions of precondition facts, once the two wrappers are unfolded. *)
Ltac msat_capacity_copy_facts_p5 :=
  try unfold propagation_scan_open;
  try msat_conj_from_facts_p5;
  try (unfold propagation_capacity_target_facts, vector_capacity_exhausted,
    minisat_max_growable_cap;
    repeat split; try assumption; try reflexivity; lia);
  try unfold propagation_capacity_target_facts, vector_capacity_exhausted,
    minisat_max_growable_cap;
  try msat_conj_from_facts_p5.

(* The copy-progress residues: nothing has been copied yet, so the witness is the
   empty prefix and the whole remaining suffix, and the written memory is the
   candidate memory with the current word planted at [jj]. *)
Ltac msat_capacity_copy_progress_p5 jj :=
  try (lazymatch goal with
  | Hlits : clause_lits_pointer ?scan_current ?lits,
    Hmem : ?watch_memory = ?raw_prefix ++ ?scan_current :: ?raw_suffix,
    Hkept : Zlength ?raw_prefix = ?ii,
    Hcopy : ?candidate_post_memory = ?watch_memory |- _ =>
      unfold binary_watch_copy_progress;
      Exists nil raw_suffix; repeat split;
      try exact Hmem; try exact Hkept; try lia;
      try (simpl; reflexivity);
      try (simpl; rewrite Hcopy; reflexivity);
      try (rewrite Hcopy, Zlength_replace_Znth; reflexivity)
  end);
  try (lazymatch goal with
  | Hlits : clause_lits_pointer ?scan_current ?lits,
    Hmem : ?watch_memory = ?raw_prefix ++ ?scan_current :: ?raw_suffix,
    Hcopy : ?candidate_post_memory = ?watch_memory |- _ =>
      assert (Hsame :
        replace_Znth jj scan_current candidate_post_memory =
        replace_Znth jj scan_current watch_memory) by
        (rewrite Hcopy; reflexivity);
      assert (Hsamelen :
        Zlength (replace_Znth jj scan_current candidate_post_memory) =
        Zlength watch_memory) by
        (rewrite Hsame, Zlength_replace_Znth; reflexivity)
  end);
  try unfold binary_watch_copy_progress;
  try (lazymatch goal with
  | Hlits : clause_lits_pointer ?scan_current ?lits,
    Hmem : ?watch_memory = ?raw_prefix ++ ?scan_current :: ?raw_suffix,
    Hcopy : ?candidate_post_memory = ?watch_memory |- _ =>
      Exists nil raw_suffix; simpl
  end);
  try msat_conj_from_facts_p5.

(* Normalise the sign byte of the routed literal: the layout predicate asks for
   the byte and for its doubled-minus-one form, both of which are
   [signed_last_nbits] no-ops because [lit_sign_c] is 0 or 1. *)
Ltac msat_capacity_copy_sign_p5 :=
  try (lazymatch goal with
  | Hretval : ?retval = lit_sign_c ?candidate |- _ =>
      unfold propagation_scan_candidate_layout;
      repeat split; try assumption; try reflexivity;
      try (split; assumption);
      rewrite Hretval;
      assert (Hsign : signed_last_nbits (lit_sign_c candidate) 8 =
        lit_sign_c candidate) by
        (apply signed_last_nbits_eq;
        [lia | pose proof (lit_sign_c_range candidate); lia]);
      rewrite Hsign;
      apply signed_last_nbits_eq;
      [lia | pose proof (lit_sign_c_range candidate); lia]
  end);
  try (lazymatch goal with
  | Hretval : ?retval = lit_sign_c ?candidate |- _ =>
      assert (Hbyte : signed_last_nbits retval 8 = retval) by
        (rewrite Hretval; apply signed_last_nbits_eq;
        [lia | pose proof (lit_sign_c_range candidate); lia]);
      assert (Hbytepair :
        signed_last_nbits
          (signed_last_nbits retval 8 + signed_last_nbits retval 8 - 1) 8 =
        2 * lit_sign_c candidate - 1) by
        (rewrite Hbyte, Hretval; apply signed_last_nbits_eq;
        [lia | pose proof (lit_sign_c_range candidate); lia])
  end);
  try unfold propagation_scan_candidate_layout;
  try msat_conj_from_facts_p5.

(* The two residues that survive the generic conjunction closer: the candidate
   layout still spelled through [clause_lits_pointer], whose last conjunct needs
   the sign-byte normalisation again, and the copy-progress existential, whose
   cursor equations need the length of the empty copied prefix. *)
Ltac msat_capacity_copy_pack_p5 jj :=
  try (lazymatch goal with
  | Hretval : ?retval = lit_sign_c ?candidate
    |- clause_lits_pointer _ _ /\ _ =>
      repeat (lazymatch goal with |- _ /\ _ => split end);
      try assumption; try reflexivity;
      rewrite Hretval;
      assert (Hsign : signed_last_nbits (lit_sign_c candidate) 8 =
        lit_sign_c candidate) by
        (apply signed_last_nbits_eq;
        [lia | pose proof (lit_sign_c_range candidate); lia]);
      rewrite Hsign;
      pose proof (lit_sign_c_range candidate) as Hsignrange;
      replace (2 * lit_sign_c candidate - 1) with
        (lit_sign_c candidate + lit_sign_c candidate - 1) by lia;
      apply signed_last_nbits_eq;
      [lia | pose proof (lit_sign_c_range candidate); lia]
  end);
  try (lazymatch goal with
  | Hlits : clause_lits_pointer ?scan_current ?lits,
    Hmem : ?watch_memory = ?raw_prefix ++ ?scan_current :: ?raw_suffix,
    Hkept : Zlength ?raw_prefix = ?ii,
    Hcopy : ?candidate_post_memory = ?watch_memory
    |- exists copied rest, _ =>
      exists nil, raw_suffix; simpl;
      assert (Hsrc : ii + 1 = ii + 1 + Zlength (@nil Z)) by
        (rewrite Zlength_correct; simpl; lia);
      assert (Hdst : jj + 1 = jj + 1 + Zlength (@nil Z)) by
        (rewrite Zlength_correct; simpl; lia);
      repeat (lazymatch goal with |- _ /\ _ => split end);
      try assumption; try reflexivity
  end).

(* The candidate slot is read back at the index it was just written to, so the
   [Znth]/[replace_Znth] pair on the literal array cancels.  One goal only: the
   index fact is derived from the clause length. *)
Ltac msat_capacity_copy_index_p5 :=
  lazymatch goal with
  | Hcand : ?candidate = Znth (?offset - 2)
              (sublist 2 (Zlength ?clause_contents) ?clause_contents) 0 |- _ =>
      assert (Htail : 0 <= offset - 2 <
        Zlength (sublist 2 (Zlength clause_contents) clause_contents)) by
        (rewrite Zlength_sublist by lia; lia);
      try rewrite Znth_replace_Znth_Same by exact Htail
  end.

(* Drop the write from the literal array's [missing_i] hole: the hole is at the
   written index, so the segment predicate does not see the replacement.  Proved
   by induction on the segment contents; [hdrop] names the derived fact.  One
   goal only -- the induction is paid once, not once per residue. *)
Ltac msat_capacity_copy_drop_p5 hdrop :=
  lazymatch goal with
  | Hcand : ?candidate = Znth (?offset - 2)
              (sublist 2 (Zlength ?clause_contents) ?clause_contents) 0,
    Hlits : clause_lits_pointer ?scan_current ?lits |- _ =>
      assert (hdrop : forall (l : list Z) (idx base bound value : Z),
        base <= idx ->
        IntArray.missing_i lits idx base bound
          (replace_Znth (idx - base) value l) |--
        IntArray.missing_i lits idx base bound l) by
        (intros l; induction l as [|a l IH];
         intros idx base bound value Hbase;
         unfold IntArray.missing_i; simpl;
         [ entailer_with ltac:(lia)
         | pose proof (Z_le_lt_eq_dec base idx Hbase) as [Hlt | Heq];
           [ rewrite replace_Znth_cons by lia;
             replace (idx - (base + 1)) with (idx - base - 1) by lia;
             simpl;
             Split; Intros;
             [ lia
             | Right;
               pose proof (IH idx (base + 1) bound value ltac:(lia)) as Hlemma;
               unfold IntArray.missing_i in Hlemma;
               replace (idx - (base + 1)) with (idx - base - 1) in Hlemma by lia;
               sep_apply_l_atomic Hlemma;
               entailer_with ltac:(lia) ]
           | subst idx;
             replace (base - base) with 0 by lia;
             simpl;
             Split; Intros;
             [ Left; entailer_with ltac:(lia)
             | lia ] ] ]);
      sep_apply (hdrop
        (sublist 2 (Zlength clause_contents) clause_contents)
        offset 2 (Zlength clause_contents) candidate ltac:(lia))
  end.

(* Merge the frame back: cancel the cells the entailer left open, then discharge
   the remaining capacity-target residues, which only differ from the ones
   [msat_capacity_copy_facts_p5] closed in that the candidate is still spelled
   through its defining [Znth]. *)
Ltac msat_capacity_copy_merge_p5 :=
  try csimpl;
  try cancel;
  try sep_apply store_char_undef_store_char;
  try cancel;
  try (lazymatch goal with
  | Hcand : ?candidate = Znth (?offset - 2)
              (sublist 2 (Zlength ?clause_contents) ?clause_contents) 0 |- _ =>
      rewrite <- ?Hcand;
      try (repeat (lazymatch goal with |- _ /\ _ => split end);
        try reflexivity; try assumption;
        rewrite Hcand at 1; assumption)
  end);
  try msat_conj_from_facts_p5;
  try assumption;
  try (lazymatch goal with
  | Hcand : ?candidate = Znth (?offset - 2)
              (sublist 2 (Zlength ?clause_contents) ?clause_contents) 0 |- _ =>
      rewrite Hcand at 1; assumption
  end);
  try cancel.

(* Close the two [solver_propagate] capacity-exhausted watcher-copy obligations
   (the two program points differ in their precondition, not in the closing
   argument).  [rsn_scan] and [trl_scan] are the witnesses the right-hand side
   asks for, [jj] the copy cursor and [hdrop] the name given to the segment fact
   derived on the way; the twenty-four precondition facts the closer reads are
   bound by their shape inside the pieces that use them. *)
Ltac msat_propagate_capacity_copy_close_p5 rsn_scan trl_scan jj hdrop :=
  msat_capacity_copy_open_p5 rsn_scan trl_scan jj;
  msat_capacity_copy_facts_p5;
  msat_capacity_copy_progress_p5 jj;
  msat_capacity_copy_sign_p5;
  msat_capacity_copy_pack_p5 jj;
  [> msat_capacity_copy_index_p5 | idtac ..];
  try unfold solver_propagation_scan_arrays_noqh_at;
  [> msat_capacity_copy_drop_p5 hdrop | idtac ..];
  msat_capacity_copy_merge_p5.

(* The frame step shared by every clause-scan tag obligation: rewrite the clause
   remainder through the tag step, expand the [set] name [Mnext] under the frame
   lemma and the inert-resource bundle, and push all twenty-one projection
   equations of [analyze_tag_step_msolver] into the goal.  The remaining
   arguments are the tag step's own arguments plus the clause the remainder is
   taken of.  [solver_analyze_inert_at_tag_step] is the bundle's mirror of
   [solver_analyze_frame_analyze_tag_step]: the six uninitialised tails, the
   [stack] vector and the two literal counters are folded into one atom by the
   annotation, so the twenty-one projection rewrites below no longer reach the
   [ms_cap] / [ms_qtail] / [ms_stack] / [ms_stats] occurrences inside it and
   the whole bundle has to be moved from the post-tag state to [Mscan] in one
   step instead. *)
Tactic Notation "msat_analyze_tag_step_frame_p5" ident(Mnext) constr(Mscan)
    constr(v) constr(tcap) constr(act) constr(opos) constr(ord) constr(vinc)
    constr(c) constr(isl) constr(words) :=
  assert (Hrem : analysis_clause_remainder Mnext c isl words =
      analysis_clause_remainder Mscan c isl words) by reflexivity;
  rewrite Hrem;
  unfold Mnext;
  rewrite solver_analyze_frame_analyze_tag_step;
  rewrite solver_analyze_inert_at_tag_step;
  pose proof (analyze_tag_step_msolver_proj Mscan
    (replace_Znth v 1 (ms_tags Mscan)) (ms_tagged Mscan ++ (v :: nil))
    tcap act opos ord vinc) as Hproj;
  cbv zeta in Hproj;
  destruct Hproj as (Etags & Etagged & Etaggedcap & Eactivity & Eorderpos &
      Eorder & Evarinc & Esize & Ecap & Eqtail & Ecore & Ereasonwords &
      Ereasonof & Eordercap & Estack & Estackcap & Estats & Eclainc & Elimcap);
  assert (Elearnt : ms_learnt (analyze_tag_step_msolver Mscan
      (replace_Znth v 1 (ms_tags Mscan)) (ms_tagged Mscan ++ (v :: nil))
      tcap act opos ord vinc) = ms_learnt Mscan) by reflexivity;
  assert (Elearntcap : ms_learnt_cap (analyze_tag_step_msolver Mscan
      (replace_Znth v 1 (ms_tags Mscan)) (ms_tagged Mscan ++ (v :: nil))
      tcap act opos ord vinc) = ms_learnt_cap Mscan) by reflexivity;
  try rewrite Etags; try rewrite Etagged; try rewrite Etaggedcap;
  try rewrite Eactivity; try rewrite Eorderpos; try rewrite Eorder;
  try rewrite Evarinc; try rewrite Esize; try rewrite Ecap;
  try rewrite Eqtail; try rewrite Ecore; try rewrite Ereasonwords;
  try rewrite Ereasonof; try rewrite Eordercap; try rewrite Estack;
  try rewrite Estackcap; try rewrite Estats; try rewrite Eclainc;
  try rewrite Elimcap; try rewrite Elearnt; try rewrite Elearntcap.

(* Same closer for the tag steps that grow the learnt word vector instead: two
   further residual goals ask for the new word-vector length [Hwl] and for the
   denotation of its tail [Hws]. *)
Tactic Notation "msat_analyze_scan_inv_word_p5" ident(Mnext) ident(phase)
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

(* Close the spatial residue of a tag step: rewrite the two literal read-backs
   [H7] / [H6] to the tagged variable [v], reopen the tagged vector as a raw
   segment and instantiate its single [veci_rep] witness with [p]. *)
Tactic Notation "msat_analyze_tagged_reseal_p5" constr(v) constr(Mscan)
    constr(p) ident(H7) ident(H6) ident(HZ) :=
  fold v in H7, H6;
  rewrite H7, H6;
  rewrite H7 in HZ;
  pose proof (Zlength_nonneg (ms_tagged Mscan ++ (v :: nil)))
    as Htaggedlen_nonneg;
  sep_apply CharArray.full_to_seg;
  unfold veci_rep;
  Exists p;
  unfold veci_rep_at;
  (entailer_with ltac:(lia));
  try (unfold veci_size_addr, veci_cap_addr, veci_ptr_addr;
    csimpl; cancel).

(* Variant of the reseal for the obligations whose right-hand side carries three
   [veci_rep] existentials (tagged, order, trail_lim) spelled at the scan state
   while the left-hand side keeps two of them spelled at the active state: [HM]
   is the [Mscan = Mact] equation that aligns the two spellings, and [plim] /
   [porder] name the two left-hand witnesses that have to be introduced before
   all three right-hand ones can be instantiated. *)
Tactic Notation "msat_analyze_tagged_reseal_scan_p5" constr(v) constr(Mscan)
    constr(p) ident(H7) ident(H6) ident(HZ) ident(HM)
    ident(plim) ident(porder) :=
  fold v in H7, H6;
  rewrite H7, H6;
  rewrite H7 in HZ;
  pose proof (Zlength_nonneg (ms_tagged Mscan ++ (v :: nil)))
    as Htaggedlen_nonneg;
  sep_apply CharArray.full_to_seg;
  unfold veci_rep;
  rewrite HM;
  (Intros plim porder; Exists p porder plim);
  unfold veci_rep_at;
  (entailer_with lia);
  try (unfold veci_size_addr, veci_cap_addr, veci_ptr_addr;
    csimpl; cancel);
  apply Zlength_nonneg.

(* Transport the decision level [dq] and trail rank [rq] of the scanned literal
   from the active state to the scan state: [Eqv] renames the literal's variable
   to [v], [Eview] aligns the two views and [Htrailwf] supplies the
   levels/trail agreement.  It leaves [Edq], [Hagree], [Hlevq0] and [Hrqb]
   behind for the level comparisons that follow. *)
Tactic Notation "msat_analyze_scan_level_transport_p5" constr(v) constr(Mscan)
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

(* The tag step only rewrites heuristic and scratch fields, so a
   [analysis_cancel_ready] of the pre-state survives it: the reason-bearing core
   is unchanged and the fresh order heap is covered by the old one. *)
Lemma ms_analyze_tag_step_cancel_ready_p5 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z)
         (tags tagged : list Z) (tagged_cap : Z) (activity : list fp64)
         (orderpos order : list Z) (var_inc : fp64),
    analysis_cancel_ready n F A_arr K M focus ->
    order_heap_wf n order orderpos ->
    (forall u : Z, 0 <= u < n -> Znth u orderpos (-1) = -1 ->
       Znth u (ms_orderpos M) (-1) = -1) ->
    analysis_cancel_ready n F A_arr K
      (analyze_tag_step_msolver M tags tagged tagged_cap activity orderpos
         order var_inc) focus.
Proof.
  intros n F A_arr K M focus tags tagged tagged_cap activity orderpos order
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

(* Appending a literal to the learnt component instead: its variable is what
   lands in the tagged vector. *)
Lemma ms_analyze_tags_perm_snoc_l_p5 :
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

(* The five cells of an int vector fold back into [veci_rep_at] once the two
   capacity side conditions of that predicate are available. *)
Lemma ms_veci_cells_to_rep_at_p5 :
  forall (a p : Z) (l : list Z) (cap : Z),
    0 <= Zlength l <= cap -> 0 < cap <= INT_MAX ->
    (veci_size_addr a # Int |-> Zlength l **
     veci_cap_addr a # Int |-> cap **
     veci_ptr_addr a # Ptr |-> p **
     IntArray.seg p 0 (Zlength l) l **
     IntArray.undef_seg p (Zlength l) cap)
    |-- veci_rep_at a p l cap.
Proof.
  intros a p l cap Hlen Hcap. unfold veci_rep_at. (entailer_with ltac:(lia));
  (unfold veci_size_addr, veci_cap_addr, veci_ptr_addr; csimpl; cancel).
Qed.

(* The learnt word vector carries one header word in front of the denoted
   learnt clause, so its length is one more than the clause's. *)
Lemma ms_learnt_words_len_p5 :
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

(* Appending a word to that vector appends the corresponding literal to the
   denoted clause. *)
Lemma ms_learnt_words_snoc_p5 :
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

(* The tagged vector has as many entries as the three analysis components put
   together. *)
Lemma ms_analyze_tags_len_p5 :
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

(* One iteration of the watcher-list compaction copy: as long as the read cursor
   is still inside the watcher list, copying cell [src] to cell [dst] advances
   both cursors and keeps the copy invariant. *)
Lemma ms_binary_watch_copy_step_p5 :
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

(* The copied cell together with the untouched suffix is exactly the suffix of
   the source memory that starts one past the write cursor. *)
Lemma ms_watch_copy_tail_merge_p5 :
  forall (m : list Z) (dst src n : Z),
    Zlength m = n -> 0 <= dst + 1 -> dst + 1 <= src -> src < n ->
    (sublist (dst + 1) src m ++ Znth src m 0 :: nil) ++ sublist (src + 1) n m =
    sublist (dst + 1) n m.
Proof.
  intros m dst src n Hlen Hdst Hdstsrc Hsrc.
  rewrite <- Hlen.
  rewrite (sublist_split (dst + 1) (Zlength m) src m) by lia.
  rewrite (sublist_split src (Zlength m) (src + 1) m) by lia.
  rewrite (sublist_single 0 src m) by lia.
  rewrite <- app_assoc. reflexivity.
Qed.

(* The one-element window that the selected-reason scan starts from is empty. *)
Lemma ms_sublist_one_one_nil_p5 : forall (l : clause), sublist 1 1 l = nil.
Proof.
  intros l. unfold sublist. change (skipn 1 (firstn 1 l) = nil).
  destruct l; reflexivity.
Qed.

(* Reserving the second watcher room: once the watcher list of the first negated
   literal has been given the larger capacity [cap], the stage-1 reservation
   grows to a stage-2 one.  Only the [ms_wcaps] entry at that literal changes,
   so the learnt-database room of stage 1 carries over unchanged. *)
Lemma ms_clause_new_second_room_p5 :
  forall (M : msolver) (words : list Z) (db_cap cap sel : Z),
    clause_new_reserved_rooms_gen 1 words
      (msolver_with_clause_caps_gen M db_cap (ms_wcaps M) sel) sel ->
    0 <= lit_neg_c (Znth 0 words 0) < Zlength (ms_wcaps M) ->
    Zlength (Znth (lit_neg_c (Znth 0 words 0)) (ms_wm M) (@nil Z)) < cap ->
    clause_new_reserved_rooms_gen 2 words
      (msolver_with_clause_caps_gen M db_cap
        (replace_Znth (lit_neg_c (Znth 0 words 0)) cap (ms_wcaps M)) sel) sel.
Proof.
  intros M words db_cap cap sel Hrooms Hidx Hroom.
  unfold clause_new_reserved_rooms_gen in Hrooms |- *.
  cbv zeta in Hrooms |- *.
  rewrite ?sel_db_with_caps, ?sel_cap_with_caps in Hrooms |- *.
  unfold msolver_with_clause_caps_gen, msolver_capacity_update in Hrooms |- *.
  cbn [ms_wm ms_wcaps] in Hrooms |- *.
  destruct Hrooms as [Hdb _].
  split; [intros _; apply Hdb; lia|].
  split.
  - intros _.
    rewrite (Znth_replace_Znth_Same 1 (ms_wcaps M)
      (lit_neg_c (Znth 0 words 0)) cap Hidx).
    exact Hroom.
  - intros Hbad. lia.
Qed.

(* The cell just past the copy window carries the word that was read: the
   appended element is the last of the window. *)
Lemma ms_copy_middle_last_p5 :
  forall (m : list Z) (dst src : Z),
    0 <= dst + 1 -> dst + 1 <= src -> src <= Zlength m ->
    Znth (src - (dst + 1))
      (sublist (dst + 1) src m ++ Znth src m 0 :: nil) 0 = Znth src m 0.
Proof.
  intros m dst src H1 H2 H3.
  rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (src - (dst + 1) - (src - (dst + 1))) with 0 by lia.
  simpl. reflexivity.
Qed.

(* A variable absent from the resolved tag sets is absent from the initial ones:
   the resolved [S] only drops the pivot [x] and the resolved [R] only adds it,
   so the initial membership would have shown up in the resolved one. *)
Lemma ms_analyze_notin_initial_resolved_p5 :
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

(* ---- shared skeleton of the solver_analyze clause-scan tag-step VCs ----
   The six obligations that re-establish [analyze_clause_scan_inv] after the
   tag step of solver_analyze's inner clause scan (five in this file, one in
   part 7) run the same script with a handful of local variations.  The steps
   part 7 shares with this file are declared once in
   solver_qcp_proof_common.v, section 9.  What remains here is the [Lemma]
   that reads the invariant's AnalyzeInitial arm, the [Lemma] that bounds the
   learnt word vector in that arm, and the [Tactic Notation]s that spell each
   part-5 tactic block once.  Every ghost name and every hypothesis a block
   needs is an argument: an [Ltac] body may only mention globals and its own
   parameters. *)

(* The three conjuncts the AnalyzeInitial arm adds: the propagation conflict
   certificate for the scanned clause and the two start sets the scanned prefix
   computes. *)
Lemma ms_analyze_scan_initial_pack_p5 :
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

(* Room for one more learnt word.  The AnalyzeInitial start-learnt set of any
   prefix of a conflicting clause [C] holds literals of pairwise distinct
   variables, all strictly below the current decision level, so the current
   level's own literal [lcur] of [C] is not among them; the [n] variables of
   the solver therefore leave room for that one extra slot. *)
Lemma ms_analyze_start_learnt_room_p5 :
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

(* Name the tagged variable [v] at index [idx] of the clause word list [w] and
   the post-tag state [Mnext] built from the scan state [Mscan] and the tag
   step's own arguments ([tcap], [act], [opos], [ord], [vinc]), then transport
   the cancel-readiness [Hready] and the tag exactness [Htags] of the scan
   state across the step; [Hheap] and [Hu] are the order-heap facts the fresh
   heap needs.  Leaves [Hreadynew] and [Htagsnew]. *)
Tactic Notation "msat_analyze_tag_step_open_p5" ident(v) ident(Mnext)
    constr(n) constr(F) constr(A_arr) constr(K) constr(focus)
    constr(Mscan) constr(idx) constr(w) constr(tcap) constr(act)
    constr(opos) constr(ord) constr(vinc) ident(Hready) ident(Hheap)
    ident(Hu) ident(Htags) :=
  set (v := lit_var_c (Znth (idx - 0) w 0));
  set (Mnext := analyze_tag_step_msolver Mscan
    (replace_Znth v 1 (ms_tags Mscan))
    (ms_tagged Mscan ++ (v :: nil)) tcap act opos ord vinc);
  assert (Hreadynew : analysis_cancel_ready n F A_arr K Mnext focus)
    by (unfold Mnext; apply ms_analyze_tag_step_cancel_ready_p5;
        [exact Hready | exact Hheap | exact Hu]);
  assert (Htagsnew : analysis_tags_exact n (replace_Znth v 1 (ms_tags Mscan))
      (ms_tagged Mscan ++ (v :: nil)))
    by (apply ms_analysis_tags_exact_snoc;
        [exact Htags | unfold v; lia | unfold v in *; lia]).

(* The selected-reason level comes from [Edq]; the two native read-backs
   establish positivity and inequality with the current level.  The existing
   trail-level bound then makes that inequality strict in the right direction. *)
Tactic Notation "msat_analyze_selected_level_bounds_p5" ident(v) constr(Mscan)
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

(* Read the trail rank and level in the initial-conflict arm.  Unlike the
   selected arm, [dq] is defined directly at the rank; no reason-level equation
   is substituted. The active/scan view equality is an explicit argument. *)
Tactic Notation "msat_analyze_initial_level_readback_p5" ident(v) constr(n)
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

(* The scanned literal [q] sits strictly below the current decision level:
   [Hlev] gives its level [dq], [Hne] separates that level from the current
   one, [Eq] renames its variable and [Ev] aligns the active view [Ma] with the
   scan view.  Leaves the two boolean flags [Hat] and [Hbelow] that the
   resolved-set step below reads. *)
Tactic Notation "msat_analyze_offlevel_flags_p5" constr(n) constr(Ma)
    constr(q) constr(dq) ident(Hlev) ident(Hne) ident(Eq) ident(Ev) :=
  assert (Hat : at_current_level_b (msolver_view n Ma) (lit_denote q) = false)
    by (unfold at_current_level_b; rewrite Eq, Hlev;
        rewrite Ev, msolver_view_current_level;
        apply Z.eqb_neq; exact Hne);
  assert (Hbelow : below_current_b (msolver_view n Ma) (lit_denote q) = true)
    by (apply (proj2 (below_current_b_true_iff _ _));
        exists dq; rewrite Eq; split; [exact Hlev|];
        rewrite Ev, msolver_view_current_level; lia).

(* Extend the AnalyzeSelected resolved sets by the scanned word [q] at index
   [idx] of the clause word list [w]: the new slice is the old one snoc [q],
   the flag [Hlv] keeps [q]'s variable out of the resolved [S] and the flag
   [Hbl] puts [q] into the resolved learnt list, where [Heqv] renames its
   variable and [Hmem] says that variable was not tagged initially.  [HC] and
   [Hjhi] are the clause denotation and the scan index bound; [HS] and [HL] are
   the old resolved-set equations.  Leaves [Hprefix], [HSnext], [HLnext]. *)
Tactic Notation "msat_analyze_resolve_step_word_p5" ident(q) constr(n)
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

(* Extend the initial scan prefix by a current-level literal.  The three
   outputs are the prefix equation and the updated start-set equations. *)
Tactic Notation "msat_analyze_start_step_tag_p5" ident(q) constr(v) constr(n)
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

(* The same extension for the AnalyzeInitial arm, whose start sets are computed
   from the whole scanned prefix rather than resolved against a pivot.
   Leaves [Hprefix], [HSnext] and [HLnext]. *)
Tactic Notation "msat_analyze_start_step_word_p5" ident(q) constr(n)
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

(* The learnt word vector [wl] grows by the scanned word [q].  Its old length
   comes from the invariant's denotation conjuncts (left in the context by
   [ms_analyze_scan_inv_pack]), and its new length is bounded by the tagged
   list's, which the permutation [Hperm] and the resolved-trail equation [HR]
   split into [Sc], [Rc] and [Lc].  Leaves [Hwordlenold], [Htaglen],
   [Hwordlennew] and [Hwordsnext]. *)
Tactic Notation "msat_analyze_scan_words_grow_p5" constr(n) constr(q)
    constr(Mscan) constr(wl) constr(Sc) constr(Rc) constr(R0) constr(Lc)
    ident(Hperm) ident(HR) :=
  assert (Hwordlenold : Zlength wl = 1 + Zlength Lc)
    by (apply ms_learnt_words_len_p5; assumption);
  assert (Htaglen : Zlength (ms_tagged Mscan) =
      Zlength Sc + Zlength Rc + Zlength Lc)
    by (apply ms_analyze_tags_len_p5; exact Hperm);
  assert (Hwordlennew : 1 <= Zlength (wl ++ (q :: nil)) <= n)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil;
        rewrite HR, Zlength_cons in Htaglen;
        pose proof (Zlength_nonneg Sc);
        pose proof (Zlength_nonneg R0);
        pose proof (Zlength_nonneg Lc); lia);
  assert (Hwordsnext : lits_denote (tl (wl ++ (q :: nil))) =
      Lc ++ (lit_denote q :: nil))
    by (apply ms_learnt_words_snoc_p5; assumption).

(* The spatial residue of a word-arm obligation: re-spell the clause index
   [idx] and the two literal read-backs [H7] / [H6] at the scanned word [q] and
   the tagged variable [v], then reopen the learnt word vector [lv] at pointer
   [lp] and capacity [lcap] and the solver's tagged vector [sv] at [tp] /
   [tcap] as raw segments and reseal both as [veci_rep]s.  [Hlp] and [Hlen] are
   the pushed-vector equation and its capacity bound; [Htlen] is the tagged
   capacity bound and must already be spelled at [Mscan]. *)
Tactic Notation "msat_analyze_word_reseal_p5" ident(v) ident(q) constr(Mscan)
    constr(idx) constr(wl) constr(lv) constr(lp) constr(lcap) constr(sv)
    constr(tp) constr(tcap) ident(Hlp) ident(Hlen) ident(H7) ident(H6)
    ident(Htlen) :=
  replace (idx - 0) with idx in Hlp, Hlen by lia;
  fold q in Hlp, Hlen;
  replace (idx - 0) with idx by lia;
  fold q;
  fold v in H7, H6, Htlen;
  rewrite H7, H6;
  rewrite H7 in Htlen;
  pose proof (Zlength_nonneg (ms_tagged Mscan ++ (v :: nil)))
    as Htaggedlen_nonneg;
  sep_apply CharArray.full_to_seg;
  fold (veci_size_addr lv);
  fold (veci_cap_addr lv);
  fold (veci_ptr_addr lv);
  sep_apply (ms_veci_cells_to_rep_at_p5 lv lp (wl ++ (q :: nil)) lcap
    ltac:(split; [apply Zlength_nonneg | exact Hlen]) ltac:(lia));
  sep_apply veci_rep_at_rep;
  sep_apply (ms_solver_tagged_cells_to_rep_at sv tp
    (ms_tagged Mscan ++ (v :: nil)) tcap
    ltac:(split; [apply Zlength_nonneg | exact Htlen]) ltac:(lia));
  sep_apply veci_rep_at_rep;
  entailer_with ltac:(lia).

(* ===== act_clause_bump partial_solve wits ===== *)


Lemma proof_of_act_clause_bump_partial_solve_wit_4_pure : act_clause_bump_partial_solve_wit_4_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact (msat_fp32_same retval activity_now) as Hsame.
  assert (Hretval : msat_fp32_nonnegative retval).
  { unfold msat_fp32_same in Hsame. rewrite Hsame. assumption. }
  assert (Hadded : msat_fp32_nonnegative (fp32_add retval cla_inc0)).
  { apply MSatFloatFacts.fp32_nonnegative_add; assumption. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_act_clause_bump_partial_solve_wit_5_pure : act_clause_bump_partial_solve_wit_5_pure.
Proof.
  (aggressive_pre_process);
  try solve [msat_manual_entailer_with ltac:(lia)].
Qed.

(* ===== act_clause_bump which_implies wits (2 proofs) ===== *)
Lemma proof_of_act_clause_bump_which_implies_wit_1 : act_clause_bump_which_implies_wit_1.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( learnt_db db ) as H_learnt_db.
  bind_fact ( In c (db_words db) ) as H_In.
  sep_apply
    (learnt_clause_focus_by_word__act_var_bump db c H_learnt_db H_In).
  Intros clause_words activity_now.
  Exists clause_words activity_now.
  entailer_with ltac:(int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  tauto.
Qed.

Lemma proof_of_act_clause_bump_which_implies_wit_2 : act_clause_bump_which_implies_wit_2.
Proof.
  (aggressive_pre_process);
  bind_fact ( c % 2 = 0 ) as H_c.
  - unfold clause_db_pair_remainder at 1.
    Split.
    + Intros co pre post.
      destruct H as (Hdb & Hlits & Htag).
      unfold db_nil in Hdb. destruct pre; discriminate Hdb.
    + Intros co pre post.
      destruct H as (Hdb & Hlits & Htag).
      subst db. unfold msat_true in *; simpl in Htag.
      assert (Hmod : c mod 2 = 0) by
        (rewrite <- (Z.rem_mod_nonneg c 2) by lia; exact H_c).
      sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep, activity_state.
      cbn [fst snd]. rewrite Htag, Hlits.
      Exists a_v. entailer_with ltac:(lia).
      * unfold db_nil. simpl. entailer_with ltac:(lia).
      * apply Zlength_nonneg.
  - unfold clause_db_pair_remainder at 1.
    Split.
    + Intros co pre post.
      destruct H as (Hdb & Hlits & Htag).
      unfold db_nil in Hdb. destruct pre; discriminate Hdb.
    + Intros co pre post.
      destruct H as (Hdb & Hlits & Htag).
      subst db. dump_pre_spatial.
      unfold db_words. rewrite map_app. simpl.
      apply in_or_app. right. left. reflexivity.
Qed.

(* ===== act_clause_decay return wits (1 proofs) ===== *)
Lemma proof_of_act_clause_decay_return_wit_1 : act_clause_decay_return_wit_1.
Proof.
  aggressive_pre_process.
  apply MSatFloatFacts.fp32_nonnegative_mul_positive_finite; assumption.
Qed.


(* ===== act_clause_rescale partial_solve wits ===== *)


Lemma proof_of_act_clause_rescale_partial_solve_wit_8_pure : act_clause_rescale_partial_solve_wit_8_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact (msat_fp32_same retval activity_now) as Hsame.
  assert (Hretval : msat_fp32_nonnegative retval).
  { unfold msat_fp32_same in Hsame. rewrite Hsame. assumption. }
  pose proof
    (MSatFloatFacts.fp32_nonnegative_mul_positive_finite
       _ _ Hretval MSatFloatFacts.fp32_scale_positive_finite) as Hscaled.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== act_clause_rescale return wits (1 proofs) ===== *)
Lemma proof_of_act_clause_rescale_return_wit_1 : act_clause_rescale_return_wit_1.
Proof.
  aggressive_pre_process.
  apply MSatFloatFacts.fp32_nonnegative_mul_positive_finite.
  - assumption.
  - apply MSatFloatFacts.fp32_scale_positive_finite.
Qed.


(* ===== act_clause_rescale which_implies wits (2 proofs) ===== *)
Lemma proof_of_act_clause_rescale_which_implies_wit_1 : act_clause_rescale_which_implies_wit_1.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( learnt_db db ) as H_learnt_db.
  assert (Hin : In (Znth (i - 0) (db_words db) 0) (db_words db)).
  { apply Znth_In. lia. }
  sep_apply
    (learnt_clause_focus_by_word__act_var_bump db
       (Znth (i - 0) (db_words db) 0) H_learnt_db Hin).
  Intros clause_words activity_now.
  Exists clause_words activity_now.
  entailer_with ltac:(int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  tauto.
Qed.

Lemma proof_of_act_clause_rescale_which_implies_wit_2 : act_clause_rescale_which_implies_wit_2.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( Znth (i - 0) (db_words db) 0 % 2 = 0 ) as H_Znth.
  set (c := Znth (i - 0) (db_words db) 0) in *.
  unfold clause_db_pair_remainder at 1.
  Split.
  - Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    unfold db_nil in Hdb. destruct pre; discriminate Hdb.
  - Intros co pre post.
    destruct H as (Hdb & Hlits & Htag).
    rewrite Hdb. unfold msat_true in *; simpl in Htag.
    assert (Hmod : c mod 2 = 0) by
      (rewrite <- (Z.rem_mod_nonneg c 2) by lia; exact H_Znth).
    sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
    rewrite clause_db_rep_cons.
    unfold MiniSatClause.rep, activity_state.
    cbn [fst snd]. rewrite Htag, Hlits.
    Exists activity_after. entailer_with ltac:(lia).
    + unfold db_nil. simpl. entailer_with ltac:(lia).
    + apply Zlength_nonneg.
Qed.

(* ===== act_var_bump entail wits (1 proofs) ===== *)
Lemma proof_of_act_var_bump_entail_wit_1_2 : act_var_bump_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  rewrite Zlength_replace_Znth by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== act_var_bump partial_solve wits (2 proofs) ===== *)
Lemma proof_of_act_var_bump_partial_solve_wit_4_pure : act_var_bump_partial_solve_wit_4_pure.
Proof.
  (aggressive_pre_process);
  (rewrite Zlength_replace_Znth by lia; msat_manual_entailer_with ltac:(lia)).
Qed.

Lemma proof_of_act_var_bump_partial_solve_wit_6_pure : act_var_bump_partial_solve_wit_6_pure.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( Znth (v - 0) orderpos0 0 <> -1 ) as H_Znth.
  bind_fact ( order_heap_wf n heap0 orderpos0 ) as H_order_heap_wf.
  bind_fact ( Zlength activity1 = n ) as H_Zlength.
  unfold order_heap_wf in H_order_heap_wf.
  pose proof
    (heap_wf_orderpos_length n
       {| mh_heap := heap0; mh_orderpos := orderpos0 |} H_order_heap_wf) as Hoplen.
  cbn [mh_orderpos] in Hoplen.
  replace (v - 0) with v in H_Znth by lia.
  assert (Hne : Znth v orderpos0 (-1) <> -1).
  { assert (Hvpos : 0 <= v < Zlength orderpos0) by lia.
    rewrite (Znth_indep orderpos0 v (-1) 0 Hvpos).
    exact H_Znth. }
  assert (Hpre : order_update_pre n v heap0 orderpos0).
  { unfold order_update_pre, order_heap_wf.
    split; [exact H_order_heap_wf |].
    split; [lia | exact Hne]. }
  assert (Hpre_len : order_update_pre (Zlength activity1) v heap0 orderpos0).
  { rewrite H_Zlength. exact Hpre. }
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== act_var_bump return wits (2 proofs) ===== *)
Lemma proof_of_act_var_bump_return_wit_1 : act_var_bump_return_wit_1.
Proof.
  (* The emission re-spelled order_update_post's first argument from [n] to
     [Zlength activity1_2] (the equation survives as a hypothesis).  bind_fact
     matches a hypothesis by EXACT spelling, so the pattern must follow; then
     rewrite back to [n] so the rest of this proof is unchanged. *)
  Unfold.
  right.
  intros.
  bind_fact ( order_update_post (Zlength activity1_2) v heap0 orderpos0 heap1_2 orderpos1_2 ) as H_order_update_post.
  bind_fact ( Zlength activity1_2 = n ) as H_Zlength.
  rewrite H_Zlength in H_order_update_post.
  unfold order_update_post in H_order_update_post.
  destruct H_order_update_post as (_ & Hwf & Hperm & Hiff).
  entailer_with lia.
  - intros u Hu Hz.
    pose proof (Hiff u ltac:(rewrite <- H_Zlength; exact Hu)) as Huiff.
    apply (proj1 Huiff). exact Hz.
  - intros u Hu Hz.
    pose proof (Hiff u ltac:(rewrite <- H_Zlength; exact Hu)) as Huiff.
    apply (proj2 Huiff). exact Hz.
Qed.

Lemma proof_of_act_var_bump_return_wit_2 : act_var_bump_return_wit_2.
Proof.
  (aggressive_pre_process);
  auto using Permutation_refl.
Qed.

(* ===== act_var_rescale entail wits (2 proofs) ===== *)
Lemma proof_of_act_var_rescale_entail_wit_1 : act_var_rescale_entail_wit_1.
Proof.
  Unfold.
  intros.
  destruct (Z.eq_dec n 0) as [-> | Hnpos].
  - Left. Exists activity0. entailer_with ltac:(lia).
  - Right. Exists activity0 0.
    sep_apply_l_atomic
      (DoubleArray.seg_split_to_missing_i
         activity_ptr 0 0 n activity0 msat_fp64_zero).
    + dump_pre_spatial. lia.
    + unfold StoreDoubleAsElement.storeA, double_Znth.
      msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_act_var_rescale_entail_wit_2 : act_var_rescale_entail_wit_2.
Proof.
  Unfold.
  intros.
  match goal with
  | |- context [fp64_mul ?value ?scale] =>
      remember (fp64_mul value scale) as scaled
  end.
  destruct (Z.eq_dec (i_2 + 1) n) as [Hdone | Hnext].
  - Left.
    Exists (replace_Znth i_2 scaled activity_now_2).
    sep_apply_l_atomic
      (DoubleArray.missing_i_merge_to_seg
         activity_ptr 0 i_2 n scaled activity_now_2).
    + dump_pre_spatial. lia.
    + replace (i_2 - 0) with i_2 by lia.
      subst n.
      rewrite Zlength_replace_Znth by lia.
      rewrite <- Hdone.
      entailer_with ltac:(lia).
  - Right.
    Exists (replace_Znth i_2 scaled activity_now_2) (i_2 + 1).
    sep_apply_l_atomic
      (DoubleArray.missing_i_merge_to_seg
         activity_ptr 0 i_2 n scaled activity_now_2).
    + dump_pre_spatial. lia.
    + replace (i_2 - 0) with i_2 by lia.
      sep_apply_l_atomic
        (DoubleArray.seg_split_to_missing_i
           activity_ptr 0 (i_2 + 1) n
           (replace_Znth i_2 scaled activity_now_2)
           msat_fp64_zero).
      * dump_pre_spatial. lia.
      * unfold StoreDoubleAsElement.storeA, double_Znth.
        rewrite Zlength_replace_Znth by lia.
        msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_new entail wits (6 proofs) ===== *)
Lemma proof_of_clause_new_entail_wit_2 : clause_new_entail_wit_2.
Proof.
  (* D1: `wl` is no longer a local existential -- clause_new's contract now takes it
     as the spec ghost `cn_wl_clause_new_spec`.  QCP has no congruence closure, so
     the proof must spell the binder exactly as the STATE spells it. *)
  (aggressive_pre_process);
  ((subst watch_words0; subst watch_words1;
       subst watch_cap0; subst watch_cap1);
    bind_fact ( vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth (0 - 0) cn_words_clause_new_spec 0)) <> vecp_slot
        cn_wl_clause_new_spec (lit_neg_c (Znth (1 - 0) cn_words_clause_new_spec 0)) ) as H_vecp_slot).
  - entailer_with lia.
  - (* The RHS asks for the two watch literals to be distinct; [H_vecp_slot] is exactly that fact
          one [vecp_slot] application out, so intro the equality and push it through the slot. *)
    replace (0 - 0) with 0 in H_vecp_slot by lia.
    replace (1 - 0) with 1 in H_vecp_slot by lia.
    apply (derivable1s_coq_prop_r _).
    intros Heq.
    apply H_vecp_slot.
    rewrite Heq.
    reflexivity.
  - unfold clause_new_stage_ready_root, clause_new_caps_progress_gen.
    entailer_with lia.
    (* the pending certificate, restated at the C parameter: the Assert pins
       [learnt_pre = cn_sel], so it is the precondition's own conjunct. *)
    match goal with H : learnt_pre = _ |- _ => rewrite H end.
    assumption.
Qed.

Lemma proof_of_clause_new_entail_wit_3 : clause_new_entail_wit_3.
Proof.
  (* D1: this refold TAKES cn_wl_clause_new_spec but its conclusion re-HIDES wl,
     while clause_new_post_at_gen now demands the rep at that exact wl.  Hiding ->
     named-at-a-specific-wl is unprovable, so use the wl-named twin. *)
  (* D1: `wl` is no longer a local existential -- clause_new's contract now takes it
     as the spec ghost `cn_wl_clause_new_spec`.  QCP has no congruence closure, so
     the proof must spell the binder exactly as the STATE spells it. *)
  aggressive_pre_process.
  subst database watch0 watch1.
  bind_fact ( Zlength (db_words ((solver_selected_db cn_sel_clause_new_spec cn_M_clause_new_spec))) =
      (solver_selected_cap cn_sel_clause_new_spec cn_M_clause_new_spec) ) as H_Zlength.
  bind_fact ( vector_capacity_exhausted (Zlength (db_words ((solver_selected_db cn_sel_clause_new_spec
      cn_M_clause_new_spec)))) ((solver_selected_cap cn_sel_clause_new_spec cn_M_clause_new_spec)) ) as
      H_vector_capacity_exhausted.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as H_clause_new_stage_ready.
  bind_fact ( lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <> lit_neg_c (Znth 1 cn_words_clause_new_spec 0) ) as
      H_lit_neg_c.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof Hphysical as Hshape.
  pose proof (msi_size Hinv) as Hsize.
  change (cn_n_clause_new_spec = ms_size cn_M_clause_new_spec) in Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  pose proof (clause_install_pending_cert_wf _ _ _ _ _ Hcert) as (_ & Hall & _).
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 Hall ltac:(lia)) as Hlit0.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 Hall ltac:(lia)) as Hlit1.
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0.
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg0; lia).
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg1; lia).
  assert (Hfailure : clause_new_capacity_failure_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec).
  { unfold clause_new_capacity_failure_root, solver_internal_capacity_ready.
    split; [exact Hcaps |].
    split.
    - split; [exact Hpending |].
      exact (msolver_inv_propagation_of_strong _ _ _ _ _ Hinv).
    - split; [| exact Hseed].
      left. unfold db_words in H_vector_capacity_exhausted.
      rewrite !Zlength_correct in H_vector_capacity_exhausted.
      rewrite length_map in H_vector_capacity_exhausted.
      rewrite Zlength_correct. exact H_vector_capacity_exhausted. }
  subst cn_n_clause_new_spec.
  unfold vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  sep_apply (clause_new_full_db_stage_refold__act_clause_bump_gen_wl
    s_pre begin_pre clause_out_pre
    ((solver_selected_vec s_pre cn_sel_clause_new_spec))
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
    cn_wl_clause_new_spec lvl_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec p cn_sel_clause_new_spec
        ltac:(lia)
    Hshape eq_refl eq_refl eq_refl H_lit_neg_c H_Zlength ltac:(lia) Hidx0 Hidx1).
  unfold clause_new_post_at_root.
  Right.
  entailer_with ltac:(lia).
  Exists cn_M_clause_new_spec.
  split_pure_spatial.
  - entailer_with ltac:(lia).
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact Hfailure.
Qed.

Lemma proof_of_clause_new_entail_wit_4 : clause_new_entail_wit_4.
Proof.
  aggressive_pre_process.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as H_clause_new_stage_ready.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof (solver_support_inv_with_clause_caps__api_reentry cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec cn_M_clause_new_spec cap_prime (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec ltac:(lia) Hinv eq_refl) as Hinv'.
  assert (Hcaps' : clause_new_caps_progress_gen cn_M_clause_new_spec
    cn_words_clause_new_spec
    (msolver_with_clause_caps_gen cn_M_clause_new_spec cap_prime
      (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec) cn_sel_clause_new_spec).
  { right. left. exists cap_prime. reflexivity. }
  Exists cap_prime.
  cn_proj.
  unfold clause_new_stage_ready_root in *.
  unfold clause_new_caps_progress_gen, clause_new_reserved_rooms_gen in *.
  cbn in *.
  entailer_with ltac:(lia).
  - unfold db_words. entailer_with ltac:(int_auto).
    (* the remainder is blind to a cap bump on the selected database *)
    rewrite rest_at_gen_caps_same by lia.
    entailer_with ltac:(int_auto).
  - (* the cap bump is the SELECTED database's; the gates say what the
       selector sees through it. *)
    intros _. rewrite sel_db_with_caps, sel_cap_with_caps.
    unfold db_words in *. lia.
Qed.

(* All three watch-allocation arms read the same stage certificate and the
   first two clause literals. Capacity and watcher-index proofs remain local. *)
Ltac msat_clause_new_watch_facts_p5 n words Hstage :=
  pose proof Hstage as Hready;
  unfold clause_new_stage_ready_root in Hready;
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert);
  pose proof Hphysical as Hshape;
  pose proof (clause_install_pending_cert_wf _ _ _ _ _ Hcert) as (_ & Hall & _);
  pose proof (Forall_Znth_elim Z (lit_wf_c n) words 0 0 Hall ltac:(lia)) as Hlit0;
  pose proof (Forall_Znth_elim Z (lit_wf_c n) words 0 1 Hall ltac:(lia)) as Hlit1;
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0;
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.

Lemma proof_of_clause_new_entail_wit_5 : clause_new_entail_wit_5.
Proof.
  (* D1: this refold TAKES cn_wl_clause_new_spec but its conclusion re-HIDES wl,
     while clause_new_post_at_gen now demands the rep at that exact wl.  Hiding ->
     named-at-a-specific-wl is unprovable, so use the wl-named twin. *)
  (* D1: `wl` is no longer a local existential -- clause_new's contract now takes it
     as the spec ghost `cn_wl_clause_new_spec`.  QCP has no congruence closure, so
     the proof must spell the binder exactly as the STATE spells it. *)
  aggressive_pre_process.
  subst database watch0 watch1 watch_words0 watch_words1.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec)) nil) <= 2147483647 )
      as H_Zlength.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec)) nil) >= -2147483648 )
      as H_Zlength_2.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec)) nil) = Znth (lit_neg_c
      (Znth 0 cn_words_clause_new_spec 0)) (ms_wcaps Mstage1) 1 ) as H_Zlength_3.
  bind_fact ( vector_capacity_exhausted (Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1 (ms_wcaps cn_M_clause_new_spec)
      cn_sel_clause_new_spec)) nil)) (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wcaps Mstage1) 1) ) as
      H_vector_capacity_exhausted.
  bind_fact ( Mstage1 = msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1 (ms_wcaps cn_M_clause_new_spec)
      cn_sel_clause_new_spec ) as H_Mstage1.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage1 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready.
  (* The first watch slot's word list is spelled through Mstage1's defining expression rather
          than through the binder the width and capacity hypotheses use.  [H_Mstage1] IS that
          definition, so fold it back once, up front; QCP cancellation and [exact] are both
          syntactic. *)
  rewrite <- H_Mstage1 in H_Zlength, H_Zlength_2, H_Zlength_3, H_vector_capacity_exhausted |- *.
  msat_clause_new_watch_facts_p5 cn_n_clause_new_spec
    cn_words_clause_new_spec H_clause_new_stage_ready.
  pose proof (msi_size Hinv) as Hsize.
  change (cn_n_clause_new_spec = ms_size Mstage1) in Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm Mstage1)) by
    (unfold lit_wf_c in Hneg0; lia).
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm Mstage1)) by
    (unfold lit_wf_c in Hneg1; lia).
  assert (Hidx0c :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wcaps Mstage1)) by
    (unfold solver_shape in Hshape; lia).
  assert (Hfailure : clause_new_capacity_failure_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage1 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec).
  { unfold clause_new_capacity_failure_root, solver_internal_capacity_ready.
    split; [exact Hcaps |].
    split.
    - split; [exact Hpending |].
      exact (msolver_inv_propagation_of_strong _ _ _ _ _ Hinv).
    - split; [| exact Hseed].
      apply (solver_capacity_exhausted_watch_gen Mstage1
        (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) cn_sel_clause_new_spec Hidx0).
      rewrite (Znth_indep (ms_wcaps Mstage1)
        (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) 0 1 Hidx0c).
      exact H_vector_capacity_exhausted. }
  subst cn_n_clause_new_spec.
  fold (vecp_size_addr
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))).
  fold (vecp_cap_addr
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))).
  fold (vecp_ptr_addr
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))).
  sep_apply (vecp_full_refold__act_clause_bump
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))) p
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wm Mstage1) nil)
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage1) 1) H_Zlength_3 ltac:(lia)).
  transitivity
    (clause_new_stage_rep_at_gen s_pre begin_pre clause_out_pre
      ((solver_selected_vec s_pre cn_sel_clause_new_spec))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
      cn_wl_clause_new_spec lvl_clause_new_spec Mstage1 cn_words_clause_new_spec cn_sel_clause_new_spec).
  - unfold clause_new_stage_rep_at_gen. cbn.
    split_pure_spatial.
    + entailer_with ltac:(int_auto).
    + unfold db_words. entailer_with ltac:(lia).
  - sep_apply (clause_new_stage_rep_at_refold__act_clause_bump_gen_wl
      s_pre begin_pre clause_out_pre
      ((solver_selected_vec s_pre cn_sel_clause_new_spec))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
      cn_wl_clause_new_spec lvl_clause_new_spec Mstage1 cn_words_clause_new_spec cn_sel_clause_new_spec ltac:(lia)
      Hshape Hidx0 Hidx1).
    unfold clause_new_post_at_root.
    Right.
    entailer_with ltac:(lia).
    Exists Mstage1.
    split_pure_spatial.
    + entailer_with ltac:(lia).
    + split_pures.
      * dump_pre_spatial. reflexivity.
      * dump_pre_spatial. exact Hfailure.
Qed.

Lemma proof_of_clause_new_entail_wit_6 : clause_new_entail_wit_6.
Proof.
  (* D1: `wl` is no longer a local existential -- clause_new's contract now takes it
     as the spec ghost `cn_wl_clause_new_spec`.  QCP has no congruence closure, so
     the proof must spell the binder exactly as the STATE spells it. *)
  aggressive_pre_process.
  subst Mstage1.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wm (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec)) nil) < cap_prime ) as H_Zlength.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec
      learnt_cap1 (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec) cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as H_clause_new_stage_ready.
  bind_fact ( clause_new_reserved_rooms_gen 1 cn_words_clause_new_spec
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1 (ms_wcaps cn_M_clause_new_spec)
      cn_sel_clause_new_spec) cn_sel_clause_new_spec ) as H_clause_new_reserved_rooms.
  bind_fact ( lit_neg_c (Znth 0 cn_words_clause_new_spec 0)
      <> lit_neg_c (Znth 1 cn_words_clause_new_spec 0) ) as H_lit_neg_c.
  msat_clause_new_watch_facts_p5 cn_n_clause_new_spec
    cn_words_clause_new_spec H_clause_new_stage_ready.
  pose proof Hcert as Hcert_full.
  pose proof (msi_size Hinv) as Hsize.
  change (cn_n_clause_new_spec = ms_size cn_M_clause_new_spec) in Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  pose proof (solver_shape_wcaps_len _ Hshape) as Hwcaps_len6.
  change (Zlength (ms_wcaps cn_M_clause_new_spec) =
    2 * ms_size cn_M_clause_new_spec) in Hwcaps_len6.
  assert (Hwmcaps_len :
    Zlength (ms_wm cn_M_clause_new_spec) =
    Zlength (ms_wcaps cn_M_clause_new_spec)).
  { unfold msolver_with_clause_caps_gen, msolver_capacity_update in Hwm_len, Hwcaps_len6.
    cbn in Hwm_len, Hwcaps_len6. lia. }
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wcaps cn_M_clause_new_spec)).
  { rewrite Hwcaps_len6. unfold lit_wf_c in Hneg0. lia. }
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wcaps cn_M_clause_new_spec)).
  { rewrite Hwcaps_len6. unfold lit_wf_c in Hneg1. lia. }
  assert (Hlen :
    Zlength (replace_Znth
      (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) cap_prime
      (ms_wcaps cn_M_clause_new_spec)) =
    Zlength (ms_wcaps
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec))).
  { cbn. apply Zlength_replace_Znth. }
  pose proof (solver_support_inv_with_clause_caps__api_reentry cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
      (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec) learnt_cap1 (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec ltac:(lia) Hinv Hlen) as Hinv'.
  rewrite with_caps_gen_idem in Hinv'.
  assert (Hcaps' : clause_new_caps_progress_gen cn_M_clause_new_spec
    cn_words_clause_new_spec
    (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
      (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
        cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec) cn_sel_clause_new_spec).
  { right. right. left. exists learnt_cap1, cap_prime. reflexivity. }
  assert (Hready' : clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
      (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
        cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec) cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec).
  { unfold clause_new_stage_ready_root.
    split; [eapply solver_shape_with_clause_caps__api_reentry; eassumption |];
    split; [exact Hwords |]; split; [exact Hwords_bound |];
    split; [exact Hcaps' |]; split; [exact Hinv' |];
    split; [exact Hpending | split; [exact Hseed | exact Hcert_full]]. }
  assert (Hrooms' : clause_new_reserved_rooms_gen 2 cn_words_clause_new_spec
    (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
      (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
        cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec) cn_sel_clause_new_spec)
    by (apply ms_clause_new_second_room_p5;
        [exact H_clause_new_reserved_rooms | exact Hidx0 | exact H_Zlength]).
  assert (Hcap0 :
    Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps
        (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
          (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
            cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) 1 = cap_prime).
  { cbn. apply Znth_replace_Znth_Same. exact Hidx0. }
  assert (Hcap1 :
    Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps
        (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
          (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
            cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) 1 =
    Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps cn_M_clause_new_spec) 1).
  { cbn. apply Znth_replace_Znth_Diff; assumption. }
  Exists cap_prime.
  rewrite Hcap0, Hcap1.
  sep_apply
    (clause_new_txn_rest_at_replace_i__act_clause_bump_gen
      s_pre cn_wl_clause_new_spec
      (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      cn_M_clause_new_spec learnt_cap1 (ms_wcaps cn_M_clause_new_spec)
      lvl_clause_new_spec cap_prime cn_sel_clause_new_spec ltac:(lia)
      Hwmcaps_len ltac:(lia) ltac:(lia) H_lit_neg_c).
  assert (Hwm_state :
    ms_wm
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
          cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec) =
    ms_wm
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec)) by reflexivity.
  assert (Hlearnt_state :
    (solver_selected_db cn_sel_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
          cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) =
    (solver_selected_db cn_sel_clause_new_spec
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec))) by reflexivity.
  assert (Hlearnt_cap_state :
    (solver_selected_cap cn_sel_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
          cap_prime (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) =
    (solver_selected_cap cn_sel_clause_new_spec
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec))) by reflexivity.
  assert (Hwcaps_old :
    ms_wcaps
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (ms_wcaps cn_M_clause_new_spec) cn_sel_clause_new_spec) =
    ms_wcaps cn_M_clause_new_spec) by reflexivity.
  rewrite Hwm_state, Hlearnt_state, Hlearnt_cap_state.
  rewrite <- Hwcaps_old.
  entailer_with ltac:(int_auto).
  apply Z.lt_le_incl. exact H_Zlength.
Qed.

Lemma proof_of_clause_new_entail_wit_7 : clause_new_entail_wit_7.
Proof.
  (* D1: this refold TAKES cn_wl_clause_new_spec but its conclusion re-HIDES wl,
     while clause_new_post_at_gen now demands the rep at that exact wl.  Hiding ->
     named-at-a-specific-wl is unprovable, so use the wl-named twin. *)
  (* D1: `wl` is no longer a local existential -- clause_new's contract now takes it
     as the spec ghost `cn_wl_clause_new_spec`.  QCP has no congruence closure, so
     the proof must spell the binder exactly as the STATE spells it. *)
  aggressive_pre_process.
  subst database watch0 watch1 watch_words0 watch_words1.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
      (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) nil) <= 2147483647 ) as H_Zlength.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
      (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) nil) >= -2147483648 ) as H_Zlength_2.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
      (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) nil) = Znth (lit_neg_c (Znth 1
      cn_words_clause_new_spec 0)) (ms_wcaps Mstage2) 1 ) as H_Zlength_3.
  bind_fact ( vector_capacity_exhausted (Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1 (replace_Znth (lit_neg_c (Znth 0
      cn_words_clause_new_spec 0)) watch_cap01 (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) nil)) (Znth
      (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wcaps Mstage2) 1) ) as H_vector_capacity_exhausted.
  bind_fact ( Mstage2 = msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1 (replace_Znth (lit_neg_c (Znth 0
      cn_words_clause_new_spec 0)) watch_cap01 (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec ) as H_Mstage2.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage2 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready.
  rewrite <- H_Mstage2 in H_Zlength, H_Zlength_2, H_Zlength_3, H_vector_capacity_exhausted |- *.
  msat_clause_new_watch_facts_p5 cn_n_clause_new_spec
    cn_words_clause_new_spec H_clause_new_stage_ready.
  pose proof (msi_size Hinv) as Hsize.
  change (cn_n_clause_new_spec = ms_size Mstage2) in Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm Mstage2)) by
    (unfold lit_wf_c in Hneg0; lia).
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm Mstage2)) by
    (unfold lit_wf_c in Hneg1; lia).
  assert (Hidx1c :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wcaps Mstage2)) by
    (unfold solver_shape in Hshape; lia).
  assert (Hfailure : clause_new_capacity_failure_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage2 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec).
  { unfold clause_new_capacity_failure_root, solver_internal_capacity_ready.
    split; [exact Hcaps |].
    split.
    - split; [exact Hpending |].
      exact (msolver_inv_propagation_of_strong _ _ _ _ _ Hinv).
    - split; [| exact Hseed].
      apply (solver_capacity_exhausted_watch_gen Mstage2
        (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) cn_sel_clause_new_spec Hidx1).
      rewrite (Znth_indep (ms_wcaps Mstage2)
        (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) 0 1 Hidx1c).
      exact H_vector_capacity_exhausted. }
  subst cn_n_clause_new_spec.
  fold (vecp_size_addr
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))).
  fold (vecp_cap_addr
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))).
  fold (vecp_ptr_addr
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))).
  sep_apply (vecp_full_refold__act_clause_bump
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))) p
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wm Mstage2) nil)
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage2) 1) H_Zlength_3 ltac:(lia)).
  transitivity
    (clause_new_stage_rep_at_gen s_pre begin_pre clause_out_pre
      ((solver_selected_vec s_pre cn_sel_clause_new_spec))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
      cn_wl_clause_new_spec lvl_clause_new_spec Mstage2 cn_words_clause_new_spec cn_sel_clause_new_spec).
  - unfold clause_new_stage_rep_at_gen. cbn.
    split_pure_spatial.
    + entailer_with ltac:(int_auto).
    + unfold db_words. entailer_with ltac:(lia).
  - sep_apply (clause_new_stage_rep_at_refold__act_clause_bump_gen_wl
      s_pre begin_pre clause_out_pre
      ((solver_selected_vec s_pre cn_sel_clause_new_spec))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
      (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
      cn_wl_clause_new_spec lvl_clause_new_spec Mstage2 cn_words_clause_new_spec cn_sel_clause_new_spec ltac:(lia)
      Hshape Hidx0 Hidx1).
    unfold clause_new_post_at_root.
    Right.
    entailer_with ltac:(lia).
    Exists Mstage2.
    split_pure_spatial.
    + entailer_with ltac:(lia).
    + split_pures.
      * dump_pre_spatial. reflexivity.
      * dump_pre_spatial. exact Hfailure.
Qed.

(* ===== clause_new which_implies wits (1 proofs) ===== *)
Lemma proof_of_clause_new_which_implies_wit_6 : clause_new_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia).
  unfold MiniSatClause.undef at 1. coq_prop_lift.
  apply coq_prop_andp_left. intros [Hsize [Hpos Hmod]].
  entailer_with ltac:(lia).
  rewrite Z.rem_mod_nonneg by lia. exact Hmod.
Qed.

(* ===== clause_remove entail wits (7 proofs) ===== *)
Lemma proof_of_clause_remove_entail_wit_1 : clause_remove_entail_wit_1.
Proof.
  unfold clause_remove_entail_wit_1, clause_remove_open_at.
  Unfold.
  right.
  intros.
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready.
  unfold clause_remove_ready in H_clause_remove_ready.
  destruct H_clause_remove_ready as
    (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
  assert (Hlit0 : lit_wf_c n (Znth 0 clause_words 0)).
  { rewrite Forall_forall in Hforall. apply Hforall, Znth_In. lia. }
  assert (Hlit1 : lit_wf_c n (Znth 1 clause_words 0)).
  { rewrite Forall_forall in Hforall. apply Hforall, Znth_In. lia. }
  assert (Hneg0 : lit_wf_c n (lit_neg_c (Znth 0 clause_words 0)))
    by (apply lit_neg_c_wf; exact Hlit0).
  assert (Hneg1 : lit_wf_c n (lit_neg_c (Znth 1 clause_words 0)))
    by (apply lit_neg_c_wf; exact Hlit1).
  unfold lit_wf_c in Hlit0, Hlit1, Hneg0, Hneg1.
  subst retval.
  sep_apply_l_atomic
    (intarray_expose_first_two__clause_new
      (clause_lits_addr c_pre) clause_words Hlen).
  entailer_with ltac:(lia).
  replace (clause_lits_addr c_pre + 0 * sizeof(INT))
    with (clause_lits_addr c_pre) by lia.
  replace (1 * sizeof(INT)) with (sizeof(INT)) by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_remove_entail_wit_2_1 : clause_remove_entail_wit_2_1.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( vecp_remove_found c_pre (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found ) as H_vecp_remove_found.
  bind_fact ( retval_5 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_5.
  bind_fact ( retval_3 = lit_neg_c (Znth 0 clause_words 0) ) as H_retval_3.
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready.
  unfold clause_remove_ready in H_clause_remove_ready.
  destruct H_clause_remove_ready as (Hlen & _).
  assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize).
  rewrite zdiv_equiv in H_retval_5 by lia.
  rewrite clause_hdr_word_div2 in H_retval_5 by lia.
  unfold clause_watch_word.
  assert (Hb : (2 <? Zlength clause_words)%Z = true)
    by (apply Z.ltb_lt; lia).
  rewrite Hb.
  entailer_with ltac:(lia).
  rewrite H_retval_3.
  exact H_vecp_remove_found.
Qed.

Lemma proof_of_clause_remove_entail_wit_2_2 : clause_remove_entail_wit_2_2.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( retval_5 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_5.
  bind_fact ( retval_3 = lit_neg_c (Znth 0 clause_words 0) ) as H_retval_3.
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready.
  unfold clause_remove_ready in H_clause_remove_ready.
  destruct H_clause_remove_ready as (Hlen & _).
  assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize).
  rewrite zdiv_equiv in H_retval_5 by lia.
  rewrite clause_hdr_word_div2 in H_retval_5 by lia.
  unfold clause_watch_word.
  assert (Hb : (2 <? Zlength clause_words)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hb.
  (* The goal spells the watch-list index as the named result [retval_3] rather than as its
          defining expression; [H_retval_3] carries that definition. *)
  rewrite H_retval_3.
  subst retval_6.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_remove_entail_wit_3_1 : clause_remove_entail_wit_3_1.
Proof.
  naive_C_Rules.aggressive_pre_process.
  unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals in *.
  bind_fact ( retval_8 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_8.
  bind_fact ( vecp_remove_found (clause_watch_word c_pre clause_words (Znth 1 clause_words 0)) (Znth (lit_neg_c (Znth
      0 clause_words 0)) wm nil) found0 ) as H_vecp_remove_found.
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready.
  unfold clause_remove_ready in H_clause_remove_ready.
  destruct H_clause_remove_ready as (Hlen & _).
  assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize).
  rewrite zdiv_equiv in H_retval_8 by lia.
  rewrite clause_hdr_word_div2 in H_retval_8 by lia.
  assert (Hb : (2 <? Zlength clause_words)%Z = true)
    by (apply Z.ltb_lt; lia).
  unfold clause_watch_word in H_vecp_remove_found.
  rewrite Hb in H_vecp_remove_found.
  set (wm' :=
    replace_Znth (lit_neg_c (Znth 1 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 1 clause_words 0))
          (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
            (vecp_remove_result
              (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)
          nil) found_2)
      (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
        (vecp_remove_result
          (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)).
  set (stats' :=
    Znth 0 stats0 0 :: Znth 1 stats0 0 :: Znth 2 stats0 0 ::
    Znth 3 stats0 0 :: Znth 4 stats0 0 :: Znth 5 stats0 0 ::
    Znth 6 stats0 0 ::
    unsigned_last_nbits (Znth 7 stats0 0 - 1) 64 ::
    unsigned_last_nbits
      (Znth 8 stats0 0 - unsigned_last_nbits retval_10 64) 64 ::
    Znth 9 stats0 0 :: Znth 10 stats0 0 :: nil).
  sep_apply
    (stats_rep_from_solver_cells__clause_new s_pre
      (Znth 0 stats0 0) (Znth 1 stats0 0) (Znth 2 stats0 0)
      (Znth 3 stats0 0) (Znth 4 stats0 0) (Znth 5 stats0 0)
      (Znth 6 stats0 0)
      (unsigned_last_nbits (Znth 7 stats0 0 - 1) 64)
      (unsigned_last_nbits
        (Znth 8 stats0 0 - unsigned_last_nbits retval_10 64) 64)
      (Znth 9 stats0 0) (Znth 10 stats0 0)).
  unfold clause_remove_post.
  Exists wm'. Exists stats'.
  unfold clause_remove_result, wmap_remove_first.
  entailer_with ltac:(int_auto).
  exists found0, found_2.
  exists
    (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm).
  subst wm'.
  unfold clause_watch_word. rewrite Hb.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_remove_entail_wit_3_2 : clause_remove_entail_wit_3_2.
Proof.
  naive_C_Rules.aggressive_pre_process.
  unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals in *.
  bind_fact ( retval_9 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_9.
  bind_fact ( vecp_remove_found (clause_watch_word c_pre clause_words (Znth 1 clause_words 0)) (Znth (lit_neg_c (Znth
      0 clause_words 0)) wm nil) found0 ) as H_vecp_remove_found.
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready.
  unfold clause_remove_ready in H_clause_remove_ready.
  destruct H_clause_remove_ready as (Hlen & _).
  assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize).
  rewrite zdiv_equiv in H_retval_9 by lia.
  rewrite clause_hdr_word_div2 in H_retval_9 by lia.
  assert (Hb : (2 <? Zlength clause_words)%Z = false)
    by (apply Z.ltb_ge; lia).
  unfold clause_watch_word in H_vecp_remove_found.
  rewrite Hb in H_vecp_remove_found.
  subst retval_10.
  set (wm' :=
    replace_Znth (lit_neg_c (Znth 1 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 1 clause_words 0))
          (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
            (vecp_remove_result
              (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)
          nil) found_2)
      (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
        (vecp_remove_result
          (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)).
  set (stats' :=
    Znth 0 stats0 0 :: Znth 1 stats0 0 :: Znth 2 stats0 0 ::
    Znth 3 stats0 0 :: Znth 4 stats0 0 :: Znth 5 stats0 0 ::
    Znth 6 stats0 0 ::
    unsigned_last_nbits (Znth 7 stats0 0 - 1) 64 ::
    unsigned_last_nbits
      (Znth 8 stats0 0 - unsigned_last_nbits retval_12 64) 64 ::
    Znth 9 stats0 0 :: Znth 10 stats0 0 :: nil).
  sep_apply
    (stats_rep_from_solver_cells__clause_new s_pre
      (Znth 0 stats0 0) (Znth 1 stats0 0) (Znth 2 stats0 0)
      (Znth 3 stats0 0) (Znth 4 stats0 0) (Znth 5 stats0 0)
      (Znth 6 stats0 0)
      (unsigned_last_nbits (Znth 7 stats0 0 - 1) 64)
      (unsigned_last_nbits
        (Znth 8 stats0 0 - unsigned_last_nbits retval_12 64) 64)
      (Znth 9 stats0 0) (Znth 10 stats0 0)).
  unfold clause_remove_post.
  Exists wm'. Exists stats'.
  unfold clause_remove_result, wmap_remove_first.
  entailer_with ltac:(int_auto).
  exists found0, found_2.
  exists
    (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm).
  subst wm'.
  unfold clause_watch_word. rewrite Hb.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_remove_entail_wit_3_3 : clause_remove_entail_wit_3_3.
Proof.
  naive_C_Rules.aggressive_pre_process.
  unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals in *.
  bind_fact ( retval_8 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_8.
  bind_fact ( vecp_remove_found (clause_watch_word c_pre clause_words (Znth 1 clause_words 0)) (Znth (lit_neg_c (Znth
      0 clause_words 0)) wm nil) found0 ) as H_vecp_remove_found.
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready.
  unfold clause_remove_ready in H_clause_remove_ready.
  destruct H_clause_remove_ready as (Hlen & _).
  assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize).
  rewrite zdiv_equiv in H_retval_8 by lia.
  rewrite clause_hdr_word_div2 in H_retval_8 by lia.
  assert (Hb : (2 <? Zlength clause_words)%Z = true)
    by (apply Z.ltb_lt; lia).
  unfold clause_watch_word in H_vecp_remove_found.
  rewrite Hb in H_vecp_remove_found.
  set (wm' :=
    replace_Znth (lit_neg_c (Znth 1 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 1 clause_words 0))
          (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
            (vecp_remove_result
              (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)
          nil) found_2)
      (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
        (vecp_remove_result
          (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)).
  set (stats' :=
    Znth 0 stats0 0 :: Znth 1 stats0 0 :: Znth 2 stats0 0 ::
    Znth 3 stats0 0 :: Znth 4 stats0 0 ::
    unsigned_last_nbits (Znth 5 stats0 0 - 1) 64 ::
    unsigned_last_nbits
      (Znth 6 stats0 0 - unsigned_last_nbits retval_10 64) 64 ::
    Znth 7 stats0 0 :: Znth 8 stats0 0 :: Znth 9 stats0 0 ::
    Znth 10 stats0 0 :: nil).
  sep_apply
    (stats_rep_from_solver_cells__clause_new s_pre
      (Znth 0 stats0 0) (Znth 1 stats0 0) (Znth 2 stats0 0)
      (Znth 3 stats0 0) (Znth 4 stats0 0)
      (unsigned_last_nbits (Znth 5 stats0 0 - 1) 64)
      (unsigned_last_nbits
        (Znth 6 stats0 0 - unsigned_last_nbits retval_10 64) 64)
      (Znth 7 stats0 0) (Znth 8 stats0 0)
      (Znth 9 stats0 0) (Znth 10 stats0 0)).
  unfold clause_remove_post.
  Exists wm'. Exists stats'.
  unfold clause_remove_result, wmap_remove_first.
  entailer_with ltac:(int_auto).
  exists found0, found_2.
  exists
    (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm).
  subst wm'.
  unfold clause_watch_word. rewrite Hb.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_remove_entail_wit_3_4 : clause_remove_entail_wit_3_4.
Proof.
  naive_C_Rules.aggressive_pre_process.
  unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals in *.
  bind_fact ( retval_9 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_9.
  bind_fact ( vecp_remove_found (clause_watch_word c_pre clause_words (Znth 1 clause_words 0)) (Znth (lit_neg_c (Znth
      0 clause_words 0)) wm nil) found0 ) as H_vecp_remove_found.
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready.
  unfold clause_remove_ready in H_clause_remove_ready.
  destruct H_clause_remove_ready as (Hlen & _).
  assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
  assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize).
  rewrite zdiv_equiv in H_retval_9 by lia.
  rewrite clause_hdr_word_div2 in H_retval_9 by lia.
  assert (Hb : (2 <? Zlength clause_words)%Z = false)
    by (apply Z.ltb_ge; lia).
  unfold clause_watch_word in H_vecp_remove_found.
  rewrite Hb in H_vecp_remove_found.
  subst retval_10.
  set (wm' :=
    replace_Znth (lit_neg_c (Znth 1 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 1 clause_words 0))
          (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
            (vecp_remove_result
              (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)
          nil) found_2)
      (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
        (vecp_remove_result
          (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm)).
  set (stats' :=
    Znth 0 stats0 0 :: Znth 1 stats0 0 :: Znth 2 stats0 0 ::
    Znth 3 stats0 0 :: Znth 4 stats0 0 ::
    unsigned_last_nbits (Znth 5 stats0 0 - 1) 64 ::
    unsigned_last_nbits
      (Znth 6 stats0 0 - unsigned_last_nbits retval_12 64) 64 ::
    Znth 7 stats0 0 :: Znth 8 stats0 0 :: Znth 9 stats0 0 ::
    Znth 10 stats0 0 :: nil).
  sep_apply
    (stats_rep_from_solver_cells__clause_new s_pre
      (Znth 0 stats0 0) (Znth 1 stats0 0) (Znth 2 stats0 0)
      (Znth 3 stats0 0) (Znth 4 stats0 0)
      (unsigned_last_nbits (Znth 5 stats0 0 - 1) 64)
      (unsigned_last_nbits
        (Znth 6 stats0 0 - unsigned_last_nbits retval_12 64) 64)
      (Znth 7 stats0 0) (Znth 8 stats0 0)
      (Znth 9 stats0 0) (Znth 10 stats0 0)).
  unfold clause_remove_post.
  Exists wm'. Exists stats'.
  unfold clause_remove_result, wmap_remove_first.
  entailer_with ltac:(int_auto).
  exists found0, found_2.
  exists
    (replace_Znth (lit_neg_c (Znth 0 clause_words 0))
      (vecp_remove_result
        (Znth (lit_neg_c (Znth 0 clause_words 0)) wm nil) found0) wm).
  subst wm'.
  unfold clause_watch_word. rewrite Hb.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_remove partial_solve wits (4 proofs) ===== *)
Lemma proof_of_clause_remove_partial_solve_wit_12_pure : clause_remove_partial_solve_wit_12_pure.
Proof.
  naive_C_Rules.aggressive_pre_process.
  msat_clause_hdr_word_bounds_pure clause_words is_learnt.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_14_pure : clause_remove_partial_solve_wit_14_pure.
Proof.
  (naive_C_Rules.aggressive_pre_process);
  (bind_fact ( retval_5 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_5;
    bind_fact ( retval = lit_neg_c (Znth 0 clause_words 0) ) as H_retval;
    bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready).
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    dump_pre_spatial. exact Hwm.
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    dump_pre_spatial. exact Hcaps.
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; exact Hsize).
    rewrite zdiv_equiv in H_retval_5 by lia.
    rewrite clause_hdr_word_div2 in H_retval_5 by lia.
    assert (Hb : (2 <? Zlength clause_words)%Z = true)
      by (apply Z.ltb_lt; lia).
    unfold clause_watch_word in Hin0.
    rewrite Hb in Hin0.
    unfold vecp_remove_member.
    dump_pre_spatial. rewrite H_retval. exact Hin0.
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; exact Hsize).
    rewrite zdiv_equiv in H_retval_5 by lia.
    rewrite clause_hdr_word_div2 in H_retval_5 by lia.
    assert (Hb : (2 <? Zlength clause_words)%Z = true)
      by (apply Z.ltb_lt; lia).
    unfold clause_watch_word in Hin0.
    rewrite Hb in Hin0.
    unfold vecp_remove_member.
    dump_pre_spatial. rewrite H_retval. exact Hin0.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_15_pure : clause_remove_partial_solve_wit_15_pure.
Proof.
  (naive_C_Rules.aggressive_pre_process);
  (bind_fact ( retval_2 = tag_of_lit (Znth 1 clause_words 0) ) as H_retval_2;
    bind_fact ( retval_6 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_6;
    bind_fact ( retval = lit_neg_c (Znth 0 clause_words 0) ) as H_retval;
    bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready).
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    dump_pre_spatial. exact Hwm.
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    dump_pre_spatial. exact Hcaps.
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; exact Hsize).
    rewrite zdiv_equiv in H_retval_6 by lia.
    rewrite clause_hdr_word_div2 in H_retval_6 by lia.
    assert (Hb : (2 <? Zlength clause_words)%Z = false)
      by (apply Z.ltb_ge; lia).
    unfold clause_watch_word in Hin0.
    rewrite Hb in Hin0.
    unfold vecp_remove_member.
    dump_pre_spatial. rewrite H_retval_2, H_retval. exact Hin0.
  - unfold clause_remove_ready in H_clause_remove_ready.
    destruct H_clause_remove_ready as
      (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1).
    assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg.
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; exact Hsize).
    rewrite zdiv_equiv in H_retval_6 by lia.
    rewrite clause_hdr_word_div2 in H_retval_6 by lia.
    assert (Hb : (2 <? Zlength clause_words)%Z = false)
      by (apply Z.ltb_ge; lia).
    unfold clause_watch_word in Hin0.
    rewrite Hb in Hin0.
    unfold vecp_remove_member.
    dump_pre_spatial. rewrite H_retval_2, H_retval. exact Hin0.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_20_pure : clause_remove_partial_solve_wit_20_pure.
Proof.
  naive_C_Rules.aggressive_pre_process.
  msat_clause_hdr_word_bounds_pure clause_words is_learnt.
Qed.


(* ===== order_select return wits (5 proofs) ===== *)
Lemma proof_of_order_select_return_wit_3 : order_select_return_wit_3.
Proof.
  Unfold; left; intros.
  msat_order_select_sift_close_p5 s_pre order_ptr order_cap orderpos_ptr activity_ptr.
Qed.

Lemma proof_of_order_select_return_wit_4 : order_select_return_wit_4.
Proof.
  Unfold; left; intros.
  msat_order_select_sift_close_p5 s_pre order_ptr order_cap orderpos_ptr activity_ptr.
Qed.

Lemma proof_of_order_select_return_wit_5 : order_select_return_wit_5.
Proof.
  Unfold; left; intros.
  bind_fact ( Znth (next - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( order_select_sift_inv n next x i heap0 sift_heap_before sift_heap_now sift_orderpos_now assigns0 trail0
      qhead ) as H_order_select_sift_inv.
  replace (next - 0) with next in * by lia.
  assert (Hati : Znth i (replace_Znth i x sift_heap_now) 0 = x)
    by (rewrite Znth_replace_Znth_Same; lia).
  rewrite Hati in *.
  pose proof (order_select_sift_close_post__order_select
    n next x i heap0 sift_heap_before sift_heap_now sift_orderpos_now
    assigns0 trail0 qhead H_order_select_sift_inv H_Znth) as Hpost.
  prop_apply (store_int_range
    (&((s_pre) # "solver_t" ->ₛ "order" .ₛ "cap")) order_cap).
  Intros_p Hcap_range.
  prop_apply (IntArray.undef_seg_valid
    order_ptr (Zlength sift_heap_now) order_cap).
  Intros_p Hcap_room.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth x i sift_orderpos_now)).
  sep_apply_l_atomic (IntArray.full_to_seg order_ptr
    (Zlength sift_heap_now) (replace_Znth i x sift_heap_now)).
  Exists sift_seed_shadow_now sift_seed_value_now
    (replace_Znth i x sift_heap_now) (replace_Znth x i sift_orderpos_now).
  unfold veci_rep, veci_rep_at,
    veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists order_ptr.
  rewrite Zlength_replace_Znth.
  entailer_with ltac:(lia).
  csimpl. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_select_return_wit_6 : order_select_return_wit_6.
Proof.
  Unfold; left; intros.
  bind_fact ( Znth (Znth (0 - 0) heap_now 0 - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( order_select_loop_inv n heap0 heap_now orderpos_now assigns0 trail0 qhead ) as H_order_select_loop_inv.
  replace (0 - 0) with 0 in * by lia.
  replace (Znth 0 heap_now 0 - 0)
    with (Znth 0 heap_now 0) in * by lia.
  assert (Hzero : retval_2 - 1 = 0) by lia.
  rewrite Hzero in *.
  change (sublist 0 0 heap_now) with (@nil Z) in *.
  pose proof (order_select_singleton_post__order_select
    n heap0 heap_now orderpos_now assigns0 trail0 qhead
    H_order_select_loop_inv ltac:(lia) H_Znth) as Hpost.
  sep_apply_l_atomic (IntArray.full_to_seg orderpos_ptr n
    (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now)).
  Exists seed_shadow_now seed_value_now (@nil Z)
    (replace_Znth (Znth 0 heap_now 0) (-1) orderpos_now).
  unfold veci_rep, veci_rep_at,
    veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists order_ptr.
  entailer_with ltac:(lia).
  csimpl. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_select_return_wit_7 : order_select_return_wit_7.
Proof.
  Unfold; left; intros.
  bind_fact ( Znth (retval - 0) assigns0 0 = 0 ) as H_Znth.
  bind_fact ( 0 <= retval ) as H_retval.
  bind_fact ( retval < n ) as H_retval_2.
  bind_fact ( order_select_pre n heap0 orderpos0 assigns0 trail0 qhead ) as H_order_select_pre.
  replace (retval - 0) with retval in * by lia.
  pose proof (order_select_noop_post__order_select
    n retval heap0 orderpos0 assigns0 trail0 qhead
    H_order_select_pre (conj H_retval H_retval_2) H_Znth) as Hpost.
  Exists z2 v2_2 heap0 orderpos0.
  unfold veci_rep, veci_rep_at,
    veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists order_ptr.
  entailer_with lia.
  csimpl. msat_manual_entailer_with lia.
Qed.

(* ===== order_select which_implies wits (1 proofs) ===== *)
Lemma proof_of_order_select_which_implies_wit_1 : order_select_which_implies_wit_1.
Proof.
  Unfold; right; intros.
  bind_fact ( order_select_pre n heap0 orderpos0 assigns0 trail0 qhead ) as H_order_select_pre.
  unfold order_select_pre in H_order_select_pre.
  assert (Hn : 0 <= n).
  { destruct H_order_select_pre as (_ & _ & _ & _ & Hlen & _).
    rewrite <- Hlen. apply Zlength_nonneg. }
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_analyze entail wits (13 proofs) ===== *)
Lemma proof_of_solver_analyze_entail_wit_1 : solver_analyze_entail_wit_1.
Proof.
  Unfold. unfold solver_analyze_pre.
  left. intros.
  Exists cap_prime.
  assert (Hpack :
    ((&(learnt_pre # "veci_t" ->ₛ "size")) # Int |->
       Zlength (z_nil +:: (-2)) **
     (&(learnt_pre # "veci_t" ->ₛ "cap")) # Int |-> cap_prime **
     (&(learnt_pre # "veci_t" ->ₛ "ptr")) # Ptr |-> p_prime **
     IntArray.seg p_prime 0 (Zlength (z_nil +:: (-2))) (z_nil +:: (-2)) **
     IntArray.undef_seg p_prime (Zlength (z_nil +:: (-2))) cap_prime)
    |-- veci_rep learnt_pre (z_nil +:: (-2)) cap_prime).
  { unfold veci_rep.
    Exists p_prime.
    unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
    pose proof (Zlength_nonneg (z_nil +:: (-2))) as Hlength_nonnegative.
    entailer_with ltac:(lia). }
  sep_apply Hpack.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_2_learnt : solver_analyze_entail_wit_12_2_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_2_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 = retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mact)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( Zlength (ms_tagged Mact +:: retval_7) <= cap_prime ) as H_Zlength.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & Hreason & HSold & ERscan & HLold).
  msat_analyze_tag_step_open_p5 v Mnext anz_n anz_F anz_A_arr K anz_focus
    Mscan_2 j clause_words2 cap_prime activity1 orderpos1 heap1 var_inc1
    Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2))
    by (apply ms_analyze_tags_perm_snoc_s; exact Hpermold).
  assert (Hempty : sublist 1 1 Ccur = nil) by (apply ms_sublist_one_one_nil_p5).
  assert (ESbase : Sscan_2 = zremove x_2 S0_2).
  { rewrite HSold. subst j. rewrite Hempty.
    unfold resolve_S, resolve_new_S. cbn [filter map app].
    rewrite app_nil_r. reflexivity. }
  assert (ELbase : learnt_scan_2 = learnt0_2).
  { rewrite HLold. subst j. rewrite Hempty.
    unfold resolve_learnt, resolve_new_lits. cbn [filter map app].
    rewrite app_nil_r. reflexivity. }
  assert (Hnotcur : ~ In v (analyze_tags Sscan_2 Rscan_2 learnt_scan_2))
    by (apply (ms_analyze_var_untagged anz_n (ms_tags Mscan_2)
          (ms_tagged Mscan_2));
        [exact Htagsold | exact Hpermold | unfold v; lia | unfold v in *; lia]).
  assert (Hnotinitial : ~ In v (analyze_tags S0_2 R0_2 learnt0_2))
    by (apply (ms_analyze_notin_initial_resolved_p5 v x_2 S0_2 R0_2 Sscan_2
          Rscan_2 learnt0_2 learnt_scan_2);
        [exact Hnotcur | exact ESbase | exact ERscan | exact ELbase]).
  assert (Hnotmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = false).
  { apply zmem_false_iff. exact Hnotinitial. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  assert (Hvneqx : v <> x_2).
  { intro Evx. apply Hnotinitial.
    unfold analyze_tags. apply in_or_app. left. rewrite Evx. exact Hinx. }
  destruct Hreason as
    [bx [dx [rx [Hassx [Hlevx [Hrankx [Hsatx Hside]]]]]]].
  assert (Hvarqneq : literal_var (lit_denote q) <> x_2)
    by (rewrite lit_var_c_denote; unfold q, v in *;
        replace (j - 0) with j in Hvneqx by lia; exact Hvneqx).
  destruct (Hside (lit_denote q) HqC Hvarqneq) as
    [_ [dq [rq [Hlevq [Hrankq [Hdqle Hrqlt]]]]]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Eqcv : lit_var_c q = v).
  { rewrite <- lit_var_c_denote. exact Eqv. }
  rewrite Eqv in Hlevq, Hrankq.
  assert (Hdqcur : dq = Zlength (mt_lim (ms_core Mscan_2))).
  { rewrite <- H_Mscan_2 in Hlevq, Hrankq.
    unfold msolver_view, view_of in Hlevq, Hrankq.
    cbn [level_of assignment_rank] in Hlevq, Hrankq.
    rewrite Hrankq in Hlevq. cbn in Hlevq. injection Hlevq as Edq.
    pose proof (trail_pos_bound (ms_core Mscan_2) v rq Hrankq) as Hrqb.
    pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
    rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrankq) in Hagree.
    fold v in H_retval_10. rewrite H_retval_10, H_retval_11 in H_Znth.
    rewrite Edq in Hagree.
    replace (v - 0) with v in H_Znth by lia.
    (* The read-back hypothesis is spelled at Mact, not at Mscan_2. *)
    rewrite H_Mscan_2.
    lia. }
  assert (Hat : at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = true).
  { apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite Eqv, Hlevq.
    rewrite msolver_view_current_level, <- H_Mscan_2, Hdqcur. reflexivity. }
  assert (Hbelow : below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { unfold below_current_b. rewrite Eqv, Hlevq.
    rewrite msolver_view_current_level, <- H_Mscan_2, Hdqcur.
    rewrite Z.ltb_irrefl, Bool.andb_false_r. reflexivity. }
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HSnext : Sscan_2 ++ (v :: nil) =
      resolve_S (msolver_view anz_n Mact) x_2 (sublist 1 (j + 1) Ccur)
        S0_2 R0_2 learnt0_2).
  { unfold resolve_S, resolve_new_S in *.
    rewrite Hprefix, filter_app, map_app, filter_app.
    cbn [filter map]. rewrite Hat.
    replace (map literal_var (lit_denote q :: nil)) with (v :: nil)
      by (cbn [map]; rewrite Eqv; reflexivity).
    cbn [filter]. rewrite Hnotmem. cbn [negb].
    rewrite HSold. rewrite !app_assoc. reflexivity. }
  assert (HLnext : learnt_scan_2 =
      resolve_learnt (msolver_view anz_n Mact) (sublist 1 (j + 1) Ccur)
        S0_2 R0_2 learnt0_2).
  { unfold resolve_learnt, resolve_new_lits in *.
    rewrite Hprefix, filter_app. cbn [filter]. rewrite Hbelow. cbn [filter andb].
    rewrite app_nil_r. exact HLold. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2 words_scan_2 (cnt + 1))
    by (msat_analyze_scan_inv_tag Mnext phase H_Ccur HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 (Sscan_2 ++ (v :: nil)) Rscan_2
    learnt_scan_2 words_scan_2 Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame_p5 Mnext Mscan_2 v cap_prime activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    msat_analyze_tagged_reseal_scan_p5 v Mscan_2 p_prime H_retval_7 H_retval_6
      H_Zlength H_Mscan_2 p_lim p_order.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_3_learnt : solver_analyze_entail_wit_12_3_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_3_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 = retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( Zlength (ms_tagged Mscan_2 +:: retval_7) <= cap_prime ) as H_Zlength.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  set (v := lit_var_c (Znth (j - 0) clause_words2 0)).
  set (Mnext := analyze_tag_step_msolver Mscan_2
    (replace_Znth v 1 (ms_tags Mscan_2))
    (ms_tagged Mscan_2 ++ (v :: nil)) cap_prime activity1 orderpos1 heap1 var_inc1).
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & _).
  assert (HSold : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hreadynew : analysis_cancel_ready anz_n anz_F anz_A_arr K Mnext anz_focus)
    by (unfold Mnext; apply ms_analyze_tag_step_cancel_ready_p5;
        [exact Hreadyold | exact H_order_heap_wf | exact H_u_2]).
  assert (Htagsnew : analysis_tags_exact anz_n (replace_Znth v 1 (ms_tags Mscan_2))
      (ms_tagged Mscan_2 ++ (v :: nil)))
    by (apply ms_analysis_tags_exact_snoc;
        [exact Htagsold | unfold v; lia | unfold v in *; lia]).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2))
    by (apply ms_analyze_tags_perm_snoc_s; exact Hpermold).
  assert (Hcert : propagation_conflict_cert anz_n anz_F Mact Ccur)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (EscanCore : ms_core Mscan_2 = ms_core Mact).
  { unfold analysis_core_equiv in H_analysis_core_equiv.
    destruct H_analysis_core_equiv as [_ [_ [_ [EcoreEq _]]]]. exact EcoreEq. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [_ [_ _]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite EscanCore. rewrite Eqv in Hass. exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  assert (Hrqb : Z.of_nat rq < Zlength (mt_trail (ms_core Mscan_2))).
  { apply (trail_pos_bound (ms_core Mscan_2) v rq Hrank). }
  pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
  rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrank) in Hagree.
  assert (Hdqcur : level_of_index (ms_core Mscan_2) (Z.of_nat rq) =
      Zlength (mt_lim (ms_core Mscan_2))).
  { fold v in H_retval_10. rewrite H_retval_10, H_retval_11 in H_Znth.
    replace (v - 0) with v in H_Znth by lia. lia. }
  assert (Hat : at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = true).
  { apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite Eqv.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite <- EscanCore.
    rewrite Hrank. cbn. f_equal. exact Hdqcur. }
  assert (Hbelow : below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { unfold below_current_b.
    rewrite Eqv.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite <- EscanCore.
    rewrite Hrank. cbn. rewrite Hdqcur, Z.ltb_irrefl, Bool.andb_false_r.
    reflexivity. }
  msat_analyze_start_step_tag_p5 q v anz_n Mact Ccur j clause_words2
    Sscan_2 learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow Eqv.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext anz_focus phase Ccur
      (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2 words_scan_2 (cnt + 1))
    by (msat_analyze_scan_inv_tag Mnext phase H_Ccur HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 (Sscan_2 ++ (v :: nil)) Rscan_2
    learnt_scan_2 words_scan_2 Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame_p5 Mnext Mscan_2 v cap_prime activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    msat_analyze_tagged_reseal_p5 v Mscan_2 p_prime H_retval_7 H_retval_6 H_Zlength.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_4_learnt : solver_analyze_entail_wit_12_4_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_4_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 = retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mact)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( Zlength (ms_tagged Mact +:: retval_7) <= cap_prime ) as H_Zlength.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  set (v := lit_var_c (Znth (j - 0) clause_words2 0)).
  set (Mnext := analyze_tag_step_msolver Mscan_2
    (replace_Znth v 1 (ms_tags Mscan_2))
    (ms_tagged Mscan_2 ++ (v :: nil)) cap_prime activity1 orderpos1 heap1 var_inc1).
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & _).
  assert (HSold : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hreadynew : analysis_cancel_ready anz_n anz_F anz_A_arr K Mnext anz_focus)
    by (unfold Mnext; apply ms_analyze_tag_step_cancel_ready_p5;
        [exact Hreadyold | exact H_order_heap_wf | exact H_u_2]).
  assert (Htagsnew : analysis_tags_exact anz_n (replace_Znth v 1 (ms_tags Mscan_2))
      (ms_tagged Mscan_2 ++ (v :: nil)))
    by (apply ms_analysis_tags_exact_snoc;
        [exact Htagsold | unfold v; lia | unfold v in *; lia]).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2))
    by (apply ms_analyze_tags_perm_snoc_s; exact Hpermold).
  assert (Hcert : propagation_conflict_cert anz_n anz_F Mact Ccur)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [_ [_ _]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite H_Mscan_2. rewrite Eqv in Hass. exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  assert (Hrqb : Z.of_nat rq < Zlength (mt_trail (ms_core Mscan_2))).
  { apply (trail_pos_bound (ms_core Mscan_2) v rq Hrank). }
  pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
  rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrank) in Hagree.
  assert (Hdqcur : level_of_index (ms_core Mscan_2) (Z.of_nat rq) =
      Zlength (mt_lim (ms_core Mscan_2))).
  { fold v in H_retval_10. rewrite H_retval_10, H_retval_11 in H_Znth.
    replace (v - 0) with v in H_Znth by lia.
    (* The read-back hypothesis is spelled at Mact, not at Mscan_2. *)
    rewrite <- H_Mscan_2 in H_Znth. lia. }
  assert (Hat : at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = true).
  { apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite Eqv, <- H_Mscan_2.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite Hrank. cbn. f_equal. exact Hdqcur. }
  assert (Hbelow : below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { unfold below_current_b.
    rewrite Eqv, <- H_Mscan_2.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite Hrank. cbn. rewrite Hdqcur, Z.ltb_irrefl, Bool.andb_false_r.
    reflexivity. }
  msat_analyze_start_step_tag_p5 q v anz_n Mact Ccur j clause_words2
    Sscan_2 learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow Eqv.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext anz_focus phase Ccur
      (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2 words_scan_2 (cnt + 1))
    by (msat_analyze_scan_inv_tag Mnext phase H_Ccur HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 (Sscan_2 ++ (v :: nil)) Rscan_2
    learnt_scan_2 words_scan_2 Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame_p5 Mnext Mscan_2 v cap_prime activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    msat_analyze_tagged_reseal_scan_p5 v Mscan_2 p_prime H_retval_7 H_retval_6
      H_Zlength H_Mscan_2 p_lim p_order.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_5_learnt : solver_analyze_entail_wit_12_5_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_5_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  assert (H_l_prime_2 :
      words_scan_2 +:: Znth (j - 0) clause_words2 0 =
      words_scan_2 +:: Znth (j - 0) clause_words2 0) by reflexivity.
  bind_fact ( Zlength (words_scan_2 +:: Znth (j - 0) clause_words2 0) <= cap_prime_2 ) as H_Zlength.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( Zlength (ms_tagged Mscan_2 +:: retval_7) <= cap_prime ) as H_Zlength_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 > 0 ) as H_Znth_2.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & Hreason & HSold & ERscan & HLold).
  msat_analyze_tag_step_open_p5 v Mnext anz_n anz_F anz_A_arr K anz_focus
    Mscan_2 j clause_words2 cap_prime activity1 orderpos1 heap1 var_inc1
    Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Hnotcur : ~ In v (analyze_tags Sscan_2 Rscan_2 learnt_scan_2))
    by (apply (ms_analyze_var_untagged anz_n (ms_tags Mscan_2)
          (ms_tagged Mscan_2));
        [exact Htagsold | exact Hpermold | unfold v; lia | unfold v in *; lia]).
  assert (Hvneqx : v <> x_2).
  { intro Heq. apply Hnotcur. rewrite Heq.
    unfold analyze_tags. apply in_or_app. right.
    apply in_or_app. left. rewrite ERscan. simpl. tauto. }
  assert (Hnotinitial : ~ In v (analyze_tags S0_2 R0_2 learnt0_2)).
  { intro Hin. apply Hnotcur.
    unfold analyze_tags in *.
    rewrite !in_app_iff in *.
    destruct Hin as [HinS|[HinR|HinL]].
    - left. rewrite HSold. unfold resolve_S.
      apply in_or_app. left. apply In_zremove_iff. tauto.
    - right. left. rewrite ERscan. simpl. tauto.
    - right. right. rewrite HLold. unfold resolve_learnt.
      rewrite map_app. apply in_or_app. left. exact HinL. }
  assert (Hnotmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = false).
  { apply zmem_false_iff. exact Hnotinitial. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hreason as
    [bx [dx [rx [Hassx [Hlevx [Hrankx [Hsatx Hside]]]]]]].
  assert (Hvarqneq : literal_var (lit_denote q) <> x_2)
    by (rewrite lit_var_c_denote; unfold q, v in *;
        replace (j - 0) with j in Hvneqx by lia; exact Hvneqx).
  destruct (Hside (lit_denote q) HqC Hvarqneq) as
    [_ [dq [rq [Hlevq [Hrankq [Hdqle Hrqlt]]]]]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags Sscan_2 Rscan_2
        (learnt_scan_2 ++ (lit_denote q :: nil))))
    by (rewrite <- Eqv; apply ms_analyze_tags_perm_snoc_l_p5; exact Hpermold).
  msat_analyze_scan_level_transport_p5 v Mscan_2 rq Hlevq Hrankq Eqv Eview
    Htrailwf.
  msat_analyze_selected_level_bounds_p5 v Mscan_2 rq dq
    H_retval_5 H_Znth_2 H_retval_10 H_retval_11 H_Znth Edq Hagree.
  msat_analyze_offlevel_flags_p5 anz_n Mact q dq Hlevq0 Hdqne Eqv Eview.
  msat_analyze_scan_words_grow_p5 anz_n q Mscan_2 words_scan_2 Sscan_2 Rscan_2
    R0_2 learnt_scan_2 Hpermold ERscan.
  msat_analyze_resolve_step_word_p5 q anz_n Mact Ccur j clause_words2 x_2 S0_2
    R0_2 learnt0_2 Sscan_2 learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow
    Eqv Hnotmem.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      Sscan_2 Rscan_2 (learnt_scan_2 ++ (lit_denote q :: nil))
      (words_scan_2 ++ (q :: nil)) cnt)
    by (msat_analyze_scan_inv_word_p5 Mnext phase H_Ccur Hwordlennew
          Hwordsnext HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists cap_prime_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
    (learnt_scan_2 ++ (lit_denote q :: nil))
    (words_scan_2 ++ (q :: nil)) Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame_p5 Mnext Mscan_2 v cap_prime activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    msat_analyze_word_reseal_p5 v q Mscan_2 j words_scan_2 learnt_pre p_prime_2
      cap_prime_2 s_pre p_prime cap_prime H_l_prime_2 H_Zlength H_retval_7
      H_retval_6 H_Zlength_2.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_6_learnt : solver_analyze_entail_wit_12_6_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_6_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  assert (H_l_prime_2 :
      words_scan_2 +:: Znth (j - 0) clause_words2 0 =
      words_scan_2 +:: Znth (j - 0) clause_words2 0) by reflexivity.
  bind_fact ( Zlength (words_scan_2 +:: Znth (j - 0) clause_words2 0) <= cap_prime_2 ) as H_Zlength.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mact)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( Zlength (ms_tagged Mact +:: retval_7) <= cap_prime ) as H_Zlength_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 > 0 ) as H_Znth_2.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  (* The level-limit read-back and the tagged-capacity bound arrive spelled at
     the active state; [H_Mscan_2] puts them at the scan state, which is the
     spelling every step below (and the shared closer) uses. *)
  rewrite <- H_Mscan_2 in H_retval_11, H_Zlength_2.
  Left.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & Hreason & HSold & ERscan & HLold).
  msat_analyze_tag_step_open_p5 v Mnext anz_n anz_F anz_A_arr K anz_focus
    Mscan_2 j clause_words2 cap_prime activity1 orderpos1 heap1 var_inc1
    Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Hempty : sublist 1 1 Ccur = nil) by (apply ms_sublist_one_one_nil_p5).
  assert (ESbase : Sscan_2 = zremove x_2 S0_2).
  { rewrite HSold. subst j. rewrite Hempty.
    unfold resolve_S, resolve_new_S. cbn [filter map app].
    rewrite app_nil_r. reflexivity. }
  assert (ELbase : learnt_scan_2 = learnt0_2).
  { rewrite HLold. subst j. rewrite Hempty.
    unfold resolve_learnt, resolve_new_lits. cbn [filter map app].
    rewrite app_nil_r. reflexivity. }
  assert (Hnotcur : ~ In v (analyze_tags Sscan_2 Rscan_2 learnt_scan_2))
    by (apply (ms_analyze_var_untagged anz_n (ms_tags Mscan_2)
          (ms_tagged Mscan_2));
        [exact Htagsold | exact Hpermold | unfold v; lia | unfold v in *; lia]).
  assert (Hnotinitial : ~ In v (analyze_tags S0_2 R0_2 learnt0_2))
    by (apply (ms_analyze_notin_initial_resolved_p5 v x_2 S0_2 R0_2 Sscan_2
          Rscan_2 learnt0_2 learnt_scan_2);
        [exact Hnotcur | exact ESbase | exact ERscan | exact ELbase]).
  assert (Hnotmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = false).
  { apply zmem_false_iff. exact Hnotinitial. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  assert (Hvneqx : v <> x_2).
  { intro Evx. apply Hnotinitial.
    unfold analyze_tags. apply in_or_app. left. rewrite Evx. exact Hinx. }
  destruct Hreason as
    [bx [dx [rx [Hassx [Hlevx [Hrankx [Hsatx Hside]]]]]]].
  assert (Hvarqneq : literal_var (lit_denote q) <> x_2)
    by (rewrite lit_var_c_denote; unfold q, v in *;
        replace (j - 0) with j in Hvneqx by lia; exact Hvneqx).
  destruct (Hside (lit_denote q) HqC Hvarqneq) as
    [_ [dq [rq [Hlevq [Hrankq [Hdqle Hrqlt]]]]]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags Sscan_2 Rscan_2
        (learnt_scan_2 ++ (lit_denote q :: nil))))
    by (rewrite <- Eqv; apply ms_analyze_tags_perm_snoc_l_p5; exact Hpermold).
  msat_analyze_scan_level_transport_p5 v Mscan_2 rq Hlevq Hrankq Eqv Eview
    Htrailwf.
  msat_analyze_selected_level_bounds_p5 v Mscan_2 rq dq
    H_retval_5 H_Znth_2 H_retval_10 H_retval_11 H_Znth Edq Hagree.
  msat_analyze_offlevel_flags_p5 anz_n Mact q dq Hlevq0 Hdqne Eqv Eview.
  msat_analyze_scan_words_grow_p5 anz_n q Mscan_2 words_scan_2 Sscan_2 Rscan_2
    R0_2 learnt_scan_2 Hpermold ERscan.
  msat_analyze_resolve_step_word_p5 q anz_n Mact Ccur j clause_words2 x_2 S0_2
    R0_2 learnt0_2 Sscan_2 learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow
    Eqv Hnotmem.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      Sscan_2 Rscan_2 (learnt_scan_2 ++ (lit_denote q :: nil))
      (words_scan_2 ++ (q :: nil)) cnt)
    by (msat_analyze_scan_inv_word_p5 Mnext phase H_Ccur Hwordlennew
          Hwordsnext HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists cap_prime_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
    (learnt_scan_2 ++ (lit_denote q :: nil))
    (words_scan_2 ++ (q :: nil)) Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame_p5 Mnext Mscan_2 v cap_prime activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    (* The residual LHS spells trail_lim / order / tagged at Mact while the RHS
       (and the folds below) stay at Mscan_2; cancellation is syntactic. *)
    rewrite <- H_Mscan_2.
    msat_analyze_word_reseal_p5 v q Mscan_2 j words_scan_2 learnt_pre p_prime_2
      cap_prime_2 s_pre p_prime cap_prime H_l_prime_2 H_Zlength H_retval_7
      H_retval_6 H_Zlength_2.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_7_learnt : solver_analyze_entail_wit_12_7_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_7_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  assert (H_l_prime_2 :
      words_scan_2 +:: Znth (j - 0) clause_words2 0 =
      words_scan_2 +:: Znth (j - 0) clause_words2 0) by reflexivity.
  bind_fact ( Zlength (words_scan_2 +:: Znth (j - 0) clause_words2 0) <= cap_prime_2 ) as H_Zlength.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( Zlength (ms_tagged Mscan_2 +:: retval_7) <= cap_prime ) as H_Zlength_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 > 0 ) as H_Znth_2.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_initial_pack_p5 H_phase H_analyze_clause_scan_inv)
    as (Hcert & HSold & HLold).
  msat_analyze_tag_step_open_p5 v Mnext anz_n anz_F anz_A_arr K anz_focus
    Mscan_2 j clause_words2 cap_prime activity1 orderpos1 heap1 var_inc1
    Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (EcoreScan : ms_core Mscan_2 = ms_core Mact).
  { unfold analysis_core_equiv in H_analysis_core_equiv. tauto. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [HwfC [HndC [lcur [Hlcur Hlevcur]]]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags Sscan_2 Rscan_2
        (learnt_scan_2 ++ (lit_denote q :: nil))))
    by (rewrite <- Eqv; apply ms_analyze_tags_perm_snoc_l_p5; exact Hpermold).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite EcoreScan. rewrite Eqv in Hass.
    exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  msat_analyze_initial_level_readback_p5 v anz_n Mact Mscan_2 rq
    Hrank Htrailwf Eview H_retval_5 H_Znth_2 H_retval_10 H_retval_11 H_Znth.
  msat_analyze_offlevel_flags_p5 anz_n Mact q dq Hlevq Hdqne Eqv Eview.
  assert (Hwordlenold : Zlength words_scan_2 = 1 + Zlength learnt_scan_2)
    by (apply ms_learnt_words_len_p5; assumption).
  assert (Hwordsnext : lits_denote (tl (words_scan_2 ++ (q :: nil))) =
      learnt_scan_2 ++ (lit_denote q :: nil))
    by (apply ms_learnt_words_snoc_p5; assumption).
  msat_analyze_start_step_word_p5 q anz_n Mact Ccur j clause_words2 Sscan_2
    learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow.
  assert (Hwordlennew :
      1 <= Zlength (words_scan_2 ++ (q :: nil)) <= anz_n).
  { pose proof (ms_analyze_start_learnt_room_p5 anz_n (j + 1)
      (msolver_view anz_n Mact) Ccur lcur HwfC HndC Hlcur
      ltac:(rewrite msolver_view_current_level; exact Hlevcur)) as Hroom.
    rewrite <- HLnext, Zlength_app, Zlength_cons, Zlength_nil in Hroom.
    rewrite Zlength_app, Zlength_cons, Zlength_nil, Hwordlenold.
    pose proof (Zlength_nonneg learnt_scan_2). lia. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      Sscan_2 Rscan_2 (learnt_scan_2 ++ (lit_denote q :: nil))
      (words_scan_2 ++ (q :: nil)) cnt)
    by (msat_analyze_scan_inv_word_p5 Mnext phase H_Ccur Hwordlennew
          Hwordsnext HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists cap_prime_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
    (learnt_scan_2 ++ (lit_denote q :: nil))
    (words_scan_2 ++ (q :: nil)) Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame_p5 Mnext Mscan_2 v cap_prime activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    msat_analyze_word_reseal_p5 v q Mscan_2 j words_scan_2 learnt_pre p_prime_2
      cap_prime_2 s_pre p_prime cap_prime H_l_prime_2 H_Zlength H_retval_7
      H_retval_6 H_Zlength_2.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_8_learnt : solver_analyze_entail_wit_12_8_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_8_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  assert (H_l_prime_2 :
      words_scan_2 +:: Znth (j - 0) clause_words2 0 =
      words_scan_2 +:: Znth (j - 0) clause_words2 0) by reflexivity.
  bind_fact ( Zlength (words_scan_2 +:: Znth (j - 0) clause_words2 0) <= cap_prime_2 ) as H_Zlength.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mact)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( Zlength (ms_tagged Mact +:: retval_7) <= cap_prime ) as H_Zlength_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 > 0 ) as H_Znth_2.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  (* The level-limit read-back and the tagged-capacity bound arrive spelled at
     the active state; [H_Mscan_2] puts them at the scan state, which is the
     spelling every step below (and the shared closer) uses. *)
  rewrite <- H_Mscan_2 in H_retval_11, H_Zlength_2.
  Right.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_initial_pack_p5 H_phase H_analyze_clause_scan_inv)
    as (Hcert & HSold & HLold).
  msat_analyze_tag_step_open_p5 v Mnext anz_n anz_F anz_A_arr K anz_focus
    Mscan_2 j clause_words2 cap_prime activity1 orderpos1 heap1 var_inc1
    Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [HwfC [HndC [lcur [Hlcur Hlevcur]]]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags Sscan_2 Rscan_2
        (learnt_scan_2 ++ (lit_denote q :: nil))))
    by (rewrite <- Eqv; apply ms_analyze_tags_perm_snoc_l_p5; exact Hpermold).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite H_Mscan_2. rewrite Eqv in Hass. exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  msat_analyze_initial_level_readback_p5 v anz_n Mact Mscan_2 rq
    Hrank Htrailwf Eview H_retval_5 H_Znth_2 H_retval_10 H_retval_11 H_Znth.
  msat_analyze_offlevel_flags_p5 anz_n Mact q dq Hlevq Hdqne Eqv Eview.
  assert (Hneqcur : literal_var lcur <> v).
  { intro Heq. rewrite Heq, Hlevq in Hlevcur.
    injection Hlevcur as Ecur. rewrite <- H_Mscan_2 in Ecur. lia. }
  assert (Hn2 : 2 <= anz_n).
  { rewrite Forall_forall in HwfC.
    pose proof (HwfC (lit_denote q) HqC) as Hqwf.
    pose proof (HwfC lcur Hlcur) as Hcurwf.
    unfold literal_wf, var_in_range in Hqwf, Hcurwf.
    rewrite Eqv in Hqwf. lia. }
  assert (HLempty : learnt_scan_2 = nil).
  { rewrite HLold. subst j. unfold sublist, analyze_start_learnt.
    cbn. reflexivity. }
  assert (Htailnil : tl words_scan_2 = nil).
  { unfold lits_denote in Hwordsold. rewrite HLempty in Hwordsold.
    apply map_eq_nil in Hwordsold. exact Hwordsold. }
  assert (Hwordlenold : Zlength words_scan_2 = 1).
  { destruct words_scan_2 as [|w ws].
    - rewrite Zlength_nil in Hwordlower. lia.
    - cbn in Htailnil. subst ws. reflexivity. }
  assert (Hwordlennew : 1 <= Zlength (words_scan_2 ++ (q :: nil)) <= anz_n).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hwordsnext : lits_denote (tl (words_scan_2 ++ (q :: nil))) =
      learnt_scan_2 ++ (lit_denote q :: nil)).
  { destruct words_scan_2 as [|w ws].
    - rewrite Zlength_nil in Hwordlower. lia.
    - cbn in Htailnil. subst ws.
      cbn [lits_denote]. rewrite HLempty. reflexivity. }
  msat_analyze_start_step_word_p5 q anz_n Mact Ccur j clause_words2 Sscan_2
    learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      Sscan_2 Rscan_2 (learnt_scan_2 ++ (lit_denote q :: nil))
      (words_scan_2 ++ (q :: nil)) cnt)
    by (msat_analyze_scan_inv_word_p5 Mnext phase H_Ccur Hwordlennew
          Hwordsnext HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists cap_prime_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
    (learnt_scan_2 ++ (lit_denote q :: nil))
    (words_scan_2 ++ (q :: nil)) Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame_p5 Mnext Mscan_2 v cap_prime activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    (* The residual LHS spells trail_lim / order / tagged at Mact while the RHS
       (and the folds below) stay at Mscan_2; cancellation is syntactic. *)
    rewrite <- H_Mscan_2.
    msat_analyze_word_reseal_p5 v q Mscan_2 j words_scan_2 learnt_pre p_prime_2
      cap_prime_2 s_pre p_prime cap_prime H_l_prime_2 H_Zlength H_retval_7
      H_retval_6 H_Zlength_2.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_9_learnt : solver_analyze_entail_wit_12_9_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_9_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_4 - 0) (ms_tags Mscan_2) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_4 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_4.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  Right.
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mscan_2)
      (ms_tagged Mscan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hperm : Permutation (ms_tagged Mscan_2)
      (analyze_tags Sscan_2 Rscan_2 learnt_scan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (HS : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HR : Rscan_2 = nil) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HL : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  subst j. unfold sublist, analyze_start_S in HS.
  unfold sublist, analyze_start_learnt in HL. cbn in HS, HL.
  subst Sscan_2 Rscan_2 learnt_scan_2.
  unfold analyze_tags in Hperm. cbn in Hperm.
  assert (Htaggednil : ms_tagged Mscan_2 = nil).
  { apply Permutation_nil. apply Permutation_sym. exact Hperm. }
  destruct Htags as [Hlen [_ [_ [Hcells Hiff]]]].
  set (v := lit_var_c (Znth (0 - 0) clause_words2 0)).
  assert (Hv : 0 <= v < anz_n) by (unfold v; lia).
  assert (Hvr : 0 <= v < Zlength (ms_tags Mscan_2)) by lia.
  pose proof (Forall_Znth_elim Z (fun z => z = 0 \/ z = 1)
    (ms_tags Mscan_2) 0 v Hcells Hvr) as Hcell.
  assert (Htag1 : Znth v (ms_tags Mscan_2) 0 = 1).
  { destruct Hcell as [H0|H1]; [exfalso|exact H1].
    apply H_Znth. rewrite H_retval_4. fold v.
    replace (v - 0) with v by lia. exact H0. }
  apply (proj1 (Hiff v Hv)) in Htag1.
  rewrite Htaggednil in Htag1. contradiction.
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_10_learnt : solver_analyze_entail_wit_12_10_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_10_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_4 - 0) (ms_tags Mscan_2) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_4 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_4.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( 0 <= lit_var_c (Znth (j - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (j - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  set (q := Znth j clause_words2 0).
  set (v := lit_var_c q).
  assert (Eqv : literal_var (lit_denote q) = v).
  { rewrite lit_var_c_denote. reflexivity. }
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mscan_2)
      (ms_tagged Mscan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hperm : Permutation (ms_tagged Mscan_2)
      (analyze_tags Sscan_2 Rscan_2 learnt_scan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (HS : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HR : Rscan_2 = nil) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HL : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HndC : NoDup (map literal_var Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  destruct Htags as [Hlen [_ [_ [Hcells Hiff]]]].
  assert (Hv : 0 <= v < anz_n).
  { unfold v, q. replace (j - 0) with j in H_lit_var_c, H_lit_var_c_2 by lia. lia. }
  assert (Hvr : 0 <= v < Zlength (ms_tags Mscan_2)) by lia.
  pose proof (Forall_Znth_elim Z (fun z => z = 0 \/ z = 1)
    (ms_tags Mscan_2) 0 v Hcells Hvr) as Hcell.
  assert (Htag1 : Znth v (ms_tags Mscan_2) 0 = 1).
  { destruct Hcell as [H0|H1]; [exfalso|exact H1].
    apply H_Znth. rewrite H_retval_4.
    replace (j - 0) with j by lia. fold q. fold v.
    replace (v - 0) with v by lia. exact H0. }
  apply (proj1 (Hiff v Hv)) in Htag1.
  pose proof (Permutation_in v Hperm Htag1) as HinAnalyze.
  assert (HinPrefix : In v (map literal_var (sublist 0 j Ccur))).
  { rewrite HS, HR, HL in HinAnalyze.
    unfold analyze_tags, analyze_start_S, analyze_start_learnt in HinAnalyze.
    cbn in HinAnalyze. rewrite !in_app_iff in HinAnalyze.
    destruct HinAnalyze as [HinS|HinL].
    - apply in_map_iff in HinS. destruct HinS as [l [<- Hl]].
      apply filter_In in Hl. destruct Hl as [Hl _].
      apply in_map. exact Hl.
    - apply in_map_iff in HinL. destruct HinL as [l [<- Hl]].
      apply filter_In in Hl. destruct Hl as [Hl _].
      apply in_map. exact Hl. }
  assert (Hprefix : sublist 0 (j + 1) Ccur =
      sublist 0 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 0 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HndSub : NoDup (map literal_var (sublist 0 (j + 1) Ccur))).
  { unfold sublist. cbn. pose proof HndC as Hndpre.
    rewrite <- (firstn_skipn (Z.to_nat (j + 1)) Ccur) in Hndpre.
    rewrite map_app in Hndpre.
    eapply NoDup_app_remove_r. exact Hndpre. }
  rewrite Hprefix, map_app in HndSub. cbn in HndSub. rewrite Eqv in HndSub.
  pose proof (NoDup_app_disjoint _ _ v HndSub HinPrefix) as Hdis.
  exfalso. apply Hdis. simpl. tauto.
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_11_learnt : solver_analyze_entail_wit_12_11_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_11_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_4 - 0) (ms_tags Mscan_2) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_4 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_4.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( 0 <= lit_var_c (Znth (j - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (j - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  set (q := Znth j clause_words2 0).
  set (v := lit_var_c q).
  assert (Eqv : literal_var (lit_denote q) = v).
  { rewrite lit_var_c_denote. reflexivity. }
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mscan_2)
      (ms_tagged Mscan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hperm : Permutation (ms_tagged Mscan_2)
      (analyze_tags Sscan_2 Rscan_2 learnt_scan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (HSold : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (ERscan : Rscan_2 = x_2 :: R0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hinx : In x_2 S0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hempty : sublist 1 1 Ccur = nil) by (apply ms_sublist_one_one_nil_p5).
  destruct Htags as [Hlen [_ [_ [Hcells Hiff]]]].
  assert (Hv : 0 <= v < anz_n).
  { unfold v, q. replace (j - 0) with j in H_lit_var_c, H_lit_var_c_2 by lia. lia. }
  assert (Hvr : 0 <= v < Zlength (ms_tags Mscan_2)) by lia.
  pose proof (Forall_Znth_elim Z (fun z => z = 0 \/ z = 1)
    (ms_tags Mscan_2) 0 v Hcells Hvr) as Hcell.
  assert (Htag1 : Znth v (ms_tags Mscan_2) 0 = 1).
  { destruct Hcell as [H0|H1]; [exfalso|exact H1].
    apply H_Znth. rewrite H_retval_4.
    replace (j - 0) with j by lia. fold q. fold v.
    replace (v - 0) with v by lia. exact H0. }
  apply (proj1 (Hiff v Hv)) in Htag1.
  pose proof (Permutation_in v Hperm Htag1) as HinCur.
  assert (HinInitial : In v (analyze_tags S0_2 R0_2 learnt0_2)).
  { unfold analyze_tags in HinCur |- *.
    rewrite !in_app_iff in HinCur |- *.
    destruct HinCur as [HinS|[HinR|HinL]].
    - left. rewrite HSold in HinS.
      subst j. rewrite Hempty in HinS.
      unfold resolve_S, resolve_new_S in HinS.
      cbn in HinS. rewrite app_nil_r in HinS.
      apply In_zremove_iff in HinS. tauto.
    - rewrite ERscan in HinR. cbn in HinR.
      destruct HinR as [<-|HinR].
      + left. exact Hinx.
      + right. left. exact HinR.
    - right. right. rewrite HLold in HinL.
      subst j. rewrite Hempty in HinL.
      unfold resolve_learnt, resolve_new_lits in HinL.
      cbn in HinL. rewrite app_nil_r in HinL. exact HinL. }
  assert (Hmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = true).
  { apply zmem_true_iff. exact HinInitial. }
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HSnext : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_S, resolve_new_S in *.
    rewrite Hprefix, filter_app, map_app, filter_app.
    cbn [filter map].
    destruct (at_current_level_b (msolver_view anz_n Mact) (lit_denote q))
      eqn:Hat; cbn [filter map].
    - rewrite Eqv, Hmem. cbn [negb filter map].
      rewrite HSold. rewrite !app_nil_r. reflexivity.
    - rewrite HSold. rewrite !app_nil_r. reflexivity. }
  assert (HLnext : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_learnt, resolve_new_lits in *.
    rewrite Hprefix, filter_app. cbn [filter].
    destruct (below_current_b (msolver_view anz_n Mact) (lit_denote q))
      eqn:Hbelow; cbn [andb filter].
    - rewrite Eqv, Hmem. cbn [negb andb filter].
      rewrite HLold. rewrite !app_nil_r. reflexivity.
    - rewrite HLold. rewrite !app_nil_r. reflexivity. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase
      Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
      learnt_scan_2 words_scan_2 cnt).
  { unfold analyze_clause_scan_inv in *.
    subst phase. cbn -[Z.add Z.sub Z.mul Z.div Z.modulo] in *.
    intuition (try lia; try assumption);
    (try (rewrite H_Ccur; rewrite lits_denote_length; lia);
      try exact HSnext;
      try exact HLnext). }
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2
    words_scan_2 Mscan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* Advancing the selected scan without changing its tag state preserves all
   invariant fields except the prefix equations supplied by the caller. *)
Tactic Notation "msat_analyze_scan_unchanged_close_p5" ident(phase)
    constr(HC) constr(HS) constr(HL) :=
  unfold analyze_clause_scan_inv in *;
  subst phase;
  cbn -[Z.add Z.sub Z.mul Z.div Z.modulo] in *;
  intuition (try lia; try assumption);
  (try (rewrite HC; rewrite lits_denote_length; lia);
   try exact HS;
   try exact HL).

Lemma proof_of_solver_analyze_entail_wit_12_12_learnt : solver_analyze_entail_wit_12_12_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_12_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_4 - 0) (ms_tags Mscan_2) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_4 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_4.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( 0 <= lit_var_c (Znth (j - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (j - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  set (q := Znth j clause_words2 0).
  set (v := lit_var_c q).
  assert (Eqv : literal_var (lit_denote q) = v).
  { rewrite lit_var_c_denote. reflexivity. }
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (_ & Htags & Hperm & _ & _ & _).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & _ & HSold & ERscan & HLold).
  assert (HndC : NoDup (map literal_var Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  destruct Htags as [Hlen [_ [_ [Hcells Hiff]]]].
  assert (Hv : 0 <= v < anz_n).
  { unfold v, q. replace (j - 0) with j in H_lit_var_c, H_lit_var_c_2 by lia. lia. }
  assert (Hvr : 0 <= v < Zlength (ms_tags Mscan_2)) by lia.
  pose proof (Forall_Znth_elim Z (fun z => z = 0 \/ z = 1)
    (ms_tags Mscan_2) 0 v Hcells Hvr) as Hcell.
  assert (Htag1 : Znth v (ms_tags Mscan_2) 0 = 1).
  { destruct Hcell as [H0|H1]; [exfalso|exact H1].
    apply H_Znth. rewrite H_retval_4.
    replace (j - 0) with j by lia. fold q. fold v.
    replace (v - 0) with v by lia. exact H0. }
  apply (proj1 (Hiff v Hv)) in Htag1.
  pose proof (Permutation_in v Hperm Htag1) as HinCur.
  assert (HcurSplit :
      In v (analyze_tags S0_2 R0_2 learnt0_2) \/
      In v (map literal_var (sublist 1 j Ccur))).
  { unfold analyze_tags in HinCur |- *.
    rewrite !in_app_iff in HinCur |- *.
    destruct HinCur as [HinS|[HinR|HinL]].
    - rewrite HSold in HinS. unfold resolve_S, resolve_new_S in HinS.
      apply in_app_iff in HinS. destruct HinS as [HinOld|HinNew].
      + left. left. apply In_zremove_iff in HinOld. tauto.
      + right. apply filter_In in HinNew. destruct HinNew as [HinNew _].
        apply in_map_iff in HinNew.
        destruct HinNew as [l [<- Hl]].
        apply filter_In in Hl. destruct Hl as [Hl _].
        apply in_map. exact Hl.
    - rewrite ERscan in HinR. cbn in HinR.
      destruct HinR as [<-|HinR].
      + left. left. exact Hinx.
      + left. right. left. exact HinR.
    - rewrite HLold in HinL. unfold resolve_learnt in HinL.
      rewrite map_app in HinL.
      apply in_app_iff in HinL. destruct HinL as [HinOld|HinNew].
      + left. right. right. exact HinOld.
      + right. apply in_map_iff in HinNew.
        destruct HinNew as [l [<- Hl]].
        apply filter_In in Hl. destruct Hl as [Hl _].
        apply in_map. exact Hl. }
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HndFirst :
      NoDup (map literal_var (firstn (Z.to_nat (j + 1)) Ccur))).
  { pose proof HndC as Hnd.
    rewrite <- (firstn_skipn (Z.to_nat (j + 1)) Ccur) in Hnd.
    rewrite map_app in Hnd.
    eapply NoDup_app_remove_r. exact Hnd. }
  assert (HndSub :
      NoDup (map literal_var (sublist 1 (j + 1) Ccur))).
  { unfold sublist. cbn.
    rewrite <- (firstn_skipn 1 (firstn (Z.to_nat (j + 1)) Ccur))
      in HndFirst.
    rewrite map_app in HndFirst.
    eapply NoDup_app_remove_l. exact HndFirst. }
  destruct HcurSplit as [HinInitial|HinPrefix].
  2: { rewrite Hprefix, map_app in HndSub. cbn in HndSub.
       rewrite Eqv in HndSub.
       pose proof (NoDup_app_disjoint _ _ v HndSub HinPrefix) as Hdis.
       exfalso. apply Hdis. simpl. tauto. }
  assert (Hmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = true).
  { apply zmem_true_iff. exact HinInitial. }
  assert (HSnext : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_S, resolve_new_S in *.
    rewrite Hprefix, filter_app, map_app, filter_app.
    cbn [filter map].
    destruct (at_current_level_b (msolver_view anz_n Mact) (lit_denote q))
      eqn:Hat; cbn [filter map].
    - rewrite Eqv, Hmem. cbn [negb filter map].
      rewrite HSold. rewrite !app_nil_r. reflexivity.
    - rewrite HSold. rewrite !app_nil_r. reflexivity. }
  assert (HLnext : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_learnt, resolve_new_lits in *.
    rewrite Hprefix, filter_app. cbn [filter].
    destruct (below_current_b (msolver_view anz_n Mact) (lit_denote q))
      eqn:Hbelow; cbn [andb filter].
    - rewrite Eqv, Hmem. cbn [negb andb filter].
      rewrite HLold. rewrite !app_nil_r. reflexivity.
    - rewrite HLold. rewrite !app_nil_r. reflexivity. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase
      Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
      learnt_scan_2 words_scan_2 cnt).
  { msat_analyze_scan_unchanged_close_p5 phase H_Ccur HSnext HLnext. }
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2
    words_scan_2 Mscan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_13_learnt : solver_analyze_entail_wit_12_13_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_13_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 <= 0 ) as H_Znth.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  set (q := Znth j clause_words2 0).
  set (v := lit_var_c q).
  assert (Eqv : literal_var (lit_denote q) = v).
  { rewrite lit_var_c_denote. reflexivity. }
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Hready : analysis_cancel_ready anz_n anz_F anz_A_arr K Mscan_2 anz_focus)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hrootlt :
      ms_root_level Mscan_2 < Zlength (mt_lim (ms_core Mscan_2)))
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  pose proof (analysis_cancel_ready_trail_wf__analyze
    anz_n anz_F anz_A_arr K Mscan_2 anz_focus Hready) as Htrailwf.
  assert (Hrootnonneg : 0 <= ms_root_level Mscan_2).
  { destruct Hready as [Mentry [[[_ Hbase] _] [Hequiv _]]].
    assert (Eroot : ms_root_level Mscan_2 = ms_root_level Mentry).
    { unfold analysis_core_equiv in Hequiv. tauto. }
    rewrite Eroot.
    destruct K; [pose proof (msw_shape Hbase) as Hshape |
                 pose proof (msa_shape Hbase) as Hshape];
      unfold solver_shape in Hshape; tauto. }
  assert (Hcurpos : 0 < Zlength (mt_lim (ms_core Mscan_2))) by lia.
  assert (Hphys : Znth v (mt_levels (ms_core Mscan_2)) 0 <= 0).
  { replace (j - 0) with j in H_retval_5 by lia.
    fold q in H_retval_5. fold v in H_retval_5.
    rewrite H_retval_5 in H_Znth.
    replace (v - 0) with v in H_Znth by lia. exact H_Znth. }
  assert (Hclass :
      at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = false /\
      below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
    - pose proof (trail_pos_bound (ms_core Mscan_2) v rq Hrank) as Hrqb.
      pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia))
        as Hagree.
      rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrank) in Hagree.
      set (dq := level_of_index (ms_core Mscan_2) (Z.of_nat rq)).
      assert (Hlev : level_of (msolver_view anz_n Mact) v = Some dq).
      { rewrite Eview. unfold msolver_view, view_of.
        cbn [level_of]. rewrite Hrank. reflexivity. }
      assert (Hdqle : dq <= 0).
      { unfold dq. rewrite <- Hagree. exact Hphys. }
      split.
      + unfold at_current_level_b. rewrite Eqv, Hlev.
        rewrite Eview, msolver_view_current_level.
        apply Z.eqb_neq. lia.
      + unfold below_current_b. rewrite Eqv, Hlev.
        destruct (0 <? dq)%Z eqn:Hdq.
        * apply Z.ltb_lt in Hdq. lia.
        * reflexivity.
    - assert (Hlev : level_of (msolver_view anz_n Mact) v = None).
      { rewrite Eview. unfold msolver_view, view_of.
        cbn [level_of]. rewrite Hrank. reflexivity. }
      split; [unfold at_current_level_b|unfold below_current_b];
        rewrite Eqv, Hlev; reflexivity. }
  destruct Hclass as [Hat Hbelow].
  assert (HSold : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HSnext : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_S, resolve_new_S in *.
    rewrite Hprefix, filter_app, map_app, filter_app.
    cbn [filter map]. rewrite Hat. cbn [filter map].
    rewrite HSold. rewrite !app_nil_r. reflexivity. }
  assert (HLnext : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_learnt, resolve_new_lits in *.
    rewrite Hprefix, filter_app. cbn [filter].
    rewrite Hbelow. cbn [andb filter].
    rewrite HLold. rewrite !app_nil_r. reflexivity. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase
      Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
      learnt_scan_2 words_scan_2 cnt).
  { msat_analyze_scan_unchanged_close_p5 phase H_Ccur HSnext HLnext. }
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2
    words_scan_2 Mscan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_analyze partial_solve wits ===== *)
Lemma proof_of_solver_analyze_partial_solve_wit_102_learnt_pure : solver_analyze_partial_solve_wit_102_learnt_pure.
Proof.
  Unfold; LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_103_learnt_pure : solver_analyze_partial_solve_wit_103_learnt_pure.
Proof.
  msat_analyze_tagged_veci_open_p5; subst Mact.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_104_learnt_pure : solver_analyze_partial_solve_wit_104_learnt_pure.
Proof.
  Unfold; LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_105_learnt_pure : solver_analyze_partial_solve_wit_105_learnt_pure.
Proof.
  msat_analyze_tagged_veci_open_p5.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_106_learnt_pure : solver_analyze_partial_solve_wit_106_learnt_pure.
Proof.
  Unfold; LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_107_learnt_pure : solver_analyze_partial_solve_wit_107_learnt_pure.
Proof.
  msat_analyze_tagged_veci_open_p5; subst Mact.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_112_learnt_pure : solver_analyze_partial_solve_wit_112_learnt_pure.
Proof.
  Unfold; LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_113_learnt_pure : solver_analyze_partial_solve_wit_113_learnt_pure.
Proof.
  Unfold; LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_114_learnt_pure : solver_analyze_partial_solve_wit_114_learnt_pure.
Proof.
  Unfold; LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_115_learnt_pure : solver_analyze_partial_solve_wit_115_learnt_pure.
Proof.
  Unfold; LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_116_learnt_pure : solver_analyze_partial_solve_wit_116_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R0 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  pose proof H_analyze_clause_scan_inv as Hscan.
  unfold analyze_clause_scan_inv in Hscan.
  destruct Hscan as [Hready Hscan_rest].
  unfold analysis_cancel_ready in Hready.
  destruct Hready as [Mbase [Hcancel [Hequiv [Hheap Hready_rest]]]].
  unfold order_heap_wf, msolver_heap in Hheap.
  prop_apply_p (DoubleArray.seg_Zlength
    activity_ptr_scan 0 anz_n (ms_activity Mscan)).
  Intros_p Hactivity.
  replace (anz_n - 0) with anz_n in Hactivity by lia.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. exact Hactivity.
  - dump_pre_spatial. exact Hheap.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_117_learnt_pure : solver_analyze_partial_solve_wit_117_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  subst Mact.
  subst j.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mscan Mscan anz_focus phase Ccur 1 ind S0 R0 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= lit_var_c (Znth (1 - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (1 - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  pose proof H_analyze_clause_scan_inv as Hscan.
  unfold analyze_clause_scan_inv in Hscan.
  destruct Hscan as [Hready Hscan_rest].
  unfold analysis_cancel_ready in Hready.
  destruct Hready as [Mbase [Hcancel [Hequiv [Hheap Hready_rest]]]].
  unfold order_heap_wf, msolver_heap in Hheap.
  prop_apply_p (DoubleArray.seg_Zlength
    activity_ptr_scan 0 anz_n (ms_activity Mscan)).
  Intros_p Hactivity.
  replace (anz_n - 0) with anz_n in Hactivity by lia.
  split_pures.
  - dump_pre_spatial. exact Hheap.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. exact Hactivity.
  - dump_pre_spatial. exact H_lit_var_c_2.
  - dump_pre_spatial. exact H_lit_var_c.
  - dump_pre_spatial. exact Hheap.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_184_pure : solver_analyze_partial_solve_wit_184_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia).
  unfold veci_rep_at.
  Intros_p Hbounds.
  split_pures.
  all: (try (dump_pre_spatial; lia));
    (try (dump_pre_spatial;
      lazymatch goal with
      | H : ?fact |- ?fact => exact H
      end));
    (try (dump_pre_spatial;
      lazymatch goal with
      | H : Znth ?index ?words ?default < ?bound |-
        Znth (?index - 0) ?words ?default < ?bound =>
          replace (index - 0) with index by lia; exact H
      end)).
  all: try (dump_pre_spatial;
      lazymatch goal with
      | H : 0 <= Znth ?index ?words ?default |-
        0 <= Znth (?index - 0) ?words ?default =>
          replace (index - 0) with index by lia; exact H
      end).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_192_pure : solver_analyze_partial_solve_wit_192_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia).
  bind_fact ( Forall (lit_wf_c anz_n) words_compact ) as H_Forall.
  bind_fact ( solver_shape Mclear ) as H_solver_shape.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mclear anz_focus ) as H_analysis_cancel_ready.
  assert (Hindex : 0 <= 1 < Zlength words_compact) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 1 H_Forall Hindex) as Hlit.
  unfold lit_wf_c in Hlit.
  destruct Hlit as [Hlow Hhigh].
  pose proof (analysis_cancel_ready_reason_core anz_n anz_F anz_A_arr K Mclear anz_focus H_analysis_cancel_ready)
    as Hreason_core.
  destruct Hreason_core as [Hn_size _].
  unfold solver_shape in H_solver_shape.
  destruct H_solver_shape as [_ [_ [Htwo [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]]].
  split_pures.
  - dump_pre_spatial. replace (1 - 0) with 1 by lia. exact Hlow.
  - dump_pre_spatial. replace (1 - 0) with 1 by lia. lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_197_pure : solver_analyze_partial_solve_wit_197_pure.
Proof.
  right; LLM_pre_process ltac:(lia).
  msat_analyze_word_range_from_cancel_p5 anz_n anz_F anz_A_arr K Mclear anz_focus words_compact i Hfa Hcr.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_200_pure : solver_analyze_partial_solve_wit_200_pure.
Proof.
  right; LLM_pre_process ltac:(lia).
  msat_analyze_word_range_from_cancel_p5 anz_n anz_F anz_A_arr K Mclear anz_focus words_compact i Hfa Hcr.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_207_pure : solver_analyze_partial_solve_wit_207_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mclear anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( ms_tags Mclear = repeat_Z 0 anz_n ) as H_ms_tags.
  assert (Hactivity_keep :
    solver_reason_levels_frame_at s_pre Mclear trail tags anz_wl |--
      “ Zlength (ms_activity Mclear) = ms_size Mclear ” &&
      solver_reason_levels_frame_at s_pre Mclear trail tags anz_wl).
  {
    unfold solver_reason_levels_frame_at, solver_removable_frame_at at 1.
    Intros act asg opos.
    prop_apply (DoubleArray.seg_Zlength act 0
      (ms_size Mclear) (ms_activity Mclear)).
    Intros_p Hactivity_len.
    unfold solver_reason_levels_frame_at, solver_removable_frame_at.
    Exists act asg opos.
    entailer_with ltac:(lia).
  }
  assert (Hstats_keep :
    solver_reason_levels_frame_at s_pre Mclear trail tags anz_wl |--
      “ Zlength (ms_stats Mclear) = 11 ” &&
      solver_reason_levels_frame_at s_pre Mclear trail tags anz_wl).
  {
    unfold solver_reason_levels_frame_at, solver_removable_frame_at at 1.
    unfold stats_rep at 1.
    Intros act asg opos.
    unfold solver_reason_levels_frame_at, solver_removable_frame_at,
      stats_rep.
    Exists act asg opos.
    entailer_with ltac:(lia).
  }
  sep_apply Hactivity_keep.
  Intros_p Hactivity_len.
  sep_apply Hstats_keep.
  Intros_p Hstats_len.
  pose proof (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mclear anz_focus H_analysis_cancel_ready) as Hreason_core.
  destruct Hreason_core as [Hsize _].
  unfold analysis_cancel_ready in H_analysis_cancel_ready.
  destruct H_analysis_cancel_ready as
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
  assert (Horder_shape :
    Zlength (ms_orderpos Mclear) = ms_size Mclear).
  { destruct Hheap as [Horder_len _].
    change (Zlength (ms_orderpos Mclear) = anz_n) in Horder_len.
    lia. }
  assert (Hn_nonneg : 0 <= anz_n).
  { pose proof (solver_shape_size_nonneg Mbase Hshape_base) as Hbase_nonneg.
    rewrite Hsize, Esize. exact Hbase_nonneg. }
  assert (Htags_shape :
    Zlength (ms_tags Mclear) = ms_size Mclear).
  { rewrite H_ms_tags. unfold repeat_Z.
    rewrite Zlength_correct, List.repeat_length.
    rewrite <- Hsize. lia. }
  assert (Hshape : solver_shape Mclear).
  { unfold solver_shape in Hshape_base |- *.
    rewrite Horder_shape, Hactivity_len, Htags_shape, Hstats_len,
      Esize, Ecap, Eqtail, Ecore, Eroot, Ewords, Ebinary, Ebinarylits,
      Ewm, Ewcaps, Ependingq, Epending.
    tauto. }
  apply derivable1s_coq_prop_r. exact Hshape.
Qed.

(* ===== solver_analyze safety wits (11 proofs) ===== *)
Lemma proof_of_solver_analyze_safety_wit_73_learnt : solver_analyze_safety_wit_73_learnt.
Proof.
  Unfold.
  left. intros.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R0 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( j = 0 ) as H_j.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as (_ & _ & _ & _ & _ & _ & _ & Hcnt & _ & _ & _ & _ & Hinitial).
  rewrite H_phase in Hinitial.
  change (S0 = @nil Z /\ R0 = @nil Z /\ learnt0 = @nil literal /\ x = -1 /\
          ind + 1 = ms_qtail Mact /\
          propagation_conflict_cert anz_n anz_F Mact Ccur /\
          Sscan = analyze_start_S (msolver_view anz_n Mact) (sublist 0 j Ccur) /\
          Rscan = @nil Z /\
          learnt_scan = analyze_start_learnt (msolver_view anz_n Mact) (sublist 0 j Ccur)) in Hinitial.
  destruct Hinitial as (_ & _ & _ & _ & _ & _ & HS & _ & _).
  rewrite H_j in HS.
  rewrite Zsublist_nil in HS by lia.
  subst Sscan.
  unfold analyze_start_S in Hcnt. simpl in Hcnt.
  change (cnt = 0) in Hcnt.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_safety_wit_86_learnt : solver_analyze_safety_wit_86_learnt.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  msat_analyze_bound_scan_index_by_nodup Heq Hscan anz_n Ccur j Hinv clause_words2.
Qed.

Lemma proof_of_solver_analyze_safety_wit_88_learnt : solver_analyze_safety_wit_88_learnt.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  msat_analyze_bound_scan_index_by_nodup Heq Hscan anz_n Ccur j Hinv clause_words2.
Qed.

Lemma proof_of_solver_analyze_safety_wit_90_learnt : solver_analyze_safety_wit_90_learnt.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  msat_analyze_bound_scan_index_by_nodup Heq Hscan anz_n Ccur j Hinv clause_words2.
Qed.

Lemma proof_of_solver_analyze_safety_wit_92_learnt : solver_analyze_safety_wit_92_learnt.
Proof.
  Unfold.
  left. intros.
  prop_rewrite (store_int_range (clause_hdr_addr c)
    (clause_hdr_word is_learnt2 (Zlength clause_words2))).
  Intros_p Hheader_range.
  change Int.min_signed with INT_MIN in Hheader_range.
  change Int.max_signed with INT_MAX in Hheader_range.
  destruct Hheader_range as [_ Hheader_max].
  pose proof (Zlength_nonneg clause_words2) as Hlength_nonnegative.
  assert (Hbounds : j + 1 <= INT_MAX /\ INT_MIN <= j + 1).
  { unfold clause_hdr_word in Hheader_max.
    destruct is_learnt2.
    - change (2 * Zlength clause_words2 + 1 <= INT_MAX) in Hheader_max.
      split; lia.
    - change (2 * Zlength clause_words2 + 0 <= INT_MAX) in Hheader_max.
      split; lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_safety_wit_95_learnt : solver_analyze_safety_wit_95_learnt.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  msat_analyze_bound_scan_index_by_nodup Heq Hscan anz_n Ccur j Hinv clause_words2.
Qed.

Lemma proof_of_solver_analyze_safety_wit_97_learnt : solver_analyze_safety_wit_97_learnt.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  msat_analyze_bound_scan_index_by_nodup Heq Hscan anz_n Ccur j Hinv clause_words2.
Qed.

Lemma proof_of_solver_analyze_safety_wit_98_learnt : solver_analyze_safety_wit_98_learnt.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  msat_analyze_bound_scan_index_by_nodup Heq Hscan anz_n Ccur j Hinv clause_words2.
Qed.

Lemma proof_of_solver_analyze_safety_wit_100_learnt : solver_analyze_safety_wit_100_learnt.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  msat_analyze_bound_scan_index_by_nodup Heq Hscan anz_n Ccur j Hinv clause_words2.
Qed.

Lemma proof_of_solver_analyze_safety_wit_107 : solver_analyze_safety_wit_107.
Proof.
  Unfold.
  left. intros.
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  assert (Hbounds : cnt - 1 <= INT_MAX /\ INT_MIN <= cnt - 1).
  { unfold analyze_backward_scan_inv in H_analyze_backward_scan_inv.
    destruct H_analyze_backward_scan_inv as
      (Hready & Hinv & Hcnt & Hcntpos & Hind & Hwords & Hroot & Hlits &
       Htags & Hperm & HrankS & HrankR & Hex).
    assert (Hnmax : 2 * anz_n <= INT_MAX).
    { destruct Hready as [M_ready_base_hyp [Hcancel Hready_rest]].
      destruct Hcancel as [Hweak Hcancel_rest].
      destruct Hweak as [Hcapacity Hcontext].
      destruct K as [A_inst | A_proc]; cbn in Hcontext.
      - pose proof (msw_shape Hcontext) as Hshape.
        pose proof (msw_size Hcontext) as Hsize.
        unfold solver_shape in Hshape.
        destruct Hshape as (_ & _ & Hliteral_bound & _).
        rewrite <- Hsize in Hliteral_bound. exact Hliteral_bound.
      - pose proof (msa_shape Hcontext) as Hshape.
        pose proof (msa_size Hcontext) as Hsize.
        unfold solver_shape in Hshape.
        destruct Hshape as (_ & _ & Hliteral_bound & _).
        rewrite <- Hsize in Hliteral_bound. exact Hliteral_bound. }
    destruct Hinv as (_ & Hnodup & HlevelsS & HassignedS & HlevelsR &
                      HrankOrder & HlevelsLearnt & HfalseLearnt).
    destruct Htags as (Htags_length & Htagged_nodup & Htagged_range &
                       Htag_values & Htag_exact).
    assert (Hanalysis_range :
      Forall (fun v => 0 <= v < anz_n) (analyze_tags Sresolved Rresolved learnt_resolved)).
    { rewrite Forall_forall in Htagged_range |- *.
      intros v Hv.
      apply Htagged_range.
      eapply Permutation_in.
      - apply Permutation_sym. exact Hperm.
      - exact Hv. }
    unfold analyze_tags in Hnodup, Hanalysis_range.
    assert (HnodupS : NoDup Sresolved).
    { eapply NoDup_app_remove_r. exact Hnodup. }
    assert (HrangeS : Forall (fun v => 0 <= v < anz_n) Sresolved).
    { rewrite Forall_app in Hanalysis_range.
      exact (proj1 Hanalysis_range). }
    assert (Hn : 0 <= anz_n) by lia.
    rewrite Forall_forall in HrangeS.
    pose proof (NoDup_Z_bounded_length Sresolved anz_n Hn HnodupS HrangeS) as HlenS.
    rewrite Zlength_correct in Hcnt.
    split; lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_safety_wit_114 : solver_analyze_safety_wit_114.
Proof.
  Unfold.
  left. intros.
  assert (Hmask :
    Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 31 <= 31 /\
    0 <= Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 31).
  { assert (Hland :
      Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 31 =
      Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0 mod 32).
    { change
        (Z.land (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0)
          (Z.ones 5) =
         Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0 mod 2 ^ 5).
      apply Z.land_ones. lia. }
    rewrite Hland.
    pose proof (Z.mod_pos_bound
      (Znth (retval - 0) (mt_levels (ms_core Mresolution)) 0) 32 ltac:(lia))
      as Hmod_bound.
    split; lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_analyze which_implies wits (4 proofs) ===== *)
Lemma proof_of_solver_analyze_which_implies_wit_1 : solver_analyze_which_implies_wit_1.
Proof.
  right.
  LLM_pre_process ltac:(lia).
  unfold solver_analyze_pre, solver_rep_levels_wl_at,
    solver_rep_analyze_at, solver_rep_at.
  Intros act asg opos rsn trl tgs.
  Exists rsn trl tgs.
  Exists act asg opos.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_2 : solver_analyze_which_implies_wit_2.
Proof.
  left; intros.
  lazymatch goal with
  | Hready : analysis_cancel_ready ?n ?F ?A ?K ?Msol ?focus |-
      solver_rep_analyze_at ?s ?Msol ?reasons ?levels ?trail ?tags ?wl |-- _ =>
      let Hsize := fresh "Hsize" in
      pose proof (analysis_cancel_ready_reason_core n F A K Msol focus Hready)
        as [Hsize _];
      sep_apply (solver_rep_analyze_at_open
        s Msol n reasons levels trail tags wl (eq_sym Hsize))
  end.
  Intros activity orderpos.
  Exists activity orderpos.
  unfold msat_false.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_28 : solver_analyze_which_implies_wit_28.
Proof.
  left; intros.
  lazymatch goal with
  | Hsize : ms_size ?Msol = ?n |-
      solver_rep_analyze_at ?s ?Msol ?reasons ?levels ?trail ?tags ?wl |-- _ =>
      sep_apply (solver_rep_analyze_at_open
        s Msol n reasons levels trail tags wl Hsize)
  end.
  Intros activity orderpos.
  Exists activity orderpos.
  unfold msat_false.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_3 : solver_analyze_which_implies_wit_3.
Proof.
  exact proof_of_solver_analyze_which_implies_wit_28.
Qed.

(* ===== solver_lit_removable partial_solve wits ===== *)


Lemma proof_of_solver_lit_removable_partial_solve_wit_26_pure : solver_lit_removable_partial_solve_wit_26_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( retval = Zlength stack_now ) as H_retval.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  (* The RHS carries the same conjunct twice, the second copy spelled with retval.
          [H_retval : retval = Zlength stack_now] puts it back in the LHS form -- QCP
          cancellation is syntactic. *)
  rewrite H_retval.
  unfold removable_reason_focus, reason_target_wf in *.
  destruct H_removable_reason_focus as [_ [_ [_ [_ Hkind]]]].
  destruct Hkind as [[_ [Hpositive _]] | [co [_ [_ [Hin _]]]]].
  - entailer_with lia.
  - pose proof (analysis_cancel_ready_db_wf__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as Hdb.
    pose proof (db_wf_ptr_pos lrm_n (msolver_db M0) _ co Hdb Hin) as Hpositive.
    msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_28_pure : solver_lit_removable_partial_solve_wit_28_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) = msat_true ) as H_is_tag.
  bind_fact ( retval = Zlength stack_now ) as H_retval.
  (* The duplicated RHS conjuncts are spelled through [retval - 1];
          [H_retval : retval = Zlength stack_now] puts them back in the LHS spelling. *)
  rewrite H_retval.
  unfold removable_reason_focus, reason_target_wf, tagged_word in *.
  destruct H_removable_reason_focus as [_ [_ [_ [_ Hkind]]]].
  destruct Hkind as [[Htag [Hpositive Hlit]] | [co [Htag [_ [_ _]]]]].
  - unfold lit_wf_c in Hlit.
    split_pures;
    (dump_pre_spatial;
     (* Eight residual conjuncts: the tag equation is [Htag] itself, every other
        one is an arithmetic bound; select on the goal shape rather than
        backtracking over the two closers. *)
     lazymatch goal with
     | |- is_tag _ = _ => exact Htag
     | |- _ => lia
     end).
  - unfold msat_true in H_is_tag.
    rewrite Htag in H_is_tag. discriminate.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_29_pure : solver_lit_removable_partial_solve_wit_29_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) = msat_true ) as H_is_tag.
  unfold removable_reason_focus, reason_target_wf in *.
  destruct H_removable_reason_focus as [_ [_ [_ [_ Hkind]]]].
  destruct Hkind as [[Htag [Hpositive Hlit]] | [co [Htag [_ [_ _]]]]].
  - unfold lit_wf_c in Hlit.
    entailer_with ltac:(lia).
  - unfold msat_true in H_is_tag.
    rewrite Htag in H_is_tag. discriminate.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_30_pure : solver_lit_removable_partial_solve_wit_30_pure.
Proof.
  Unfold.
  right; intros.
  split_pures;
  (dump_pre_spatial; subst retval retval_7; lia).
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_31_pure : solver_lit_removable_partial_solve_wit_31_pure.
Proof.
  Unfold; left; intros.
  msat_lit_removable_retval_var_bounds_p5 retval retval_7 stack_now M0 lrm_n Hv Hw Hlo Hhi.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_32_pure : solver_lit_removable_partial_solve_wit_32_pure.
Proof.
  Unfold; left; intros.
  msat_lit_removable_retval_var_bounds_p5 retval retval_7 stack_now M0 lrm_n Hv Hw Hlo Hhi.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_33_pure : solver_lit_removable_partial_solve_wit_33_pure.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( retval = lit_var_c retval_7 ) as H_retval.
  bind_fact ( retval_7 = tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) ) as
      H_retval_7.
  bind_fact ( 0 <= lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) ) as
      H_lit_var_c.
  bind_fact ( lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) < lrm_n )
      as H_lit_var_c_2.
  assert (Hretval_nonneg : 0 <= retval).
  { rewrite H_retval, H_retval_7. exact H_lit_var_c. }
  assert (Hretval_bound : retval < lrm_n).
  { rewrite H_retval, H_retval_7. exact H_lit_var_c_2. }
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_35_pure : solver_lit_removable_partial_solve_wit_35_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( stack_now = stack_after +:: Znth (Zlength stack_now - 1) stack_now 0 ) as H_stack_now.
  bind_fact ( Zlength (sublist 0 (retval - 1) stack_now) = retval - 1 ) as H_Zlength.
  bind_fact ( retval = Zlength stack_now ) as H_retval.
  (* The RHS already carries the sublist identity, so what [entailer_with] leaves is not the
          sublist equation but the two Zlength side conditions on the same term; both follow from
          the stack decomposition and the length equation, plus the capacity bound. *)
  (entailer_with ltac:(lia));
  (rewrite <- H_stack_now;
    rewrite H_retval in H_Zlength;
    rewrite H_Zlength;
    lia).
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_38_pure : solver_lit_removable_partial_solve_wit_38_pure.
Proof.
  Unfold.
  msat_lit_removable_close_tagged_caps_by_entailer.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_44_pure : solver_lit_removable_partial_solve_wit_44_pure.
Proof.
  Unfold.
  left.
  intros.
  replace (j - 0) with j by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_lit_removable which_implies wits (1 proofs) ===== *)
Lemma proof_of_solver_lit_removable_which_implies_wit_12 : solver_lit_removable_which_implies_wit_12.
Proof.
  Unfold.
  right.
  (* Bind every term binder explicitly rather than relying on the statement's own
     names: `M` collides with `Base.Model` in some scopes and gets auto-renamed, so
     the names the statement introduces depend on the ambient scope.  The facts that
     follow them are left to the default naming and picked up by content below. *)
  intros minl_pre l_pre focus Msol Kctx A_arr F n
         tags_now tagged_now stack_now done_lits stack_after.
  intros.
  bind_fact ( analysis_cancel_ready n F A_arr Kctx Msol focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_dfs_loop_inv n Msol l_pre minl_pre (ms_tagged Msol) tags_now tagged_now stack_now done_lits )
      as H_removable_dfs_loop_inv.
  bind_fact ( stack_after = sublist 0 (Zlength stack_now - 1) stack_now ) as H_stack_after.
  (* n = ms_size Msol comes from the analysis_cancel_ready conjunct on the which-implies LHS.
          Without it the bound is underivable: the LHS is TT && emp, so no spatial atom can
          force it. *)
  destruct (analysis_cancel_ready_reason_core n F A_arr Kctx Msol focus H_analysis_cancel_ready) as [Hsize _].
  destruct H_removable_dfs_loop_inv as [fresh [_ [_ [_ [Hnodup [_ [_ [Htargets _]]]]]]]].
  assert (Hnodup_stack : NoDup stack_now).
  { eapply NoDup_app_remove_l. exact Hnodup. }
  pose proof (msat_reason_target_stack_var_range n Msol stack_now Hsize Htargets)
    as Hbounded.
  assert (Hn : 0 <= n).
  { assert (Hin : In (Znth (Zlength stack_now - 1) stack_now 0) stack_now)
      by (apply Znth_In; lia).
    pose proof (Hbounded _ Hin). lia. }
  pose proof (NoDup_Z_bounded_length stack_now n Hn Hnodup_stack Hbounded) as Hlen.
  rewrite <- Zlength_correct in Hlen.
  assert (Hafterlen : Zlength stack_after = Zlength stack_now - 1).
  { rewrite H_stack_after. rewrite Zlength_sublist by lia. lia. }
  assert (Hcat : Zlength (stack_after ++ (cons (Znth (Zlength stack_now - 1) stack_now 0) nil))
                 = Zlength stack_now).
  { rewrite Zlength_app, Hafterlen. rewrite Zlength_cons, Zlength_nil. lia. }
  assert (H1 : Zlength stack_after < n) by lia.
  assert (H2 : Zlength (sublist 0 (Zlength stack_now - 1)
     (stack_after ++ (cons (Znth (Zlength stack_now - 1) stack_now 0) nil))) < n).
  { rewrite Zlength_sublist by lia. lia. }
  msat_manual_entailer_with lia.
Qed.

(* ===== solver_propagate entail wits (14 proofs) ===== *)
Lemma proof_of_solver_propagate_entail_wit_12_7_scan_move : solver_propagate_entail_wit_12_7_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_7_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_8_scan_move : solver_propagate_entail_wit_12_8_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_8_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_9_scan_move : solver_propagate_entail_wit_12_9_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_9_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_10_scan_move : solver_propagate_entail_wit_12_10_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_10_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_11_scan_move : solver_propagate_entail_wit_12_11_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_11_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_12_scan_move : solver_propagate_entail_wit_12_12_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_12_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_13_scan_same : solver_propagate_entail_wit_13_scan_same.
Proof.
  unfold solver_propagate_entail_wit_13_scan_same.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) offset ) as H_propagation_replacement_scan_inv.
  all: (try unfold propagation_int_missing);
    (try csimpl);
    (try entailer_with ltac:(lia)).
  all: assert (Hcandidate' : candidate =
      Znth offset (propagation_normalized_clause watch0 false_lit clause_contents) 0) by
      (rewrite H_candidate; unfold propagation_normalized_clause;
      rewrite Znth_cons by lia;
      rewrite Znth_cons by lia;
      replace (offset - 1 - 1) with (offset - 2) by lia; reflexivity).
  all: (destruct H_propagation_replacement_scan_inv as [_ [Hwf _]]);
    (assert (Hcand : lit_wf_c n candidate) by
      (rewrite Hcandidate'; apply (Forall_Znth_elim Z (lit_wf_c n)
        (propagation_normalized_clause watch0 false_lit clause_contents) 0 offset Hwf);
      unfold propagation_normalized_clause;
      rewrite !Zlength_cons;
      rewrite Zlength_sublist by lia;
      lia)).
  all: (unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics);
    ((destruct H_solver_propagation_scan_semantics as [[_ [Hweak _]] | [Hconf _]]; [|lia]));
    (pose proof (solver_propagation_weak_reason_core n F A_arr K Mscan Hweak) as [Hsize _]);
    (pose proof (lit_var_c_in_range n candidate Hcand) as Hrange);
    (lia).
Qed.

Lemma proof_of_solver_propagate_entail_wit_14_1_capacity_copy : solver_propagate_entail_wit_14_1_capacity_copy.
Proof.
  unfold solver_propagate_entail_wit_14_1_capacity_copy.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  msat_propagate_capacity_copy_close_p5 rsn_scan trl_scan jj Hdrop.
  all: lazymatch goal with
  | |- minisat_propagation_reuse_scan _ _ _ ?cf _ =>
      match goal with Hzero : cf = 0 |- _ => rewrite Hzero; assumption end
  end.
Qed.

Lemma proof_of_solver_propagate_entail_wit_14_2_capacity_copy : solver_propagate_entail_wit_14_2_capacity_copy.
Proof.
  unfold solver_propagate_entail_wit_14_2_capacity_copy.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  msat_propagate_capacity_copy_close_p5 rsn_scan trl_scan jj Hdrop.
  all: lazymatch goal with
  | |- minisat_propagation_reuse_scan _ _ _ ?cf _ =>
      match goal with Hzero : cf = 0 |- _ => rewrite Hzero; assumption end
  end.
Qed.

Lemma proof_of_solver_propagate_entail_wit_15_1_capacity_copy : solver_propagate_entail_wit_15_1_capacity_copy.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( propagation_scan_open n F A_arr K M0 Mentry Mscan p confl source_words retained moved rest garbage
      watch_memory ii jj scan_current raw_suffix ) as H_propagation_scan_open.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_dst_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  Exists s_reasons_2 s_trail_2 copy_memory_2
    (copy_dst_2 + 1) (copy_src_2 + 1).
  assert (Hcursor : copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in *. solve_arch. }
  assert (Hbound : 0 <= copy_src_2 < Zlength source_words) by lia.
  (entailer_with ltac:(lia));
  (try subst copy_dst_2;
    try rewrite !replace_Znth_Znth).
  (* The copied cell is no longer refolded into [PtrArray.full] on the left -- it stays split as
          the store cell at [begin + copy_dst_2 * sizeof(PTR)] against a [missing_i] hole indexed
          by copy_src_2.  The equation identifying the two indices is discharged by the [subst]
          above; what is left is the standard missing_i -> full merge at copy_src_2, whose index
          bound is the arch-scaled form of the copy-cursor bounds. *)
  all: (try (change (sizeof (PTR)) with ptr_size_Z; fold_arch;
    pose proof (PtrArray.missing_i_merge_to_full begin copy_src_2
      (Zlength source_words) (Znth copy_src_2 copy_memory_2 0)
      copy_memory_2 Hbound) as Hmerge;
    rewrite replace_Znth_Znth in Hmerge;
    exact Hmerge));
    (try cancel);
    (try lia).
  assert (Hwatch_len : Zlength watch_memory = Zlength source_words).
  { unfold propagation_scan_open in H_propagation_scan_open.
    destruct H_propagation_scan_open as [_ [_ [_ [_ [_ [Hphysical _]]]]]].
    unfold propagation_watch_scan_physical in Hphysical.
    tauto. }
  assert (Hcursor_words : copy_src_2 < Zlength watch_memory) by lia.
  pose proof msat_binary_watch_write_snoc as Hwrite_app.
  pose proof msat_binary_watch_write_endpoint as Hwrite_endpoint.
  assert (Hprogress_next :
    binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix
      ii jj (copy_src_2 + 1) (copy_src_2 + 1) copy_memory_2).
  { unfold binary_watch_copy_progress in H_binary_watch_copy_progress |- *.
    destruct H_binary_watch_copy_progress as [copied [copy_rest
      [Hwords [Hkept [Hbounds [Hsuffix
        [Hsrc [Hdst [Hmemory Hmemory_len]]]]]]]]].
    destruct copy_rest as [|x copy_rest].
    - rewrite Hwords, Hsuffix, app_nil_r, !Zlength_app,
        Zlength_cons, Hkept in Hcursor_words.
      rewrite Hsrc in Hcursor_words. lia.
    - assert (Hii_jj : ii = jj) by lia.
      pose proof (Zlength_nonneg copied) as Hcopied_nonneg.
      assert (Hnext_words : Znth copy_src_2 watch_memory 0 = x).
      { rewrite Hwords, app_Znth2 by (rewrite Hkept, Hsrc; lia).
        rewrite Hsrc, Hkept.
        replace (ii + 1 + Zlength copied - ii) with
          (1 + Zlength copied) by lia.
        rewrite Znth_cons by lia.
        replace (1 + Zlength copied - 1) with
          (Zlength copied) by lia.
        rewrite Hsuffix, app_Znth2 by lia.
        replace (Zlength copied - Zlength copied) with 0 by lia.
        reflexivity. }
      assert (Hnext_memory : Znth copy_src_2 copy_memory_2 0 = x).
      { rewrite Hmemory.
        pose proof
          (Hwrite_endpoint (jj + 1) copied
            (replace_Znth jj scan_current watch_memory) 0)
          as Hendpoint.
        rewrite Hdst.
        rewrite Hendpoint by
          (try rewrite Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Diff by lia.
        rewrite <- Hdst.
        exact Hnext_words. }
      exists (copied ++ (x :: nil)), copy_rest.
      split; [exact Hwords|].
      split; [exact Hkept|].
      split; [exact Hbounds|].
      split.
      { rewrite Hsuffix.
        change (copied ++ (x :: copy_rest) =
          (copied ++ (x :: nil)) ++ copy_rest).
        rewrite <- app_assoc. reflexivity. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Hwrite_app, <- Hmemory.
        replace (jj + 1 + Zlength copied) with copy_src_2 by lia.
        rewrite <- Hnext_memory, replace_Znth_Znth. reflexivity. }
      exact Hmemory_len. }
  all: try exact Hprogress_next.
Qed.

Lemma proof_of_solver_propagate_entail_wit_15_2_capacity_copy : solver_propagate_entail_wit_15_2_capacity_copy.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( propagation_scan_open n F A_arr K M0 Mentry Mscan p confl source_words retained moved rest garbage
      watch_memory ii jj scan_current raw_suffix ) as H_propagation_scan_open.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_dst_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  Exists s_reasons_2 s_trail_2
    (replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0)
      copy_memory_2)
    (copy_dst_2 + 1) (copy_src_2 + 1).
  (entailer_with ltac:(lia));
  (try rewrite !replace_Znth_Znth;
    try cancel;
    try lia).
  2: {
    assert (Hcursor : copy_src_2 < Zlength source_words).
    { change (sizeof (PTR)) with ptr_size_Z in *. solve_arch. }
    assert (Hwatch_len : Zlength watch_memory = Zlength source_words).
    { unfold propagation_scan_open in H_propagation_scan_open.
      destruct H_propagation_scan_open as [_ [_ [_ [_ [_ [Hphysical _]]]]]].
      unfold propagation_watch_scan_physical in Hphysical.
      tauto. }
    assert (Hcursor_words : copy_src_2 < Zlength watch_memory) by lia.
    apply ms_binary_watch_copy_step_p5;
      [exact H_binary_watch_copy_progress | exact Hcursor_words].
  }
  sep_apply_l_atomic
    (PtrArray.full_to_seg begin (copy_dst_2 + 1)
      (replace_Znth copy_dst_2
        (Znth (copy_src_2 - (copy_dst_2 + 1))
          (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
           Znth copy_src_2 copy_memory_2 0 :: nil) 0)
        (sublist 0 copy_dst_2 copy_memory_2 ++
         Znth copy_dst_2 copy_memory_2 0 :: nil)));
  try (entailer_with ltac:(lia); lia).
  sep_apply_l_atomic
    (PtrArray.seg_merge_to_full begin 0 (copy_dst_2 + 1)
      (copy_src_2 + 1)
      (replace_Znth copy_dst_2
        (Znth (copy_src_2 - (copy_dst_2 + 1))
          (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
           Znth copy_src_2 copy_memory_2 0 :: nil) 0)
        (sublist 0 copy_dst_2 copy_memory_2 ++
         Znth copy_dst_2 copy_memory_2 0 :: nil))
      (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
       Znth copy_src_2 copy_memory_2 0 :: nil));
  try (entailer_with ltac:(lia); lia).
  (* arch port A01: the stride cancels for any pointer width (0 * n = 0),
     so this rewrite is arch-blind. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (copy_src_2 + 1 - 0) with (copy_src_2 + 1) by lia.
  (* arch port A04: the goal carries the unfolded Arch32.ptr_size_Z while
     PtrArray's lemmas are stated with the derived ptr_size_Z; move
     sizeof(PTR) to the Arch alias then fold it to the derived name. *)
  try change (sizeof (PTR)) with ptr_size_Z. fold_arch.
  (* arch port A01: the stride cancels for any pointer width (0 * n = 0),
     so this rewrite is arch-blind. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  sep_apply_l_atomic
    (PtrArray.full_to_seg begin (copy_src_2 + 1)
      (replace_Znth copy_dst_2
        (Znth (copy_src_2 - (copy_dst_2 + 1))
          (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
           Znth copy_src_2 copy_memory_2 0 :: nil) 0)
        (sublist 0 copy_dst_2 copy_memory_2 ++
         Znth copy_dst_2 copy_memory_2 0 :: nil) ++
       sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
       Znth copy_src_2 copy_memory_2 0 :: nil));
  try (entailer_with ltac:(lia); lia).
  sep_apply_l_atomic
    (PtrArray.seg_merge_to_full begin 0 (copy_src_2 + 1)
      (Zlength source_words)
      (replace_Znth copy_dst_2
        (Znth (copy_src_2 - (copy_dst_2 + 1))
          (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
           Znth copy_src_2 copy_memory_2 0 :: nil) 0)
        (sublist 0 copy_dst_2 copy_memory_2 ++
         Znth copy_dst_2 copy_memory_2 0 :: nil) ++
       sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
       Znth copy_src_2 copy_memory_2 0 :: nil)
      (sublist (copy_src_2 + 1) (Zlength source_words) copy_memory_2)).
  1: { entailer_with ltac:(lia). change (sizeof (PTR)) with ptr_size_Z in *. solve_arch. }
  assert (Hcopy_src_lt : copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in *. solve_arch. }
  assert (Hcopy_len : Zlength copy_memory_2 = Zlength source_words).
  { unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
    destruct H_binary_watch_copy_progress as [copied [copy_rest
      [Hwords [Hkept [Hbounds [Hsuffix
        [Hsrc [Hdst [Hmemory Hmemory_len]]]]]]]]].
    unfold propagation_scan_open in H_propagation_scan_open.
    destruct H_propagation_scan_open as [_ [_ [_ [_ [_ [Hphysical _]]]]]].
    unfold propagation_watch_scan_physical in Hphysical.
    destruct Hphysical as [_ [_ [_ [_ Hwatch_len]]]].
    rewrite Hmemory_len, Hwatch_len.
    reflexivity. }
  assert (Hmiddle :
    Znth (copy_src_2 - (copy_dst_2 + 1))
      (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
       Znth copy_src_2 copy_memory_2 0 :: nil) 0 =
    Znth copy_src_2 copy_memory_2 0)
    by (apply ms_copy_middle_last_p5; lia).
  assert (Hprefix_update :
    replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0)
      (sublist 0 copy_dst_2 copy_memory_2 ++
       Znth copy_dst_2 copy_memory_2 0 :: nil) =
    sublist 0 copy_dst_2 copy_memory_2 ++
      Znth copy_src_2 copy_memory_2 0 :: nil).
  { rewrite replace_Znth_app_r by
      (rewrite Zlength_sublist by lia; lia).
    rewrite replace_Znth_nothing by
      (rewrite Zlength_sublist by lia; lia).
    replace (copy_dst_2 - Zlength (sublist 0 copy_dst_2 copy_memory_2))
      with 0 by (rewrite Zlength_sublist by lia; lia).
    simpl. reflexivity. }
  assert (Htail :
    (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
     Znth copy_src_2 copy_memory_2 0 :: nil) ++
      sublist (copy_src_2 + 1) (Zlength source_words) copy_memory_2 =
    sublist (copy_dst_2 + 1) (Zlength source_words) copy_memory_2)
    by (exact (ms_watch_copy_tail_merge_p5 copy_memory_2 copy_dst_2 copy_src_2
          (Zlength source_words) Hcopy_len ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hlist :
    ((replace_Znth copy_dst_2
        (Znth (copy_src_2 - (copy_dst_2 + 1))
          (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
           Znth copy_src_2 copy_memory_2 0 :: nil) 0)
        (sublist 0 copy_dst_2 copy_memory_2 ++
         Znth copy_dst_2 copy_memory_2 0 :: nil) ++
      sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
      Znth copy_src_2 copy_memory_2 0 :: nil) ++
      sublist (copy_src_2 + 1) (Zlength source_words) copy_memory_2) =
    replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0)
      copy_memory_2).
  { rewrite Hmiddle, Hprefix_update, !app_assoc.
    change (
      (((sublist 0 copy_dst_2 copy_memory_2 ++
         (Znth copy_src_2 copy_memory_2 0 :: nil)) ++
        sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2) ++
       (Znth copy_src_2 copy_memory_2 0 :: nil)) ++
       sublist (copy_src_2 + 1) (Zlength source_words) copy_memory_2 =
      replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0)
        copy_memory_2).
    rewrite <- app_assoc in Htail.
    rewrite <- !app_assoc.
    rewrite Htail.
    rewrite (replace_Znth_split 0 (Znth copy_src_2 copy_memory_2 0)
      copy_dst_2 copy_memory_2) by lia.
    rewrite <- Hcopy_len. reflexivity. }
  (* arch port A01: the stride cancels for any pointer width (0 * n = 0),
     so this rewrite is arch-blind. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  rewrite Hlist.
  cancel.
  all: try (change (sizeof (PTR)) with ptr_size_Z in *; solve_arch).
Qed.

Lemma proof_of_solver_propagate_entail_wit_16_scan_same : solver_propagate_entail_wit_16_scan_same.
Proof.
  unfold solver_propagate_entail_wit_16_scan_same.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  bind_fact ( candidate = Znth (offset_2 - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  Exists (offset_2 + 1) watch0_2.
  (entailer_with ltac:(lia));
  (try cancel;
    try lia).
  unfold propagation_int_missing.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_seg lits 2 offset_2
      (Zlength clause_contents) candidate
      (sublist 2 (Zlength clause_contents) clause_contents));
  (try lia;
    try cancel;
    try (entailer_with ltac:(lia); lia);
    try (rewrite H_candidate, replace_Znth_Znth; cancel)).
Qed.

Lemma proof_of_solver_propagate_entail_wit_17_1_unit_conflict_copy :
  solver_propagate_entail_wit_17_1_unit_conflict_copy.
Proof.
  unfold solver_propagate_entail_wit_17_1_unit_conflict_copy.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  msat_propagate_unit_conflict_copy_close_p5 jj.
Qed.

Lemma proof_of_solver_propagate_entail_wit_17_2_unit_conflict_copy :
  solver_propagate_entail_wit_17_2_unit_conflict_copy.
Proof.
  unfold solver_propagate_entail_wit_17_2_unit_conflict_copy.
  unfold stats_propagations.
  LLM_pre_process ltac:(lia).
  msat_propagate_unit_conflict_copy_close_p5 jj.
Qed.

(* ===== solver_propagate which_implies wits (21 proofs) ===== *)
Lemma proof_of_solver_propagate_which_implies_wit_27 : solver_propagate_which_implies_wit_27.
Proof.
  Unfold.
  intros.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan (Zlength scan_wm_pre) confl retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( logical_words = retained ++ rest ) as H_logical_words.
  bind_fact ( ms_wm Mscan = scan_wm_pre ++ logical_words :: scan_wm_post ) as H_ms_wm.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_2.
  bind_fact ( clause_is_lit_result scan_current 0 ) as H_clause_is_lit_result.
  bind_fact ( clause_db_pair_contents (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents ) as
      H_clause_db_pair_contents.
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as
    (Hscan & Hmemory & Hkept_len & Hprefix_len & Hmemory_len).
  assert (Hrest : rest = scan_current :: raw_suffix).
  {
    assert (Hparts :
      (retained ++ garbage) ++ rest =
      raw_prefix ++ scan_current :: raw_suffix).
    {
      rewrite <- app_assoc, <- Hmemory, H_watch_memory.
      reflexivity.
    }
    apply app_eq_app in Hparts as
      [[middle [Hleft Hright]] | [middle [Hleft Hright]]].
    - assert (Hmiddle_len : Zlength middle = 0).
      {
        rewrite Hleft, Zlength_app in Hprefix_len.
        lia.
      }
      assert (Hmiddle : middle = nil).
      {
        destruct middle as [|x middle]; [reflexivity|].
        rewrite Zlength_cons in Hmiddle_len.
        pose proof (Zlength_nonneg middle).
        lia.
      }
      subst middle. simpl in Hright. symmetry. exact Hright.
    - assert (Hmiddle_len : Zlength middle = 0).
      {
        rewrite Hleft, Zlength_app in H_Zlength.
        lia.
      }
      assert (Hmiddle : middle = nil).
      {
        destruct middle as [|x middle]; [reflexivity|].
        rewrite Zlength_cons in Hmiddle_len.
        pose proof (Zlength_nonneg middle).
        lia.
      }
      subst middle. simpl in Hright. exact Hright.
  }
  unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
  destruct H_solver_propagation_scan_semantics as [[Hconfl Hlive] | Hconflict].
  - subst confl.
    assert (Hreuse_scan : minisat_propagation_reuse_scan M0 Mscan p 0 rest).
    { rewrite <- H_Zlength_2. assumption. }
    pose proof Hlive as Hlive_all.
    destruct Hlive as
      (Hweak & Hproplevel & Hheapready & Hcovers & Hearliest & Hlevel &
       Hp_wf & Hprocessed & Hwatch_except & Hcarrier).
    assert (Hsemantics :
      solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest).
    {
      unfold solver_propagation_scan_semantics.
      left. rewrite <- H_Zlength_2. split; [reflexivity|exact Hlive_all].
    }
    assert (Hdbwf : db_wf n (msolver_db Mscan)).
    {
      unfold solver_propagation_weak in Hweak.
      destruct K; destruct Hweak as [_ Hinv].
      - exact (msw_db_wf Hinv).
      - exact (msa_db_wf Hinv).
    }
    assert (Hwmexact : wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
    {
      unfold solver_propagation_weak in Hweak.
      destruct K; destruct Hweak as [_ Hinv].
      - exact (msw_wmap_exact Hinv).
      - exact (msa_wmap_exact Hinv).
    }
    assert (Hcurrent_in : In scan_current (Znth p (ms_wm Mscan) nil)).
    {
      rewrite H_ms_wm, <- H_Zlength_2.
      unfold Znth.
      rewrite Zlength_correct, Nat2Z.id, app_nth2 by lia.
      replace (length scan_wm_pre - length scan_wm_pre)%nat with 0%nat by lia.
      simpl. rewrite H_logical_words, Hrest.
      apply in_or_app. right. left. reflexivity.
    }
    unfold clause_is_lit_result in H_clause_is_lit_result.
    destruct H_clause_is_lit_result as [[Hret _] | [_ Hreal]]; [lia|].
    destruct (wmap_real_witness n (msolver_db Mscan) (ms_wm Mscan)
      p scan_current Hdbwf Hwmexact
      ltac:(rewrite <- H_Zlength_2; exact Hp_wf) Hcurrent_in Hreal)
      as [co [Hco [Hco_len Hco_watch]]].
    unfold clause_db_pair_contents in H_clause_db_pair_contents.
    destruct H_clause_db_pair_contents as [co_target [Htarget Htarget_lits]].
    change (In (scan_current, co_target) (msolver_db Mscan)) in Htarget.
    assert (Hsame : co = co_target).
    {
      eapply db_wf_lookup_unique; eassumption.
    }
    subst co_target.
    unfold co_watch0, co_watch1 in Hco_watch.
    rewrite Htarget_lits in Hco_watch.
    destruct Hco_watch as [Hwatch | Hwatch].
    + Right.
      assert (Hslot : Znth 0 clause_contents 0 = lit_neg_c p).
      {
        rewrite <- Hwatch.
        rewrite lit_neg_c_involutive. reflexivity.
      }
      entailer_with ltac:(lia).
      unfold real_watch_pair. rewrite H_Zlength_2. left. exact Hslot.
    + Left.
      assert (Hslot : Znth 1 clause_contents 0 = lit_neg_c p).
      {
        rewrite <- Hwatch.
        rewrite lit_neg_c_involutive. reflexivity.
      }
      entailer_with ltac:(lia).
      unfold real_watch_pair. rewrite H_Zlength_2. right. exact Hslot.
  - destruct Hconflict as [_ [Hnil _]].
    rewrite Hrest in Hnil. discriminate.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_28 : solver_propagate_which_implies_wit_28.
Proof.
  Unfold.
  right.
  intros.
  pose proof (lit_sign_c_range w0) as Hsign.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_32 : solver_propagate_which_implies_wit_32.
Proof.
  Unfold.
  right.
  intros.
  unfold clause_db_pair_frame.
  Intros is_learnt_scan.
  Exists is_learnt_scan.
  pose proof
    (clause_hdr_word_div2 is_learnt_scan (Zlength clause_contents)
      (Zlength_nonneg clause_contents)) as Hhdr.
  entailer_with ltac:(lia).
  rewrite zdiv_equiv.
  - exact Hhdr.
  - unfold clause_hdr_word.
    destruct is_learnt_scan;
      pose proof (Zlength_nonneg clause_contents); lia.
  - lia.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_33 : solver_propagate_which_implies_wit_33.
Proof.
  Unfold.
  right.
  intros.
  unfold clause_db_pair_frame.
  Exists is_learnt_scan.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_34 : solver_propagate_which_implies_wit_34.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  rewrite <- H_raw_prefix.
  unfold propagation_ptr_segment.
  prop_apply (PtrArray.seg_valid begin 0 ii raw_prefix).
  Intros.
  prop_apply (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    raw_prefix (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words) (raw_prefix ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  (* arch port A01: the stride cancels for any pointer width (0 * n = 0),
     so this rewrite is arch-blind. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  replace ((raw_prefix ++ scan_current :: nil) ++ raw_suffix) with
    (raw_prefix ++ scan_current :: raw_suffix) by
    (rewrite <- app_assoc; reflexivity).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_35 : solver_propagate_which_implies_wit_35.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  pose proof (list_Znth_split 0 raw_prefix jj ltac:(lia)) as Hsplit.
  rewrite <- H_raw_prefix.
  unfold propagation_ptr_segment.
  prop_apply (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin jj (Znth jj raw_prefix 0)).
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj raw_prefix) (Znth jj raw_prefix 0 :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
    (sublist 0 jj raw_prefix ++ Znth jj raw_prefix 0 :: nil)
    (sublist (jj + 1) ii raw_prefix) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    ((sublist 0 jj raw_prefix ++ Znth jj raw_prefix 0 :: nil) ++
      sublist (jj + 1) ii raw_prefix)
    (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words)
    (((sublist 0 jj raw_prefix ++ Znth jj raw_prefix 0 :: nil) ++
      sublist (jj + 1) ii raw_prefix) ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  (* arch port A01: the stride cancels for any pointer width (0 * n = 0),
     so this rewrite is arch-blind. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  rewrite <- !app_assoc.
  simpl.
  entailer_with ltac:(lia).
  rewrite H_Zlength in Hsplit.
  assert (Hwords :
    sublist 0 jj raw_prefix ++
      Znth jj raw_prefix 0 ::
      sublist (jj + 1) ii raw_prefix ++ scan_current :: raw_suffix =
    raw_prefix ++ scan_current :: raw_suffix).
  {
    pose proof
      (f_equal (fun words => words ++ scan_current :: raw_suffix) Hsplit)
      as Happ.
    cbn in Happ.
    rewrite <- app_assoc in Happ.
    symmetry. exact Happ.
  }
  rewrite Hwords.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_37 : solver_propagate_which_implies_wit_37.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( Forall (lit_wf_c n) clause_contents ) as H_Forall.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
  destruct H_solver_propagation_scan_semantics as [[_ Hlive] | [Hcontra _]]; [|lia].
  destruct Hlive as
    (_ & _ & _ & _ & _ & _ & Hp_wf & Hprocessed & _ & _).
  destruct Hprocessed as [Hp_true _].
  assert (Hwatch_wf : lit_wf_c n watch0_base).
  { unfold lit_wf_c. lia. }
  assert (Hfalse_wf : lit_wf_c n false_lit).
  { rewrite H_false_lit. apply lit_neg_c_wf. exact Hp_wf. }
  assert (Htail_wf :
    Forall (lit_wf_c n)
      (sublist 2 (Zlength clause_contents) clause_contents)).
  {
    rewrite <- (sublist_self clause_contents (Zlength clause_contents) eq_refl)
      in H_Forall.
    rewrite (sublist_split 0 (Zlength clause_contents) 2 clause_contents)
      in H_Forall by lia.
    apply Forall_app in H_Forall.
    exact (proj2 H_Forall).
  }
  assert (Hwords_wf :
    Forall (lit_wf_c n)
      (propagation_normalized_clause watch0_base false_lit clause_contents)).
  {
    unfold propagation_normalized_clause.
    constructor; [exact Hwatch_wf|].
    constructor; [exact Hfalse_wf|exact Htail_wf].
  }
  assert (Hfalse : lit_false (mt_assigns (ms_core Mscan)) false_lit).
  {
    rewrite H_false_lit.
    unfold lit_false, lit_true in *.
    rewrite lit_var_c_neg, lit_sig_neg.
    lia.
  }
  assert (Hinv :
    propagation_replacement_scan_inv n Mscan false_lit
      (propagation_normalized_clause watch0_base false_lit clause_contents) 2).
  {
    unfold propagation_replacement_scan_inv.
    split.
    - rewrite propagation_normalized_clause_length by lia. lia.
    - split; [exact Hwords_wf|].
      split.
      + unfold propagation_normalized_clause. simpl. reflexivity.
      + split; [exact Hfalse|].
        intros j Hj. lia.
  }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_38 : solver_propagate_which_implies_wit_38.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( k = lits + offset * sizeof ( INT ) ) as H_k.
  unfold propagation_int_missing.
  sep_apply (IntArray.seg_split_to_missing_i lits 2 offset
    (Zlength clause_contents)
    (sublist 2 (Zlength clause_contents) clause_contents) 0); try lia.
  entailer_with ltac:(lia).
  rewrite H_k. cancel.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_39 : solver_propagate_which_implies_wit_39.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( 0 <= lit_var_c candidate ) as H_lit_var_c.
  assert (Hcandidate : 0 <= candidate).
  {
    unfold lit_var_c in H_lit_var_c.
    pose proof (Z.mod_pos_bound candidate 2 ltac:(lia)) as Hmod.
    pose proof (Z.div_mod candidate 2 ltac:(lia)) as Hdivmod.
    lia.
  }
  assert (Hcandidate_wf : lit_wf_c (ms_size Mscan) candidate).
  {
    unfold lit_wf_c.
    pose proof (lit_pack_unpack candidate Hcandidate) as Hpack.
    pose proof (lit_sign_c_range candidate) as Hsign.
    lia.
  }
  pose proof (lit_neg_c_wf (ms_size Mscan) candidate Hcandidate_wf) as Hneg_wf.
  unfold lit_wf_c in Hneg_wf.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_52 : solver_propagate_which_implies_wit_52.
Proof.
  Unfold.
  right. intros.
  bind_fact ( j = begin + copy_dst * sizeof ( PTR ) ) as H_j.
  prop_apply_p (PtrArray.full_Zlength begin
    (Zlength source_words) copy_memory).
  Intros_p Hcopy_len.
  sep_apply (PtrArray.full_to_seg begin
    (Zlength source_words) copy_memory).
  entailer_with ltac:(lia).
  - rewrite Hcopy_len.
    cancel (PtrArray.undef_seg begin (Zlength source_words) scan_wcap).
    cancel (PtrArray.seg begin 0 (Zlength source_words) copy_memory).
  - (* After [sizeof_ptr] the DIVISOR is the Arch constant while the [replace] below puts a
          literal in the numerator, so [Z.quot_mul]'s [?a * ?c / ?c] cannot match.  [fold_arch]
          keeps BOTH symbolic, which is arch-generic.  This mirrors the V2.0.5 CRules arch
          migration, which routed ptr_size_Z and addr_max_unsigned through the Arch functor
          parameter instead of a literal width. *)
    rewrite H_j, sizeof_ptr. fold_arch.
    replace (begin + copy_dst * ptr_size_Z - begin) with (copy_dst * ptr_size_Z) by lia.
    rewrite Z.quot_mul by (pose proof ptr_size_pos; lia). lia.
  - rewrite H_j, sizeof_ptr, Hcopy_len. fold_arch.
    replace (begin + copy_dst * ptr_size_Z - begin) with (copy_dst * ptr_size_Z) by lia.
    rewrite Z.quot_mul by (pose proof ptr_size_pos; lia). lia.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_54 : solver_propagate_which_implies_wit_54.
Proof.
  Unfold.
  right. intros.
  subst p.
  unfold solver_propagation_capacity_raw.
  Exists M_after.
  entailer_with ltac:(lia).
  unfold solver_propagation_capacity_rep_at.
  Exists (Zlength scan_wm_pre) (lit_neg_c candidate).
  Exists scan_wm_pre
    (sublist 0 ((j - begin) ÷ sizeof(PTR)) copy_memory)
    scan_wm_post.
  Exists scan_caps_pre scan_wcap scan_caps_post.
  unfold solver_propagation_capacity_focus_at.
  Exists ws destination_base.
  Exists (wlists_split_target_words (Zlength scan_wm_pre)
    (lit_neg_c candidate) scan_wm_pre scan_wm_post).
  Exists (wlists_split_target_cap (Zlength scan_wm_pre)
    (lit_neg_c candidate) scan_caps_pre scan_caps_post).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_55 : solver_propagate_which_implies_wit_55.
Proof.
  Unfold.
  right. intros. (entailer_with ltac:(lia));
  (pose proof (Zlength_nonneg
    (wlists_split_target_words (Zlength scan_wm_pre)
      (lit_neg_c candidate) scan_wm_pre scan_wm_post));
    lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_56 : solver_propagate_which_implies_wit_56.
Proof.
  Unfold.
  right. intros.
  subst i.
  sep_apply (PtrArray.full_split_to_missing_i begin ii
    (Zlength source_words) candidate_post_memory 0 ltac:(lia)).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_57 : solver_propagate_which_implies_wit_57.
Proof.
  Unfold.
  right. intros.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
 entailer_with ltac:(lia).
  rewrite <- H_Znth.
  rewrite replace_Znth_Znth by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_58 : solver_propagate_which_implies_wit_58.
Proof.
  Unfold.
  right. intros.
  subst destination.
  bind_fact ( Znth ii migration_post_memory 0 = scan_current ) as H_Znth.
 rewrite H_Znth.
  Exists (lit_neg_c candidate).
  entailer_with ltac:(lia).
  constructor; reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_59 : solver_propagate_which_implies_wit_59.
Proof.
  Unfold.
  right. intros.
  unfold vecp_rep, vecp_rep_at.
  Intros destination_base.
  Exists destination_base.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_60 : solver_propagate_which_implies_wit_60.
Proof.
  Unfold.
  right. intros.
  bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) offset ) as H_propagation_replacement_scan_inv.
  bind_fact ( candidate = Znth offset (propagation_normalized_clause watch0 false_lit clause_contents) 0 ) as
      H_candidate.
  bind_fact ( sig = 2 * lit_sign_c candidate - 1 ) as H_sig.
  bind_fact ( Znth (lit_var_c candidate) (mt_assigns (ms_core Mscan)) 0 = sig ) as H_Znth.
  unfold propagation_replacement_scan_inv in H_propagation_replacement_scan_inv |- *.
  destruct H_propagation_replacement_scan_inv as (Hbounds & Hwf & Hslot & Hfalse & Hold).
  entailer_with ltac:(lia).
  - rewrite propagation_normalized_clause_length by lia. lia.
  - intros j Hj.
    destruct (Z_lt_le_dec j offset) as [Hlt | Hge].
    + apply Hold. lia.
    + assert (j = offset) by lia. subst j.
      rewrite <- H_candidate.
      unfold lit_false, lit_sig.
      rewrite H_Znth, H_sig.
      unfold lit_sign_c.
      destruct (Z.odd candidate); reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_61 : solver_propagate_which_implies_wit_61.
Proof.
  Unfold.
  right. intros.
  bind_fact ( k = lits + offset * sizeof ( INT ) ) as H_k.
  bind_fact ( stop = lits + Zlength clause_contents * sizeof ( INT ) ) as H_stop.
  rewrite sizeof_int in H_k, H_stop.
  assert (offset = Zlength clause_contents) by lia.
  subst offset. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_62 : solver_propagate_which_implies_wit_62.
Proof.
  Unfold.
  intros.
  prop_apply_p (PtrArray.full_Zlength begin
    (Zlength source_words) candidate_post_memory).
  Intros_p Hcandidate_len.
  sep_apply (PtrArray.full_to_seg begin
    (Zlength source_words) candidate_post_memory).
  destruct (Z.eq_dec jj ii) as [Heq | Hneq].
  - subst jj. Left. entailer_with ltac:(lia).
    unfold propagation_ptr_segment.
    sep_apply (PtrArray.seg_split_to_seg begin 0 ii
      (Zlength source_words) candidate_post_memory ltac:(lia)).
    rewrite (PtrArray.seg_split_to_seg begin ii (ii + 1)
      (Zlength source_words)
      (sublist (ii - 0) (Zlength source_words - 0)
        candidate_post_memory)) by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (ii - 0) with ii by lia.
    replace (ii + 1 - ii) with 1 by lia.
    replace (0 + ii) with ii by lia.
    replace (1 + ii) with (ii + 1) by lia.
    replace (Zlength source_words - ii + ii)
      with (Zlength source_words) by lia.
    rewrite sublist_single with (d := 0)
      by (rewrite Hcandidate_len; lia).
    rewrite PtrArray.seg_unfold.
    rewrite PtrArray.seg_empty.
    entailer_with ltac:(lia).
  - Right. entailer_with ltac:(lia).
    unfold propagation_ptr_segment.
    sep_apply (PtrArray.seg_split_to_seg begin 0 jj
      (Zlength source_words) candidate_post_memory ltac:(lia)).
    rewrite (PtrArray.seg_split_to_seg begin jj (jj + 1)
      (Zlength source_words)
      (sublist (jj - 0) (Zlength source_words - 0)
        candidate_post_memory)) by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (jj - 0) with jj by lia.
    replace (jj + 1 - jj) with 1 by lia.
    replace (0 + jj) with jj by lia.
    replace (1 + jj) with (jj + 1) by lia.
    replace (Zlength source_words - jj + jj)
      with (Zlength source_words) by lia.
    rewrite (PtrArray.seg_split_to_seg begin (jj + 1) ii
      (Zlength source_words)
      (sublist (jj + 1) (Zlength source_words)
        candidate_post_memory)) by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (0 + (jj + 1)) with (jj + 1) by lia.
    replace (ii - (jj + 1) + (jj + 1)) with ii by lia.
    replace (Zlength source_words - (jj + 1) + (jj + 1))
      with (Zlength source_words) by lia.
    rewrite (PtrArray.seg_split_to_seg begin ii (ii + 1)
      (Zlength source_words)
      (sublist ii (Zlength source_words) candidate_post_memory)) by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (ii + 1 - ii) with 1 by lia.
    replace (0 + ii) with ii by lia.
    replace (1 + ii) with (ii + 1) by lia.
    replace (Zlength source_words - ii + ii)
      with (Zlength source_words) by lia.
    rewrite !sublist_single with (d := 0)
      by (rewrite Hcandidate_len; lia).
    rewrite !PtrArray.seg_unfold.
    rewrite !PtrArray.seg_empty.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_48 : solver_propagate_which_implies_wit_48.
Proof.
 exact proof_of_solver_propagate_which_implies_wit_62.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_63 : solver_propagate_which_implies_wit_63.
Proof.
  unfold solver_propagate_which_implies_wit_63.
  unfold stats_inspects.
  Unfold.
  right. intros.
  bind_fact ( enqueue_input (ms_size Mscan) watch0 (ms_qtail Mscan) (mt_assigns (ms_core Mscan)) (mt_levels (ms_core
      Mscan)) (ms_reason_words Mscan) (mt_trail (ms_core Mscan)) ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  unfold solver_propagation_scan_core_at, stats_propagate_scan.
  entailer_with ltac:(lia).
  unfold Znth. cbn. csimpl.
  intros m Hm. exact Hm.
Qed.

(* ===== solver_search which_implies wits (8 proofs) ===== *)
Lemma proof_of_solver_search_which_implies_wit_29 : solver_search_which_implies_wit_29.
Proof.
  Unfold.
  left; intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mprogress ) as H_msolver_inv.
  unfold solver_cancel_post.
  Split.
  - Intros.
    Exists Mprogress.
    split_pure_spatial.
    + apply solver_cancel_join_rep_levels_at.
    + pose proof (msw_root_range (msi_weak H_msolver_inv)) as Hr.
      assert (Hroot : solver_at_root Mprogress).
      { unfold solver_at_root. lia. }
      entailer_with ltac:(lia).
  - Intros orderpos order order_cap.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hre).
    set (Mrestart := msolver_cancel_project Mprogress
      (ms_root_level Mprogress) orderpos order order_cap
      (ms_root_level Mprogress)).
    assert (Hweak : msolver_inv_weak n F A_arr A_inst Mrestart).
    { unfold Mrestart. apply msolver_inv_weak_cancel__search
        with (M := Mprogress) (level := ms_root_level Mprogress)
             (orderpos := orderpos) (order := order) (order_cap := order_cap).
      - exact (msi_weak H_msolver_inv).
      - exact Hlevel.
      - reflexivity.
      - exact Hcap.
      - exact Hheap.
      - exact Hincl.
      - exact Hre. }
    Exists Mrestart.
    split_pure_spatial.
    + unfold Mrestart. apply solver_cancel_project_join_rep_levels_at.
    + pose proof (msi_trail_wf H_msolver_inv) as Htrail.
      assert (Hbound : Znth (ms_root_level Mprogress)
          (mt_lim (ms_core Mprogress)) 0 <= mt_qhead (ms_core Mprogress)).
      { apply Forall_Znth_elim; [exact (msi_prop_level H_msolver_inv)|lia]. }
      lazymatch goal with
      | Hreuse : solver_search_reuse ?entry Mprogress |- _ =>
          assert (Hreuse_restart : solver_search_reuse entry Mrestart)
            by (intro Hbase; unfold Mrestart;
                exact (minisat_base_completion_cancel__api_reentry
                  n Mprogress (ms_root_level Mprogress) orderpos order order_cap
                  (ms_root_level Mprogress) Htrail
                  (msw_db_wf (msi_weak H_msolver_inv)) Hlevel Hbound
                  (Hreuse Hbase)))
      end.
      assert (Hprop : prop_level (ms_core Mrestart)).
      { unfold Mrestart. apply (prop_level_cancel n (ms_core Mprogress)
          (ms_root_level Mprogress)).
        - exact Htrail.
        - exact Hlevel. }
      assert (Hwatch : minisat_watch_frontier n (msolver_db Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply minisat_watch_frontier_cancel__search
          with (M := Mprogress) (level := ms_root_level Mprogress)
               (orderpos := orderpos) (order := order) (order_cap := order_cap)
               (root := ms_root_level Mprogress).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_watch_frontier H_msolver_inv). }
      assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
      { rewrite (msi_size H_msolver_inv). exact Hheap. }
      assert (Hheapcov : heap_covers n (msolver_heap Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply heap_covers_cancel_project__canceluntil_cap
          with (M := Mprogress) (level := ms_root_level Mprogress)
               (orderpos := orderpos) (order := order).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_heap_wf H_msolver_inv).
        - exact Hheap_n.
        - exact Hincl.
        - exact (msi_heap_covers H_msolver_inv).
        - exact Hre. }
      assert (Hreasonless : current_reasonless_earliest n Mrestart).
      { unfold current_reasonless_earliest.
        intros d Hd v Hlev Hword.
        unfold Mrestart, msolver_cancel_project, msolver_core_heap_update in Hd.
        simpl in Hd. rewrite Zlength_ztake in Hd by lia. lia. }
      assert (Hinv : msolver_inv n F A_arr A_inst Mrestart).
      { refine {| msi_weak := Hweak; msi_prop_level := Hprop;
                 msi_watch_frontier := Hwatch; msi_heap_covers := Hheapcov;
                 msi_reasonless_current := Hreasonless |}. }
      assert (HrootM : solver_at_root Mrestart).
      { unfold solver_at_root, Mrestart, msolver_cancel_project,
          msolver_core_heap_update. simpl. rewrite Zlength_ztake by lia.
        lia. }
      assert (Hqtail : mt_qhead (ms_core Mrestart) = ms_qtail Mrestart).
      { unfold Mrestart, msolver_cancel_project, msolver_core_heap_update.
        reflexivity. }
      msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_31 : solver_search_which_implies_wit_31.
Proof.
  Unfold.
  left; intros.
  bind_fact (msolver_inv n F A_arr A_inst Mstable) as Hentry.
  bind_fact (Zlength (mt_lim (ms_core Mstable)) = 0) as Hdepth.
  pose proof (solver_level_zero_assuming__api_reentry
    n F A_arr A_inst Mstable Hentry Hdepth) as Hassuming.
  pose proof (solver_installed_assumptions_at_zero__api_reentry
    n F A_arr A_inst Mstable Hentry Hdepth) as Hinst.
  assert (Hroot : ms_root_level Mstable = 0).
  { pose proof (msi_root_range Hentry). lia. }
  unfold solver_simplify_pre_at, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_search_root_frame_at,
    solver_search_bundle_at, solver_search_payload, solver_payload_cells, solver_scalars_rep,
    solver_scalars_without_root_rep,
    solver_fp_rep, solver_vecs_without_lim_rep,
    solver_var_arrays_rep, solver_trail_array_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold solver_vecs_rep, solver_levels_slice_at.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_33 : solver_search_which_implies_wit_33.
Proof.
  Unfold.
  left; intros.
  bind_fact ( ms_model Mstable = nil ) as H_ms_model.
  bind_fact (msolver_inv n F A_arr A_inst Mstable) as Hentry_inv.
  bind_fact (Zlength (mt_lim (ms_core Mstable)) = 0) as Hentry_depth.
  bind_fact (ms_root_level Mstable = 0) as Hentry_root.
  bind_fact (A_inst = nil) as Hinst.
  subst A_inst.
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mstable |- _ =>
      assert (Hentry_full : minisat_base_watch_completed entry ->
          minisat_watch_completed Mstable)
        by (intro Hbase;
            exact (minisat_base_completion_at_depth_zero__api_reentry
              n Mstable (msi_trail_wf Hentry_inv)
              (msw_db_wf (msi_weak Hentry_inv)) Hentry_depth (Hentry Hbase)))
  end.
  unfold solver_simplify_post_at.
  Split.
  - Split.
    + Intros Mone. Intros. cancel. exfalso; lia.
    + Intros Mzero. Intros. cancel. exfalso; lia.
  - Intros.
    Intros Msimplify_cap.
    match goal with
    | Hpost : ms_cap Msimplify_cap = ms_cap Mstable /\ _ |- _ =>
        destruct Hpost as (Hcap & Hroot & Hprop & Hdepth & Hcomplete & Hcapacity & Hseed & Hmodel)
    end.
    assert (Hroot0 : ms_root_level Msimplify_cap = 0) by lia.
    pose proof (solver_assuming_propagation_zero_stable__api_reentry
      n F A_arr Msimplify_cap Hprop Hdepth Hroot0) as Hstable.
    assert (Hmodel_nil : ms_model Msimplify_cap = nil)
      by (exact (Hmodel H_ms_model)).
    lazymatch type of Hentry_full with
    | minisat_base_watch_completed ?entry -> _ =>
        assert (Hreuse_out : solver_search_reuse entry Msimplify_cap)
          by (intro Hbase;
              apply (minisat_full_completion_implies_base__api_reentry
                n Msimplify_cap (msa_trail_wf (msap_weak n F A_arr A_arr Msimplify_cap (proj2 Hprop)))
                (msa_db_wf (msap_weak n F A_arr A_arr Msimplify_cap (proj2 Hprop))));
              exact (Hcomplete (Hentry_full Hbase)))
    end.
    Exists Msimplify_cap.
    unfold solver_internal_capacity_ready.
    sep_apply (store_int_undef_store_int &("simplify_status") simplify_status).
    entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_34 : solver_search_which_implies_wit_34.
Proof.
  Unfold.
  left; intros.
  bind_fact (msolver_inv n F A_arr A_inst Mstable) as Hentry_inv.
  bind_fact (Zlength (mt_lim (ms_core Mstable)) = 0) as Hentry_depth.
  bind_fact (ms_root_level Mstable = 0) as Hentry_root.
  bind_fact (A_inst = nil) as Hinst.
  subst A_inst.
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mstable |- _ =>
      assert (Hentry_full : minisat_base_watch_completed entry ->
          minisat_watch_completed Mstable)
        by (intro Hbase;
            exact (minisat_base_completion_at_depth_zero__api_reentry
              n Mstable (msi_trail_wf Hentry_inv)
              (msw_db_wf (msi_weak Hentry_inv)) Hentry_depth (Hentry Hbase)))
  end.
  unfold solver_simplify_post_at.
  Split.
  - Split.
    + Intros Mone. Intros. cancel. exfalso; lia.
    + Intros Mzero. Intros.
      match goal with
      | Hpost : ms_cap Mzero = ms_cap Mstable /\ _ |- _ =>
          destruct Hpost as (Hcap & Hroot & Hweak & Hdepth & Hrecovery & Hcancel & Hpending & Hresident & Hunsat)
      end.
      assert (Hroot0 : ms_root_level Mzero = 0) by lia.
      pose proof (solver_assuming_weak_zero_stable__api_reentry
        n F A_arr Mzero Hweak Hdepth Hroot0) as Hstable.
      assert (Hatroot : solver_at_root Mzero) by (unfold solver_at_root; lia).
      lazymatch type of Hentry_full with
      | minisat_base_watch_completed ?entry -> _ =>
          assert (Hreuse_out : minisat_base_watch_completed entry ->
              solver_search_conflict_reuse n F A_arr (@nil literal) Mzero)
            by (intro Hbase; destruct (Hrecovery (Hentry_full Hbase)) as (Hbase_state & Hseed);
                split; [exact Hseed|right; split; [exact Hbase_state|exact Hresident]])
      end.
      Exists Mzero.
      sep_apply (store_int_undef_store_int &("simplify_status") simplify_status).
      entailer_with ltac:(int_auto).
  - Intros Mminus2. Intros. cancel. exfalso; lia.
Qed.

Lemma proof_of_solver_search_which_implies_wit_35 : solver_search_which_implies_wit_35.
Proof.
  Unfold.
  left; intros.
  bind_fact ( ms_model Mstable = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mstable) ) as H_msat_fp32_positive_finite.
  bind_fact (msolver_inv n F A_arr A_inst Mstable) as Hentry_inv.
  bind_fact (Zlength (mt_lim (ms_core Mstable)) = 0) as Hentry_depth.
  bind_fact (ms_root_level Mstable = 0) as Hentry_root.
  bind_fact (A_inst = nil) as Hinst.
  subst A_inst.
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mstable |- _ =>
      assert (Hentry_full : minisat_base_watch_completed entry ->
          minisat_watch_completed Mstable)
        by (intro Hbase;
            exact (minisat_base_completion_at_depth_zero__api_reentry
              n Mstable (msi_trail_wf Hentry_inv)
              (msw_db_wf (msi_weak Hentry_inv)) Hentry_depth (Hentry Hbase)))
  end.
  unfold solver_simplify_post_at.
  Split.
  - Split.
    + Intros Mone. Intros.
      match goal with
      | Hpost : ms_cap Mone = ms_cap Mstable /\ _ |- _ =>
          destruct Hpost as (Hcap & Hroot & Hinv & Hreuse & Hdepth & Hqueue & Hpending & Hseed & Hmodel & Hdecay)
      end.
      assert (Hroot0 : ms_root_level Mone = 0) by lia.
      pose proof (solver_assuming_zero_stable__api_reentry
        n F A_arr Mone Hinv Hdepth Hroot0) as Hstable.
      assert (Hmodel_nil : ms_model Mone = nil) by (exact (Hmodel H_ms_model)).
      assert (Hdecay_pos : msat_fp32_positive_finite (ms_cla_decay Mone))
        by (exact (Hdecay H_msat_fp32_positive_finite)).
      lazymatch type of Hentry_full with
      | minisat_base_watch_completed ?entry -> _ =>
          assert (Hreuse_out : solver_search_reuse entry Mone)
            by (intro Hbase;
                apply (minisat_full_completion_implies_base__api_reentry
                  n Mone (msi_trail_wf Hstable) (msw_db_wf (msi_weak Hstable)));
                apply Hreuse; left; exact (Hentry_full Hbase))
      end.
      Exists Mone.
      sep_apply (store_int_undef_store_int &("simplify_status") simplify_status).
      entailer_with ltac:(int_auto).
    + Intros Mzero. Intros. cancel. exfalso; lia.
  - Intros Mminus2. Intros. cancel. exfalso; lia.
Qed.

Lemma proof_of_solver_search_which_implies_wit_38 : solver_search_which_implies_wit_38.
Proof.
  Unfold.
  left; intros.
  unfold solver_reducedb_pre_at, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_search_reducedb_frame_at,
    solver_search_bundle_at, solver_search_payload, solver_payload_cells, solver_scalars_rep,
    solver_scalars_without_qtail_rep,
    solver_fp_rep, solver_vecs_without_learnts_rep,
    solver_var_arrays_rep, solver_trail_array_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold solver_vecs_rep, solver_levels_slice_at.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_39 : solver_search_which_implies_wit_39.
Proof.
  Unfold.
  left; intros.
  bind_fact ( ms_model Mclean = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mclean) ) as H_msat_fp32_positive_finite.
  unfold solver_reducedb_post_at.
  Intros Mreduced.
  match goal with
  | Hpost : msolver_inv n F A_arr A_inst Mreduced /\ _ |- _ =>
      destruct Hpost as (Hinv & Hq & Hp & Hseed & Hmodel & Hdecay & Hcap & Hreuse)
  end.
  assert (Hmodel_nil : ms_model Mreduced = nil)
    by (rewrite Hmodel; exact H_ms_model).
  assert (Hdecay_pos : msat_fp32_positive_finite (ms_cla_decay Mreduced))
    by (rewrite Hdecay; exact H_msat_fp32_positive_finite).
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mclean |- _ =>
      assert (Hreuse_out : solver_search_reuse entry Mreduced)
        by (intro Hbase; exact (Hreuse (Hentry Hbase)))
  end.
  Exists Mreduced.
  entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_41 : solver_search_which_implies_wit_41.
Proof.
  Unfold.
  right; intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mdb ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core Mdb) = ms_qtail Mdb ) as H_mt_qhead.
  unfold order_select_pre.
  Intros.
  pose proof (msi_shape H_msolver_inv) as Hshape.
  unfold solver_shape in Hshape.
  destruct Hshape as
    (Hsize & Hcap & Htwice & Hassign & Hlevels & Hreasons & Hopos & Hactivity &
     Htags & Htrail & Hqhead & Hpending & Hflag & Hflag_pending & Hqtail &
     Hwm & Hwcaps & Hbinary_lits & Hstats & Hroot & Hbinary & Heven).
  pose proof (msi_size H_msolver_inv) as Hn.
  entailer_with ltac:(lia).
  - unfold order_heap_wf.
    rewrite <- Hn.
    exact (msi_heap_wf H_msolver_inv).
  - rewrite <- Hn.
    exact (msi_heap_covers H_msolver_inv).
  - rewrite <- Hn.
    apply mtrail_wf_assigned_below_qhead.
    + exact (msi_trail_wf H_msolver_inv).
    + transitivity (ms_qtail Mdb).
      * exact H_mt_qhead.
      * symmetry; exact Htrail.
  - exact (mtw_cells (msi_trail_wf H_msolver_inv)).
Qed.


(* Additional obligations for the constructor and incremental public API. *)

Lemma proof_of_solver_new_which_implies_wit_1 : solver_new_which_implies_wit_1.
Proof.
  unfold solver_new_which_implies_wit_1. left. intros s.
  unfold solver_storage_undef. msat_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_new_which_implies_wit_2 : solver_new_which_implies_wit_2.
Proof.
  unfold solver_new_which_implies_wit_2. left. intros s binary.
  unfold MiniSatClause.undef at 1. coq_prop_lift.
  apply coq_prop_andp_left. intros [Hsize [Hpositive Hmod]].
  entailer_with ltac:(lia).
  rewrite Z.rem_mod_nonneg by lia. exact Hmod.
Qed.

Lemma proof_of_solver_new_which_implies_wit_3 : solver_new_which_implies_wit_3.
Proof.
  unfold solver_new_which_implies_wit_3. left.
  intros binary s clauses learnts order limits tagged stack model
    Hnonnull Hpositive Hrem.
  assert (Hmod : Z.modulo binary 2 = 0).
  { rewrite <- Z.rem_mod_nonneg by lia. exact Hrem. }
  Exists binary.
  unfold solver_initial_layout, solver_scalars_rep, solver_fp_rep,
    solver_vecs_rep, solver_ptrs_rep, stats_rep, MiniSatClause.rep.
  unfold vecp_rep, veci_rep.
  Exists clauses learnts tagged stack order limits model.
  unfold vecp_rep_at, veci_rep_at, vecp_size_addr, vecp_cap_addr,
    vecp_ptr_addr, veci_size_addr, veci_cap_addr, veci_ptr_addr,
    clause_hdr_addr, clause_act_addr, clause_lits_addr, clause_hdr_word,
    activity_state, stats_starts, stats_decisions, stats_propagations,
    stats_inspects, stats_conflicts, stats_clauses, stats_clauses_literals,
    stats_learnts, stats_learnts_literals, stats_max_literals, stats_tot_literals,
    solver_initial_model, solver_initial_core, msat_fp64_seed.
  cbn.
  PtrArray.ArraySimplify.
  IntArray.ArraySimplify.
  unfold clause_act_addr, msat_seed_default.
  cbn [Pos.to_nat].
  assert (Hnested : forall (L : lvalue_expr) (t : front_end_type) (f : string),
    eval_addr_expr (RE_addr_of (LE_dot_field L f)) =
    eval_addr_expr (RE_addr_of
      (LE_arrow_field (RE_const (eval_addr_expr (RE_addr_of L)) t) f))).
  { intros L t f. apply eval_addr_expr_congr.
    eapply rvalue_expr_equiv_trans.
    - apply addr_of_arrow_field.
    - apply RE_addr_of_congr. apply LE_arrow_field_congr.
      + apply rvalue_expr_equiv_sym. apply eval_addr.
      + reflexivity. }
  rewrite <- !Hnested.
  assert (Hknown_pure : forall (P : Prop) (Q : Assertion),
    P -> (“ P ” && Q --||-- Q)).
  { intros P Q HP. split; msat_entailer_with ltac:(tauto). }
  assert (Hknown_pure_right : forall (P : Prop) (Q : Assertion),
    P -> (Q && “ P ” --||-- Q)).
  { intros P Q HP. split; msat_entailer_with ltac:(tauto). }
  repeat match goal with
  | |- context [“ ?P ” && ?Q] =>
      let HP := fresh "Hknown" in
      assert (HP : P) by (first [reflexivity | tauto | lia]);
      rewrite (Hknown_pure P Q HP); clear HP
  | |- context [?Q && “ ?P ”] =>
      let HP := fresh "Hknown" in
      assert (HP : P) by (first [reflexivity | tauto | lia]);
      rewrite (Hknown_pure_right P Q HP); clear HP
  end.
  msat_cancel_sound.
  reflexivity.
Qed.

Lemma proof_of_solver_new_which_implies_wit_4 : solver_new_which_implies_wit_4.
Proof.
  unfold solver_new_which_implies_wit_4. left. intros binary s.
  sep_apply solver_initial_layout_result. Intros M.
  Exists M. unfold cnf_nil. msat_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_new_return_wit_1 : solver_new_return_wit_1.
Proof.
  unfold solver_new_return_wit_1. left.
  intros. Exists M_2.
  assert (Hflag : ms_capacity_root_propagation_pending M_2 = 0)
    by (destruct PreH4 as [_ [_ [_ [_ Hflag]]]]; exact Hflag).
  pose proof (solver_normal_root_query_ready__solve 0 cnf_nil M_2 PreH4)
    as Hready.
  pose proof (solver_query_update_ready__incremental_public 0 cnf_nil M_2 Hready)
    as Hupdate.
  unfold solver_incremental_ownership_at.
  msat_entailer_with ltac:(tauto || lia).
Qed.
