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

(* ------------------------------------------------------------------ *)
(* Part 9 file index.  C functions covered, in the order their proofs *)
(* appear below, with the wit families each one contributes:          *)
(*   lit_neg           -- return wits (3)                             *)
(*   solver_addclause  -- safety, entail, return, partial_solve,      *)
(*                        which_implies wits (48)                     *)
(*   clause_new        -- entail, safety wits (3)                     *)
(*   solver_record     -- partial_solve wit (1)                       *)
(*   solver_setnvars   -- entail, partial_solve, return, safety,      *)
(*                        which_implies wits (28)                     *)
(* Every proof_of_* below is a VC named in solver_qcp_goal.v; this     *)
(* part contributes no shared (cross-part) declarations.               *)
(* ------------------------------------------------------------------ *)

(* Part-local proof tactics.  Each collapses a family of solver_addclause /
   solver_setnvars obligations that were byte-identical scripts; the call sites
   keep whatever opener introduces the binders a tactic takes as arguments. *)

(* Every [lit_neg] return: the postcondition differs from the precondition only
   by the definition of [lit_neg_c], so unfolding that leaves pure arithmetic. *)
Ltac msat_lit_neg_close_p9 :=
  aggressive_pre_process;
  unfold lit_neg_c;
  entailer_with ltac:(lia).

(* The addclause "shape + sign + spatial" opener followed by the standard
   closer: the whole obligation is discharged by the three ac_ dispatchers. *)
Ltac msat_addclause_shape_spatial_close_p9 :=
  aggressive_pre_process;
  ac_shape;
  ac_sign;
  ac_spatial;
  entailer_with ltac:(ac_close).

(* An addclause side condition that needs the shape and the sign facts but no
   spatial rearrangement; plain arithmetic closes what is left. *)
Ltac msat_addclause_shape_sign_close_p9 :=
  aggressive_pre_process;
  ac_shape;
  ac_sign;
  entailer_with ltac:(lia).

(* Residual: the sort cursor is inside the buffer.  [Zlength pre = p] and the
   split equation [Zlength (pre ++ junk :: suf ++ rest2) = Zlength input] give
   it, but only after the app/cons expansion -- the [junk] cell is what makes
   the inequality STRICT, so the two tails' non-negativity is also needed. *)
Ltac msat_addclause_sort_cursor_close_p9 :=
  aggressive_pre_process; ac_shape; ac_sign; ac_spatial;
  entailer_with ltac:(ac_close);
  try (match goal with
       | H : Zlength (?a ++ ?x :: ?b ++ ?c) = _ |- _ =>
           rewrite !Zlength_app, !Zlength_cons in H;
           pose proof (Zlength_nonneg (b ++ c))
       end);
  solve [ lia ].

(* The setnvars obligations whose whole content is the shape dispatcher plus
   arithmetic: [snv_shape] restores the model view and [lia] closes the rest. *)
Ltac msat_setnvars_shape_close_p9 :=
  aggressive_pre_process;
  snv_shape;
  entailer_with ltac:(lia).

(* The order-heap precondition for one more variable, in the form the setnvars
   growth obligations need it: the fact at the model size, and a copy of it
   rewritten to the concrete [ms_size].  Callers add their own closer. *)
Ltac msat_setnvars_order_update_pre_p9 :=
  aggressive_pre_process; snv_shape;
  let hp := fresh "Hpre" in
  let hp2 := fresh "Hpre2" in
  (match goal with
   | H : solver_support_inv _ _ _ _ ?root ?M |- _ =>
       pose proof (solver_support_inv_order_update_pre__api_reentry
         _ _ _ _ root M H ltac:(lia) ltac:(lia)) as hp
   end;
   pose proof hp as hp2;
   match goal with H : ms_size _ = _ |- _ => rewrite H in hp2 end).

(* Dedup "skip" (complement arm): the element at k is dropped, so kept/tail/q
   are unchanged and only the scan index advances.  Every carried fact
   transports by [assumption]; the un-scanned region just loses its head
   ([all_ge_tail]).  The [Zlength sorted] bridge is asserted up front: S30's
   lemmas all carry an [n <= Zlength src] side condition and the Inv states
   only [Permutation].  The loop body's four locals (l, v, sig, val) are
   read-only scratch: the Inv asks only for the permission back, not the
   value. *)
Tactic Notation "msat_addclause_dedup_skip_p9" ident(sorted) ident(input)
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
        by (rewrite addclause_prefix_snoc by lia; rewrite <- Hcursor;
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
  entailer_with ltac:(ac_close);
  try (eapply all_ge_tail; [ lia | lia | lia | eassumption ]);
  try (ac_forget_locals; entailer_with idtac).

(* Dedup "keep": the element at k is copied down to slot q, so the buffer
   becomes [kept ++ x :: tl] where [x = Znth k (kept ++ junk :: tl)] and the
   head of the old tail is consumed.  [replace_Znth_hole] turns the in-place
   write into that shape.  The tail cannot be empty: q < Zlength input and
   Zlength (kept ++ tail) = Zlength input pin it.  The four model facts about
   [x] are established UP FRONT so [entailer_with] finds them by [assumption];
   [last < x] is precisely what the invariant did not carry before S30.
   The keep-condition reaches the VC as
   [Znth v (replace_Znth v (Znth v A 0) A) 0] -- the loop re-reads the slot it
   just wrote, so the write is the identity; with the `v' temp gone it arrives
   through the CALL RETURN binders, each pinned to [lit_var_c ..] by its own
   equation, so those are substituted before the self-replace is collapsed.
   The loop body's four locals are read-only scratch, as in the skip arm. *)
Tactic Notation "msat_addclause_dedup_keep_p9" ident(sortl) ident(inpt)
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
          match goal with
          | H : context[replace_Znth ?i (Znth ?i ?l 0) ?l] |- _ =>
              rewrite (replace_Znth_same i l 0) in H; [ exact H | ac_lia ]
          end);
    assert (Hcursor : Znth kidx (keptl ++ junk :: tl) 0 = Znth kidx sortl 0)
      by (eapply Znth_buffer_eq_src with
            (q := Zlength keptl) (n := Zlength inpt); ac_prem);
    match goal with
    | Hp : addclause_prefix_equiv ?F (sublist 0 kidx sortl) keptl |- _ =>
        assert (Hprefix_next : addclause_prefix_equiv F
            (sublist 0 (kidx + 1) sortl)
            (keptl ++ (Znth kidx (keptl ++ junk :: tl) 0 :: nil)))
          by (rewrite addclause_prefix_snoc by lia; rewrite <- Hcursor;
              apply addclause_prefix_keep; exact Hp)
    end;
    rewrite replace_Znth_hole;
    Exists tl (keptl ++ Znth kidx (keptl ++ junk :: tl) 0 :: nil)
              (Zlength keptl + 1) (kidx + 1);
    rewrite <- app_assoc; simpl app;
    match goal with H : endv = _ |- _ => rewrite <- H in * end;
    entailer_with ltac:(ac_close);
    try assumption;
    try (eapply keep_forall; ac_prem);
    try (eapply addclause_dedup_step; ac_prem);
    try (eapply keep_all_from; ac_prem);
    try ac_lia;
    try assumption;
    try (eapply keep_forall; ac_prem);
    try (eapply keep_all_from; ac_prem);
    try ac_lia;
    try (ac_forget_locals; entailer_with idtac) ].

(* Only the conditional completion guarantee is transported. The original
   construction precondition does not acquire a new watch premise. *)
Ltac ac_completed_p9 :=
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

Ltac ac_support_transition_p9 :=
  unfold addclause_support_transition;
  split; [unfold addclause_transition | ac_completed_p9].

(* The addclause returns that install nothing: the solver is still [M] and the
   buffer is [kept ++ tl] AS THE DEDUP LOOP LEFT IT (not a permutation of the
   input).  [ac_spatial] closes the
   assigns focus back to [solver_rep] and the growth tail that every cut
   restates rebuilds [solver_rep_growable]. The four bounds and conditional
   control preservation precede the return disjunct selected by [arm].
   [repeat split] must NOT be used on the transition: it sees through
   [msolver_inv] and shatters it into its component Foralls. *)
Tactic Notation "msat_addclause_return_frame_p9" ident(M) ident(kept) ident(tl)
    ident(F) tactic0(arm) :=
  unfold addclause_support_post_at;
  Exists M (kept ++ tl) F;
  split_pure_spatial;
  [ sep_apply solver_assigns_focus_close_levels_wl;
    sep_apply solver_rep_growable_of_wl;
    entailer_with lia
  | dump_pre_spatial; ac_support_transition_p9;
    split; [ assumption |];
    split; [ assumption |];
    split; [ assumption |];
    split; [ change (2 * ms_cap M <= INT_MAX); assumption |];
    split; [ intros _; split; [ assumption | split; assumption ] |];
    arm ].

(* ===== lit_neg return wits (3 proofs) ===== *)
Lemma proof_of_lit_neg_return_wit_1_sentinel : lit_neg_return_wit_1_sentinel.
Proof.
  msat_lit_neg_close_p9.
Qed.

Lemma proof_of_lit_neg_return_wit_2_original : lit_neg_return_wit_2_original.
Proof.
  msat_lit_neg_close_p9.
Qed.

Lemma proof_of_lit_neg_return_wit_3_bounded : lit_neg_return_wit_3_bounded.
Proof.
  aggressive_pre_process;
    pose proof (lit_neg_c_wf lit_bound_n_bounded l_pre
      ltac:(unfold lit_wf_c; lia)) as Hneg;
    unfold lit_wf_c in Hneg;
    unfold lit_neg_c in *;
    msat_manual_entailer_with lia.
Qed.

(* ===== solver_addclause safety wits (1 proofs) ===== *)
Lemma proof_of_solver_addclause_safety_wit_5 : solver_addclause_safety_wit_5.
Proof.
  msat_addclause_shape_spatial_close_p9.
  change (ac_n_addclause_spec <=
    Z.max (ms_cap ac_M_addclause_spec) 536870911) in PreH12.
  destruct (Z_le_gt_dec (ms_cap ac_M_addclause_spec) 536870911)
    as [Hcap | Hcap].
  - rewrite Z.max_r in PreH12 by lia. lia.
  - rewrite Z.max_l in PreH12 by lia. lia.
Qed.

(* ===== solver_addclause entail wits (17 proofs) ===== *)
Lemma proof_of_solver_addclause_entail_wit_1 : solver_addclause_entail_wit_1.
Proof.
  unfold solver_addclause_entail_wit_1; right; intros.
  clear PreH11 ac_physical_entry_addclause_spec.
(* Entering the insertion sort.  [maxvar = lit_var( *begin )] has already run,
   so the sorted prefix is the single first element and the rest is the tail.
   Only TWO existentials are supplied: the loop counter k is pinned by
   [Zlength sorted] and QCP unifies it on its own.

   The read of *begin left its cell handed out, so the array has to be merged
   back before the invariant's single [IntArray.seg] can appear -- and the
   written-back value is the one already there, which is what makes
   [replace_Znth_same] the identity that finishes the merge. *)
aggressive_pre_process; ac_shape; ac_sign.
Exists (sublist 1 (Zlength ac_input_addclause_spec) ac_input_addclause_spec)
       (Znth 0 ac_input_addclause_spec 0 :: nil).
assert (Hlen1 : 1 <= Zlength ac_input_addclause_spec) by ac_arith.
assert (Hinit := addclause_sort_outer_init ac_n_addclause_spec
                   ac_input_addclause_spec Hlen1 ltac:(assumption)).
rewrite Z.sub_0_r.
(* the read of *begin emits its cell at the BARE address, which
   missing_i_merge_to_seg cannot unify with its own [storeA x 0 _];
   [int_head_merge] bridges the two. *)
(* its two premises are discharged inline (return_wit_3 hands the same lemma
   its proofs the same way), so the closer below is left with ONE goal. *)
sep_apply (int_head_merge begin_pre (Zlength ac_input_addclause_spec)
             ac_input_addclause_spec ltac:(lia) ltac:(lia)).
simpl app.
rewrite hd_sublist_app by exact Hlen1.
msat_manual_entailer_with ltac:(ac_close).
Qed.

Lemma proof_of_solver_addclause_entail_wit_2_1 : solver_addclause_entail_wit_2_1.
Proof.
  (* Inner-loop ESTABLISHMENT, `lv > maxvar' branch: j = i, so the sorted prefix
     is all of [sorted] with an empty [suf], and the element being inserted is
     the HEAD of the unsorted remainder.  maxvar is raised to its var. *)
  aggressive_pre_process.
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout].
  assert (Hrne : rest <> nil).
  { intro Hn; rewrite Hn in *;
    rewrite ?Zlength_app, ?Zlength_nil in *; lia. }
  destruct rest as [|r0 rst]; [contradiction|].
  (* the read index appears as [k - 0] in some places and, once k has been
     substituted, as [Zlength sorted - 0] in others -- normalise both. *)
  try (replace (k - 0) with (Zlength sorted) in * by lia).
  try (replace (Zlength sorted - 0) with (Zlength sorted) in * by lia).
  rewrite (Znth_app_hd sorted r0 rst 0) in *.
  Exists r0 rst (@nil Z) sorted.
  rewrite app_nil_r.
  entailer_with ltac:(ac_close).
  (* [ac_znth] will NOT pose the var-range fact here: its arm is guarded on
     [0 <= x] not already being known, and the annotation already supplies
     that -- so the whole arm, including the range, is skipped. Pose it. *)
  - pose proof (lit_var_c_in_range ac_n_addclause_spec r0 ltac:(assumption)). lia.
  - apply (addclause_sort_outer_maxvar_mono ac_n_addclause_spec maxvar (lit_var_c r0));
      [ exact Hout | lia
      | pose proof (lit_var_c_in_range ac_n_addclause_spec r0 ltac:(assumption)); lia
      | pose proof (lit_var_c_in_range ac_n_addclause_spec r0 ltac:(assumption)); lia ].
  - unfold addclause_sort_inner_inv; rewrite ?app_nil_r;
      repeat split; [ assumption | constructor ].
Qed.

Lemma proof_of_solver_addclause_entail_wit_2_2 : solver_addclause_entail_wit_2_2.
Proof.
  (* Inner-loop ESTABLISHMENT, `lv <= maxvar' branch: j = i, so the sorted prefix
     is all of [sorted] with an empty [suf], and the element being inserted is
     the HEAD of the unsorted remainder.  maxvar is UNCHANGED here, so no monotonicity step is needed. *)
  aggressive_pre_process.
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout].
  assert (Hrne : rest <> nil).
  { intro Hn; rewrite Hn in *;
    rewrite ?Zlength_app, ?Zlength_nil in *; lia. }
  destruct rest as [|r0 rst]; [contradiction|].
  (* Same read-index-normalise note as in [proof_of_solver_addclause_entail_wit_2_1] above. *)
  try (replace (k - 0) with (Zlength sorted) in * by lia).
  try (replace (Zlength sorted - 0) with (Zlength sorted) in * by lia).
  rewrite (Znth_app_hd sorted r0 rst 0) in *.
  Exists r0 rst (@nil Z) sorted.
  rewrite app_nil_r.
  entailer_with ltac:(ac_close).
  unfold addclause_sort_inner_inv; rewrite ?app_nil_r;
    repeat split; [ assumption | constructor ].
Qed.

Lemma proof_of_solver_addclause_entail_wit_3 : solver_addclause_entail_wit_3.
Proof.
  (* Inner-loop SHIFT step (`*j = *(j-1); j--').  The hole moves one slot left,
     so the split point of [pre ++ suf] moves -- but the CONCATENATION is the
     same list, which is why both sort invariants carry over with no new
     sortedness reasoning.  The element shifted right is [last pre 0], and the
     loop-continue test [*(j-1) > l] is exactly what puts it above l. *)
  aggressive_pre_process.
  try ac_selfrepl.
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  match goal with H : addclause_sort_inner_inv _ _ _ _ |- _ =>
    pose proof (conj I H) as Hin end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout]; destruct Hin as [_ Hin].
  assert (Hne : pre_2 <> nil)
    by (intro Hn; rewrite Hn in *; rewrite Zlength_nil in *; lia).
  (* The inlined read [*(j-1)] (no tmpv temp) makes symexec emit the store's
     array as [replace_Znth p (Znth p arr 0) arr] -- a self-replace, i.e. [arr]
     itself.  Cancel it BEFORE the index bridge, or the bridge cannot see its
     own list.  Bounds come from ac_shape/ac_sign above, so ordering matters. *)
  (* The guard hypothesis [*(j-1) > l] carries the index as [p + -1 - 0] while
     the store's value carries it as [p + -1].  Same integer, unrelated atoms --
     normalise to ONE spelling before bridging, or the bridge reaches only the
     store and the [Forall] side goal is left without its ordering fact. *)
  replace (p_2 + -1 - 0) with (p_2 + -1) in * by lia.
  match goal with Harr : arr_2 = _ |- _ =>
    assert (Ha : Znth (p_2 + -1) arr_2 0 = last pre_2 0)
      by (rewrite Harr;
          replace (p_2 + -1) with (Zlength pre_2 - 1) by lia;
          apply Znth_pred_app_last; exact Hne) end.
  rewrite Ha in *.
  subst arr_2.
  Exists (last pre_2 0) rest2_2 (last pre_2 0 :: suf_2) (removelast pre_2).
  try (rewrite replace_Znth_twice).
  replace p_2 with (Zlength pre_2) by lia.
  rewrite (replace_Znth_hole pre_2 junk_2 (suf_2 ++ rest2_2) (last pre_2 0)).
  rewrite <- app_comm_cons.
  rewrite (removelast_app_last pre_2 (last pre_2 0 :: suf_2 ++ rest2_2) Hne).
  sep_apply IntArray.full_to_seg.
  entailer_with ltac:(ac_close).
  - rewrite (removelast_app_last pre_2 suf_2 Hne). exact Hout.
  - (* [repeat split] discharges the [sorted = pre ++ suf] conjunct itself by
       eq_refl, so exactly two survive: the rebuilt prefix is still sorted, and
       the shifted element is above the suffix it was moved past *)
    unfold addclause_sort_inner_inv; repeat split;
      [ rewrite (removelast_app_last pre_2 suf_2 Hne); assumption
      | constructor; [ lia | assumption ] ].
  - rewrite (Zlength_removelast pre_2 Hne). lia.
  - rewrite (removelast_app_last pre_2 suf_2 Hne). assumption.
  - rewrite (Zlength_removelast pre_2 Hne). lia.
Qed.

Lemma proof_of_solver_addclause_entail_wit_4_1 : solver_addclause_entail_wit_4_1.
Proof.
  (* Inner-loop exit via `j <= begin': j = begin + p*sizeof(INT) with 0 <= p
     forces p = 0, so nothing was shifted and [pre] is empty; the insertion puts
     l at the front.

     [ac_shape] DESTRUCTS both sort invariants, but
     [addclause_sort_insert_outer] consumes them whole -- so stash folded copies
     first.  A plain [pose proof] does not survive: ac_shape's arms match any
     hypothesis of that type and its [repeat] would eat the copy too.  Pairing
     with [I] changes the type enough that no arm matches. *)
  aggressive_pre_process.
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  match goal with H : addclause_sort_inner_inv _ _ _ _ |- _ =>
    pose proof (conj I H) as Hin end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout]; destruct Hin as [_ Hin].
  assert (Hp0 : p = 0) by (rewrite ?sizeof_int in *; lia).
  subst p.
  assert (Hpre : pre = nil) by (apply Zlength_nil_inv; lia).
  subst pre. subst arr.
  Exists rest2 (l :: suf).
  try (rewrite replace_Znth_twice).
  (* must fire BEFORE any [simpl app], which would normalise the `nil ++' away *)
  rewrite (replace_Znth_hole (@nil Z) junk (suf ++ rest2) l).
  simpl app.
  sep_apply IntArray.full_to_seg.
  entailer_with ltac:(ac_close).
  - exact (addclause_sort_insert_outer _ _ _ nil suf rest2 l Hout Hin
             (Forall_nil _) ltac:(assumption)).
  - (* [Zlength (nil ++ suf)] never reduces on its own; normalise the appends
       away first, or lia sees an opaque atom. *)
    simpl app in *; rewrite ?Zlength_cons, ?Zlength_app in *; ac_zlen; lia.
Qed.

Lemma proof_of_solver_addclause_entail_wit_4_2 : solver_addclause_entail_wit_4_2.
Proof.
  (* Inner-loop exit via the `*(j-1) <= l' BREAK: here [pre] is non-empty and l
     is inserted after it.  The invariant does not record [Forall (y <= l) pre];
     it comes from the break condition, which compares the LAST element of the
     sorted prefix -- [Znth (Zlength pre - 1) (pre ++ _) 0] is [last pre 0] for
     ANY tail, which is what lets the array's spelling and the invariant's
     spelling meet. *)
  aggressive_pre_process.
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  match goal with H : addclause_sort_inner_inv _ _ _ _ |- _ =>
    pose proof (conj I H) as Hin end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout]; destruct Hin as [_ Hin].
  subst arr.
  assert (Hne : pre <> nil)
    by (intro Hn; rewrite Hn in *; rewrite Zlength_nil in *; lia).
  assert (Hlast : last pre 0 <= l).
  { rewrite <- (Znth_pred_app_last pre (junk :: suf ++ rest2) 0 Hne).
    replace (Zlength pre - 1) with (p + -1 - 0) by lia.
    assumption. }
  assert (Hple : Forall (fun y => y <= l) pre)
    by (apply (sorted_le_last_bound pre l 0);
        [ exact (sorted_le_app_l pre suf ltac:(assumption)) | exact Hne | exact Hlast ]).
  Exists rest2 (pre ++ l :: suf).
  try (rewrite replace_Znth_twice).
  replace p with (Zlength pre) by lia.
  rewrite (replace_Znth_hole pre junk (suf ++ rest2) l).
  (* the witness is [pre ++ l :: suf], so the RHS reads [(pre ++ l :: suf) ++ rest2];
     re-associate and un-cons it to meet the array's own spelling. *)
  rewrite <- app_assoc, <- app_comm_cons.
  sep_apply IntArray.full_to_seg.
  entailer_with ltac:(ac_close).
  - exact (addclause_sort_insert_outer _ _ _ pre suf rest2 l Hout Hin Hple
             ltac:(assumption)).
  - (* the rewrite pair must be INTERLEAVED: splitting the append exposes a
       fresh cons node, and a single [?Zlength_cons] pass has already run by
       then, leaving [Zlength (junk :: suf ++ rest2)] as an opaque atom. *)
    rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_app, ?Zlength_cons in *;
      ac_zlen; lia.
Qed.

Lemma proof_of_solver_addclause_entail_wit_5 : solver_addclause_entail_wit_5.
Proof.
(* The cut at the solver_setnvars return: open solver_rep_growable into the
   assigns-focus shape the dedup loop reads through, AND keep the wlists growth
   tail that every later cut now restates.

   [ac_shape] has ALREADY destructed addclause_sort_outer_inv, so its folded
   form is gone -- work from the components it left instead of re-matching on
   the predicate.

   Literal well-formedness is REBUILT at the post-setnvars variable count, not
   transported: setnvars promises only [maxvar + 1 <= ms_size Mnew_2], and the
   caller's own bound ac_n need not be below ms_size Mnew_2, so lit_wf_c_mono does
   not apply.  [lit_wf_c_of_var_bound] goes via [lit_var_c l <= maxvar]. *)
aggressive_pre_process; ac_shape; ac_sign.
match goal with
| HI : solver_support_inv _ _ _ _ 0 ac_M_addclause_spec |- _ =>
    pose proof (msw_F_wf (msi_weak HI)) as Hinput_formula_wf
end.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
try ac_shape.
(* the sort loop has consumed the whole buffer, so the untouched tail is empty
   and both `sorted'-only facts upgrade to the whole array *)
assert (Hnil : rest = nil) by (apply (app_nil_of_Zlength sorted rest); ac_arith).
subst rest. try rewrite app_nil_r in *.
(* The downstream cuts now carry [all_from] (the dedup loop needs it to keep an
   element).  Its establishing fact is the sort loop's OWN first conjunct --
   [Permutation (sorted ++ rest) input] -- which ac_shape already unpacked. *)
match goal with
| H : Permutation sorted _ |- _ =>
    pose proof (all_from_of_Permutation _ _ H)
end.
assert (Hwf : Forall (lit_wf_c (ms_size Mnew_2)) sorted).
{ match goal with
  | Hp : Forall (fun x : Z => 0 <= x) sorted,
    Hb : Forall (fun x : Z => lit_var_c x <= maxvar) sorted |- _ =>
      rewrite Forall_forall in Hp, Hb |- *;
      intros x Hx; apply (lit_wf_c_of_var_bound maxvar);
        [ apply Hp, Hx | apply Hb, Hx | ac_arith ]
  end.
}
assert (Hinput_wf : Forall (lit_wf_c ac_n_addclause_spec)
    ac_input_addclause_spec).
{ eapply Permutation_Forall; eassumption. }
(* The public post preserves this continuation summary, not field equality. *)
match goal with
| H : (_ /\ _ /\ _ ->
       Zlength (mt_lim (ms_core Mnew_2)) = 0 /\
       ms_capacity_root_propagation_pending Mnew_2 = 0 /\ msolver_seed_shadow Mnew_2) |- _ =>
    let Hroot := fresh "Hroot" in
    pose proof (H ltac:(split; [ | split ]; assumption)) as Hroot;
    destruct Hroot as [Hlim0 [Hpending0 Hseed0]]
end.
assert (Hphysical_shape : solver_shape Mnew_2).
{ eapply (solver_shape_restore_physical_root__api_reentry Mnew_2 0).
  - match goal with HI : solver_support_inv _ _ _ _ 0 Mnew_2 |- _ =>
      exact (msi_shape HI)
    end.
  - match goal with Hr : ms_root_level Mnew_2 = ms_root_level ac_M_addclause_spec |- _ =>
      rewrite Hr
    end. assumption.
  - intro Hpending. rewrite Hpending0 in Hpending. discriminate. }
sep_apply solver_rep_growable_focus_open_wl.  (* Shares wl with the tail. *)
Intros asg lvl wl.
Exists wl lvl asg Mnew_2.
msat_manual_entailer_with ltac:(ac_close).
Qed.

Lemma proof_of_solver_addclause_entail_wit_6 : solver_addclause_entail_wit_6.
Proof.
  (* Dedup-loop invariant ESTABLISHMENT: i = j = begin, so k = 0 and nothing is
     kept yet.  Every conjunct is vacuous at [kept = nil]; [-2] is the "no
     previous literal" sentinel, and the un-scanned region is the whole array.

     [tail == sublist(q, n, sortedf)] DETERMINES tail, so the engine solves it
     and the emitted EX therefore binds only [kept] and [k] (the older
     [EX tail kept k] arity is gone), which is the arity witnessed below.

     Residuals are dispatched by goal SHAPE and matched by pattern variable,
     never by binder name -- [entailer_with] does not keep [sortedf] reachable
     by name in every branch. *)
  aggressive_pre_process; ac_shape; ac_sign.
  assert (Hl : Zlength sortedf = Zlength ac_input_addclause_spec)
    by (eapply Permutation_Zlength_Z; eassumption).
  assert (Hprefix : addclause_prefix_equiv ac_F_addclause_spec
      (sublist 0 0 sortedf) nil).
  { rewrite Zsublist_nil by lia. apply addclause_prefix_nil. }
  Exists (@nil Z) 0.
  (* the engine SOLVES [tail] from [tail == sublist(q, n, sortedf)]; at entry
     q = 0, so the witness it picks is [sublist (Zlength nil) n sortedf] --
     a redex.  Normalise it back to [sortedf] BEFORE entailing, or every
     conjunct is stated about an un-reduced term and nothing matches. *)
  (* A bare [rewrite Zlength_nil] finds no subterm here -- the goal's occurrence
     is [@Zlength Z nil] and the lemma's implicit does not line up through the
     entailment.  Routing through an explicitly-typed equation does match. *)
  assert (Hz : Zlength (@nil Z) = 0) by apply Zlength_nil.
  assert (Hs0 : sublist 0 (Zlength ac_input_addclause_spec) sortedf = sortedf)
    by (rewrite <- Hl; apply sublist_self; reflexivity).
  rewrite Hz, Hs0, ?app_nil_l.
  entailer_with ltac:(ac_close).
  all: match goal with
       | |- addclause_dedup_inv _ _ _ nil _ => apply addclause_dedup_inv_nil
       | |- all_ge _ _ => eapply all_ge_sentinel; eassumption
       | |- _ => ac_lia
       end.
Qed.

Lemma proof_of_solver_addclause_entail_wit_7_1 : solver_addclause_entail_wit_7_1.
Proof.
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_keep_p9 sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 last Mnew endvar_pre.
Qed.

Lemma proof_of_solver_addclause_entail_wit_7_2 : solver_addclause_entail_wit_7_2.
Proof.
(* KEEP branch of the dedup-loop entailment; same body as entail_wit_7_1. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_keep_p9 sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 last Mnew endvar_pre.
Qed.

Lemma proof_of_solver_addclause_entail_wit_7_3 : solver_addclause_entail_wit_7_3.
Proof.
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip_p9 sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.

Lemma proof_of_solver_addclause_entail_wit_7_4 : solver_addclause_entail_wit_7_4.
Proof.
(* SKIP branch of the dedup-loop entailment, in the same uniform family as
   entail_wit_7_3; entail_wit_7_2's body discharges it as well. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip_p9 sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.

Lemma proof_of_solver_addclause_entail_wit_7_5 : solver_addclause_entail_wit_7_5.
Proof.
(* SKIP branch of the dedup-loop entailment, in the same uniform family as
   entail_wit_7_3; entail_wit_7_2's body discharges it as well. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip_p9 sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.

Lemma proof_of_solver_addclause_entail_wit_7_6 : solver_addclause_entail_wit_7_6.
Proof.
(* SKIP branch of the dedup-loop entailment, in the same uniform family as
   entail_wit_7_3; entail_wit_7_2's body discharges it as well. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip_p9 sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.

Lemma proof_of_solver_addclause_entail_wit_8 : solver_addclause_entail_wit_8.
Proof.
  (* Dedup-loop EXIT into the post-dedup Assert: the loop's own kept/tail are the
     witnesses unchanged.  [ac_shape] keeps a FOLDED copy of the dedup invariant
     (its guarded arm), which is what the Assert wants back. *)
  aggressive_pre_process; ac_shape; ac_sign.
  assert (Hsortedlen : Zlength sortedf = Zlength ac_input_addclause_spec)
  by (eapply Permutation_Zlength_Z; eassumption).
assert (Hprefix : addclause_prefix_equiv ac_F_addclause_spec
    ac_input_addclause_spec kept_2).
{ eapply addclause_prefix_permutation; [eassumption |].
  match goal with
  | Hp : addclause_prefix_equiv _ (sublist 0 ?k sortedf) kept_2 |- _ =>
      assert (Hend : k = Zlength sortedf) by ac_arith;
      rewrite Hend, sublist_self in Hp by reflexivity; exact Hp
  end. }
Exists tail_2 kept_2.
  entailer_with ltac:(ac_close).
  (* the engine substitutes the solved [tail] witness on one side of the
     equation and not the other; the Inv's own bridge closes the gap *)
  f_equal; ac_prem.
Qed.

Lemma proof_of_solver_addclause_entail_wit_9 : solver_addclause_entail_wit_9.
Proof.
(* clause_new's CAPACITY-ABORT exit.  [clause_new_post_at_root] is an LHS
   disjunction, so [Split] destructs it -- the corpus's own
   destructor for [||] on the left.  The success arm carries [ret = 1] and dies
   against [PreH1 : retval = -2], which the branch condition pins.
   The growth tail frames through untouched. *)
aggressive_pre_process; ac_shape; ac_sign.
unfold clause_new_post_at_root.
Split.
- Intros M' c. coq_prop_lift. exfalso. lia.
- Intros M'. coq_prop_lift.
  assert (Hlim : Zlength (mt_lim (ms_core M')) = 0).
  { match goal with
    | H : clause_new_capacity_failure_root _ _ _ _ _ _ _ _ 0 |- _ =>
        pose proof (clause_new_caps_progress_gen_trail_lim
          _ _ _ _ (proj1 H)) as Hlimits
    end.
    rewrite Hlimits. assumption. }
  assert (Hcompletion : minisat_watch_completed ac_M_addclause_spec ->
    minisat_watch_completed M').
  { intro Hentry. match goal with
    | H : clause_new_capacity_failure_root _ _ _ _ ?entry M' _ _ _ |- _ =>
        eapply minisat_watch_completed_caps_progress__api_reentry;
          [exact (proj1 H) | tauto]
    end. }
  Exists M'. msat_manual_entailer_with ltac:(ac_close).
Qed.

Lemma proof_of_solver_addclause_entail_wit_10 : solver_addclause_entail_wit_10.
Proof.
(* clause_new's SUCCESS exit -- the mirror of entail_wit_9.  Here it is the
   capacity arm that dies, against [PreH1 : retval <> -2]. *)
aggressive_pre_process; ac_shape; ac_sign.
unfold clause_new_post_at_root.
Split.
- Intros M' c. coq_prop_lift.
  assert (Hlim : Zlength (mt_lim (ms_core M')) = 0).
  { match goal with
    | H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
        pose proof H as Hsource
    end.
    destruct Hsource as (Mcaps & Hprog & Hfresh & Heq & Hrest).
    rewrite Heq. change (Zlength (mt_lim (ms_core Mcaps)) = 0).
    rewrite (clause_new_caps_progress_gen_trail_lim _ _ _ _ Hprog).
    assumption. }
  assert (Hcompletion : minisat_watch_completed ac_M_addclause_spec ->
    minisat_watch_completed M').
  { intro Hentry. eapply clause_new_problem_completed__api_reentry;
      [eassumption | tauto]. }
  (* Expose only the already owned representation's physical shape. *)
  unfold solver_rep_levels_wl_at at 1.
  Intros act asg_after opos rsn trl tgs.
  Exists c M'.
  unfold solver_rep_levels_wl_at.
  Exists act asg_after opos rsn trl tgs.
  entailer_with ltac:(ac_close).
- Intros M'. coq_prop_lift. exfalso. lia.
Qed.

(* ===== solver_addclause return wits (10 proofs) ===== *)
Lemma proof_of_solver_addclause_return_wit_1 : solver_addclause_return_wit_1.
Proof.
(* The clause-INSTALLED return.  Two statistics fields were written in place, so
   the post's model is [msolver_addclause_finish Mclause kept] -- clause_new's
   result with the two counters bumped.  The refold is
   [addclause_stats_close_wl_finish]; before it can fire, the eleven loose cells have to
   go back into [stats_rep] at the UPDATED list, and the C pointer difference
   has to become [Zlength kept].

   [ac_ptrdiff] only rewrites HYPOTHESES and this redex is in the goal, so the
   pointer arithmetic is done by hand from the cut's own [j = begin + q * 4]. *)
try left.
all: aggressive_pre_process.
all: ac_shape.
all: ac_sign.
all: ac_spatial.
rewrite ?sizeof_int in *.
match goal with
| H : j = begin_pre + ?q * 4 |- _ => replace (j - begin_pre) with (q * 4) by lia
end.
rewrite quot_mul_four.
rewrite !ulnb64_lo64.
(* The engine truncates the pointer difference before adding it; the model does
   not.  [lo64_add_idem] reconciles them by modular idempotence -- no range
   reasoning about the literal count is needed at all. *)
rewrite lo64_add_idem.
match goal with H : Zlength kept = q |- _ => rewrite <- H end.
sep_apply stats_rep_addclause_fold.
sep_apply addclause_stats_close_wl_finish.
(* clause_new moves no variables and the stats bump moves none either (S20 +
   addclause_finish_size/cap), so the growth tail's bounds at [Mnew] are the
   post's bounds -- that identification is the whole reason S20 exists. *)
match goal with
| H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
    destruct (clause_new_success_root_bounds__api_reentry _ _ _ _ _ _ _ _ _ _ H)
      as [Hcs Hcc]
end.
unfold addclause_support_post_at.
Exists (msolver_addclause_finish Mclause kept) (kept ++ tail)
       (ac_F_addclause_spec ++ (lits_denote kept :: nil)).
split_pure_spatial.
-   rewrite ?addclause_finish_size, ?addclause_finish_cap, ?Hcs, ?Hcc.
  (* Growth tail spelled at the pre-call model; re-spell at the post's. *)
  replace (ms_size Mnew) with (ms_size (msolver_addclause_finish Mclause kept))
    by (rewrite ?addclause_finish_size; congruence).
  replace (ms_cap Mnew) with (ms_cap (msolver_addclause_finish Mclause kept))
    by (rewrite ?addclause_finish_cap; congruence).
  sep_apply solver_rep_growable_of_wl.
  sep_apply IntArray.seg_merge_to_seg.
  entailer_with lia.
  (* what is left is the seg-merge bound: both halves have non-negative length *)
  match goal with
  | H : Zlength (?k ++ ?t) = _ |- _ =>
      pose proof (Zlength_nonneg k); pose proof (Zlength_nonneg t);
      rewrite Zlength_app in H
  end; lia.
- dump_pre_spatial. ac_support_transition_p9.
  (* [clause_new_success_transition_gen] already carries the
     model invariant at the NEW cnf -- [cn_F F kept 0] is definitionally
     [F ++ [lits_denote kept]] (cn_F_prob).  All that is added here is the stats
     bump, which preserves it ([msolver_inv_addclause_finish]). *)
  match goal with
  | H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
      destruct H as (Mcaps & Hprog & Hfresh & Hinst & Hinv & Hpend & Hseed & Hcert)
  end.
  (* The support transition measures the semantic root view. *)
  change (ms_size (msolver_set_root (msolver_addclause_finish Mclause kept) 0) =
    ms_size Mnew) in Hcs.
  change (ms_cap (msolver_set_root (msolver_addclause_finish Mclause kept) 0) =
    ms_cap Mnew) in Hcc.
  rewrite Hcs, Hcc.
  split; [ assumption |].
  split; [ assumption |].
  split; [ assumption |].
  split; [ lia |].
  split; [ intros _; split; [ assumption | split; assumption ] |].
  right; right.
  split; [ reflexivity |].
  split.
  + apply solver_support_inv_addclause_finish__api_reentry. rewrite cn_F_prob in Hinv. exact Hinv.
  + apply addclause_install_equiv. assumption.
- match goal with
  | H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
      destruct H as (Mcaps & Hprog & Hfresh & Hinst & Hinv & Hpend & Hseed & Hcert)
  end.
  assumption.
- match goal with
  | H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
      destruct H as (Mcaps & Hprog & Hfresh & Hinst & Hinv & Hpend & Hseed & Hcert)
  end.
  assert (Sh : solver_shape Mclause) by assumption.
  unfold solver_shape in Sh; decompose [and] Sh; assumption.
Qed.

Lemma proof_of_solver_addclause_return_wit_2 : solver_addclause_return_wit_2.
Proof.
(* The clause_new capacity-abort return.  Three things this arm needs that no
   other does:

   1. [clause_new_caps_progress_gen_bounds] -- clause_new moves
      no variables, which is what lets the growth tail, restated at Mnew's
      bounds, retype at Mcap's.
   2. [IntArray.seg_merge_to_seg] -- the cut handed the buffer back SPLIT at
      Zlength kept (that is where clause_new's window ended), and the post
      wants one segment over the whole input.
   3. The RIGHT half of the -2 arm's disjunction: clause_new promises only
      [solver_internal_capacity_ready_gen], never msolver_inv.  That is the
      whole reason msolver_inv is per-arm. *)
try left;
  aggressive_pre_process; ac_shape; ac_sign.
match goal with H : clause_new_capacity_failure_root _ _ _ _ _ _ _ _ 0 |- _ =>
  let Hp := fresh in let Hr := fresh in
  destruct H as [Hp Hr];
  let B := fresh in
  pose proof (clause_new_caps_progress_gen_bounds _ _ _ _ Hp) as B;
  destruct B as [Hsz Hcp]
end.
unfold addclause_support_post_at.
Exists Mcap (kept ++ tail) ac_F_addclause_spec.
split_pure_spatial.
-   try (rewrite Hsz, Hcp).
  (* seg_merge_to_seg leaves its [lo <= mid <= hi] side condition as goal 2 *)
  sep_apply IntArray.seg_merge_to_seg; [ idtac | ac_arith ].
  (* Growth tail spelled at the pre-call model; re-spell at the post's. *)
  replace (ms_size Mnew) with (ms_size Mcap)
    by (rewrite ?addclause_finish_size; congruence).
  replace (ms_cap Mnew) with (ms_cap Mcap)
    by (rewrite ?addclause_finish_cap; congruence).
  sep_apply solver_rep_growable_of_wl.
  entailer_with lia.
- dump_pre_spatial. ac_support_transition_p9.
  change (ms_size (msolver_set_root Mcap 0) = ms_size Mnew) in Hsz.
  change (ms_cap (msolver_set_root Mcap 0) = ms_cap Mnew) in Hcp.
  rewrite Hsz, Hcp.
  split; [ assumption |].
  split; [ assumption |].
  split; [ assumption |].
  split; [ lia |].
  split.
  + intros _.
    match goal with
    | H : solver_internal_capacity_ready_gen _ _ _ _ (msolver_set_root Mcap 0) _ |- _ =>
        destruct H as [[Hpending Hinv] [Hexhausted Hseed]]
    end.
    split; [ assumption | split; assumption ].
  + right. left. split; [ lia | split; [ reflexivity | right; assumption ] ].
Qed.

Lemma proof_of_solver_addclause_return_wit_3 : solver_addclause_return_wit_3.
Proof.
(* The unit exit installs its retained literal on the root trail.
   Keep that invariant proof; prefix equivalence identifies the input clause. *)
try left;
  aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
rewrite ?Z.sub_0_r in *.
rewrite ?sizeof_int in *.
destruct Hded as (HdIn & HdSS & HdNA & HdPos & HdWF & HdUn & HdLe & HdLast & HdLst).
(* the branch condition pins the survivor count: (j - begin) / 4 = 1 with
   j = begin + q * 4 gives q = 1, hence Zlength kept = 1 *)
assert (Hq1 : q = 1).
{ match goal with
  | Hj : j = begin_pre + q * 4, Hd : (j - begin_pre) ÷ 4 = 1 |- _ =>
      rewrite Hj in Hd;
      replace (begin_pre + q * 4 - begin_pre) with (q * 4) in Hd by lia;
      rewrite quot_mul_four in Hd; exact Hd
  end. }
assert (Hk1 : Zlength kept = 1)
  by (match goal with H : Zlength kept = q |- _ => rewrite H; exact Hq1 end).
assert (Hk : 1 <= Zlength kept) by lia.
assert (Hhd : Znth 0 (kept ++ tail) 0 = Znth 0 kept 0).
{ destruct kept as [|a r]; [ rewrite Zlength_nil in Hk; lia | reflexivity ]. }
assert (Hfresh : Znth (lit_var_c (Znth 0 (kept ++ tail) 0))
                      (mt_assigns (ms_core Mnew)) 0 = 0).
{ rewrite Hhd. rewrite Forall_forall in HdUn. apply HdUn.
  apply ac_Znth_In. ac_lia. }
assert (Hlwf : lit_wf_c (ms_size Mnew) (Znth 0 (kept ++ tail) 0)).
{ rewrite Hhd. rewrite Forall_forall in HdWF. apply HdWF.
  apply ac_Znth_In. ac_lia. }
assert (Hkeq : lits_denote kept = lit_denote (Znth 0 (kept ++ tail) 0) :: nil).
{ rewrite Hhd. pose proof (singleton_of_Zlength_one kept Hk1) as Hs.
  unfold lits_denote. rewrite Hs at 1. reflexivity. }
match goal with H : solver_support_inv _ _ _ _ 0 Mnew |- _ =>
  assert (HshapeM : solver_shape Mnew) by assumption end.
match goal with H : enqueue_input _ _ _ _ _ _ _ |- _ =>
  pose proof H as Hein end.
unfold enqueue_input in Hein.
assert (Hroom : ms_qtail Mnew < ms_cap Mnew).
{ unfold solver_shape in HshapeM. decompose [and] HshapeM.
  decompose [and] Hein.
  match goal with Himp : (Znth _ _ 0 = 0 -> _) |- _ =>
    specialize (Himp Hfresh) end.
  lia. }
assert (HshapeE : solver_shape
   (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)).
{ apply solver_shape_enqueue_fresh__record;
    [ exact HshapeM | exact Hroom | assumption ]. }
unfold enqueue_post_at.
Intros qtail' assigns' levels' reasons' trail'.
match goal with H : enqueue_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rename H into Htr end.
pose proof Htr as Htr0.
unfold enqueue_transition in Htr.
destruct Htr as [Hsame | [Hconf | Hnew]].
{ destruct Hsame as [Hs _]. rewrite Hfresh in Hs.
  pose proof (lit_sig_nonzero (Znth 0 (kept ++ tail) 0)). lia. }
{ destruct Hconf as [Hne _]. contradiction. }
destruct Hnew as [Hz [Hret [Ha' [Hl' [Hr' [Ht' Hq']]]]]].
subst qtail' assigns' levels' reasons' trail' retval.
assert (Hsz : ms_size (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
              = ms_size Mnew) by reflexivity.
assert (Hcp : ms_cap (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
              = ms_cap Mnew) by reflexivity.
assert (Htrans : addclause_support_transition ac_n_addclause_spec ac_F_addclause_spec
    ac_A_arr_addclause_spec ac_A_inst_addclause_spec ac_M_addclause_spec
    ac_input_addclause_spec 1
    (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
    (kept ++ tail) (ac_F_addclause_spec ++ (lits_denote kept :: nil))).
{ ac_support_transition_p9.
  change (ms_size (msolver_set_root
    (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None) 0) =
    ms_size Mnew) in Hsz.
  change (ms_cap (msolver_set_root
    (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None) 0) =
    ms_cap Mnew) in Hcp.
  split; [ assumption | ].
  split; [ change (ms_size ac_M_addclause_spec <= ms_size Mnew); assumption | ].
  split; [ change (ms_cap ac_M_addclause_spec <= ms_cap Mnew); assumption | ].
  split; [ change (2 * ms_cap Mnew <= INT_MAX); assumption | ].
  split; [ intros _; split; [ assumption | split; assumption ] | ].
  right; right.
  split; [ reflexivity | ].
  split.
  - rewrite Hkeq.
    apply solver_support_inv_addclause_unit__api_reentry;
      [ assumption | exact Hlwf | exact Hfresh | assumption | exact Hroom
      | assumption ].
  - apply addclause_install_equiv. assumption. }
unfold addclause_support_post_at.
Exists (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
       (kept ++ tail) (ac_F_addclause_spec ++ (lits_denote kept :: nil)).
split_pure_spatial; [ | dump_pre_spatial; exact Htrans ].
eassert (Href : _ |-- enqueue_post_at s_pre asg lvlp
    (Znth 0 (kept ++ tail) 0) 0 (ms_size Mnew) (ms_cap Mnew) (ms_qtail Mnew) 1
    (mt_assigns (ms_core Mnew)) (mt_levels (ms_core Mnew)) (ms_reason_words Mnew)
    (mt_trail (ms_core Mnew)) (mt_lim (ms_core Mnew)) (ms_lim_cap Mnew)).
{ unfold enqueue_post_at.
  Exists (ms_qtail Mnew + 1)
    (replace_Znth (lit_var_c (Znth 0 (kept ++ tail) 0))
                  (lit_sig (Znth 0 (kept ++ tail) 0)) (mt_assigns (ms_core Mnew)))
    (replace_Znth (lit_var_c (Znth 0 (kept ++ tail) 0))
                  (Zlength (mt_lim (ms_core Mnew))) (mt_levels (ms_core Mnew)))
    (replace_Znth (lit_var_c (Znth 0 (kept ++ tail) 0)) 0 (ms_reason_words Mnew))
    (mt_trail (ms_core Mnew) ++ (Znth 0 (kept ++ tail) 0) :: nil).
  apply split_pure_and_spatial_goals; [ reflexivity | dump_pre_spatial; exact Htr0 ]. }
sep_apply Href.
(* The _wl clone keeps the watch-list pointer NAMED across the refold, so
   the growth tail at wlg can still be re-tied to the rep afterwards. *)
sep_apply (enqueue_post_record_refold_wl s_pre asg lvlp
  (Znth 0 (kept ++ tail) 0) 0 (ms_size Mnew) (ms_cap Mnew) (ms_qtail Mnew)
  (mt_assigns (ms_core Mnew)) (mt_levels (ms_core Mnew)) (ms_reason_words Mnew)
  (mt_trail (ms_core Mnew)) (mt_lim (ms_core Mnew)) (ms_lim_cap Mnew) Mnew None wlg
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  HshapeE Hfresh).
(* Growth tail spelled at the pre-call model; re-spell at the post's. *)
replace (ms_size Mnew) with (ms_size (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None))
  by (rewrite ?addclause_finish_size; congruence).
replace (ms_cap Mnew) with (ms_cap (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None))
  by (rewrite ?addclause_finish_cap; congruence).
sep_apply solver_rep_growable_of_wl.
sep_apply (int_head_merge begin_pre (Zlength ac_input_addclause_spec)
             (kept ++ tail) ltac:(ac_lia) ltac:(ac_lia)).
(* the post IS growable now -- no split, no re-hiding *)
msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_addclause_return_wit_4 : solver_addclause_return_wit_4.
Proof.
(* The `j == begin' empty-clause return: nothing was installed, so F' = F,
   the solver is still Mnew, and the FIRST arm of the return disjunction is
   the one this obligation carries. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  assert (Hnil : kept = nil) by (apply Zlength_nil_inv; ac_arith).
  assert (Hunsat : cnf_unsat
      (Z.max (ms_size ac_M_addclause_spec) ac_n_addclause_spec)
      (ac_F_addclause_spec ++ (lits_denote ac_input_addclause_spec :: nil))).
  { apply addclause_empty_unsat.
    - apply addclause_formula_wf; assumption.
    - rewrite Hnil in *. assumption. }
  msat_addclause_return_frame_p9 Mnew kept tail ac_F_addclause_spec
    (left; split; [reflexivity |]; split; [reflexivity |];
     split; [assumption | exact Hunsat]).
Qed.

Lemma proof_of_solver_addclause_return_wit_5 : solver_addclause_return_wit_5.
Proof.
(* A tautology return from inside the dedup loop (ret = 1, nothing installed):
   same shape as return_wit_4, but the THIRD arm of the return disjunction --
   ret = 1 with F' = F, which is what distinguishes "clause is trivially true"
   from "clause was added". *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  rewrite ?Z.sub_0_r in *.
  assert (Hin : In (Znth k (kept ++ tail) 0) ac_input_addclause_spec)
    by (eapply all_from_Znth; ac_prem).
  assert (Hent : entails_clause ac_F_addclause_spec
      (lits_denote ac_input_addclause_spec)).
  { intros rho HF.
    eapply addclause_dedup_complement;
      [eassumption | exact Hin | ac_arith | rewrite ?Z.sub_0_r in *; congruence]. }
  msat_addclause_return_frame_p9 Mnew kept tail ac_F_addclause_spec
    (right; right; split; [reflexivity |]; split; [assumption |];
     apply addclause_entailed_equiv; exact Hent).
Qed.

Lemma proof_of_solver_addclause_return_wit_6 : solver_addclause_return_wit_6.
Proof.
(* Same tautology-return note as in [proof_of_solver_addclause_return_wit_5] above. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  rewrite ?Z.sub_0_r in *.
  assert (Hin : In (Znth k (kept ++ tail) 0) ac_input_addclause_spec)
    by (eapply all_from_Znth; ac_prem).
  assert (Hent : entails_clause ac_F_addclause_spec
      (lits_denote ac_input_addclause_spec)).
  { intros rho HF.
    eapply addclause_dedup_complement;
      [eassumption | exact Hin | ac_arith | rewrite ?Z.sub_0_r in *; congruence]. }
  msat_addclause_return_frame_p9 Mnew kept tail ac_F_addclause_spec
    (right; right; split; [reflexivity |]; split; [assumption |];
     apply addclause_entailed_equiv; exact Hent).
Qed.

Lemma proof_of_solver_addclause_return_wit_7 : solver_addclause_return_wit_7.
Proof.
(* This statement corresponds to the obligation formerly cataloged as
   return_wit_5. *)
(* A ret = 1 return from inside the dedup loop (nothing installed), but via
   the ROOT-SATISFIED route (addclause_root_satisfied_input /
   addclause_root_true): the clause holds a literal already TRUE at the root,
   which is a different reason for F' = F than the dedup-tautology route of
   return_wit_5/6 above. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  rewrite ?Z.sub_0_r in *.
  assert (Hin : In (Znth k (kept ++ tail) 0) ac_input_addclause_spec)
    by (eapply all_from_Znth; ac_prem).
  assert (Hent : entails_clause ac_F_addclause_spec
      (lits_denote ac_input_addclause_spec)).
  { eapply addclause_root_satisfied_input; [exact Hin |].
    match goal with HI : solver_support_inv _ _ _ _ 0 Mnew |- _ =>
      eapply addclause_root_true;
        [exact (msi_trail_wf HI) | exact (msi_trail_impl HI) |
         eassumption | eassumption |]
    end.
    unfold lit_true, lit_sig.
    repeat match goal with
    | H : ?r = lit_var_c _ |- _ => is_var r; subst r
    end.
    ac_selfrepl. rewrite ?Z.sub_0_r in *.
    unfold lit_sign_c in *.
    destruct (Z.odd (Znth k (kept ++ tail) 0)); simpl in *; lia. }
  msat_addclause_return_frame_p9 Mnew kept tail ac_F_addclause_spec
    (right; right; split; [reflexivity |]; split; [assumption |];
     apply addclause_entailed_equiv; exact Hent).
Qed.

Lemma proof_of_solver_addclause_return_wit_8 : solver_addclause_return_wit_8.
Proof.
(* This statement corresponds to the obligation formerly cataloged as
   return_wit_6. *)
(* Same root-satisfied-route note as in [proof_of_solver_addclause_return_wit_7] above. *)
  try left; aggressive_pre_process; ac_shape; ac_sign; ac_spatial.
  rewrite ?Z.sub_0_r in *.
  assert (Hin : In (Znth k (kept ++ tail) 0) ac_input_addclause_spec)
    by (eapply all_from_Znth; ac_prem).
  assert (Hent : entails_clause ac_F_addclause_spec
      (lits_denote ac_input_addclause_spec)).
  { eapply addclause_root_satisfied_input; [exact Hin |].
    match goal with HI : solver_support_inv _ _ _ _ 0 Mnew |- _ =>
      eapply addclause_root_true;
        [exact (msi_trail_wf HI) | exact (msi_trail_impl HI) |
         eassumption | eassumption |]
    end.
    unfold lit_true, lit_sig.
    repeat match goal with
    | H : ?r = lit_var_c _ |- _ => is_var r; subst r
    end.
    ac_selfrepl. rewrite ?Z.sub_0_r in *.
    unfold lit_sign_c in *.
    destruct (Z.odd (Znth k (kept ++ tail) 0)); simpl in *; lia. }
  msat_addclause_return_frame_p9 Mnew kept tail ac_F_addclause_spec
    (right; right; split; [reflexivity |]; split; [assumption |];
     apply addclause_entailed_equiv; exact Hent).
Qed.

Lemma proof_of_solver_addclause_return_wit_9 : solver_addclause_return_wit_9.
Proof.
(* The setnvars capacity-failure return; corresponds to the former
   return_wit_7, with the split detour removed. *)
(* setnvars returned capacity failure before the assignment array was opened.
   Its postcondition already supplies solver_rep_growable, including the growth
   tail. The sorted buffer is unchanged because deduplication has not run. *)
try left;
  aggressive_pre_process; ac_shape; ac_sign.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
unfold addclause_support_post_at.
Exists Mnew (sorted ++ rest) ac_F_addclause_spec.
split_pure_spatial.
(* The post IS solver_rep_growable now -- no split, no re-hiding. *)
- entailer_with lia.
- dump_pre_spatial. ac_support_transition_p9.
  (* peel the conjunct chain, solving each left half, and STOP at the return
     disjunction -- which is not a [/\] so the match no longer fires *)
  repeat match goal with
         | |- _ /\ _ => split; [ solve [ assumption | lia | ac_arith ] | ]
         end.
  (* the setnvars -2 source: the solver is still fully invariant, so this
     arm's disjunction takes its LEFT half *)
  right. left. split; [ lia | split; [ reflexivity | left; assumption ] ].
Qed.

Lemma proof_of_solver_addclause_return_wit_10 : solver_addclause_return_wit_10.
Proof.
  unfold solver_addclause_return_wit_10; right; intros.
  clear PreH2 ac_physical_entry_addclause_spec.
(* This statement corresponds to the obligation formerly cataloged as
   return_wit_8. *)
  (* The `begin == endvar' early return.  Together with
     [endvar = begin + Zlength input * sizeof(INT)] that forces the input to be
     empty, and the goal is then exactly [addclause_support_post_empty__api_reentry] -- the ret = 0
     arm of [addclause_support_transition], nothing installed. *)
  aggressive_pre_process.
  all: ac_shape.
  all: (assert (Hnil : ac_input_addclause_spec = nil)
    by (apply Zlength_nil_inv; rewrite ?sizeof_int in *; lia));
    (rewrite Hnil);
    (apply addclause_support_post_empty__api_reentry);
    (assumption).
Qed.

(* ===== solver_addclause partial_solve wits (7 proofs) ===== *)
Lemma proof_of_solver_addclause_partial_solve_wit_17_pure : solver_addclause_partial_solve_wit_17_pure.
Proof.
  msat_addclause_sort_cursor_close_p9.
Qed.

Lemma proof_of_solver_addclause_partial_solve_wit_20_pure : solver_addclause_partial_solve_wit_20_pure.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_partial_solve_wit_21_pure : solver_addclause_partial_solve_wit_21_pure.
Proof.
  msat_addclause_shape_sign_close_p9.
Qed.

Lemma proof_of_solver_addclause_partial_solve_wit_26_pure : solver_addclause_partial_solve_wit_26_pure.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_partial_solve_wit_27_pure : solver_addclause_partial_solve_wit_27_pure.
Proof.
  msat_addclause_shape_sign_close_p9.
Qed.

Lemma proof_of_solver_addclause_partial_solve_wit_40_pure : solver_addclause_partial_solve_wit_40_pure.
Proof.
  msat_addclause_sort_cursor_close_p9.
Qed.

Lemma proof_of_solver_addclause_partial_solve_wit_43_pure : solver_addclause_partial_solve_wit_43_pure.
Proof.
  msat_addclause_sort_cursor_close_p9.
Qed.

(* ===== solver_addclause which_implies wits (11 proofs) ===== *)
Lemma proof_of_solver_addclause_which_implies_wit_3 : solver_addclause_which_implies_wit_3.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_4 : solver_addclause_which_implies_wit_4.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_5 : solver_addclause_which_implies_wit_5.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_6 : solver_addclause_which_implies_wit_6.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_7 : solver_addclause_which_implies_wit_7.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_8 : solver_addclause_which_implies_wit_8.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_9 : solver_addclause_which_implies_wit_9.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_10 : solver_addclause_which_implies_wit_10.
Proof.
  msat_addclause_shape_spatial_close_p9.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_11 : solver_addclause_which_implies_wit_11.
Proof.
(* The enqueue peel for the unit-clause arm.

   aggressive_pre_process CANCELS the three assigns atoms (they sit on both
   sides of this which-implies), so the s27 lemma no longer matches -- what is
   left is the frame rearrangement alone, done by the same unfold set.  The
   double unfold is required because solver_assigns_focus_frame_wl_at passes
   solver_scalars_rep / solver_vecs_rep as arguments, so a single pass cannot
   reach the copies substitution creates.

   The one semantic obligation, enqueue_input, comes from the dedup invariant
   via s28: the kept literal is unassigned, so its variable is off the trail,
   so the trail is strictly shorter than the variable count. *)
aggressive_pre_process; ac_shape; ac_sign.
unfold enqueue_state_at, solver_enqueue_frame_wl,
  solver_enqueue_frame_with_scalars_wl, solver_enqueue_cells_at, solver_enqueue_scalars_frame,
  solver_enqueue_vecs_frame,
  solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
unfold solver_scalars_rep, solver_vecs_rep, solver_trail_array_rep,
  solver_levels_slice_at, solver_var_arrays_rep, solver_ptrs_rep.
(* [_wl_at] makes wl a PARAMETER, so the LHS has 5 binders, not 6. *)
Intros act opos rsn trl tgs.
(* The RHS frame is now spelled at wlg, so wl is no longer existential
   on either side -- five witnesses, not six. *)
Exists trl rsn act opos tgs.
repeat lazymatch goal with
| |- _ |-- _ && _ => apply _derivable1_andp_intros
end;
lazymatch goal with
| |- _ |-- “ _ ” =>
    apply dump_spatial_left;
    solve
      [ ac_close
      | match goal with
        | Hsupport : solver_support_inv _ ?F ?A_arr ?A_inst ?root ?M |- _ =>
            eapply (addclause_dedup_enqueue_input F A_arr A_inst
              (msolver_set_root M root));
              [ exact Hsupport | eassumption | ac_arith ]
        end ]
| |- _ |-- _ =>
    msat_cancel_sound; change (emp |-- emp); reflexivity
end.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_12 : solver_addclause_which_implies_wit_12.
Proof.
(* Hand the solver to clause_new: close the assigns focus at the LEVEL-INDEXED
   rep (clause_new's Require wants solver_rep_levels_at at this lvlp, and plain
   solver_rep has already thrown lvlp away), then split the buffer at the
   kept/tail boundary because clause_new is handed [begin, j) only. *)
aggressive_pre_process; ac_shape; ac_sign.
sep_apply solver_assigns_focus_close_levels_wl.
sep_apply (IntArray.seg_split_to_seg begin 0 (Zlength kept)
             (Zlength ac_input_addclause_spec) (kept ++ tail)).
(* seg_split_to_seg emits the bounds as [mid - lo] / [hi - lo]; normalise the
   [- 0] away FIRST or neither sublist identity finds its redex *)
rewrite !Z.sub_0_r.
rewrite sublist_app_exact1.
match goal with H : Zlength (kept ++ tail) = Zlength ac_input_addclause_spec |- _ =>
  rewrite <- H end.
rewrite sublist_app_exact2.
(* the split leaves EIGHT goals of three KINDS -- the reordered spatial
   entailment, the [lo <= mid <= hi] side condition, and the which-implies' own
   pure conjuncts (database == solver_selected_vec s 0, and the literal
   well-formedness the clause_new Require asks for) -- and the corpus's standard
   addclause closer discharges every one of them, so one selector, one closer. *)
all: msat_manual_entailer_with ltac:(ac_close).
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_13 : solver_addclause_which_implies_wit_13.
Proof.
  (* The stats OPEN direction.  Both disjuncts are the same entailment and the
     _split_goal_spatial twin is the bare one, so [try left] serves all three.
     The LHS is [solver_rep_levels_wl_at .. wlg ..] -- wl is a PARAMETER now,
     so nothing has to be chosen for it.  [addclause_stats_open_wl_noshape] does
     the peel; [stats_rep_open_dotted] bridges [stats_rep] to the dotted field
     spelling the VC uses. *)
  try left. intros lvlp wlg Mclause s.
  sep_apply (addclause_stats_open_wl_noshape s Mclause wlg lvlp).
  sep_apply (stats_rep_open_dotted s (ms_stats Mclause)).
  msat_manual_entailer_with lia.
Qed.

(* ===== clause_new entail wits (2 proofs) ===== *)
Lemma proof_of_clause_new_entail_wit_11_1 : clause_new_entail_wit_11_1.
Proof.
  Unfold.
  left.
  intros.
  cn_pin_learnt cn_sel_clause_new_spec.
  bind_fact ( c % 2 = 0 ) as H_c.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage3 cn_words_clause_new_spec 1 cn_root_clause_new_spec ) as H_clause_new_stage_ready.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof Hphysical as Hshape.
  destruct Hcert as (_ & Hall & _).
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 Hall ltac:(lia)) as Hlit0.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 Hall ltac:(lia)) as Hlit1.
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0.
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.
  unfold solver_shape in Hshape.
  unfold lit_wf_c in Hlit0, Hlit1, Hneg0, Hneg1.
  aggressive_pre_process; entailer_with ltac:(lia).
  assert (Hi : i = size) by lia.
  subst i.
  subst size.
  rewrite (sublist_self cn_words_clause_new_spec
    (Zlength cn_words_clause_new_spec)) by reflexivity.
  rewrite IntArray.undef_seg_empty.
  unfold MiniSatClause.rep, clause_hdr_word, activity_state.
  cbn.
  Exists _.
  unfold clause_hdr_addr, clause_act_addr, clause_lits_addr.
  entailer_with ltac:(int_auto).
  - rewrite (Z.mul_comm (Zlength cn_words_clause_new_spec) 2).
    entailer_with ltac:(int_auto).
  - change (msat_fp32_nonnegative
      (fp32_of_real
        (Rdefinitions.Q2R
          {| QArith_base.Qnum := 0; QArith_base.Qden := 10 |}))).
    replace (fp32_of_real
      (Rdefinitions.Q2R
        {| QArith_base.Qnum := 0; QArith_base.Qden := 10 |})) with
      (fp32_of_real (Rdefinitions.IZR 0)).
    + exact MSatFloatFacts.fp32_of_real_zero_nonnegative.
    + f_equal. lra.
  - rewrite <- (Z.rem_mod_nonneg c 2) by lia.
    exact H_c.
Qed.

Lemma proof_of_clause_new_entail_wit_11_2 : clause_new_entail_wit_11_2.
Proof.
  Unfold.
  left.
  intros.
  cn_pin_prob cn_sel_clause_new_spec.
  bind_fact ( c % 2 = 0 ) as H_c.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage3 cn_words_clause_new_spec 0 cn_root_clause_new_spec ) as H_clause_new_stage_ready.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof Hphysical as Hshape.
  destruct Hcert as (_ & Hall & _).
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 Hall ltac:(lia)) as Hlit0.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 Hall ltac:(lia)) as Hlit1.
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0.
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.
  unfold solver_shape in Hshape.
  unfold lit_wf_c in Hlit0, Hlit1, Hneg0, Hneg1.
  aggressive_pre_process; entailer_with ltac:(lia).
  assert (Hi : i = size) by lia.
  subst i.
  subst size.
  rewrite (sublist_self cn_words_clause_new_spec
    (Zlength cn_words_clause_new_spec)) by reflexivity.
  rewrite IntArray.undef_seg_empty.
  unfold MiniSatClause.rep, clause_hdr_word, activity_state.
  cbn.
  unfold clause_hdr_addr, clause_act_addr, clause_lits_addr.
  entailer_with ltac:(int_auto).
  - rewrite (Z.mul_comm (Zlength cn_words_clause_new_spec) 2).
    entailer_with ltac:(int_auto).
  - rewrite <- (Z.rem_mod_nonneg c 2) by lia.
    exact H_c.
Qed.

(* ===== clause_new safety wits (1 proofs) ===== *)
Lemma proof_of_clause_new_safety_wit_35 : clause_new_safety_wit_35.
Proof.
  aggressive_pre_process; dump_pre_spatial;
    pose proof (signed_Lastnbits_range (size * 2 ^ 1) 32 ltac:(lia));
    cbn in H;
    replace (2 ^ 1) with 2 by reflexivity;
    lia.
Qed.

(* ===== solver_record partial_solve wits (1 proofs) ===== *)
Lemma proof_of_solver_record_partial_solve_wit_8_pure : solver_record_partial_solve_wit_8_pure.
Proof.
  (* Expose shape and the physical-root view for the four pure conjuncts. *)
  aggressive_pre_process;
    match goal with
    | Hinv : msolver_inv _ _ _ _ ?M |- _ =>
        pose proof (msi_shape Hinv) as Hshape
    end;
    rewrite ?sel_vec_learnt, ?sel_learnt_learnt;
    try unfold solver_support_inv;
    rewrite ?msolver_set_root_self__api_reentry;
    entailer_with ltac:(assumption || lia).
Qed.

(* ===== solver_setnvars entail wits (4 proofs) ===== *)
Lemma proof_of_solver_setnvars_entail_wit_1 : solver_setnvars_entail_wit_1.
Proof.
  unfold solver_setnvars_entail_wit_1; right; intros.
  pose proof (proj1 PreH3) as Hsize.
  change (n_pre <= Z.max (ms_cap sn_M_setnvars_spec) 536870911) in PreH5.
  destruct (Z_le_gt_dec (ms_cap sn_M_setnvars_spec) 536870911) as [Hcap | Hcap].
  - rewrite Z.max_r in PreH5 by lia.
    entailer_with ltac:(unfold INT_MAX in *; lia); lia.
  - rewrite Z.max_l in PreH5 by lia.
    entailer_with ltac:(unfold INT_MAX in *; lia); lia.
Qed.

Lemma proof_of_solver_setnvars_entail_wit_3_1 : solver_setnvars_entail_wit_3_1.
Proof.
  aggressive_pre_process; snv_shape.
  assert (Hsh0 : solver_shape sn_M_setnvars_spec) by (unfold solver_shape; tauto).
  (* The RHS folds the eight arrays into [setnvars_arrays_at], so the engine
     does not pin their addresses -- supply the eight grow returns in the
     bundle's own order (trail BEFORE tags) and dissolve the bundle before
     [snv_set_cap_proj], whose rewrites have to reach the projections the
     bundle body carries. *)
  Exists retval retval_2 retval_3 retval_4 retval_5 retval_6 retval_8 retval_7
         (msolver_set_cap sn_M_setnvars_spec new_cap).
  unfold setnvars_arrays_at.
  snv_set_cap_proj.
  rewrite setnvars_frame_at_set_cap.
  pose proof (solver_shape_set_cap sn_M_setnvars_spec new_cap Hsh0
                ltac:(lia) ltac:(lia)).
  match goal with
  | H : solver_support_inv _ _ _ _ ?root ?M |- _ =>
      pose proof (solver_support_inv_set_cap__api_reentry
        _ _ _ _ root M new_cap H ltac:(lia))
  end.
  pose proof (minisat_watch_completed_set_cap__api_reentry
    sn_M_setnvars_spec new_cap) as Hcompletion.
  pose proof (setnvars_core_equiv_set_cap sn_M_setnvars_spec new_cap).
  pose proof (setnvars_bound_entry (ms_size sn_M_setnvars_spec) n_pre).
  msat_manual_entailer_with ltac:(snv_dispatch).
Qed.

Lemma proof_of_solver_setnvars_entail_wit_3_2 : solver_setnvars_entail_wit_3_2.
Proof.
  aggressive_pre_process; snv_shape;
  first [apply setnvars_core_equiv_refl | apply setnvars_bound_entry | tauto].
Qed.

Lemma proof_of_solver_setnvars_entail_wit_4 : solver_setnvars_entail_wit_4.
Proof.
  aggressive_pre_process; snv_shape.
  match goal with
  | HS : ms_size ?M = ?v, HO : order_update_post _ ?v _ _ _ _ |- _ =>
      rewrite <- HS in HO
  end.
  (* Same fold as wit_3_1 -- the eight array addresses are existential on
     the RHS, and the bundle has to be dissolved before [snv_sift_proj]
     so its rewrites reach the projections inside the bundle body. *)
  Exists wlc_2 actc_2 asgc_2 oposc_2 rsnc_2 lvlc_2 trlc_2 tgsc_2
         (msolver_heap_project
            (msolver_add_var Mcur_2 cap_prime_2 (Z_to_fp64 0))
            orderpos1 heap1 cap_prime_2).
  unfold setnvars_arrays_at.
  snv_sift_proj.
  rewrite setnvars_frame_at_add_var_sift.
  match goal with
  | HI : solver_support_inv (ms_size ?M) _ _ _ ?root ?M,
    HO : order_update_post _ _ _ _ ?o1 ?op |- _ =>
      let Hs := fresh "Hsift" in
      let Hshape := fresh "Hshape" in
      assert (Hshape : solver_shape M) by (unfold solver_shape; tauto);
      pose proof (solver_support_inv_add_var_sift__api_reentry
        _ _ _ _ root M cap_prime_2 (Z_to_fp64 0) o1 op
        HI ltac:(lia) ltac:(lia) HO) as Hs;
      pose proof (setnvars_shape_from_support_view__api_reentry M _ root
        Hshape (setnvars_core_equiv_add_var_sift M cap_prime_2
          (Z_to_fp64 0) op o1 cap_prime_2) (msi_shape Hs));
      match goal with HS : ms_size M = _ |- _ => rewrite HS in Hs end
  end.
  match goal with
  | H : setnvars_core_equiv ?A ?B |- _ =>
      pose proof (setnvars_core_equiv_trans A B _ H
        (setnvars_core_equiv_add_var_sift B cap_prime_2 (Z_to_fp64 0)
           orderpos1 heap1 cap_prime_2))
  end.
  assert (Hcompletion : minisat_watch_completed sn_M_setnvars_spec ->
    minisat_watch_completed (msolver_heap_project
      (msolver_add_var Mcur_2 cap_prime_2 (Z_to_fp64 0))
      orderpos1 heap1 cap_prime_2)).
  { intro Hentry. apply minisat_watch_completed_heap_project__api_reentry.
    match goal with
    | HI : solver_support_inv ?n _ _ _ _ Mcur_2,
      HC : minisat_watch_completed sn_M_setnvars_spec ->
           minisat_watch_completed Mcur_2 |- _ =>
        exact (minisat_watch_completed_add_var__api_reentry
          n Mcur_2 cap_prime_2 (Z_to_fp64 0)
          (msi_trail_wf HI) (msw_db_wf (msi_weak HI)) (HC Hentry))
    end. }
  pose proof (setnvars_bound_step (ms_size sn_M_setnvars_spec) var n_pre
                ltac:(lia)).
  pose proof (wlists_rep_add_var_cells wlc_2 var (ms_wm Mcur_2)
                (ms_wcaps Mcur_2) p p_2 ltac:(lia)) as Hcells.
  unfold vecp_slot, vecp_size_addr, vecp_cap_addr, vecp_ptr_addr in Hcells.
  sep_apply Hcells.
  match goal with HS : ms_size ?M = ?v |- _ => rewrite HS end.
  replace (2 * (var + 1)) with (2 * var + 2) by lia.
  msat_manual_entailer_with ltac:(snv_dispatch).
Qed.

(* ===== solver_setnvars partial_solve wits (13 proofs) ===== *)
Lemma proof_of_solver_setnvars_partial_solve_wit_4_pure : solver_setnvars_partial_solve_wit_4_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_5_pure : solver_setnvars_partial_solve_wit_5_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_6_pure : solver_setnvars_partial_solve_wit_6_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_7_pure : solver_setnvars_partial_solve_wit_7_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_8_pure : solver_setnvars_partial_solve_wit_8_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_9_pure : solver_setnvars_partial_solve_wit_9_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_10_pure : solver_setnvars_partial_solve_wit_10_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_11_pure : solver_setnvars_partial_solve_wit_11_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_12_pure : solver_setnvars_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process;
  prop_apply veci_rep_bounds__canceluntil_cap;
  Intros;
  snv_shape;
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_13_pure : solver_setnvars_partial_solve_wit_13_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_15_pure : solver_setnvars_partial_solve_wit_15_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_17_pure : solver_setnvars_partial_solve_wit_17_pure.
Proof.
  msat_setnvars_shape_close_p9.
Qed.

Lemma proof_of_solver_setnvars_partial_solve_wit_28_pure : solver_setnvars_partial_solve_wit_28_pure.
Proof.
  msat_setnvars_order_update_pre_p9; pose proof (Zlength_nonneg (ms_order Mcur +:: var));
  msat_manual_entailer_with ltac:(lia).
Qed.

(* Spelling setnvars' postcondition out means the return obligations no longer
   mention setnvars_post_at.  The former shared tactic opened by unfolding that
   name and therefore failed on these two goals; this is the same tactic with
   that one `unfold` argument removed.  It is used only by the two setnvars
   proofs below, so it lives in this part file, above their first use, rather
   than in solver_qcp_proof_common.v. *)
Ltac snv_unfold_all_unfolded_post :=
  unfold solver_rep_growable, solver_rep_at,
         solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
         solver_levels_slice_at, solver_scalars_rep,
         solver_vecs_rep, solver_fp_rep, solver_trail_array_rep,
         setnvars_frame_at, setnvars_open_at, setnvars_arrays_at.

(* ===== solver_setnvars return wits (2 proofs) ===== *)
Lemma proof_of_solver_setnvars_return_wit_1 : solver_setnvars_return_wit_1.
Proof.
  aggressive_pre_process.
  all: (snv_shape);
    (match goal with
  | HS : ms_size ?M = ?v,
    HI : solver_support_inv ?v ?F ?A ?B ?root ?M |- _ =>
      let H := fresh "HIsz" in
      pose proof HI as H; rewrite <- HS in H
  end).
  all: match goal with H : setnvars_core_equiv ?M0 ?M |- _ =>
    pose proof (setnvars_core_equiv_root_summary M0 M H) as Hroot_summary;
    assert (Hphysical_root : ms_root_level M = ms_root_level M0)
      by (unfold setnvars_core_equiv in H; tauto)
  end.
  all: (Exists Mcur);
    (pose proof (setnvars_bound_exit (ms_size sn_M_setnvars_spec) var n_pre
                ltac:(assumption) ltac:(lia)));
    (match goal with HS : ms_size ?M = ?v |- _ => rewrite <- HS end).
  all: (snv_unfold_all_unfolded_post);
    (Exists wlc actc asgc oposc rsnc lvlc trlc tgsc);
    (msat_manual_entailer_with ltac:(snv_dispatch)).
Qed.

Lemma proof_of_solver_setnvars_return_wit_2 : solver_setnvars_return_wit_2.
Proof.
  aggressive_pre_process.
  all: (snv_shape);
    (match goal with
  | HS : ms_size ?M = ?v,
    HI : solver_support_inv ?v ?F ?A ?B ?root ?M |- _ =>
      let H := fresh "HIsz" in
      pose proof HI as H; rewrite <- HS in H
  end).
  all: sep_apply (solver_nested_veci_full_from_cells
               s_pre "order" p (ms_order Mcur) (ms_order_cap Mcur)
               ltac:(assumption) ltac:(lia)).
  all: match goal with H : setnvars_core_equiv ?M0 ?M |- _ =>
    pose proof (setnvars_core_equiv_root_summary M0 M H) as Hroot_summary;
    assert (Hphysical_root : ms_root_level M = ms_root_level M0)
      by (unfold setnvars_core_equiv in H; tauto)
  end.
  all: (Exists Mcur);
    (match goal with HS : ms_size ?M = ?v |- _ => rewrite <- HS end).
  all: (snv_unfold_all_unfolded_post);
    (Exists wlc actc asgc oposc rsnc lvlc trlc tgsc);
    (msat_manual_entailer_with ltac:(snv_dispatch)).
Qed.

(* ===== solver_setnvars safety wits (3 proofs) ===== *)
Lemma proof_of_solver_setnvars_safety_wit_13 : solver_setnvars_safety_wit_13.
Proof.
  unfold solver_setnvars_safety_wit_13; left; intros.
  match goal with
  | Hshape : solver_shape ?M |- _ =>
      pose proof (proj1 (proj1 Hshape)) as Hsize_nonneg
  end.
  entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_safety_wit_15 : solver_setnvars_safety_wit_15.
Proof.
  unfold solver_setnvars_safety_wit_15; left; intros.
  match goal with
  | Hshape : solver_shape ?M |- _ =>
      pose proof (proj1 (proj1 Hshape)) as Hsize_nonneg
  end.
  entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_safety_wit_16 : solver_setnvars_safety_wit_16.
Proof.
  unfold solver_setnvars_safety_wit_16; left; intros.
  match goal with
  | Hshape : solver_shape ?M |- _ =>
      pose proof (proj1 (proj1 Hshape)) as Hsize_nonneg
  end.
  entailer_with ltac:(lia).
Qed.

(* ===== solver_setnvars which_implies wits (6 proofs) ===== *)
Lemma proof_of_solver_setnvars_which_implies_wit_1 : solver_setnvars_which_implies_wit_1.
Proof.
  (* The block's RHS is the [setnvars_arrays_at] restatement, which is
     exactly [setnvars_open_arrays]; opening with that lemma keeps the bundle
     folded on both sides, and the EX list is spelled wl..tgs. *)
  aggressive_pre_process;
  sep_apply setnvars_open_arrays;
  Intros wl0 act0 asg0 opos0 rsn0 lvl0 trl0 tgs0;
  Exists wl0 act0 asg0 opos0 rsn0 lvl0 trl0 tgs0;
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_which_implies_wit_2 : solver_setnvars_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); snv_shape;
  sep_apply (wlists_undef_peel wlc (2 * var) (2 * ms_cap Mcur) ltac:(lia));
  unfold UndefStructPredvecp_t, vecp_slot, vecp_size_addr, vecp_cap_addr,
         vecp_ptr_addr;
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_which_implies_wit_3 : solver_setnvars_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); snv_shape;
  sep_apply (wlists_undef_peel wlc (2 * var + 1) (2 * ms_cap Mcur) ltac:(lia));
  replace (2 * var + 1 + 1) with (2 * var + 2) by lia;
  unfold UndefStructPredvecp_t, vecp_slot, vecp_size_addr, vecp_cap_addr,
         vecp_ptr_addr;
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_which_implies_wit_4 : solver_setnvars_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto); snv_shape;
  rewrite (DoubleArray.undef_seg_unfold actc var (ms_cap Mcur) ltac:(lia));
  unfold StoreDoubleAsElement.undefstoreA;
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_which_implies_wit_5 : solver_setnvars_which_implies_wit_5.
Proof.
  aggressive_pre_process; snv_shape;
  sep_apply (dseg_snoc (ms_activity Mcur) actc 0 var (Z_to_fp64 0) ltac:(lia));
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_setnvars_which_implies_wit_6 : solver_setnvars_which_implies_wit_6.
Proof.
  msat_setnvars_order_update_pre_p9; msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_addclause partial_solve wits (continued: 2 proofs) ===== *)
Lemma proof_of_solver_addclause_partial_solve_wit_7_pure : solver_addclause_partial_solve_wit_7_pure.
Proof.
  unfold solver_addclause_partial_solve_wit_7_pure; right; intros.
  change (ac_n_addclause_spec <= Z.max (ms_cap ac_M_addclause_spec) 536870911) in PreH14.
  destruct (Z_le_gt_dec (ms_cap ac_M_addclause_spec) 536870911) as [Hcap | Hcap].
  - rewrite Z.max_r in PreH14 by lia.
    entailer_with ltac:(unfold INT_MAX in *; lia); lia.
  - rewrite Z.max_l in PreH14 by lia.
    entailer_with ltac:(unfold INT_MAX in *; lia); lia.
Qed.

Lemma proof_of_solver_addclause_partial_solve_wit_4_pure : solver_addclause_partial_solve_wit_4_pure.
Proof.
  unfold solver_addclause_partial_solve_wit_4_pure; right; intros.
  pose proof (Zlength_nonneg ac_input_addclause_spec) as H_input_nonneg.
  change (ac_n_addclause_spec <= Z.max (ms_cap ac_M_addclause_spec) 536870911) in PreH4.
  destruct (Z_le_gt_dec (ms_cap ac_M_addclause_spec) 536870911) as [Hcap | Hcap].
  - rewrite Z.max_r in PreH4 by lia.
    entailer_with ltac:(unfold INT_MAX in *; lia); lia.
  - rewrite Z.max_l in PreH4 by lia.
    entailer_with ltac:(unfold INT_MAX in *; lia); lia.
Qed.


(* Additional obligations for the constructor and incremental public API. *)

Lemma proof_of_solver_resume_pending_return_wit_1 : solver_resume_pending_return_wit_1.
Proof.
  unfold solver_resume_pending_return_wit_1. left.
  intros s wl lvl M asg Hpending.
  unfold msolver_resume_pending. rewrite Hpending, Z.eqb_refl.
  unfold solver_resume_frame_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  assert (Hshape : solver_shape M) by assumption.
  assert (Hshape_resume : solver_shape (msolver_resume M)).
  { unfold solver_shape, msolver_resume, msolver_propagation_update,
      mt_set_qhead in Hshape |- *.
    cbn in Hshape |- *. intuition lia. }
  unfold solver_rep_levels_wl_at, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_resume_scalars_frame,
    solver_scalars_rep, solver_vecs_without_lim_rep, solver_vecs_rep.
  Exists act asg opos rsn trl tgs.
  replace (solver_fp_rep s (msolver_resume M))
    with (solver_fp_rep s M) by reflexivity.
  replace (solver_trail_array_rep (msolver_resume M) trl)
    with (solver_trail_array_rep M trl) by reflexivity.
  replace (solver_levels_slice_at s (msolver_resume M) lvl)
    with (solver_levels_slice_at s M lvl) by reflexivity.
  simpl [msolver_resume msolver_propagation_update mt_set_qhead].
  msat_entailer_with ltac:(tauto || lia).
Qed.

Lemma proof_of_solver_resume_pending_return_wit_2 : solver_resume_pending_return_wit_2.
Proof.
  unfold solver_resume_pending_return_wit_2. left.
  intros s wl lvl M asg Hpending.
  assert (Heqb : Z.eqb (ms_capacity_root_propagation_pending M) 1 = false).
  { apply Z.eqb_neq. exact Hpending. }
  unfold msolver_resume_pending. rewrite Heqb.
  unfold solver_resume_frame_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  unfold solver_rep_levels_wl_at, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_resume_scalars_frame,
    solver_scalars_rep, solver_vecs_without_lim_rep, solver_vecs_rep.
  Exists act asg opos rsn trl tgs.
  msat_entailer_with ltac:(tauto || lia).
Qed.

Lemma proof_of_solver_resume_pending_which_implies_wit_1 : solver_resume_pending_which_implies_wit_1.
Proof.
  unfold solver_resume_pending_which_implies_wit_1. left.
  intros wl lvl M s. unfold solver_rep_levels_wl_at.
  Intros act asg opos rsn trl tgs. Exists asg.
  unfold solver_resume_frame_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at.
  Exists act opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_resume_scalars_frame, solver_scalars_rep,
    solver_vecs_without_lim_rep, solver_vecs_rep.
  msat_entailer_with ltac:(tauto || lia).
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_1 : solver_addclause_which_implies_wit_1.
Proof.
  unfold solver_addclause_which_implies_wit_1. left.
  intros M s. apply solver_rep_growable_to_wl.
Qed.

Lemma proof_of_solver_addclause_which_implies_wit_2 : solver_addclause_which_implies_wit_2.
Proof.
  unfold solver_addclause_which_implies_wit_2. left.
  intros physical M wl lvl s Hmodel. subst M.
  destruct (msolver_resume_pending_size_cap__api_reentry physical)
    as [Hsize [Hcap Hrest]].
  rewrite <- Hsize, <- Hcap.
  apply solver_rep_growable_of_wl.
Qed.

Lemma proof_of_solver_addclause_derive_solver_addclause_incremental_spec_by_addclause_spec :
  solver_addclause_derive_solver_addclause_incremental_spec_by_addclause_spec.
Proof.
  unfold solver_addclause_derive_solver_addclause_incremental_spec_by_addclause_spec.
  intros endvar begin s input physical F input_bound n.
  unfold solver_incremental_ownership_at. Intros.
  assert (Hupdate : solver_update_ready n F nil physical) by tauto.
  assert (Hwatch : solver_query_watch_ready physical) by tauto.
  assert (Hseed : msolver_seed_shadow physical) by tauto.
  assert (Hbound : 2 * ms_cap physical <= INT_MAX) by tauto.
  set (entry := msolver_resume_pending physical).
  assert (Hbase : solver_base_state n F entry) by exact Hupdate.
  pose proof (solver_update_completed_resume__incremental_public
    n F nil physical Hupdate Hwatch) as Hcomplete.
  pose proof (msolver_resume_pending_seed__api_reentry physical Hseed) as Hseed_entry.
  destruct (msolver_resume_pending_size_cap__api_reentry physical)
    as [Hsize [Hcap Hrest]].
  assert (Hentry_size : ms_size entry = n).
  { symmetry. exact (msa_size (msas_weak (proj1 Hbase))). }
  assert (Hshape : solver_shape entry).
  { exact (msa_shape (msas_weak (proj1 Hbase))). }
  assert (Hsupport : solver_support_inv (ms_size entry) F nil nil 0 entry).
  { rewrite Hentry_size. apply solver_assuming_zero_support__update_surface.
    - exact (proj1 Hbase).
    - exact (proj1 (proj2 Hbase)). }
  Exists F (@nil literal) (@nil literal) entry physical input_bound input.
  split_pure_spatial.
  - cancel (solver_rep_growable s physical).
    cancel (IntArray.seg begin 0 (Zlength input) input).
    apply derivable1_wand_sepcon_adjoint. Intros ret.
    sep_apply (solver_addclause_result_same_ret__incremental_public
      s begin n input_bound F entry input ret Hbase Hcomplete Hseed_entry).
    Intros Mout current. unfold solver_incremental_ownership_at. Intros.
    match goal with
    | Hfacts : Zlength current = Zlength input /\ n <= ms_size Mout /\
        solver_query_watch_ready Mout /\ _ |- _ =>
        destruct Hfacts as [Hlen [Hsize_out [Hwatch_out
          [Hpending_out Hcases]]]]
    end.
    destruct Hcases as [[Hret [Fnew [Hupdate_out Hequiv]]] |
      [[Hret [Hunsat Hupdate_out]] | [Hret Hupdate_out]]].
    + rewrite <- derivable1_orp_intros1.
      rewrite <- derivable1_orp_intros1.
      Exists Fnew Mout current ret. msat_entailer_with ltac:(tauto).
    + rewrite <- derivable1_orp_intros1.
      rewrite <- derivable1_orp_intros2.
      Exists Mout current ret. msat_entailer_with ltac:(tauto).
    + rewrite <- derivable1_orp_intros2.
      Exists Mout current ret. msat_entailer_with ltac:(tauto).
  - assert (Hpending : ms_capacity_root_propagation_pending entry = 0)
      by exact (proj2 (proj2 Hbase)).
    assert (Hdepth : Zlength (mt_lim (ms_core entry)) = 0)
      by exact (proj1 (proj2 Hbase)).
    change (ms_cap entry = ms_cap physical) in Hcap.
    rewrite Hcap. unfold entry. msat_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_simplify_derive_solver_simplify_incremental_spec_by_solver_simplify_spec :
  solver_simplify_derive_solver_simplify_incremental_spec_by_solver_simplify_spec.
Proof.
  unfold solver_simplify_derive_solver_simplify_incremental_spec_by_solver_simplify_spec.
  intros s physical F n. unfold solver_incremental_ownership_at. Intros.
  assert (Hupdate : solver_update_ready n F nil physical) by tauto.
  assert (Hwatch : solver_query_watch_ready physical) by tauto.
  assert (Hseed : msolver_seed_shadow physical) by tauto.
  assert (Hbound : 2 * ms_cap physical <= INT_MAX) by tauto.
  set (entry := msolver_resume_pending physical).
  assert (Hbase : solver_base_state n F entry) by exact Hupdate.
  pose proof (solver_update_completed_resume__incremental_public
    n F nil physical Hupdate Hwatch) as Hcomplete.
  pose proof (msolver_resume_pending_seed__api_reentry physical Hseed) as Hseed_entry.
  destruct (msolver_resume_pending_size_cap__api_reentry physical)
    as [Hsize [Hcap Hrest]].
  assert (Hentry_size : ms_size entry = n).
  { symmetry. exact (msa_size (msas_weak (proj1 Hbase))). }
  assert (Hphysical_size : ms_size physical = n).
  { unfold entry in Hentry_size. rewrite Hsize in Hentry_size. exact Hentry_size. }
  assert (Hentry_bound : 2 * ms_cap entry <= INT_MAX).
  { unfold entry. rewrite Hcap. exact Hbound. }
  sep_apply solver_rep_growable_to_wl. Intros wl lvl.
  Exists n F (@nil literal) entry physical lvl wl.
  unfold solver_simplify_resumed_pre_at.
  split_pure_spatial.
  - cancel. apply_sepcon_adjoint. Intros ret.
    rewrite Hphysical_size. rewrite <- Hcap.
    fold entry.
    pose proof (solver_simplify_result_same_ret__incremental_public
      s n F entry lvl wl ret Hcomplete Hentry_bound) as Hresult.
    lazymatch type of Hresult with
    | ?Raw |-- _ =>
      assert (Hraw :
        solver_simplify_post_at s n F nil entry lvl ret wl **
        wlists_undef wl (2 * n) (2 * ms_cap entry) |-- Raw) by
        (cancel (wlists_undef wl (2 * n) (2 * ms_cap entry));
         msat_entailer_with ltac:(tauto))
    end.
    rewrite Hraw. rewrite Hresult.
    Intros Mout. unfold solver_incremental_ownership_at. Intros.
    match goal with
    | Hfacts : solver_update_ready n F nil Mout /\ _ |- _ =>
        destruct Hfacts as [Hupdate_out Hcases]
    end.
    destruct Hcases as
      [[Hret [Hpublic [Hguard [Hpending_out Hwatch_out]]]] |
      [[Hret [Hunsat [Hpublic [Hpending_out Hguard]]]] |
       [Hret [Hexhausted Hwatch_out]]]].
    + rewrite <- derivable1_orp_intros1.
      rewrite <- derivable1_orp_intros1.
      Exists Mout ret. msat_entailer_with ltac:(tauto).
    + rewrite <- derivable1_orp_intros1.
      rewrite <- derivable1_orp_intros2.
      Exists Mout ret. msat_entailer_with ltac:(tauto).
    + rewrite <- derivable1_orp_intros2.
      Exists Mout ret. msat_entailer_with ltac:(tauto).
  - unfold solver_base_state in Hbase. unfold entry.
    msat_entailer_with ltac:(tauto).
Qed.

(* ------------------------------------------------------------------ *)
(* Derivations of the client-facing incremental specs:                 *)
(* solver_setnvars (the paper's newVar step) and the three accessors.  *)
(* Each one is the `<=` obligation of a spec declared on solver_qcp.h; *)
(* the route lemmas they use are in solver_qcp_lib.v's "Public route   *)
(* lemmas" section.                                                    *)
(* ------------------------------------------------------------------ *)

(* One arm of the solver_setnvars derivation: from the general spec's exit
   model [Mnew] (either the `1` or the `-2` arm of [setnvars_post_at]) rebuild
   the incremental vocabulary -- update-readiness, watch-readiness, the cleared
   flag, ownership -- and select the matching arm of the incremental Ensure
   with [intro] ([derivable1_orp_intros1] or [_intros2]).  [M] and [F] are the
   entry model and clause set; every name the tactic introduces is fresh.  The
   two arms of the proof below were byte-identical up to that selector. *)
Ltac msat_setnvars_derive_arm M F Hsize Hdepth Hpending Hseed Hcompleted intro :=
  let Mnew := fresh "Mnew" in let ret := fresh "ret" in
  let Hgrow := fresh "Hgrow" in let Hsupport_new := fresh "Hsupport_new" in
  let Hcond := fresh "Hcond" in let Hwc := fresh "Hwc" in
  let Hdepth_new := fresh "Hdepth_new" in
  let Hpending_new := fresh "Hpending_new" in
  let Hseed_new := fresh "Hseed_new" in let Hshape_new := fresh "Hshape_new" in
  let Hstrong_new := fresh "Hstrong_new" in let Hbase_new := fresh "Hbase_new" in
  let Hupdate_new := fresh "Hupdate_new" in
  let Hwatch_new := fresh "Hwatch_new" in
  Intros Mnew ret;
  assert (Hgrow : ms_size M <= ms_size Mnew) by tauto;
  assert (Hsupport_new : solver_support_inv (ms_size Mnew) F nil nil 0 Mnew)
    by tauto;
  assert (Hcond :
    (Zlength (mt_lim (ms_core M)) = 0 /\
     ms_capacity_root_propagation_pending M = 0 /\ msolver_seed_shadow M) ->
    (Zlength (mt_lim (ms_core Mnew)) = 0 /\
     ms_capacity_root_propagation_pending Mnew = 0 /\
     msolver_seed_shadow Mnew)) by tauto;
  assert (Hwc : minisat_watch_completed M -> minisat_watch_completed Mnew)
    by tauto;
  destruct (Hcond (conj Hdepth (conj Hpending Hseed)))
    as [Hdepth_new [Hpending_new Hseed_new]];
  specialize (Hwc Hcompleted);
  sep_apply solver_rep_growable_shape__public; Intros;
  assert (Hshape_new : solver_shape Mnew) by tauto;
  destruct (solver_support_zero_assuming__update_surface
    (ms_size Mnew) F nil nil Mnew Hsupport_new Hshape_new Hdepth_new)
    as [Hstrong_new _];
  assert (Hbase_new : solver_base_state (ms_size Mnew) F Mnew)
    by (split; [exact Hstrong_new | split; assumption]);
  pose proof (solver_base_update_ready__incremental_public
    (ms_size Mnew) F Mnew Hbase_new) as Hupdate_new;
  pose proof (solver_completed_query_watch__incremental_public
    Mnew Hpending_new Hwc) as Hwatch_new;
  rewrite <- Hsize;
  rewrite <- intro;
  Exists Mnew ret; unfold solver_incremental_ownership_at;
  msat_entailer_with ltac:(tauto || lia).

Lemma proof_of_solver_setnvars_derive_solver_setnvars_incremental_spec_by_setnvars_spec :
  solver_setnvars_derive_solver_setnvars_incremental_spec_by_setnvars_spec.
Proof.
  unfold solver_setnvars_derive_solver_setnvars_incremental_spec_by_setnvars_spec.
  intros n_pre s M F nv. unfold solver_incremental_ownership_at. Intros.
  assert (Hupdate : solver_update_ready nv F nil M) by tauto.
  assert (Hwatch : solver_query_watch_ready M) by tauto.
  assert (Hpending : ms_capacity_root_propagation_pending M = 0) by tauto.
  assert (Hseed : msolver_seed_shadow M) by tauto.
  assert (Hbound : 2 * ms_cap M <= INT_MAX) by tauto.
  unfold solver_update_ready, msolver_resume_pending in Hupdate.
  rewrite Hpending in Hupdate. simpl in Hupdate.
  destruct Hupdate as [Hstrong [Hdepth _]].
  assert (Hsize : ms_size M = nv)
    by (symmetry; exact (msa_size (msas_weak Hstrong))).
  assert (Hcompleted : minisat_watch_completed M)
    by (destruct Hwatch as [Hordinary _]; exact (Hordinary Hpending)).
  assert (Hsupport : solver_support_inv (ms_size M) F nil nil 0 M).
  { rewrite Hsize. apply solver_assuming_zero_support__update_surface;
      [exact Hstrong | exact Hdepth]. }
  Exists F (@nil literal) (@nil literal) M 0.
  split_pure_spatial.
  - cancel (solver_rep_growable s M).
    apply derivable1_wand_sepcon_adjoint.
    rewrite orp_sepcon_right. apply derivable1_orp_elim.
    (* growth succeeded: the `1` arm *)
    + msat_setnvars_derive_arm M F Hsize Hdepth Hpending Hseed Hcompleted
        derivable1_orp_intros1.
    (* capacity exhausted: the `-2` arm *)
    + msat_setnvars_derive_arm M F Hsize Hdepth Hpending Hseed Hcompleted
        derivable1_orp_intros2.
  - msat_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_nvars_derive_solver_nvars_incremental_spec_by_solver_nvars_spec :
  solver_nvars_derive_solver_nvars_incremental_spec_by_solver_nvars_spec.
Proof.
  unfold solver_nvars_derive_solver_nvars_incremental_spec_by_solver_nvars_spec.
  intros s_pre M. Exists (ms_size M).
  apply solver_incremental_size_cell_frame__public.
  - Intros retval_2. msat_entailer_with ltac:(tauto).
  - Exists (ms_size M). msat_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_nclauses_derive_solver_nclauses_incremental_spec_by_solver_nclauses_spec :
  solver_nclauses_derive_solver_nclauses_incremental_spec_by_solver_nclauses_spec.
Proof.
  unfold solver_nclauses_derive_solver_nclauses_incremental_spec_by_solver_nclauses_spec.
  intros s_pre M. Exists (Zlength (db_words (ms_prob M))).
  apply solver_incremental_clause_count_frame__public.
  - Intros retval_2. msat_entailer_with ltac:(tauto).
  - Exists (Zlength (db_words (ms_prob M))). msat_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_nconflicts_derive_solver_nconflicts_incremental_spec_by_solver_nconflicts_spec :
  solver_nconflicts_derive_solver_nconflicts_incremental_spec_by_solver_nconflicts_spec.
Proof.
  unfold solver_nconflicts_derive_solver_nconflicts_incremental_spec_by_solver_nconflicts_spec.
  intros s_pre M. Exists (stats_conflicts (ms_stats M)).
  apply solver_incremental_conflicts_cell_frame__public.
  - Intros retval_2. msat_entailer_with ltac:(tauto).
  - Exists (MiniSatTarget.signed_low32 (stats_conflicts (ms_stats M))).
    msat_entailer_with ltac:(tauto).
Qed.
