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
Local Open Scope sac.

(* Pure conclusions may already follow from the Coq context.
   Commit the context-only shortcut only when it closes every goal. *)
Ltac msat_manual_entailer_with tac :=
  first
    [ solve
        [ repeat lazymatch goal with
          | |- _ |-- _ && _ => apply _derivable1_andp_intros
          end;
          lazymatch goal with
          | |- _ |-- “ _ ” =>
              apply dump_spatial_left; simpl_entail_with tac
          | |- _ |-- _ =>
              msat_cancel_sound;
              reflexivity
          end ]
    |
      tryif
      (lazymatch goal with
      | |- _ |-- ?rhs => _assert_pure rhs
      | _ => fail
      end)
      then first
      [ solve [ apply dump_spatial_left; simpl_entail_with tac ]
      | entailer_with tac ]
      else msat_entailer_with tac ].

(* ===================================================================== *)
(* solver_qcp_proof_common.v                                             *)
(*                                                                       *)
(* Shared proof tactics for solver_qcp_proof_manual_part1..9.  Ltac is   *)
(* file-local, so with the manual proof split nine ways a tactic used    *)
(* from two parts would otherwise need a copy in each.  No lib.v proof   *)
(* consumes any of them, so they do not belong in solver_qcp_lib.v: a    *)
(* declaration there charges the library rebuild for text that only the  *)
(* parts read.  The same holds for the ac_* / snv_* block.               *)
(* This file sits between the library and                                *)
(* the parts: it Requires solver_qcp_lib / _goal / _proof_auto and is    *)
(* Required by every part.                                               *)
(*                                                                       *)
(* Section numbers never move: solver_qcp_proof_manual_part5.v and       *)
(* _part7.v cite "solver_qcp_proof_common.v, section 9" by number, so a  *)
(* section that empties is dropped and the rest keep their numbers.      *)
(*                                                                       *)
(* Contents                                                              *)
(*   2. CDR-01 bottom-merge closers (msat_cdr01_guard_fact,              *)
(*      msat_real_satisfied_dispatch).                                   *)
(*   3. The msat_* closers for analyze / lit_removable / order_select /  *)
(*      propagate / search / solve (38 tactics).                         *)
(*   4. The solver_addclause [ac_] and solver_setnvars [snv_] tactic     *)
(*      blocks (17 tactics), formerly at the head of part9.v.            *)
(*   5. The one watcher-scan lemma that cannot live in solver_qcp_lib.v. *)
(*   6. Closers for the clone groups that spanned two or more parts.     *)
(*   9. The solver_analyze clause-scan tag-step tactic notations that    *)
(*      solver_qcp_proof_manual_part5.v and _part7.v share.              *)
(* ===================================================================== *)

(* ===================================================================== *)
(* 2. CDR-01 bottom-merge closers                                        *)
(* ===================================================================== *)
(* ---- CDR-01 bottom-merge closers, shared by parts 2, 3 and 6.
   The annotated scan carries no `if (i < endvar)` guard, so an in-loop
   bottom-merge VC does not get that guard result handed to it as a
   hypothesis, while
   [propagation_scan_real_satisfied_step__shared_propagate] in
   solver_qcp_lib.v still takes it.  No information is lost -- the loop condition and the two
   index equations are present -- so [msat_cdr01_guard_fact] derives it by
   rewriting.  NOT by lia: `sizeof(PTR)` is the architecture constant
   [sizeof_front_end_type FET_ptr] (SeparationLogic/CNotation.v), which
   micromega does not delta-reduce, so the comparison never becomes linear
   arithmetic. *)
Ltac msat_cdr01_guard_fact :=
  match goal with
  | Hi : ?I = ?L, He : ?E = ?R, Hlt : ?I < ?E |- ?L < ?R =>
      rewrite <- Hi, <- He; exact Hlt
  | Hi : ?I = ?L, He : ?E = ?R, Hge : ?I >= ?E |- ?L >= ?R =>
      rewrite <- Hi, <- He; exact Hge
  end.

(* Dispatches the [solver_propagate_entail_wit_*_real_satisfied] family
   through its shared scan-step lemma.  The matching avoids binder names, so it survives binder
   renumbering on regeneration: [eapply] pins every existential the conclusion
   determines; the three uniquely-shaped predicate premises pin the rest; then
   equalities close before comparisons, because a comparison premise such as
   [?i < ?endvar] would otherwise unify with the first [_ < _] hypothesis in
   scope and mis-pin both sides; the tail is the guard obligation plus the
   solved-existential stubs. *)
Ltac msat_real_satisfied_dispatch :=
  intros;
  eapply propagation_scan_real_satisfied_step__shared_propagate;
  try match goal with
      | |- db_pair_lits_update _ _ _ _ _ _ _ => eassumption
      | |- propagation_real_satisfied_transition _ _ _ _ _ _ _ _ _ _ _ => eassumption
      | |- propagation_scan_keep_step _ _ _ _ _ _ _ _ _ _ _ _ => eassumption
      end;
  try lazymatch goal with
      | |- Z => idtac
      | |- _ < _ => idtac
      | |- _ <= _ => idtac
      | |- _ >= _ => idtac
      | |- _ <> _ => idtac
      | |- _ => eassumption
      end;
  try eassumption;
  first [ reflexivity | msat_cdr01_guard_fact | eassumption | exact 0 ].

(* ===================================================================== *)
(* 3. analyze / lit_removable / order_select / propagate / search / solve *)
(* ===================================================================== *)
(* Nothing bounds the analyze counter directly.  The scan invariant equates it with
   the pending list, and the tagged vector is a permutation of pending ++ resolved
   ++ learnt vars, so the lengths of the other two blocks (both nonnegative) are
   what turn the invariant's bound on the tagged vector into `cnt < n <= INT_MAX`.
   The two facts are pulled out by `tauto` rather than by position, so they survive
   the invariant growing a conjunct. *)
Ltac msat_analyze_bound_scan_count_by_tagged PreH24 cnt Sscan Rscan Mscan learnt_scan :=
  assert (Hcnt : cnt = Zlength Sscan) by
    (unfold analyze_clause_scan_inv in PreH24; tauto);
  assert (Hperm : Permutation (ms_tagged Mscan) (analyze_tags Sscan Rscan learnt_scan)) by
    (unfold analyze_clause_scan_inv in PreH24; tauto);
  pose proof (Zlength_perm_eq Z _ _ Hperm) as Hlen;
  unfold analyze_tags in Hlen;
  rewrite !Zlength_app in Hlen;
  pose proof (Zlength_nonneg Sscan);
  pose proof (Zlength_nonneg Rscan);
  pose proof (Zlength_nonneg (map literal_var learnt_scan));
  assert (Hbounds : cnt + 1 <= INT_MAX /\ INT_MIN <= cnt + 1) by (split; lia);
  entailer_with ltac:(lia).

(* The `entailer_with lia` that runs first leaves the overflow goal open: the scan
   invariant bounds the index only by the clause length, and nothing bounds a
   clause's length directly -- it takes the pigeonhole, the clause's literal
   variables being distinct and all below `n`.  The `destruct` only reads `0 <= n`
   off the head literal; the empty list has no literal to read and is closed
   instead from `j < Zlength [] = 0`. *)
Ltac msat_analyze_bound_scan_index_by_nodup Heq Hscan n Ccur j Hinv clause_words2 :=
  match goal with
  | Hscan : analyze_clause_scan_inv n _ _ _ _ _ _ _ Ccur j _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof Hscan as Hinv
  end;
  unfold analyze_clause_scan_inv in Hinv;
  destruct Hinv as [_ [_ [_ [_ [Hwf [Hnodup _]]]]]];
  match goal with
  | Heq : Ccur = lits_denote clause_words2 |- _ =>
      rewrite Heq in Hwf, Hnodup
  end;
  assert (Hn : 0 <= n);
  [ assert (Hj : j < Zlength clause_words2) by lia;
    destruct clause_words2 as [|w words];
    [ change (j < 0) in Hj;
      lia
    | rewrite lits_denote_cons in Hwf;
      inversion Hwf as [| ? ? Hw Htail];
      unfold literal_wf, var_in_range in Hw;
      simpl in Hw;
      lia ]
  | idtac .. ];
  assert (Hvals : Forall (fun v => 0 <= v < n)
                    (map literal_var (lits_denote clause_words2)));
  [ rewrite Forall_map;
    exact Hwf
  | idtac .. ];
  assert (Hlen : Zlength (lits_denote clause_words2) <= n);
  [ rewrite Zlength_correct;
    replace (Z.of_nat (List.length (lits_denote clause_words2))) with
      (Z.of_nat (List.length (map literal_var (lits_denote clause_words2))))
      by (rewrite length_map; reflexivity);
    apply NoDup_Z_bounded_length; [exact Hn | exact Hnodup |];
    intros v Hv;
    exact ((proj1 (@Forall_forall Z (fun v : Z => 0 <= v < n)
      (map literal_var (lits_denote clause_words2)))) Hvals v Hv)
  | idtac .. ];
  rewrite lits_denote_length in Hlen;
  lia.

(* Discharges `0 <= clause_hdr_word learnt (Zlength words)`, so the whole
   precondition heap is dropped: the bound needs nothing from the solver
   invariant, only `Zlength >= 0`.  Not `lia` -- `clause_hdr_word` hides a `bool`
   case split behind a definition micromega will not delta-reduce. *)
Ltac msat_analyze_close_clause_hdr_word_nonneg :=
  (LLM_pre_process ltac:(lia));
  split_pures;
  dump_pre_spatial;
  apply clause_hdr_word_nonneg;
  apply Zlength_nonneg.

(* The int-range obligations on a literal read out of the clause have no arithmetic
   proof: the only bound in scope is the clause-wide `Forall (lit_wf_c n)`, so it
   has to be eliminated at the read index by hand before `lia` sees anything usable
   (`2 * n <= INT_MAX` then supplies the upper end).  The `try subst` covers the
   callers that reach the goal with the index already substituted to a literal,
   leaving elimination and goal on different atoms. *)
Ltac msat_analyze_close_clause_word_int_range Hwf j clause_words2 Hlit :=
  assert (Hr : 0 <= j - 0 < Zlength clause_words2) by lia;
  match goal with
  | Hwf : List.Forall ?P clause_words2 |- _ =>
      pose proof (sat_shared_lib.Forall_Znth_elim Z P
        clause_words2 0 (j - 0) Hwf Hr) as Hlit
  end;
  unfold solver_qcp_model.lit_wf_c in Hlit;


  try subst j;
  lia.

(* Discharges the `0 <= Znth ...` half of the bound left by a read of a
   learnt-clause word, by instantiating the clause-wide `lit_wf_c` Forall at the
   scan index and keeping only its lower conjunct.  The `replace` is needed because
   the obligation spells the index as an offset from the segment base, and `j - 0`
   is stuck on a variable j, so `exact` would not convert. *)
Ltac msat_analyze_close_clause_word_lower_bound Hall Hj0 Hj1 clause_words2 n j Hlit :=
  match goal with
  | Hall : List.Forall (lit_wf_c n) clause_words2,
    Hj0 : 0 <= j, Hj1 : j < Zlength clause_words2 |- _ =>
      pose proof (Forall_Znth_elim _ _ _ 0 j Hall (conj Hj0 Hj1)) as Hlit
  end;
  unfold lit_wf_c in Hlit;
  replace (j - 0) with j by lia;
  exact (proj1 Hlit).

(* One `Forall` instance at the scan index covers every spelling: the right-hand
   side also names the scanned literal at the iteration's concrete index
   (`Znth (1 - 0)`, `Znth (0 - 0)`), and the `replace`'s side condition is then just
   the index equation `lia` already has in context.  `lit_wf_c` gives
   `0 <= w < 2 * n`, which the `2 * n <= INT_MAX` hypothesis turns into the INT_MAX
   bound. *)
Ltac msat_analyze_close_clause_word_range_any_index n clause_words2 j :=
  assert (Hwf : lit_wf_c n (Znth j clause_words2 0));
  [ eapply Forall_Znth_elim; eauto; lia
  | idtac .. ];
  unfold lit_wf_c in Hwf;
  destruct Hwf as [Hwf_lo Hwf_hi];
  split_pures; dump_pre_spatial;


    match goal with
    | |- context [Znth ?i clause_words2 0] => replace i with j by lia
    end;
    lia.

(* The right-hand side's bounds on the scanned clause word come from
   `Forall (lit_wf_c n)` instantiated at the scan index; `lit_wf_c` has to be
   unfolded to `0 <= l < 2 * n` before the ambient `2 * n <= INT_MAX` lets the
   entailer's `lia` reach INT_MAX.  The three context names are parameters because
   a tactic body interns its free constr identifiers at definition time. *)
Ltac msat_analyze_close_clause_word_range_via_entailer n j cw :=
  assert (Hlit : lit_wf_c n (Znth (j - 0) cw 0));
  [ apply (Forall_Znth_elim _ _ _ 0 (j - 0)); [assumption | lia]
  | unfold lit_wf_c in Hlit; entailer_with ltac:(lia) ].

(* The pair of int-range side goals on a literal read out of the learnt vector.
   The two match branches carry the same script; they exist only so the body fires
   on whichever of `0 <= _` / `_ <= INT_MAX` the entailer left standing.  Neither
   bound is arithmetic -- it lives in `Forall (lit_wf_c n)`, and the instance that
   yields is indexed one `- 0` deeper than the goal, which lia reads as an
   unrelated atom until the `replace` normalises it. *)
Ltac msat_analyze_close_learnt_vec_lit_range Hf :=
  unfold veci_rep_at in *; split_pures;
  entailer_with ltac:(lia);
  try lia;
  match goal with
       |- Znth ?idx ?lst 0 <= INT_MAX =>
         match goal with Hf : Forall (lit_wf_c ?n0) ?lst |- _ =>
           assert (Hi : 0 <= idx < Zlength lst) by lia;
           pose proof (Forall_Znth_elim _ _ _ 0 idx Hf Hi) as Hlit;
           replace (idx - 0) with idx in Hlit by lia;
           unfold lit_wf_c in Hlit; lia
         end
       | |- 0 <= Znth ?idx ?lst 0 =>
         match goal with Hf : Forall (lit_wf_c ?n0) ?lst |- _ =>
           assert (Hi : 0 <= idx < Zlength lst) by lia;
           pose proof (Forall_Znth_elim _ _ _ 0 idx Hf Hi) as Hlit;
           replace (idx - 0) with idx in Hlit by lia;
           unfold lit_wf_c in Hlit; lia
         end
       end.

(* Expose the existing vector length/capacity bounds, then discharge the
   four scan bounds from the resulting pure facts. *)
Ltac msat_analyze_close_veci_bounds learnt_pre words_scan cap_scan :=
  prop_apply (veci_rep_bounds__analyze learnt_pre words_scan cap_scan);
  Intros;
  split_pures; dump_pre_spatial; lia.

(* On the arm where the vector already appears as `veci_rep_at` with its data
   pointer exposed, the capacity facts still exist only inside that predicate's own
   conjunct, so it has to be unfolded and the conjunct introduced before any of the
   goals can close.  `lia` rather than `assumption`: one member asks `i <= cap`, one
   loop bound away from the conjunct. *)
Ltac msat_analyze_close_veci_caps_at_data_ptr :=
  right;
  (LLM_pre_process ltac:(lia));
  unfold veci_rep_at;
  Intros_p Hbounds;
  split_pures; dump_pre_spatial; lia.

(* On the arms whose scan index is pinned by a hypothesis (the index equals 1, or
   the very first word), the right-hand side restates the same bound at that
   constant index as well.  This stages the second `Forall` instance so the closer
   discharges all four conjuncts; the index side condition is linear in the
   existing `0 <= j < Zlength` facts. *)
Ltac msat_analyze_stage_clause_word_range_at_fixed_index n k cw :=
  assert (Hlitk : lit_wf_c n (Znth (k - 0) cw 0)) by
    (apply (Forall_Znth_elim _ _ _ 0 (k - 0)); [assumption | lia]);
  unfold lit_wf_c in Hlitk.

(* The tagged vector's capacity facts appear in none of the pure hypotheses -- they
   live inside `veci_rep`'s own conjunct -- so the predicate must be unfolded down
   through `veci_rep_at` and its existential data pointer introduced before
   `entailer_with` can read them off.  The arm taken asks for four conjuncts; the
   unfold yields `cap <= INT_MAX` as well, so the stronger arm costs nothing. *)
Ltac msat_lit_removable_close_tagged_caps_by_entailer :=
  left;
  intros;
  unfold veci_rep, veci_rep_at;
  Intros tagged_data_ptr;
  entailer_with ltac:(lia).

(* The `at 1` is load-bearing: the tagged vector is the first `veci_rep` in these
   goals and the stack the second, so a sibling obligation asking for the stack
   bounds must unfold `at 2` instead.  The four conjuncts are exactly the bounds
   `veci_rep_at` carries, so they must be introduced into the context before `lia`
   can see them. *)
Ltac msat_lit_removable_close_tagged_caps_by_lia :=
  left; intros;
  unfold veci_rep at 1; Intros p;
  unfold veci_rep_at at 1; Intros_p Htagged_bounds;
  split_pures;
  dump_pre_spatial; lia.

(* Discharges the signed-overflow bounds on the sift-down child index
   `2 * child + 1`.  The goal's own `size <= INT_MAX` is not enough for the
   doubling: the argument needs `size <= n` together with the invariant's
   `2 * n <= INT_MAX`.  `size <= n` is a pigeonhole fact -- the heap holds
   pairwise-distinct variables drawn from `[0, n)` -- so `NoDup_Z_bounded_length` is
   applied to the invariant's NoDup and range components and its nat-valued length
   converted back with `Zlength_correct`. *)
Ltac msat_order_select_bound_sift_child_index Hsift_src n size sift_heap_before :=
  pose proof Hsift_src as Hsift;
  destruct Hsift as
    (Htwon & Hpopped & Hincl & Hassign_len & Hassign_vals &
     Hassigned & Hcovers & Hhole);
  destruct Hhole as
    (Hpos_len & Hheap_len & Hhole_range & Hx_range & Hnodup &
     Hrange & Hperm & Hinverse & Hout);
  assert (Horigin_le_nat :
      Z.of_nat (List.length (list_without_Znth 0 sift_heap_before)) <= n) by
    (apply NoDup_Z_bounded_length;
     [ lia
     | exact Hnodup
     | intros y Hy; rewrite Forall_forall in Hrange; exact (Hrange y Hy) ]);
  rewrite <- Zlength_correct in Horigin_le_nat;
  assert (Hsize_le : size <= n) by lia;
  entailer_with ltac:(lia).

(* The residual is purely arithmetic -- the header word packs the learnt flag onto
   a length `Zlength_nonneg` already bounds -- so the whole propagate footprint is
   thrown away rather than making the entailer walk it.  lia is no substitute for
   the apply chain: `clause_hdr_word` is a definition micromega will not look
   inside. *)
Ltac msat_propagate_close_clause_hdr_word_nonneg :=
  left;
  intros;
  apply dump_spatial_left;
  apply clause_hdr_word_nonneg;
  apply Zlength_nonneg.

(* Closes both conjuncts of the scanned watch's assignment value from the
   `mt_assigns` equation the call site binds in.  That equation is indexed
   `var - 0` while the goal is indexed `var`; with no congruence closure lia sees
   two unrelated `Znth` atoms, so the index must be made syntactically equal before
   the arithmetic will go through. *)
Ltac msat_propagate_close_scan_assign_cell PreH23 var_idx :=
  entailer_with lia;
  replace (var_idx - 0) with var_idx in PreH23 by lia;
  lia.

(* Closes the scan step's `assigns[var(l)] = 1 - 2 * sign(l)` conjunct.  The goal
   spells the literal through `lit_var_c`/`lit_sign_c` while the hypothesis carries
   the C return values and the read's own `rv - 0` index; with no congruence closure
   those are unrelated atoms, so both equations are rewritten in and the index put
   back into `- 0` form.  The leading matches re-fold the propagation state, which
   `entailer_with` leaves expanded into its projections. *)
Ltac msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar :=
  entailer_with lia;
  try match goal with
    | Hstate : ?M = msolver_propagation_scan_begin ?E ?simp ?prop,
      Hsimp : ?simp = ms_simpdb_props ?M,
      Hprop : ?prop = Znth 2 (ms_stats ?M) 0
      |- context [msolver_propagation_scan_begin ?E
                    (ms_simpdb_props ?M) (Znth 2 (ms_stats ?M) 0)] =>
        rewrite <- Hsimp, <- Hprop, <- Hstate


    | Hstate : ?M = msolver_propagation_scan_begin ?E ?simp ?prop
      |- context [msolver_propagation_scan_begin ?E ?simp ?prop] =>
        rewrite <- Hstate
    end;


  try match goal with
    | Hvar : ?rv = lit_var_c ?lit,
      Hsign : ?sg = lit_sign_c ?lit
      |- Znth ?rv (mt_assigns (ms_core ?M)) 0 = 1 - 2 * ?sg =>
        rewrite Hvar, Hsign
    end;
  match goal with
    | Hassign : Znth (?rv - 0) (mt_assigns (ms_core ?M)) 0 = _,
      Hvar : ?rv = lit_var_c ?lit,
      Hsign : ?sg = lit_sign_c ?lit
      |- Znth (lit_var_c ?lit) (mt_assigns (ms_core ?M)) 0 =
           1 - 2 * lit_sign_c ?lit =>
        rewrite <- Hvar, <- Hsign;
        replace rv with (rv - 0) by lia;
        rewrite Hassign;
        lia
    end.

(* Both side conditions bound the scanned literal as an index into the watch array.
   `lit_wf_c` sits in the live disjunct of the scan semantics but is stated in `n`,
   so the reason-core lemma must identify `n` with `ms_size Mscan` before
   `solver_shape` can supply the upper bound.  The conflict disjunct dies on the
   literal 0 in the conflict slot. *)
Ltac msat_propagate_close_scan_lit_range PreH5 PreH31 n F A_arr K Mscan :=
  entailer_with ltac:(lia);
  [ unfold solver_propagation_scan_semantics in PreH5;
    destruct PreH5 as
      [[_ [Hweak [_ [_ [_ [_ [_ [Hwf _]]]]]]]] | [Habsurd _]];
    [ exact (proj1 Hwf)
    | exfalso;
      apply Habsurd;
      reflexivity ]
  | unfold solver_propagation_scan_semantics in PreH5;
    destruct PreH5 as
      [[_ [Hweak [_ [_ [_ [_ [_ [Hwf _]]]]]]]] | [Habsurd _]];
    [ apply Z.le_trans with (m := 2 * n);
      [ apply Z.lt_le_incl;
        exact (proj2 Hwf)
      | pose proof
          (solver_propagation_weak_reason_core n F A_arr K Mscan Hweak)
          as [Hsize _];
        rewrite Hsize;
        unfold solver_shape in PreH31;
        tauto ]
    | exfalso;
      apply Habsurd;
      reflexivity ] ].

(* Closes the pure leaves left over on a propagate watch-scan step by the
   automated closer. `assumption` fires only where goal and hypothesis already spell the frontier
   index alike; the other branches re-spell it first, and one must additionally
   derive `conflict = 0` -- the conflict disjunct forces `rest = nil`, which
   contradicts `ii < Zlength source_words`. *)
Ltac msat_propagate_close_scan_step_leaves Hlt Hphysical Hresult Hzero :=
  entailer_with ltac:(lia);
  first
    [ assumption
    | lazymatch goal with
      | |- solver_propagation_scan_semantics
             ?n ?F ?A ?K ?M (Zlength ?pre) ?confl ?kept ?rest =>
          lazymatch goal with
          | Hsem : solver_propagation_scan_semantics
                     n F A K M ?p confl kept rest,
            Hp : Zlength pre = ?p |- _ =>
              rewrite Hp; exact Hsem
          end
      end
    | lazymatch goal with
      | |- solver_propagation_scan_semantics
             ?n ?F ?A ?K ?M (Zlength ?pre) 0 ?kept ?rest =>
          lazymatch goal with
          | Hsem : solver_propagation_scan_semantics
                     n F A K M ?p ?confl kept rest,
            Hphysical : propagation_watch_scan_physical
                          ?source kept ?moved rest ?garbage ?memory ?ii ?jj,
            Hlt : ?ii < Zlength ?source,
            Hp : Zlength pre = ?p |- _ =>
              assert (Hconfl : confl = 0)
                by (unfold solver_propagation_scan_semantics in Hsem;
                    destruct Hsem as [[Hconfl _] | [_ [Hrest _]]];
                    [exact Hconfl|];
                    subst rest;
                    unfold propagation_watch_scan_physical in Hphysical;
                    destruct Hphysical as
                      [_ [Hmemory [_ [Hprefix Hlength]]]];
                    rewrite app_nil_r in Hmemory;
                    rewrite Hmemory, Hprefix in Hlength;
                    rewrite <- Hlength in Hlt;
                    exfalso; exact (Z.lt_irrefl ii Hlt));
              subst confl;
              rewrite Hp;
              exact Hsem
          end
      end
    | lazymatch goal with
      | |- minisat_propagation_reuse_scan ?entry ?M (Zlength ?pre) ?confl ?rest =>
          lazymatch goal with
          | Hreuse : minisat_propagation_reuse_scan entry M ?p confl rest,
            Hp : Zlength pre = ?p |- _ => rewrite Hp; exact Hreuse
          end
      end
    | lazymatch goal with
      | |- minisat_propagation_reuse_scan ?entry ?M (Zlength ?pre) 0 ?rest =>
          lazymatch goal with
          | Hreuse : minisat_propagation_reuse_scan entry M ?p ?confl rest,
            Hsem : solver_propagation_scan_semantics ?n ?F ?A ?K M ?p ?confl ?kept rest,
            Hphysical : propagation_watch_scan_physical
              ?source ?kept ?moved rest ?garbage ?memory ?ii ?jj,
            Hlt : ?ii < Zlength ?source,
            Hp : Zlength pre = ?p |- _ =>
              let Hlive := fresh "Hlive_scan" in
              assert (Hlive : confl = 0)
                by (pose proof Hsem as Hsem_copy;
                    destruct Hsem_copy as [[Hcf _]|[_ [Hempty _]]];
                    [exact Hcf|];
                    pose proof Hphysical as Hphysical_copy;
                    destruct Hphysical_copy as [_ [Hmemory [_ [Hprefix Hlength]]]];
                    rewrite Hempty, app_nil_r in Hmemory;
                    rewrite Hmemory, Hprefix in Hlength;
                    lia);
              rewrite Hlive in Hreuse; rewrite Hp; exact Hreuse
          end
      end
    | lazymatch goal with
      | Hresult : clause_is_lit_result ?current ?retval,
        Hzero : ?retval = 0 |- clause_is_lit_result ?current 0 =>
          subst retval; exact Hresult
      end ].

(* The goal indexes the watch array by the byte difference
   `(begin + k * sizeof(PTR) - begin) / sizeof(PTR)`, which `lia` cannot reduce:
   sizeof(PTR) is an Arch constant micromega will not delta-reduce, so the quotient
   is cancelled explicitly and its nonzero side condition goes to `solve_arch`.
   The three rewrites exist because the scan base arrives under three names and
   cancellation here is syntactic. *)
Ltac msat_propagate_close_watch_cursor_bounds PreH16 PreH17 PreH18 begin retained :=
  assert (Hret :
      (begin + Zlength retained * sizeof(PTR) - begin) ÷ sizeof(PTR) =
      Zlength retained);
  [ replace (begin + Zlength retained * sizeof(PTR) - begin)
      with (Zlength retained * sizeof(PTR)) by lia;
    change (Zlength retained * sizeof(PTR) ÷
      (1 * sizeof(PTR)) = Zlength retained);
    rewrite Zquot.Zquot_mult_cancel_r

      by (change (sizeof (PTR)) with ptr_size_Z; solve_arch);
    rewrite Z.quot_1_r;
    reflexivity
  | idtac .. ];
  repeat split_pures; dump_pre_spatial;
  try assumption;
  try rewrite PreH16, PreH18, PreH17;
  try rewrite Hret;
  try lia.

(* Projects one field of the msolver invariant out of `solver_propagation_weak`,
   closing both arms of the `K` split with the matching projector pair.  The
   hypothesis and `K` must be parameters: Ltac1 resolves free names at definition
   time.  The projectors are passed `@`-prefixed because a bare one elaborates at
   the call site, where its five implicit record parameters are unknown. *)
Ltac msat_propagate_project_weak_field Hweak K msw_field msa_field :=
  unfold solver_propagation_weak in Hweak;
  let Hinv := fresh "Hinv" in
  (destruct K; destruct Hweak as [_ Hinv];
   [ exact (msw_field _ _ _ _ _ Hinv) | exact (msa_field _ _ _ _ _ Hinv) ]).

(* The learnts-size bounds are premises here, but the bound on `ms_qtail` is not:
   it sits inside the msolver invariant the call site binds in, reachable only
   through the `msi_shape` projection.  lia alone leaves the goal untouched --
   `solver_shape` is a folded definition micromega will not look inside -- so it has
   to be unfolded and its conjuncts put in scope. *)
Ltac msat_search_bound_learnts_qtail_gap PreH7 :=
  entailer_with ltac:(lia);
  pose proof (msi_shape PreH7) as Hshape;
  unfold solver_shape in Hshape;
  repeat match type of Hshape with _ /\ _ => destruct Hshape end;
  lia.

(* `Zlength (ms_activity Mdb) = ms_size Mdb` appears nowhere in the pure context;
   it is forced only by the `DoubleArray.seg` atom holding the activity array, so
   it has to be read back off the heap.  The segment lemma reports the length as
   `ms_size Mdb - 0`, which is why it is normalised before it can close the goal. *)
Ltac msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len :=
  prop_apply_p (DoubleArray.seg_Zlength
    activity_ptr 0 (ms_size Mdb) (ms_activity Mdb));
  Intros_p Hactivity_len;
  replace (ms_size Mdb - 0) with (ms_size Mdb) in Hactivity_len by lia;
  apply (derivable1s_coq_prop_r _);
  exact Hactivity_len.

(* `entailer_with lia` cannot reach a conjunct still nested inside the unfolded
   `solver_shape`, so the one equation the goal needs -- activity array length =
   solver size -- is cut out as a standalone hypothesis first.  The shape fact
   itself lives inside the msolver invariant, which is why it has to be projected
   out with `msi_shape`. *)
Ltac msat_search_close_activity_length_from_shape PreH14 Mdb :=
  assert (Hshape := msi_shape PreH14);
  unfold solver_shape in Hshape;
  assert (Hactivity : Zlength (ms_activity Mdb) = ms_size Mdb);
  [ tauto
  | idtac .. ];
  entailer_with ltac:(lia).

(* Takes the disjunct whose left-hand side is `TT && emp`: no spatial frame to
   carry, leaving the wrapped conflict counter's bound as a bare arithmetic goal.
   `unsigned_last_nbits` must be unfolded to expose the modulus before
   `Z.mod_pos_bound` applies -- lia knows nothing about `mod` on a symbolic
   dividend, so it cannot close this on its own. *)
Ltac msat_search_close_conflict_count_nonneg :=
  right;
  intros;
  pre_process_default;
  entailer_with ltac:(lia);
  unfold unsigned_last_nbits;
  apply Z.mod_pos_bound;
  lia.

(* Discharges the pure residue after search picks a variable and forms the negative
   decision literal.  Everything hinges on `lit_var_c lit = var`: `lit_var_c` is a
   halving and lia does not reason about division, so the doubling is re-associated
   to `var * 2` and cancelled with `Z_div_mult_full`.  Rewritten back to the
   variable spelling, the invariant's unassigned-cell fact matches the remaining
   conjuncts syntactically. *)
Ltac msat_search_close_decision_lit_var_conjuncts PreH3 PreH4 PreH5 retval_2 retval PreH1 PreH2 :=
  unfold solver_search_selection_state in PreH5;
  destruct PreH5 as [Hinv Hrest1];
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
  destruct Hrange as [Hret Hret_lt];
  assert (Hret2 : retval_2 = lit_neg_c (retval + retval)) by
    (rewrite PreH1, PreH2; reflexivity);
  assert (Hvar : lit_var_c (lit_neg_c (retval + retval)) = retval);
  [ rewrite lit_var_c_neg;
    unfold lit_var_c;
    replace (retval + retval) with (retval * 2) by lia;
    apply Z_div_mult_full;
    lia
  | idtac .. ];
  split_pures;
  [ dump_pre_spatial;
    reflexivity
  | dump_pre_spatial;
    reflexivity
  | dump_pre_spatial;
    rewrite Hret2, Hvar;
    exact Hnth
  | dump_pre_spatial;
    exact PreH3
  | dump_pre_spatial;
    rewrite Hret2;
    exact PreH4
  | dump_pre_spatial;
    rewrite Hvar;
    exact Hnth ].

(* The same decision-literal step, but this obligation is a spatial entailment.
   `lit_var_c lit = var` is established first (`lit_var_c` is a halving, which lia
   cannot do -- `Z_div_mult_full` cancels the doubling), and the unassigned-cell
   fact is stated at `lit_var_c lit` so it survives `entailer_with`.  The residual
   goal spells the literal expanded, hence the closing rewrite folding it back. *)
Ltac msat_search_close_decision_lit_var_entail PreH1 PreH2 PreH4 PreH5 retval_2 retval Mselected :=
  pose proof PreH5 as Hsel;
  unfold solver_search_selection_state in Hsel;
  destruct Hsel as [Hinv Hrest1];
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
  destruct Hrange as [Hret Hretlt];
  assert (Hvar : lit_var_c retval_2 = retval);
  [ rewrite PreH1, PreH2;
    rewrite lit_var_c_neg;
    unfold lit_var_c;
    replace (retval + retval) with (retval * 2) by lia;
    apply Z_div_mult_full;
    lia
  | idtac .. ];
  assert (Hassign : Znth (lit_var_c retval_2) (mt_assigns (ms_core Mselected)) 0 = 0);
  [ rewrite Hvar;
    exact Hnth
  | idtac .. ];
  entailer_with ltac:(lia);
  try reflexivity;
  try (rewrite PreH1, PreH2; exact PreH4);
  try lia;
  rewrite <- PreH2, <- PreH1;
  exact Hassign.

(* The same decision-variable bounds as the two-conjunct closer, but on the arms
   whose right-hand side also restates them through the named call result, which a
   hypothesis ties to `retval + retval`.  `&&` is left-associative, so no single
   `derivable1s_coq_prop_andp_r` matches the head: split every leaf and close each
   with lia from the same three facts asserted out of the selection-state record. *)
Ltac msat_search_close_decision_var_bounds_leaves PreH4 retval :=
  unfold solver_search_selection_state in PreH4;
  destruct PreH4 as [Hinv Hrest1];
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
  destruct Hrange as [Hretval6 Hretval6_lt];
  assert (Hnonneg : 0 <= retval) by lia;
  assert (Hbound : retval <= INT_MAX) by lia;
  assert (Hdouble : retval + retval <= INT_MAX) by lia;


  repeat apply derivable1s_truep_intros;
  apply (derivable1s_coq_prop_r _); lia.

(* Closes the two coq_prop conjuncts guarding the doubling of a freshly selected
   decision variable into a literal index.  Neither bound is among the goal's own
   pure hypotheses: `0 <= retval` and `retval < n` live inside
   `solver_search_selection_state`, and freedom from overflow at `retval + retval`
   comes from that invariant's `2 * ms_size <= INT_MAX` clause, so the record is
   destructured all the way down before lia sees anything.  The right-hand side is
   exactly two `&&`-conjuncts, so one `derivable1s_coq_prop_andp_r` peels it. *)
Ltac msat_search_close_decision_var_bounds_pair PreH3 retval :=
  unfold solver_search_selection_state in PreH3;
  destruct PreH3 as [Hinv Hrest1];
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
  destruct Hrange as [Hretval Hretval_lt];
  assert (Hnonneg : 0 <= retval) by lia;
  assert (Hdouble : retval + retval <= INT_MAX) by lia;
  eapply derivable1s_coq_prop_andp_r;
  [ apply (derivable1s_coq_prop_r _);
    exact Hnonneg
  | exact Hdouble ].

(* The four bounds (`0 <= Zlength words <= cap`, `0 < cap <= INT_MAX`) on the
   local learnt-clause word vector appear in no hypothesis -- they live inside its
   `veci_rep`, so the only route is to open that to `veci_rep_at` and pull the pure
   conjunct out.  Assumes the caller already unfolded `veci_rep` and introduced its
   data pointer; the heap is then dead weight, the conclusion being pure. *)
Ltac msat_search_close_learnt_clause_vec_bounds Hcap :=
  unfold veci_rep_at at 1; Intros_p Hcap;
  split_pures;
  dump_pre_spatial;
  destruct Hcap as [[Hlen_nonneg Hlen_cap] [Hcap_pos Hcap_max]]; lia.

(* The four length/capacity bounds on the learnt-clause database vector arrive as
   one nested conjunction, lifted out of the unfolded `vecp_rep` by the caller.
   They are placed one at a time rather than by a search tactic because the
   conjunct order is disjunct-specific: the sibling obligation that commits to the
   other disjunct spells the same four bounds in the mirror order. *)
Ltac msat_search_close_learnts_db_vec_bounds H :=
  destruct H as [[Hlen Hcap] [Hpos Hmax]];
  eapply derivable1s_coq_prop_andp_r;
  [ eapply derivable1s_coq_prop_andp_r;
    [ eapply derivable1s_coq_prop_andp_r;
      [ apply (derivable1s_coq_prop_r _);
        exact Hmax
      | exact Hpos ]
    | exact Hcap ]
  | exact Hlen ].

(* Establishes the model-copy loop's entry facts at index 0 and is applied under
   `all:` to the whole residue that `aggressive_pre_process` and `Unshelve` leave,
   which is why the tail is a cascade of `try`s: each entry-invariant goal takes
   exactly one branch and must survive the others.  `msolver_inv_literal_bound` is
   stated at `2 * ms_size M`, so the size equation has to be rewritten into it
   before it reaches the goal's `2 * n`. *)
Ltac msat_search_close_model_copy_entry_facts PreH1 n F A_arr A_inst Mselected :=
  unfold solver_search_model_ready in PreH1;
  destruct PreH1 as (Hinv & _ & _ & _ & _ & _);
  assert (Hn : 0 <= n) by exact (msi_n_range Hinv);
  assert (Hsize : ms_size Mselected = n) by (symmetry; exact (msi_size Hinv));
  assert (Hshape : 2 * n <= INT_MAX) by
    (pose proof
       (msolver_inv_literal_bound n F A_arr A_inst Mselected (msi_weak Hinv))
       as Hbound;
     rewrite Hsize in Hbound;
     exact Hbound);
  try (unfold model_copy_progress; simpl; lia);
  try lia;
  try (dump_pre_spatial; exact Hshape);
  try exact Hn;
  try exact Hshape;
  try exact Hsize;
  try assumption;
  try (unfold model_copy_progress; simpl; repeat split; try lia; reflexivity).

(* Closes the pure right-hand side `“ms_size Mselected = n” && “ms_model Mselected
   = []”` straight out of the `solver_search_model_ready` bundle: the heap
   contributes nothing, so both conjuncts go through the coq_prop introduction
   rules rather than the entailer.  The `symmetry` is forced -- the invariant
   states its size field in the opposite orientation, as `n = ms_size M`. *)
Ltac msat_search_close_model_ready_conjuncts PreH7 :=
  unfold solver_search_model_ready in PreH7;
  destruct PreH7 as [Hinv [Hqtail [Horder [Hcap [Hseed Hmodel]]]]];
  eapply derivable1s_coq_prop_andp_r;
  [ apply (derivable1s_coq_prop_r _);
    exact Hmodel
  | symmetry;
    exact (msi_size Hinv) ].

(* Discharges the model-ready obligations on the arm the entailer can finish, once
   the size equation is staged.  That staging needs `symmetry`: the invariant states
   it as `n = ms_size M`, and QCP matches goals syntactically, so the goal's
   `ms_size Mselected = n` spelling has to be produced explicitly rather than left
   to the entailer. *)
Ltac msat_search_close_model_ready_size_eq PreH1 Mselected n :=
  unfold solver_search_model_ready in PreH1;
  destruct PreH1 as (Hinv & _ & _ & _ & _ & Hmodel);
  assert (Hsize : ms_size Mselected = n) by
    (symmetry; exact (msi_size Hinv));
  entailer_with ltac:(lia).

(* Re-establish the loop from the actual decision state. Capacity and the
   conditional watch invariant are supplied by the preceding decision join. *)
Ltac msat_search_reestablish_loop_after_decision PreH1 Mdecision learnt_words learnt_cap :=
  destruct PreH1 as (_ & _ & Hinv & Hseed & Hmodel & Hdecay & _);
  Exists Mdecision learnt_words learnt_cap;
  entailer_with ltac:(first [assumption | lia]).

(* Discharges the safety obligation `Znth ... (mt_assigns (ms_core M)) 0 <> INT_MIN`
   raised by negating an lbool cell.  The only source of that cell's
   three-valuedness is the assumption-strong invariant's trail well-formedness,
   whose `Forall` has to be instantiated at this index by hand; the goal spells the
   index `k - 0`, hence the `Z.sub_0_r` before each of the three lbool values is
   refuted by `discriminate`. *)
Ltac msat_solve_close_assign_cell_not_int_min PreH25 raw k Mcur retval :=
  pose proof (mtw_cells (msa_trail_wf (msas_weak PreH25))) as Hcells;
  pose proof (Forall_Znth_elim _ _ _ 0
    (lit_var_c (Znth (k - 0) raw 0)) Hcells) as Hcell;
  assert (Hrange : 0 <= lit_var_c (Znth (k - 0) raw 0) <
      Zlength (mt_assigns (ms_core Mcur))) by lia;
  specialize (Hcell Hrange);
  unfold lbool_cell in Hcell;
  destruct Hcell as [Hcell | [Hcell | Hcell]];
  dump_pre_spatial;
  subst retval;
  rewrite Z.sub_0_r, Hcell;
  discriminate.

(* The goal indexes the assumption vector at `k - 0`, the read's own spelling, so
   that is normalised first.  Some sites ask for `<= INT_MAX`, which is already a
   hypothesis; the rest ask for the literal range `< 2 * n`, which is not, and
   which has to be recovered from the vector's `Forall (lit_wf_c n)` -- hence the
   second branch of the alternation. *)
Ltac msat_solve_close_assumption_lit_bounds k :=
  left; intros; entailer_with lia;
  replace (k - 0) with k by lia;
  first
    [ assumption


    | match goal with
      | Hall : Forall (lit_wf_c _) ?rawl |- context [Znth k ?rawl 0] =>
          assert (Hkrange : 0 <= k < Zlength rawl) by lia;
          pose proof (Forall_Znth_elim _ _ _ 0 k Hall Hkrange) as Hwfk;
          unfold lit_wf_c in Hwfk; lia
      end ].

(* The assumption list arrives as `assumption_prefix raw (Zlength raw)`, i.e. a
   `sublist` of itself, while the postcondition's `assumptions_array` spells it as
   `lits_denote raw`; nothing closes that gap automatically, so the hypothesis is
   reduced by `sublist_self` before the witnesses go in.  The leftovers are
   machine-integer facts about the array, hence `int_auto` rather than `lia`. *)
Ltac msat_solve_close_unsat_return PreH25 raw Mfalse_unsat :=
  unfold assumption_prefix in PreH25;
  rewrite sublist_self in PreH25 by reflexivity;
  unfold solver_unsat_arm;
  Intros;
  Exists Mfalse_unsat raw;
  entailer_with ltac:(int_auto).

(* ===================================================================== *)
(* 4. solver_addclause [ac_] and solver_setnvars [snv_] blocks            *)
(* ===================================================================== *)
(* ------------------------------------------------------------------ *)
(* solver_addclause (item D).  Shared tactic block, emitted once.       *)
(* ------------------------------------------------------------------ *)
Ltac ac_shape :=
  repeat match goal with
  | H : solver_shape ?M |- _ =>
      assert_fails (assert (2 * ms_size M <= INT_MAX) by assumption);
      let Sh := fresh "Hshape" in pose proof H as Sh;
      unfold solver_shape in Sh; decompose [and] Sh; clear Sh
  | H : solver_support_inv _ _ _ _ _ ?M |- _ =>
      assert_fails (assert (2 * ms_size M <= INT_MAX) by assumption);
      let Sh := fresh "Hshape_view" in pose proof (msi_shape H) as Sh;
      unfold solver_shape, msolver_set_root, msolver_core_heap_update in Sh;
      cbn in Sh; decompose [and] Sh; clear Sh
  (* [msolver_inv] is opaque to lia, but it PROJECTS to [solver_shape], which
     carries the size/cap bounds and every [Zlength .. = ms_size] the addclause
     VCs need ([2 * ms_size M <= INT_MAX] for the dedup body cut's
     [Znth .. <= INT_MAX]; [Zlength (mt_assigns ..) = ms_size] for the enqueue
     peel).  Corpus idiom: project through [msi_shape] before handing the goal
     to [lia].  The [assert_fails] guard on
     one conjunct is what terminates the [repeat]. *)
  | H : msolver_inv _ _ _ _ ?M |- _ =>
      assert_fails (assert (2 * ms_size M <= INT_MAX) by assumption);
      let Sh := fresh "Hshape" in
      pose proof (msi_shape H) as Sh;
      unfold solver_shape in Sh; decompose [and] Sh; clear Sh
  | H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
      unfold addclause_sort_outer_inv in H; decompose [and] H; clear H
  | H : addclause_sort_inner_inv _ _ _ _ |- _ =>
      unfold addclause_sort_inner_inv in H; decompose [and] H; clear H
  | H : addclause_dedup_inv ?n ?a ?i ?k ?l |- _ =>
      (* keep one FOLDED copy: [addclause_dedup_install_cert] consumes the
         invariant whole, and the case split below would otherwise remove it.
         The guard is what terminates the [repeat] -- once [strict_sorted k]
         is an assumption this arm no longer fires on the copy. *)
      assert_fails (assert (strict_sorted k) by assumption);
      let C := fresh "Hded" in pose proof H as C;
      unfold addclause_dedup_inv in H; decompose [and] H; clear H
  end.

(* The dedup loop's `sig' is an lbool = char, so every assignment truncates and
   the safety VCs carry [signed_last_nbits _ 8].  Replace each retval by the
   [lit_sign_c] it equals, record that it is in [0,1], and let the truncation
   collapse.  [clear H] after the rewrite is what stops [repeat] looping. *)
Ltac ac_trunc :=
  repeat rewrite signed_last_nbits_8_lit_sign in *;
  repeat rewrite signed_last_nbits_8_one_minus_lit_sign in *.

(* Normalise every [lit_sign_c] the addclause dedup loop produces: rewrite
   each `retval = lit_sign_c x' equation away, record the [0,1] range for
   every remaining occurrence, and re-run the 8-bit truncation collapse. *)
Ltac ac_sign :=
  ac_trunc;
  repeat match goal with
  | [ H : ?r = lit_sign_c ?x |- _ ] =>
      rewrite H in *; pose proof (lit_sign_c_range x); clear H
  end;
  ac_trunc;
  (* the safety wits carry [lit_sign_c] in the GOAL with no defining equation,
     so the equation-driven arm above never sees them. *)
  repeat match goal with
  | [ |- context[lit_sign_c ?x] ] =>
      assert_fails (assert (0 <= lit_sign_c x <= 1) by assumption);
      pose proof (lit_sign_c_range x)
  end.


(* [sizeof ( INT )] is a DEFINED constant, not a literal, and [lia] treats it
   as an opaque atom -- which turns [i = begin + k * sizeof(INT)] against
   [endvar = begin + Zlength l * sizeof(INT)] with [i < endvar] into a
   NONLINEAR problem it cannot touch.  Reducing it to 4 is the single
   highest-yield normalisation in this function. *)
Ltac ac_ptrdiff :=
  repeat match goal with
  | [ H : context[(?b + ?q * 4 - ?b) ÷ 4] |- _ ] =>
      (* the shape [subst] leaves once the pointer's defining equation is
         consumed -- without this arm, substituting is a REGRESSION. *)
      replace (b + q * 4 - b) with (q * 4) in H by lia;
      rewrite quot_mul_four in H
  | [ H : context[(?a - ?b) ÷ 4], E : ?a = ?b + ?q * 4 |- _ ] =>
      replace (a - b) with (q * 4) in H by lia;
      rewrite quot_mul_four in H
  end.

(* [lia] does not know [Zlength] is non-negative, so [Zlength kept <=
   Zlength (kept ++ tail)] is out of its reach until the fact is posed.  The
   [assert_fails] guard is what terminates the [repeat]: the posed hypothesis
   itself contains [Zlength l] and would otherwise re-match forever. *)
Ltac ac_zlen :=
  repeat match goal with
  | [ |- context[Zlength ?l] ] =>
      assert_fails (assert (0 <= Zlength l) by assumption);
      pose proof (Zlength_nonneg l)
  | [ H : context[Zlength ?l] |- _ ] =>
      assert_fails (assert (0 <= Zlength l) by assumption);
      pose proof (Zlength_nonneg l)
  end.

(* The arithmetic closer of the addclause block: normalise the sizeof and
   Zlength arithmetic in the whole context, add the Zlength-nonnegativity
   facts ([ac_zlen]), and finish with lia. *)
Ltac ac_arith :=
  try (rewrite ?sizeof_int in * );
  try (rewrite ?Z.sub_0_r in * );
  try (rewrite ?Zlength_app in * );
  try (rewrite ?Zlength_cons in * );
  try ac_ptrdiff;
  ac_zlen;
  lia.

(* Every VC that reads the clause array carries [Forall (lit_wf_c n) L] plus an
   in-range index and wants the per-element fact.  Project it, then split
   [lit_wf_c] into its two bounds so [lia] can use them.  The index range is
   itself a [sizeof]-blocked goal, hence [ac_arith] rather than [lia]. *)
(* [ac_arith] minus [ac_znth].  ac_znth's projection loop calls back into
   ac_arith, and on a goal with no [Znth] to project that recursion throws
   "Cannot find witness" -- which reads as a witness problem but is really the
   normaliser failing.  Same Zlength/sizeof normalisation, no projection: use
   this whenever the goal is pure arithmetic over list lengths. *)
Ltac ac_lia :=
  try (rewrite ?sizeof_int in * );
  try (rewrite ?Z.sub_0_r in * );
  try (rewrite ?Zlength_app in * );
  try (rewrite ?Zlength_cons in * );
  (* [Zlength_app] on a snoc leaves [Zlength nil], and a bare
     [rewrite Zlength_nil] does not match [@Zlength Z nil] here -- route it
     through an explicitly-typed equation, same as entail_wit_6. *)
  try (let Hzn := fresh "Hzn" in
       assert (Hzn : Zlength (@nil Z) = 0) by apply Zlength_nil;
       rewrite ?Hzn in * );
  lia.

(* Close a model lemma's side conditions without a positional [ | | ] list.
   Bracket lists break whenever [eapply] shelves an under-determined evar or a
   premise count shifts, and the error ("No applicable tactic") names neither
   the premise nor the cause.  Order-independent and count-independent instead;
   anything left unsolved surfaces as a plain unsolved-goal error.
   [symmetry; eassumption] is in the chain because the Inv states the bridge as
   [tail = sublist q n sortedf] while the lemmas take [sublist q n l = hd :: tl]. *)
Ltac ac_prem :=
  try reflexivity; try eassumption; try (symmetry; eassumption); try ac_lia.

(* Push [Forall (lit_wf_c n)] through every [Znth i L 0] the goal or the
   context mentions, then expand each resulting [lit_wf_c] into its numeric
   bounds so that [ac_arith] can use them. *)
Ltac ac_znth :=
  repeat match goal with
  | [ HF : Forall (lit_wf_c ?n) ?L |- context[Znth ?i ?L 0] ] =>
      assert_fails (assert (lit_wf_c n (Znth i L 0)) by assumption);
      assert (lit_wf_c n (Znth i L 0)) by (apply (Forall_lit_wf_Znth n L i HF); ac_arith)
  | [ HF : Forall (lit_wf_c ?n) ?L, H : context[Znth ?i ?L 0] |- _ ] =>
      assert_fails (assert (lit_wf_c n (Znth i L 0)) by assumption);
      assert (lit_wf_c n (Znth i L 0)) by (apply (Forall_lit_wf_Znth n L i HF); ac_arith)
  end;
  repeat match goal with
  | [ H : lit_wf_c ?n ?x |- _ ] =>
      assert_fails (assert (0 <= x) by assumption);
      pose proof (proj1 (lit_wf_c_bounds n x H));
      pose proof (proj2 (lit_wf_c_bounds n x H));
      pose proof (lit_var_c_in_range n x H)
  end.

(* The closer [entailer_with] runs on each PURE side goal.  Everything above
   therefore normalises arithmetic with the full context in view but never
   rewrites the spatial state -- which is what the same rewrites at the top of
   the proof would do, and which has broken proofs in this corpus before. *)
(* The spatial normalisations the addclause VCs need before the closer can run.
   [replace_Znth_twice] collapses the write-sandwich reclose; [full_to_seg] puts
   a re-closed array back in the [seg] spelling the invariants use.  Both arms
   are guarded on the goal actually containing the shape, so this is a no-op on
   the VCs that were already passing. *)
Ltac ac_spatial :=
  rewrite ?replace_Znth_twice;
  (* a READ closes the focus sandwich as [replace_Znth v (Znth v A 0) A];
     until this fires the array is not syntactically [mt_assigns (ms_core M)]
     and the focus cannot be closed.  [lia] gets the side condition from the
     [Zlength (mt_assigns ..) = ms_size ..] that ac_shape already posed. *)
  repeat (rewrite replace_Znth_same by lia);
  try match goal with
  | |- context[IntArray.full _ _ _] => sep_apply IntArray.full_to_seg
  end;
  try match goal with
  | |- context[CharArray.full _ _ _] => sep_apply CharArray.full_to_seg
  end.
(* NOTE: the assigns-focus CLOSE is deliberately NOT here.  The entail_wit_7_x
   family re-establishes the dedup loop's invariant, whose RHS still contains
   [solver_assigns_focus_frame_at] -- closing the focus for them destroys
   exactly what they have to produce.  The close is applied per-VC, in the
   overrides that return or hand the solver on. *)

(* Hand the loop body's scratch locals back as bare permissions.  A dedup-loop
   Inv asks only for [&("l") # Int |->_]; the body left a VALUE there.  The
   corpus spelling is a fully instantiated [sep_apply_l_atomic] per atom
   (as in [proof_of_solver_analyze_entail_wit_24] of
   solver_qcp_proof_manual_part2.v) -- bare [sep_apply] cannot pick which
   atom it means.  [dump_pre_spatial] is the wrong tool here: it wants a PURE
   right-hand side, and this residual's RHS is spatial.

   The [repeat] terminates because [|->_] is a different predicate from
   [|-> v], so a rewritten atom no longer matches. *)
Ltac ac_forget_locals :=
  repeat match goal with
  | |- context [ ?x # Int  |-> ?v ] => sep_apply_l_atomic (store_int_undef_store_int x v)
  | |- context [ ?x # Char |-> ?v ] => sep_apply_l_atomic (store_char_undef_store_char x v)
  | |- context [ ?x # Ptr  |-> ?v ] => sep_apply_l_atomic (store_ptr_undef_store_ptr x v)
  end.

(* The addclause block's final closer: substitute, harvest the [Znth] literal
   bounds, then try the small menu of endings the addclause VCs actually use
   (arithmetic, the sorted/dedup certificates, the setnvars equivalences). *)
Ltac ac_close :=
  try subst;
  ac_znth;
  first
    [ assumption
    | solve [ ac_arith ]
    | solve [ apply strict_sorted_nodup_vars; assumption ]
    | solve [ eapply addclause_dedup_install_cert; [ eassumption | ac_arith ] ]
    | solve [ eapply setnvars_core_equiv_pending; eassumption ]
    | solve [ eapply setnvars_core_equiv_seed_shadow; eassumption ]
    | ac_arith ].

(* The `tmpv` temp was deleted to match upstream; symexec then emits the
   store's array as a SELF-REPLACE -- `replace_Znth p (Znth p arr 0) arr` IS
   `arr`, because a read does not write.  This cancels it.  Measured
   necessity: neutering it leaves exactly one VC unprovable
   (solver_addclause_entail_wit_3), so it is carried, not sprayed. *)
Ltac ac_selfrepl :=
  repeat match goal with
  | |- context [replace_Znth ?i (Znth ?i ?l ?d) ?l] =>
      rewrite (replace_Znth_same i l d) by (rewrite ?Zlength_app in *; simpl in *; lia)
  | H : context [replace_Znth ?i (Znth ?i ?l ?d) ?l] |- _ =>
      rewrite (replace_Znth_same i l d) in H
        by (rewrite ?Zlength_app in *; simpl in *; lia)
  end.

(* Open every [solver_shape] hypothesis and split its conjunction, so that the
   setnvars size and capacity bounds are visible to lia. *)
Ltac snv_shape :=
  repeat match goal with
         | H : solver_shape _ |- _ => unfold solver_shape in H
         end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.


(* [snv_shape] unfolds every [solver_shape] hypothesis so [lia] can see its
   conjuncts, which destroys the FOLDED predicate the return obligations still
   have to hand back.  Rebuilding it from the destructed leaves is cheaper than
   stashing a marked copy (a stash would re-match its own output). *)
Ltac snv_refold_shape :=
  match goal with
  | |- solver_shape ?M =>
      first [ match goal with
              | H : msolver_inv _ _ _ _ M |- _ => exact (msw_shape (msi_weak H))
              end
            | (unfold solver_shape; repeat split; assumption) ]
  end.

(* Split the setnvars post-condition and discharge each leaf: an assumption,
   the re-folded [solver_shape], arithmetic, or propositional reasoning. *)
Ltac snv_dispatch :=
  repeat split;
  first [ assumption | snv_refold_shape | lia | tauto ].


(* ===================================================================== *)
(* 5. The watcher-scan enqueue derivation                                *)
(* ===================================================================== *)
(* The other three pieces of this derivation --                            *)
(* [propagation_watch_scan_rest_head__propagate],                          *)
(* [solver_propagation_weak_core_facts__propagate] and                     *)
(* [propagation_scan_current_tag_facts__propagate] -- live in              *)
(* solver_qcp_lib.v; this file Requires it, so the proof below still       *)
(* reaches them.  This one stays here because its proof writes a bare      *)
(* [length]: solver_qcp_proof_common.v Requires Coq.Lists.List AFTER       *)
(* Coq.Strings.String, so [length] is [List.length] here and              *)
(* [String.length] in solver_qcp_lib.v, where the same text does not       *)
(* typecheck.                                                              *)

(* From the physical scan layout plus the memory decomposition, the pending  *)
(* list starts at the word the scan is looking at; from the scan semantics   *)
(* on that word, the tagged literal is well formed and the model's arrays    *)
(* have the lengths [enqueue_input] asks for.  The [is_tag] premise is       *)
(* spelled the way the annotation spells it; a site holding                  *)
(* [tagged_word current] can pass it directly, the two are definitionally    *)
(* equal.  Its watcher-scan consumers are in parts 3 and 8; search those   *)
(* files for [propagation_scan_current_enqueue_input__propagate].          *)
Lemma propagation_scan_current_enqueue_input__propagate :
  forall n F A_arr K Mscan p confl retained rest scan_current raw_suffix,
    solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ->
    rest = scan_current :: raw_suffix ->
    is_tag scan_current = msat_true ->
    enqueue_input (ms_size Mscan) (tag_lit scan_current) (ms_qtail Mscan)
      (mt_assigns (ms_core Mscan)) (mt_levels (ms_core Mscan))
      (ms_reason_words Mscan) (mt_trail (ms_core Mscan)).
Proof.
  intros n F A_arr K Mscan p confl retained rest scan_current raw_suffix
    Hsem Hrest Histag.
  pose proof (propagation_scan_current_tag_facts__propagate n F A_arr K Mscan p confl retained rest
    scan_current raw_suffix Hsem Hrest Histag) as [Hnsize [Hdb Htag]].
  assert (Hweak : solver_propagation_weak n F A_arr K Mscan).
  { unfold solver_propagation_scan_semantics in Hsem.
    destruct Hsem as [Hlive | Hconf].
    - destruct Hlive as [_ [Hw _]]. exact Hw.
    - destruct Hconf as [_ [Hnil _]]. exfalso. rewrite Hrest in Hnil. discriminate. }
  pose proof (solver_propagation_weak_core_facts__propagate n F A_arr K Mscan Hweak)
    as [_ [Hshape [_ [_ Htrailwf]]]].
    assert (Hcells : Forall (fun x => -1 <= x <= 1)
        (mt_assigns (ms_core Mscan))).
    { eapply Forall_impl with (P := lbool_cell)
          (Q := fun x => -1 <= x <= 1).
      - intros x Hx.
        unfold lbool_cell in Hx.
        destruct Hx as [Hx | [Hx | Hx]]; lia.
      - exact (mtw_cells Htrailwf). }
    assert (H2n : 2 * ms_size Mscan <= INT_MAX).
    { pose proof Hshape as Hshape2. unfold solver_shape in Hshape2. tauto. }
    assert (HAlen : Zlength (mt_assigns (ms_core Mscan)) = n).
    { rewrite (solver_shape_assigns_len Mscan Hshape); symmetry; exact Hnsize. }
    assert (HLlen : Zlength (mt_levels (ms_core Mscan)) = n).
    { assert (Ht : Zlength (mt_levels (ms_core Mscan)) = ms_size Mscan).
      { pose proof Hshape as Hshape3. unfold solver_shape in Hshape3. tauto. }
      rewrite Ht. symmetry; exact Hnsize. }
    assert (HRlen : Zlength (ms_reason_words Mscan) = n).
    { rewrite (solver_shape_reasons_len Mscan Hshape); symmetry; exact Hnsize. }
    assert (HTlen : Zlength (mt_trail (ms_core Mscan)) = ms_qtail Mscan).
    { pose proof Hshape as Hshape5. unfold solver_shape in Hshape5. tauto. }
    assert (Hq0 : 0 <= ms_qtail Mscan).
    { pose proof Hshape as Hshape4. unfold solver_shape in Hshape4. lia. }
    assert (HqN : ms_qtail Mscan <= n).
    { pose proof (mtw_trail_bound Htrailwf) as Hb. lia. }
    assert (Hroom : Znth (lit_var_c (tag_lit scan_current))
        (mt_assigns (ms_core Mscan)) 0 = 0 -> ms_qtail Mscan < n).
    { intro Hun.
      assert (Hv : 0 <= lit_var_c (tag_lit scan_current) < n).
      { apply lit_var_c_in_range; exact Htag. }
      assert (Hnotin : ~ In (lit_var_c (tag_lit scan_current))
          (map lit_var_c (mt_trail (ms_core Mscan)))).
      { intro Hin. exfalso.
        apply (proj2 (mtw_assigned_iff Htrailwf _ Hv) Hin). exact Hun. }
      assert (Hnd : NoDup (map lit_var_c
          (mt_trail (ms_core Mscan) ++ cons (tag_lit scan_current) nil))).
      { rewrite map_app. apply NoDup_snoc.
        - exact (mtw_trail_nodup Htrailwf).
        - intro Hin. apply Hnotin. simpl in Hin. exact Hin. }
      assert (Hbound : forall x, In x (map lit_var_c
          (mt_trail (ms_core Mscan) ++ cons (tag_lit scan_current) nil)) -> 0 <= x < n).
      { intros x Hin. apply in_map_iff in Hin.
        destruct Hin as [y [<- Hy]].
        assert (Hall : Forall (lit_wf_c n)
            (mt_trail (ms_core Mscan) ++ cons (tag_lit scan_current) nil)).
        { apply Forall_app.
          split; [exact (mtw_trail_lits Htrailwf)|constructor; [exact Htag|constructor]]. }
        rewrite Forall_forall in Hall.
        apply lit_var_c_in_range; exact (Hall y Hy). }
      pose proof (NoDup_Z_bounded_length _ n (mtw_n_nonneg Htrailwf) Hnd Hbound) as Hle.
      rewrite length_map in Hle.
      assert (HlenEq : Z.of_nat (length
          (mt_trail (ms_core Mscan) ++ cons (tag_lit scan_current) nil)) =
          Zlength (mt_trail (ms_core Mscan) ++ cons (tag_lit scan_current) nil)).
      { rewrite Zlength_correct. reflexivity. }
      rewrite HlenEq in Hle.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hle.
      rewrite HTlen in Hle. lia. }
    assert (HtagM : lit_wf_c (ms_size Mscan) (tag_lit scan_current)).
    { rewrite <- Hnsize. exact Htag. }
    assert (HAlenM : Zlength (mt_assigns (ms_core Mscan)) = ms_size Mscan).
    { rewrite <- Hnsize. exact HAlen. }
    assert (HLlenM : Zlength (mt_levels (ms_core Mscan)) = ms_size Mscan).
    { rewrite <- Hnsize. exact HLlen. }
    assert (HRlenM : Zlength (ms_reason_words Mscan) = ms_size Mscan).
    { rewrite <- Hnsize. exact HRlen. }
    assert (HqNM : ms_qtail Mscan <= ms_size Mscan) by lia.
    assert (HroomM : Znth (lit_var_c (tag_lit scan_current))
        (mt_assigns (ms_core Mscan)) 0 = 0 -> ms_qtail Mscan < ms_size Mscan).
    { intro Hfresh. rewrite <- Hnsize. apply Hroom; exact Hfresh. }
    assert (Henq : enqueue_input (ms_size Mscan) (tag_lit scan_current)
        (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
        (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
        (mt_trail (ms_core Mscan))).
    { unfold enqueue_input.
      exact (conj HtagM
        (conj H2n
            (conj HAlenM
            (conj HLlenM
              (conj HRlenM
                (conj HTlen
                  (conj (conj Hq0 HqNM)
                    (conj HroomM Hcells)))))))). }
    exact Henq.
Qed.

(* ===================================================================== *)
(* 6. Closers for the CROSS-PART clone groups                            *)
(* ===================================================================== *)
(* Every tactic below replaces a proof script that stood in byte-identical *)
(* copies in TWO OR MORE of solver_qcp_proof_manual_part1..9.v, where an   *)
(* Ltac local to one part could not serve the others.  Each entry names    *)
(* the parts it is called from.  Tactics that need values introduced by    *)
(* the caller's own opener take them as arguments; the rest find their     *)
(* hypotheses by shape, so the call site is a single line.                 *)

(* The `scan_move` / `scan_same` pure side conditions of the watcher scan:
   the whole obligation is that a clause header word is non-negative, which
   [clause_hdr_word_nonneg_entail] states at the assertion level.
   Called from parts 3 and 8 (18 sites). *)
Ltac msat_clause_hdr_word_nonneg_scan_pure :=
  Unfold; right; intros; apply clause_hdr_word_nonneg_entail.

(* Opens the VC and hands it to [msat_real_satisfied_dispatch] above; split
   out only so that the 24 bottom-merge sites in parts 2, 3 and 6 are one
   line each instead of two identical ones. *)
Ltac msat_real_satisfied_close := Unfold; msat_real_satisfied_dispatch.

(* The `0 <= retval` / `retval + retval <= INT_MAX` pair guarding a freshly
   selected decision variable.  The selection-state hypothesis is matched by
   shape instead of being renamed with [bind_fact], which is what lets the
   whole proof be one call.  Called from parts 6 and 8 (13 sites). *)
Ltac msat_search_decision_var_bounds_pure :=
  Unfold; left; intros;
  match goal with
  | H : solver_search_selection_state _ _ _ _ ?rv _ |- _ =>
      msat_search_close_decision_var_bounds_pair H rv
  end.

(* The literal-range side condition of the `clause_simplify` scan: open the
   scan invariant, collapse the header-word division carried by the retval
   equation, and read the bound off its [Forall (lit_wf_c n)] conjunct.  The
   three hypotheses are matched by shape.  Called from parts 1 and 8. *)
Ltac msat_clause_simplify_lit_range_pure :=
  aggressive_pre_process;
  match goal with
  | Hlit : ?lit = Znth ?i ?cw 0,
    Hrv : ?rv = clause_hdr_word ?isl (Zlength ?cw) ÷ 2,
    Hinv : clause_simplify_scan_inv ?n ?cw ?asg ?i |- _ =>
      unfold clause_simplify_scan_inv in Hinv;
      destruct Hinv as (Hi & Halen & Hlits & Hcells & Hprefix);
      assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
        by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
      rewrite zdiv_equiv in Hrv by lia;
      rewrite clause_hdr_word_div2 in Hrv by apply Zlength_nonneg;
      assert (Hwf : lit_wf_c n lit)
        by (rewrite Hlit;
            apply (Forall_Znth_elim Z (lit_wf_c n) cw 0 i Hlits); lia);
      unfold lit_wf_c in Hwf;
      dump_pre_spatial; lia
  end.

(* The `0 <= Znth 0 lits` / `Znth 0 lits <= INT_MAX` pair on the first literal
   of a clause being reduced: the bound lives in the model invariant's literal
   bound, rebased on [msi_size], and the two goals the entailer leaves are the
   two halves of the range.  Called from parts 4 and 8. *)
Ltac msat_reducedb_first_lit_bounds_pure :=
  Unfold; left; intros;
  match goal with
  | HF : Forall (lit_wf_c ?n) ?lits, HM : msolver_inv ?n _ _ _ _ |- _ =>
      entailer_with ltac:(lia);
      pose proof (Forall_Znth_elim _ _ _ 0 0 HF ltac:(lia)) as Hlit;
      unfold lit_wf_c in Hlit;
      pose proof (msolver_inv_literal_bound _ _ _ _ _ (msi_weak HM)) as Hbound;
      pose proof (msi_size HM) as Hsize;
      rewrite <- Hsize in Hbound;
      [ change (0 <= Znth 0 lits 0); lia
      | change (Znth 0 lits 0 <= INT_MAX); lia ]
  end.

(* The header-word range obligation of the reduce-database loop, which is
   pure arithmetic once [clause_hdr_word] and [msat_true] are unfolded.
   Called from parts 4 and 8. *)
Ltac msat_reducedb_hdr_word_range_pure :=
  Unfold; left; intros; entailer_with ltac:(lia);
  unfold clause_hdr_word, msat_true; lia.

(* The spatial tail of a binary-clause `keep` transition: rewrite the level
   equation back, cancel the scan core against the frame, and let the pure
   residue fall to the standard trio.  [H_lvl] is the `lvl = levels_entry`
   fact the call site binds; the existential witnesses stay at the call site
   because they only exist after the caller's own opener.  Parts 2 and 7. *)
Ltac msat_propagate_binary_keep_close H_lvl :=
  split_pure_spatial;
  [ rewrite <- H_lvl;
    unfold solver_propagation_scan_core_at;
    unfold PtrArray.seg, stats_propagate_scan;
    set_String_name; sepcon_assoc_change; sepcon_cancel;
    subst_all_strings; unfold Znth; cbn; csimpl;
    intros m Hm; exact Hm
  | split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia ].

(* The `order_unassigned` no-op return: the variable is already outside the
   heap, so the post-condition holds of the unchanged (cap, heap, orderpos)
   triple.  Only the order vector's data pointer has to be supplied, the rest
   is read off the [order_unassigned_pre] hypothesis.  Parts 6 and 8. *)
Tactic Notation "msat_order_unassigned_noop_return" constr(optr) :=
  match goal with
  | HZ : Znth (?v - 0) ?opos 0 <> -1,
    HP : order_unassigned_pre ?n ?v ?cap ?heap ?opos |- _ =>
      assert (Hpresent0 : Znth v opos 0 <> -1)
        by (replace (v - 0) with v in HZ by lia; exact HZ);
      assert (Hpost : order_unassigned_post n v cap heap opos cap heap opos)
        by (apply order_unassigned_post_noop__vecp_remove;
            [exact HP | exact Hpresent0]);
      Exists cap heap opos;
      unfold veci_rep, veci_rep_at, veci_size_addr, veci_cap_addr,
        veci_ptr_addr;
      Exists optr;
      entailer_with ltac:(lia);
      csimpl;
      entailer_with ltac:(lia)
  end.

(* The analyze loop's learnt-clause frame: hand back the six loop witnesses,
   then return the local `reasons` pointer as an undefined store.  Called from
   parts 1 and 2. *)
Tactic Notation "msat_analyze_learnt_undef_frame" constr(cap) constr(words)
  constr(Spend) constr(Rres) constr(learnt) constr(Mdb) :=
  Exists cap words Spend Rres learnt Mdb;
  entailer_with ltac:(lia);
  apply store_ptr_undef_store_ptr.

(* The `clause_remove` header-word bounds: the clause length is non-negative
   and so is the header word computed from it.  Called from parts 4 and 5. *)
Tactic Notation "msat_clause_hdr_word_bounds_pure" constr(cw) constr(isl) :=
  assert (Hsize : 0 <= Zlength cw) by apply Zlength_nonneg;
  assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
    by (apply clause_hdr_word_nonneg; exact Hsize);
  entailer_with ltac:(lia).

(* ===================================================================== *)
(* 9. solver_analyze clause-scan tag-step helpers (part5 + part7)        *)
(* ===================================================================== *)

(* The six VC obligations that re-establish [analyze_clause_scan_inv] after
   the tag step of solver_analyze's inner clause scan are split five/one
   across solver_qcp_proof_manual_part5.v and _part7.v.  These four tactic
   notations are the part-independent steps every one of them runs; they
   were introduced as byte-identical [_p5] / [_p7] twins (parts may not
   Require one another) and are declared here so each exists once.  The nine
   lemmas they used to sit beside are now in solver_qcp_lib.v, which this
   file Requires.  Every ghost name and every hypothesis a tactic block
   needs is an argument: a tactic body may only mention globals and its own
   parameters. *)

(* Read one phase-independent conjunct off the clause-scan invariant [H]:
   unfold it and let [tauto] pick the component the goal asks for. *)
Tactic Notation "msat_analyze_scan_inv_part" ident(H) :=
  unfold analyze_clause_scan_inv in H; tauto.

(* Same read for a conjunct that lives under the invariant's phase case split:
   [Hphase] pins the phase so the case reduces before [tauto] looks at it. *)
Tactic Notation "msat_analyze_scan_inv_part" ident(H) constr(Hphase) :=
  unfold analyze_clause_scan_inv in H; rewrite Hphase in H; cbn in H; tauto.

(* The tag step only rewrites heuristic and scratch fields, so the two
   [analysis_core_equiv]s [Hact] / [Hzero] and the seed shadow [Hseed] of the
   scan state carry over to [Mnext] unchanged.  Leaves [Hcoreactnew],
   [Hcore0new] and [Hseednew]. *)
Tactic Notation "msat_analyze_tag_step_carry" ident(Mnext) constr(Ma)
    constr(Mzero) ident(Hact) ident(Hzero) ident(Hseed) :=
  assert (Hcoreactnew : analysis_core_equiv Ma Mnext)
    by (unfold Mnext; apply analysis_core_equiv_analyze_tag_step; exact Hact);
  assert (Hcore0new : analysis_core_equiv Mzero Mnext)
    by (unfold Mnext; apply analysis_core_equiv_analyze_tag_step; exact Hzero);
  assert (Hseednew : msolver_seed_shadow Mnext)
    by (unfold Mnext; apply ms_analyze_tag_step_seed_shadow; exact Hseed).

(* Re-establish [analyze_clause_scan_inv] after a tag step that grows the [S]
   component: [intuition] leaves the clause-length side conditions and the two
   recomputed start sets [HS] / [HL]; [HC] is the [Ccur = lits_denote ...] fact.
   A goal selector [all:] is a syntax error in a tactic body, so each dispatch
   is written [ [> t .. ] ]. *)
Tactic Notation "msat_analyze_scan_inv_tag" ident(Mnext) ident(phase)
    constr(HC) constr(HS) constr(HL) :=
  unfold analyze_clause_scan_inv in *;
  subst phase;
  unfold Mnext, analyze_tag_step_msolver, msolver_analysis_update, msolver_view in *;
  cbn -[Z.add Z.sub Z.mul Z.div Z.modulo] in *;
  intuition (try lia; try assumption);
  [> try (rewrite HC; rewrite lits_denote_length; lia) ..];
  [> try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) ..];
  [> try exact HS ..];
  [> try exact HL ..].


(* Proof conveniences used only by the manual proof layer. *)
(* V2.1.0 guide 11: "尽量依赖 hypothesis 的含义，而不是固定的 PreH1、PreH2 编号."
   [bind_fact] locates a generated hypothesis by its STATEMENT and renames it, so a proof
   body names facts by content instead of by the position symexec happened to emit them in.
   Case-local by design: never define this in the framework. *)
Tactic Notation "bind_fact" constr(ty) "as" ident(na) :=
  match goal with H : ty |- _ => rename H into na end.

(* Rewrite every set_cap projection lemma over the current goal. *)
Ltac snv_set_cap_proj :=
  rewrite ?msolver_set_cap_core, ?msolver_set_cap_size, ?msolver_set_cap_cap,
          ?msolver_set_cap_qtail, ?msolver_set_cap_activity,
          ?msolver_set_cap_tags, ?msolver_set_cap_reason_words,
          ?msolver_set_cap_orderpos, ?msolver_set_cap_order,
          ?msolver_set_cap_order_cap, ?msolver_set_cap_wm,
          ?msolver_set_cap_wcaps.

(* Rewrite every sift-step projection lemma over the current goal. *)
Ltac snv_sift_proj :=
  rewrite ?msolver_sift_core, ?msolver_sift_size, ?msolver_sift_cap,
          ?msolver_sift_qtail, ?msolver_sift_reason_words,
          ?msolver_sift_tags, ?msolver_sift_activity, ?msolver_sift_wm,
          ?msolver_sift_wcaps, ?msolver_sift_orderpos, ?msolver_sift_order,
          ?msolver_sift_order_cap,
          ?mt_assigns_add_var, ?mt_levels_add_var, ?mt_trail_add_var.

(* Pin the ghost from the branch condition, then normalise. *)
Ltac cn_pin_learnt sel := assert (sel = 1) by lia; subst sel; cn_at_learnt.

(* Pin the ghost from the branch condition, then normalise (selector 0). *)
Ltac cn_pin_prob sel := assert (sel = 0) by lia; subst sel; cn_at_prob.

(* Rewrite every with_clause_caps_gen projection lemma over the current goal. *)
Ltac cn_proj :=
  rewrite ?with_caps_gen_idem, ?sel_db_with_caps, ?sel_cap_with_caps, ?wm_with_caps, ?wcaps_with_caps,
          ?(sel_other_db_with_caps _ _ _ _ ltac:(lia)),
          ?(sel_other_cap_with_caps _ _ _ _ ltac:(lia)),
          ?(sel_db_install _ _ _ _ ltac:(lia)),
          ?(sel_other_db_install _ _ _ _ ltac:(lia)),
          ?(sel_cap_install _ _ _ _ _ ltac:(lia)),
          ?(sel_other_cap_install _ _ _ _ _ ltac:(lia)) in *.
