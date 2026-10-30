From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.

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
              lazymatch goal with
              | |- ?A |-- ?B => unify A B; change (A |-- A)
              end;
              cancel
          end ]
    |
      tryif
      (lazymatch goal with
      | |- _ |-- ?rhs => _assert_pure rhs
      | _ => fail
      end)
      then solve [ apply dump_spatial_left; simpl_entail_with tac ]
      else msat_entailer_with tac ].

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
  (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).

(* The scan
   invariant bounds the index only by the clause length, and nothing bounds a
   clause's length directly -- it takes the pigeonhole, the clause's literal
   variables being distinct and all below `n`.  The `destruct` only reads `0 <= n`
   off the head literal; the empty list has no literal to read and is closed
   instead from `j < Zlength [] = 0`. *)
Ltac msat_analyze_bound_scan_index_by_nodup n Ccur j Hinv clause_words2 :=
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

(* Closes a pure side condition whose whole obligation is that a clause
   header word is non-negative, which [clause_hdr_word_nonneg_entail] states
   at the assertion level.  lia is no substitute: `clause_hdr_word` is a
   definition micromega will not look inside. *)
Ltac msat_close_clause_hdr_word_nonneg :=
  (LLM_pre_process ltac:(lia || int_auto));
  apply clause_hdr_word_nonneg_entail.

Ltac msat_analyze_close_clause_hdr_word_nonneg :=
  (LLM_pre_process ltac:(lia));
  split_pures;
  apply clause_hdr_word_nonneg_entail.

Ltac msat_analyze_close_clause_word_int_range j clause_words2 Hlit :=
  assert (Hr : 0 <= j - 0 < Zlength clause_words2) by lia;
  match goal with
  | Hwf : List.Forall ?P clause_words2 |- _ =>
      pose proof (sat_shared_lib.Forall_Znth_elim Z P
        clause_words2 0 (j - 0) Hwf Hr) as Hlit
  end;
  unfold solver_qcp_model.lit_wf_c in Hlit;

  try subst j;
  lia.

(* One `Forall` instance at the scan index covers every spelling: the right-hand
   side also names the scanned literal at the iteration's concrete index
   (`Znth (1 - 0)`, `Znth (0 - 0)`), and the `replace`'s side condition is then just
   the index equation `lia` already has in context. *)
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

Ltac msat_analyze_close_learnt_vec_lit_range Hf :=
  split_pures;
  dump_pre_spatial;
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

Ltac msat_analyze_stage_clause_word_range_at_fixed_index n k cw :=
  assert (Hlitk : lit_wf_c n (Znth (k - 0) cw 0)) by
    (apply (Forall_Znth_elim _ _ _ 0 (k - 0)); [assumption | lia]);
  unfold lit_wf_c in Hlitk.

(* Heap uniqueness and variable ranges give size <= n by pigeonhole; the
   invariant's 2 * n <= INT_MAX then bounds the doubled child index. *)
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
  (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).

Ltac msat_propagate_close_scan_first_lit_assigned :=
  match goal with
    | Hassign : Znth (?rv - 0) (mt_assigns (ms_core ?M)) 0 = _ |- _ =>
        replace (rv - 0) with rv in Hassign by lia
  end;
  subst;
  split_pures;
  dump_pre_spatial;
  solve [auto | lia].

(* The
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
   through the `msi_shape` projection. *)
Ltac msat_search_bound_learnts_qtail_gap PreH7 :=
  split_pures;
  dump_pre_spatial;
  pose proof (msi_shape PreH7) as Hshape;
  unfold solver_shape in Hshape;
  repeat match type of Hshape with _ /\ _ => destruct Hshape end;
  lia.

(* Takes the disjunct whose left-hand side is `TT && emp`: no spatial frame to
   carry, leaving the wrapped conflict counter's bound as a bare arithmetic goal.
   `unsigned_last_nbits` must be unfolded to expose the modulus before
   `Z.mod_pos_bound` applies -- lia knows nothing about `mod` on a symbolic
   dividend, so it cannot close this on its own. *)
Ltac msat_search_close_conflict_count_nonneg :=
  unfold unsigned_last_nbits;
  apply Z.mod_pos_bound;
  lia.

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
  split_pures;
  dump_pre_spatial;
  [ reflexivity
  | reflexivity
  | exact Hassign
  | lia
  | rewrite PreH1, PreH2;
    exact PreH4
  | rewrite <- PreH2, <- PreH1;
    exact Hassign ].

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

(* Some sites ask for `<= INT_MAX`, which is already a
   hypothesis; the rest ask for the literal range `< 2 * n`, which is not, and
   which has to be recovered from the vector's `Forall (lit_wf_c n)` -- hence the
   second branch of the alternation. *)
Ltac msat_solve_close_assumption_lit_bounds k :=
  (LLM_pre_process ltac:(lia || int_auto)); split_pures; dump_pre_spatial;
  replace (k - 0) with k by lia;
  first
    [ assumption

    | match goal with
      | Hall : Forall (lit_wf_c _) ?rawl |- context [Znth k ?rawl 0] =>
          assert (Hkrange : 0 <= k < Zlength rawl) by lia;
          pose proof (Forall_Znth_elim _ _ _ 0 k Hall Hkrange) as Hwfk;
          unfold lit_wf_c in Hwfk; lia
      end ].


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

Ltac ac_trunc :=
  repeat rewrite signed_last_nbits_8_lit_sign in *;
  repeat rewrite signed_last_nbits_8_one_minus_lit_sign in *.

Ltac ac_sign :=
  ac_trunc;
  repeat match goal with
  | [ H : ?r = lit_sign_c ?x |- _ ] =>
      rewrite H in *; pose proof (lit_sign_c_range x); clear H
  end;
  ac_trunc;
  repeat match goal with
  | [ |- context[lit_sign_c ?x] ] =>
      assert_fails (assert (0 <= lit_sign_c x <= 1) by assumption);
      pose proof (lit_sign_c_range x)
  end.

Ltac ac_ptrdiff :=
  repeat match goal with
  | [ H : context[(?b + ?q * 4 - ?b) ÷ 4] |- _ ] =>
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

Ltac ac_arith :=
  try (rewrite ?sizeof_int in * );
  try (rewrite ?Z.sub_0_r in * );
  try (rewrite ?Zlength_app in * );
  try (rewrite ?Zlength_cons in * );
  try ac_ptrdiff;
  ac_zlen;
  lia.

Ltac ac_lia :=
  try (rewrite ?sizeof_int in * );
  try (rewrite ?Z.sub_0_r in * );
  try (rewrite ?Zlength_app in * );
  try (rewrite ?Zlength_cons in * );
  try (let Hzn := fresh "Hzn" in
       assert (Hzn : Zlength (@nil Z) = 0) by apply Zlength_nil;
       rewrite ?Hzn in * );
  lia.

(* Symmetry
   handles the invariant's reversed tail/sublist equation. *)
Ltac ac_prem :=
  try reflexivity; try eassumption; try (symmetry; eassumption); try ac_lia.

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

(* The spatial normalisations the addclause VCs need before the closer can run.
   [replace_Znth_twice] collapses the write-sandwich reclose; [full_to_seg] puts
   a re-closed array back in the [seg] spelling the invariants use. *)
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

Ltac ac_selfrepl :=
  repeat match goal with
  | |- context [replace_Znth ?i (Znth ?i ?l ?d) ?l] =>
      rewrite (replace_Znth_same i l d) by (rewrite ?Zlength_app in *; simpl in *; lia)
  | H : context [replace_Znth ?i (Znth ?i ?l ?d) ?l] |- _ =>
      rewrite (replace_Znth_same i l d) in H
        by (rewrite ?Zlength_app in *; simpl in *; lia)
  end.

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

Ltac snv_dispatch :=
  repeat split;
  first [ assumption | snv_refold_shape | lia | (unfold vec_buf_ok; intros; lia) | tauto ].

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
  destruct (propagation_scan_current_tag_facts__propagate
    n F A_arr K Mscan p confl retained rest scan_current raw_suffix Hsem Hrest Histag)
    as [Hnsize [Hdb Htag]].
  assert (Hweak : solver_propagation_weak n F A_arr K Mscan).
  { destruct Hsem as [[Hconfl [Hweak Hlive]] | [Hconfl [Hnil Hconf]]].
    - exact Hweak.
    - rewrite Hrest in Hnil. discriminate. }
  destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mscan Hweak)
    as [_ [Hshape [_ [_ Htrailwf]]]].
  subst n.
  assert (Hcells : Forall (fun x => -1 <= x <= 1) (mt_assigns (ms_core Mscan))).
  { eapply Forall_impl; [| exact (mtw_cells Htrailwf)].
    intros x Hx. unfold lbool_cell in Hx. lia. }
  assert (Hroom : Znth (lit_var_c (tag_lit scan_current))
    (mt_assigns (ms_core Mscan)) 0 = 0 -> ms_qtail Mscan < ms_size Mscan).
  { intro Hzero.
    pose proof (mtrail_unassigned_room (ms_size Mscan) (ms_core Mscan)
      (lit_var_c (tag_lit scan_current)) Htrailwf
      (lit_var_c_in_range _ _ Htag) Hzero) as Hroom.
    unfold solver_shape in Hshape. lia. }
  pose proof (mtw_trail_bound Htrailwf) as Hbound.
  unfold enqueue_input, solver_shape in *.
  repeat split; try assumption; try lia.
  all: unfold lit_wf_c in Htag; lia.
Qed.

Tactic Notation "msat_propagate_scan_enqueue_input" constr(Hphysical)
    constr(Hwatch) constr(Hprefix) constr(Hsemantics) constr(Htag)
    "as" ident(Henq) :=
  let Hrest := constr:(propagation_watch_scan_rest_head__propagate
    _ _ _ _ _ _ _ _ _ _ _ Hphysical Hwatch Hprefix) in
  pose proof (propagation_scan_current_enqueue_input__propagate
    _ _ _ _ _ _ _ _ _ _ _ Hsemantics Hrest Htag) as Henq.


Ltac msat_split_after_llm :=
  repeat (split_pure_spatial || split_pures);
  try solve [cancel];
  try match goal with
      | |- emp |-- “ _ ” => dump_pre_spatial
      | |- emp |-- emp => cancel
      end.

Ltac msat_clause_simplify_lit_range_pure :=
  msat_split_after_llm;
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

Ltac msat_reducedb_open_state :=
  repeat match goal with
  | H : solver_reducedb_loop_state _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold solver_reducedb_loop_state in H;
      destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?)
  end;
  unfold solver_reducedb_loop_state.

Ltac msat_reducedb_state_pure :=
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state; subst; (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).

(* The `0 <= Znth 0 lits` / `Znth 0 lits <= INT_MAX` pair on the first literal
   of a clause being reduced: the bound lives in the model invariant's literal
   bound, rebased on [msi_size]. *)
Ltac msat_reducedb_first_lit_bounds_pure :=
  (LLM_pre_process ltac:(lia || int_auto)); msat_reducedb_open_state;
  match goal with
  | HF : Forall (lit_wf_c ?n) ?lits, HM : msolver_inv ?n _ _ _ _ |- _ =>
      pose proof (Forall_Znth_elim _ _ _ 0 0 HF ltac:(lia)) as Hlit;
      unfold lit_wf_c in Hlit;
      pose proof (msolver_inv_literal_bound _ _ _ _ _ (msi_weak HM)) as Hbound;
      pose proof (msi_size HM) as Hsize;
      rewrite <- Hsize in Hbound;
      split_pures; dump_pre_spatial; change (0 - 0) with 0; lia
  end.

Ltac msat_reducedb_hdr_word_range_pure :=
  (LLM_pre_process ltac:(lia || int_auto)); dump_pre_spatial;
  unfold clause_hdr_word, msat_true; lia.

(* [H_lvl] is the `lvl = levels_entry`
   fact the call site binds; the existential witnesses stay at the call site
   because they only exist after the caller's own opener. *)
Ltac msat_propagate_binary_keep_close H_lvl :=
  split_pure_spatial;
  [ rewrite <- H_lvl;
    unfold solver_propagation_scan_core_at;
    unfold PtrArray.seg, stats_propagate_scan;
    set_String_name;
    cancel (&("l_Undef") # Char |-> 0);
    cancel;
    subst_all_strings;
    unfold Znth; cbn; csimpl;
    lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel
  | split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia ].

Tactic Notation "msat_order_unassigned_noop_return" :=
  match goal with
  | HZ : Znth (?v - 0) ?opos 0 <> -1,
    HP : order_unassigned_pre ?n ?v ?heap ?opos |- _ =>
      assert (Hpresent0 : Znth v opos 0 <> -1)
        by (replace (v - 0) with v in HZ by lia; exact HZ);
      assert (Hpost : order_unassigned_post n v heap opos heap opos)
        by (apply order_unassigned_post_noop__order_unassigned;
            [exact HP | exact Hpresent0]);
      Exists heap opos;
      (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..])
  end.

Tactic Notation "msat_analyze_learnt_undef_frame" constr(words)
  constr(Spend) constr(Rres) constr(learnt) constr(Mdb) :=
  Exists words Spend Rres learnt Mdb;
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]);
  apply store_ptr_undef_store_ptr.

Tactic Notation "msat_analyze_scan_inv_part" ident(H) :=
  unfold analyze_clause_scan_inv in H; tauto.

Tactic Notation "msat_analyze_scan_inv_part" ident(H) constr(Hphase) :=
  unfold analyze_clause_scan_inv in H; rewrite Hphase in H; cbn in H; tauto.

(* The tag step only rewrites heuristic and scratch fields, so the two
   [analysis_core_equiv]s [Hact] / [Hzero] and the seed shadow [Hseed] of the
   scan state carry over to [Mnext] unchanged. *)
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

Tactic Notation "bind_fact" constr(ty) "as" ident(na) :=
  match goal with H : ty |- _ => rename H into na end.

Tactic Notation "copy_fact" constr(ty) "as" ident(na) :=
  assert (na : ty) by assumption.

Ltac snv_set_cap_proj :=
  rewrite ?msolver_set_cap_core, ?msolver_set_cap_size, ?msolver_set_cap_cap,
          ?msolver_set_cap_qtail, ?msolver_set_cap_activity,
          ?msolver_set_cap_tags, ?msolver_set_cap_reason_words,
          ?msolver_set_cap_orderpos, ?msolver_set_cap_order,
          ?msolver_set_cap_wm.

Ltac snv_sift_proj :=
  rewrite ?msolver_sift_core, ?msolver_sift_size, ?msolver_sift_cap,
          ?msolver_sift_qtail, ?msolver_sift_reason_words,
          ?msolver_sift_tags, ?msolver_sift_activity, ?msolver_sift_wm,
          ?msolver_sift_orderpos, ?msolver_sift_order,
          ?mt_assigns_add_var, ?mt_levels_add_var, ?mt_trail_add_var.

Ltac cn_pin_learnt sel := assert (sel = 1) by lia; subst sel; cn_at_learnt.

Ltac cn_pin_prob sel := assert (sel = 0) by lia; subst sel; cn_at_prob.

Lemma msat_first_two_lits_wf : forall n words,
  Forall (lit_wf_c n) words -> 2 <= Zlength words ->
  lit_wf_c n (Znth 0 words 0) /\ lit_wf_c n (Znth 1 words 0) /\
  lit_wf_c n (lit_neg_c (Znth 0 words 0)) /\
  lit_wf_c n (lit_neg_c (Znth 1 words 0)).
Proof.
  intros n words Hall Hlen.
  assert (H0 : lit_wf_c n (Znth 0 words 0))
    by (apply Forall_lit_wf_Znth; [exact Hall | lia]).
  assert (H1 : lit_wf_c n (Znth 1 words 0))
    by (apply Forall_lit_wf_Znth; [exact Hall | lia]).
  split; [exact H0 |]. split; [exact H1 |].
  split; apply lit_neg_c_wf; assumption.
Qed.

Lemma lit_neg_c_var_neq : forall a b,
  lit_var_c a <> lit_var_c b -> lit_neg_c a <> lit_neg_c b.
Proof.
  intros a b Hvar Heq. apply Hvar.
  rewrite <- (lit_var_c_neg a), <- (lit_var_c_neg b), Heq. reflexivity.
Qed.

(* Substitutes every call result that names a negated literal or a literal
   tag, so watch-list indices and watch words read as expressions over the
   clause words. *)
Ltac msat_subst_lit_retvals :=
  repeat match goal with
    | H : ?x = lit_neg_c _ |- _ => is_var x; subst x
    | H : ?x = tag_of_lit _ |- _ => is_var x; subst x
    end.

(* The `In` pure side conditions of [clause_remove]: the watch word of the
   clause is in the watch list of a negated first-two literal, possibly after
   the other watch list has been rewritten.  [long_clause] says whether the
   clause has more than two literals, which decides the watch word. *)
Tactic Notation "msat_clause_remove_watch_in_pure" constr(long_clause) :=
  lazymatch goal with
  | Hready : clause_remove_ready ?n ?c ?words ?wm ?stats |- _ =>
    let Hr := fresh "Hready_parts" in
    let Hlen := fresh "Hclause_min_length" in
    let Hvar := fresh "Hvars" in
    let Hwm := fresh "Hwm_length" in
    let Hin0 := fresh "Hin0" in
    let Hin1 := fresh "Hin1" in
    let Hneq := fresh "Hneg_neq" in
    let Hb := fresh "Hlong_clause" in
    pose proof Hready as Hr;
    unfold clause_remove_ready in Hr;
    destruct Hr as (Hlen & _ & Hvar & Hwm & _ & Hin0 & Hin1);
    pose proof (lit_neg_c_var_neq _ _ Hvar) as Hneq;
    repeat match goal with
      | H : _ = clause_hdr_word _ (Zlength _) ÷ 2 |- _ =>
        rewrite clause_hdr_word_quot2__clause_cmp in H by apply Zlength_nonneg
      end;
    assert (Hb : (2 <? Zlength words)%Z = long_clause) by
      (lazymatch long_clause with
       | true => apply Z.ltb_lt; lia
       | false => apply Z.ltb_ge; lia
       end);
    unfold clause_watch_word in Hin0, Hin1;
    rewrite Hb in Hin0, Hin1;
    msat_subst_lit_retvals;
    dump_pre_spatial;
    first
      [ exact Hin0
      | exact Hin1
      | rewrite Znth_replace_Znth_Diff by lia; exact Hin1 ]
  end.
