From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_analysis_core solver_qcp_state_search_core.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** ** Clause-pointer parity. *)

Lemma clause_ptr_even : forall c, c mod 2 = 0 -> Z.even c = true.
Proof.
  intros c H. apply Z.even_spec. exists (c / 2).
  pose proof (Z.div_mod c 2 ltac:(lia)) as Hd. lia.
Qed.

Lemma clause_ptr_mod2 : forall c, Z.even c = true -> c mod 2 = 0.
Proof.
  intros c H. apply Z.even_spec in H. destruct H as [m ->].
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.


(** The header word round-trips through MiniSat's two accessors. *)
Lemma Zdiv2_pack : forall q r, 0 <= r < 2 -> (2 * q + r) / 2 = q.
Proof.
  intros q r Hr. replace (2 * q + r) with (q * 2 + r) by lia.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma Zmod2_pack : forall q r, 0 <= r < 2 -> (2 * q + r) mod 2 = r.
Proof.
  intros q r Hr. replace (2 * q + r) with (r + q * 2) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma clause_hdr_word_div2 : forall learnt size,
  0 <= size -> clause_hdr_word learnt size / 2 = size.
Proof.
  intros learnt size _. unfold clause_hdr_word.
  destruct learnt; apply Zdiv2_pack; lia.
Qed.

Lemma clause_hdr_word_nonneg : forall learnt size,
  0 <= size -> 0 <= clause_hdr_word learnt size.
Proof. intros. unfold clause_hdr_word. destruct learnt; lia. Qed.


(** The signed [lbool] value which makes a packed literal true. *)
Definition packed_lit_satisfying_value (l : Z) : Z :=
  1 - 2 * lit_sign_c l.

Definition clause_simplify_scan_inv
    (n : Z) (lits assigns : list Z) (i : Z) : Prop :=
  0 <= i <= Zlength lits /\
  Zlength assigns = n /\
  Forall (lit_wf_c n) lits /\
  Forall lbool_cell assigns /\
  (forall j, 0 <= j < i ->
     Znth (lit_var_c (Znth j lits 0)) assigns 0 <>
       packed_lit_satisfying_value (Znth j lits 0)).

Definition clause_simplify_result
    (lits assigns : list Z) (ret : Z) : Prop :=
  (ret = 1 /\ exists i, 0 <= i < Zlength lits /\
     Znth (lit_var_c (Znth i lits 0)) assigns 0 =
       packed_lit_satisfying_value (Znth i lits 0)) \/
  (ret = -1 /\ forall i, 0 <= i < Zlength lits ->
     Znth (lit_var_c (Znth i lits 0)) assigns 0 <>
       packed_lit_satisfying_value (Znth i lits 0)).

Definition wmap_remove_first
    (wm : wmap) (index word found : Z) : wmap :=
  replace_Znth index
    (remove_nth found (Znth index wm [])) wm.

Definition clause_remove_ready
    (n c : Z) (lits : list Z) (wm : wmap) (stats : list Z) : Prop :=
  2 <= Zlength lits /\ Forall (lit_wf_c n) lits /\
  lit_var_c (Znth 0 lits 0) <> lit_var_c (Znth 1 lits 0) /\
  Zlength wm = 2 * n /\
  Zlength stats = 11 /\
  In (clause_watch_word c lits (Znth 1 lits 0))
     (Znth (lit_neg_c (Znth 0 lits 0)) wm []) /\
  In (clause_watch_word c lits (Znth 0 lits 0))
     (Znth (lit_neg_c (Znth 1 lits 0)) wm []).

Definition clause_remove_result
    (c : Z) (lits : list Z) (wm wm' : wmap) : Prop :=
  exists found0 found1 wm0,
    first_occurrence
      (clause_watch_word c lits (Znth 1 lits 0))
      (Znth (lit_neg_c (Znth 0 lits 0)) wm []) found0 /\
    wm0 = wmap_remove_first wm (lit_neg_c (Znth 0 lits 0))
            (clause_watch_word c lits (Znth 1 lits 0)) found0 /\
    first_occurrence
      (clause_watch_word c lits (Znth 0 lits 0))
      (Znth (lit_neg_c (Znth 1 lits 0)) wm0 []) found1 /\
    wm' = wmap_remove_first wm0 (lit_neg_c (Znth 1 lits 0))
            (clause_watch_word c lits (Znth 0 lits 0)) found1.

Definition clause_unlocked_words (c : Z) (reasons : list Z) : Prop :=
  Forall (fun r => r <> c) reasons.

Lemma prob_db_app : forall d1 d2,
  prob_db d1 -> prob_db d2 -> prob_db (d1 ++ d2).
Proof. intros d1 d2 H1 H2. apply Forall_app. split; assumption. Qed.

(** Sorting is a heuristic-only permutation.  No ordering theorem is exposed:
    MiniSat's comparator deliberately returns [1], not [0], on aliases. *)
Definition learnt_sort_domain (db : dbmap) (words : list Z) : Prop :=
  learnt_db db /\ Permutation words (map fst db).

(** Recursive sorting works on proper subarrays, so its domain records only
    that every segment pointer belongs to the one immutable learnt database.
    Exact whole-database provenance remains confined to [sort]. *)
Definition learnt_sort_segment_domain (db : dbmap) (words : list Z) : Prop :=
  Forall (fun p => In p (db_words db)) words.

Definition learnt_sort_context
    (db : dbmap) (activities : list fp32) : Prop :=
  NoDup (db_words db) /\
  Zlength activities = Zlength db /\
  Forall msat_fp32_nonnegative activities.

Definition selectionsort_outer_inv
    (db : dbmap) (activities : list fp32)
    (origin current : list Z) (size i : Z) : Prop :=
  learnt_sort_context db activities /\
  learnt_sort_segment_domain db origin /\
  Permutation origin current /\
  Zlength current = size /\ 0 <= i <= Z.max 0 (size - 1).

Definition selectionsort_inner_inv
    (db : dbmap) (activities : list fp32) (origin current : list Z)
    (size i j best : Z) : Prop :=
  learnt_sort_context db activities /\
  learnt_sort_segment_domain db origin /\
  Permutation origin current /\
  Zlength current = size /\
  0 <= i < size /\ i <= best < j /\ i + 1 <= j <= size.

Definition sortrnd_partition_inv
    (db : dbmap) (activities : list fp32) (origin current : list Z)
    (size pivot i j : Z) : Prop :=
  learnt_sort_segment_domain db origin /\
  learnt_sort_context db activities /\
  In pivot (db_words db) /\
  Permutation origin current /\
  Zlength current = size /\
  -1 <= i < j /\ 0 < j <= size /\
  exists L R,
    i < L < size /\ L <= j /\ 0 <= R < j /\
    learnt_cmp_stop db activities (Znth L current 0) pivot /\
    learnt_cmp_stop db activities pivot (Znth R current 0).

Definition sortrnd_left_scan_inv
    (db : dbmap) (activities : list fp32) (origin current : list Z)
    (size pivot i j : Z) : Prop :=
  sortrnd_partition_inv db activities origin current size pivot i j.

Definition sortrnd_right_scan_inv
    (db : dbmap) (activities : list fp32) (origin current : list Z)
    (size pivot i j : Z) : Prop :=
  learnt_sort_segment_domain db origin /\
  learnt_sort_context db activities /\
  In pivot (db_words db) /\
  Permutation origin current /\
  Zlength current = size /\
  0 <= i < size /\ 0 < j <= size /\
  learnt_cmp_stop db activities (Znth i current 0) pivot /\
  exists R, 0 <= R < j /\
    learnt_cmp_stop db activities pivot (Znth R current 0).

Definition sortrnd_split
    (db : dbmap) (origin current left right : list Z)
    (size cut : Z) : Prop :=
  Permutation origin current /\ Zlength current = size /\
  0 <= cut <= size /\ current = left ++ right /\
  Zlength left = cut /\ Zlength right = size - cut /\
  learnt_sort_segment_domain db left /\
  learnt_sort_segment_domain db right.

(** A database clause can be opened without conflating it with the separate
    two-cell binary scratch object.  The remainder remembers which of the
    problem/learnt lists contained the object and owns every other object;
    [clause_db_pair_focus] adds the selected object itself. *)
Definition clause_db_pair_contents
    (prob learnt : dbmap) (p : Z) (lits : list Z) : Prop :=
  exists co : clause_obj,
    In (p, co) (prob ++ learnt) /\ co_lits co = lits.

Definition clause_db_pair_focus
    (prob learnt : dbmap) (p : Z) (lits : list Z) : Assertion :=
  EX is_learnt : bool,
    MiniSatClause.rep p is_learnt lits **
    clause_db_pair_remainder prob learnt p is_learnt lits.

Lemma clause_db_rep_nil : clause_db_rep nil = emp.
Proof. reflexivity. Qed.

Lemma clause_db_rep_cons : forall e rest,
  clause_db_rep (e :: rest)
  = MiniSatClause.rep (fst e) (co_learnt (snd e)) (co_lits (snd e)) **
    clause_db_rep rest.
Proof. reflexivity. Qed.

Lemma clause_db_rep_app_elim : forall db1 db2,
  clause_db_rep (db1 ++ db2) |-- clause_db_rep db1 ** clause_db_rep db2.
Proof.
  induction db1 as [| e db1 IH]; intros db2; simpl.
  - (Intros; cancel).
  - sep_apply IH. msat_entailer_with lia.
Qed.

(** Owning the database supplies the pointer half of [db_wf]
    ([0 < p] and [Z.even p]) for every entry, so [db_wf]'s evenness conjunct
    -- which nothing else supplies -- is readable off the
    spatial bundle. *)
Lemma clause_db_rep_ptrs : forall entries,
  clause_db_rep entries
  |-- “ Forall (fun e => 0 < fst e /\ Z.even (fst e) = true) entries ” &&
      clause_db_rep entries.
Proof.
  induction entries as [| e entries IH].
  - rewrite clause_db_rep_nil.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. constructor.
  - rewrite clause_db_rep_cons at 1.
    sep_apply IH.
    rewrite clause_db_rep_cons.
    unfold MiniSatClause.rep at 1.
    Intros_p H. Intros_p H0.
    split_pure_spatial.
    + unfold MiniSatClause.rep.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial. exact H0.
    + dump_pre_spatial.
      constructor; [| exact H].
      split; [tauto | apply clause_ptr_even; tauto].
Qed.

(** A newly allocated clause cannot alias an already owned clause object:
    both would own the same initialized-or-undefined header cell. *)
Lemma MiniSatClause_undef_rep_distinct : forall c fresh_learnt size p learnt lits,
  MiniSatClause.undef c fresh_learnt size ** MiniSatClause.rep p learnt lits
  |-- “ c <> p ” &&
      (MiniSatClause.undef c fresh_learnt size ** MiniSatClause.rep p learnt lits).
Proof.
  intros c fresh_learnt size p learnt lits.
  unfold MiniSatClause.undef at 1.
  Intros_p Hc.
  unfold MiniSatClause.rep at 1.
  Intros_p Hp.
  destruct (Z.eq_dec c p) as [Heq | Hneq].
  - subst p.
    sep_apply (store_int_undef_store_int
      (clause_hdr_addr c) (clause_hdr_word learnt (Zlength lits))).
    sep_apply (dup_undef_store_int (clause_hdr_addr c)).
    Intros_p Hfalse.
    contradiction.
  - unfold MiniSatClause.undef, MiniSatClause.rep.
    msat_entailer_with lia.
Qed.


Lemma MiniSatClause_undef_binary_distinct : forall c fresh_learnt size p words,
  MiniSatClause.undef c fresh_learnt size ** binary_scratch_rep p words
  |-- “ c <> p ” &&
      (MiniSatClause.undef c fresh_learnt size ** binary_scratch_rep p words).
Proof.
  intros c fresh_learnt size p [|x xs].
  - unfold binary_scratch_rep at 1.
    destruct (Z.eq_dec c p) as [Heq | Hneq].
    + subst p. unfold MiniSatClause.undef at 1. Intros.
      sep_apply_l_atomic (store_int_undef_store_int (clause_hdr_addr c) (clause_hdr_word false 2)).
      sep_apply_l_atomic (dup_undef_store_int (clause_hdr_addr c)).
      Intros_p Hfalse.
      contradiction.
    + unfold binary_scratch_rep. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - apply MiniSatClause_undef_rep_distinct.
Qed.

(** Iterating the same separation argument extracts non-membership from the
    complete old database without trusting the allocator with ghost state. *)
Lemma MiniSatClause_undef_db_distinct : forall c fresh_learnt size db,
  MiniSatClause.undef c fresh_learnt size ** clause_db_rep db
  |-- “ ~ In c (map fst db) ” &&
      (MiniSatClause.undef c fresh_learnt size ** clause_db_rep db).
Proof.
  intros c fresh_learnt size db. induction db as [| [p co] db IH].
  - rewrite !clause_db_rep_nil. split_pure_spatial.
    + cancel (MiniSatClause.undef c fresh_learnt size).
    + dump_pre_spatial. simpl. tauto.
  - change (clause_db_rep ((p, co) :: db)) with
      (MiniSatClause.rep p (co_learnt co) (co_lits co) ** clause_db_rep db) at 1.
    sep_apply (MiniSatClause_undef_rep_distinct
      c fresh_learnt size p (co_learnt co) (co_lits co)).
    Intros_p Hcp.
    sep_apply IH.
    Intros_p Htail.
    assert (Hnotin : ~ In c (map fst ((p, co) :: db))).
    { simpl. intros [Hpc | Hin].
      - apply Hcp. symmetry. exact Hpc.
      - apply Htail. exact Hin. }
    rewrite clause_db_rep_cons.
    split_pure_spatial.
    + cbn [fst snd].
      cancel (MiniSatClause.undef c fresh_learnt size).
      cancel (MiniSatClause.rep p (co_learnt co) (co_lits co)).
      cancel (clause_db_rep db).
    + dump_pre_spatial. exact Hnotin.
Qed.

Definition stats_set_decisions        (v : Z) (l : list Z) : list Z := replace_Znth 1 v l.

Definition stats_set_propagations     (v : Z) (l : list Z) : list Z := replace_Znth 2 v l.

Definition stats_set_inspects         (v : Z) (l : list Z) : list Z := replace_Znth 3 v l.

Definition stats_set_conflicts        (v : Z) (l : list Z) : list Z := replace_Znth 4 v l.

Definition stats_set_clauses          (v : Z) (l : list Z) : list Z := replace_Znth 5 v l.

Definition stats_set_clauses_literals (v : Z) (l : list Z) : list Z := replace_Znth 6 v l.

Definition stats_set_learnts          (v : Z) (l : list Z) : list Z := replace_Znth 7 v l.

Definition stats_set_learnts_literals (v : Z) (l : list Z) : list Z := replace_Znth 8 v l.

(* Runtime configuration updates share all solver storage and logical state. *)
Definition msolver_runtime_update (M : msolver)
    (model : list Z)
    (var_inc : fp64)
    (var_decay : fp64)
    (cla_inc : fp32)
    (cla_decay : fp32)
    (progress : fp64)
    (stats : list Z) : msolver := {|
  ms_size := ms_size M;
  ms_cap := ms_cap M;
  ms_qtail := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending := ms_capacity_root_propagation_pending M;
  ms_core := ms_core M;
  ms_root_level := ms_root_level M;
  ms_reason_words := ms_reason_words M;
  ms_reason_of := ms_reason_of M;
  ms_prob := ms_prob M;
  ms_learnt := ms_learnt M;
  ms_binary := ms_binary M;
  ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M;
  ms_activity := ms_activity M;
  ms_orderpos := ms_orderpos M;
  ms_order := ms_order M;
  ms_model := model;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M;
  ms_stack := ms_stack M;
  ms_var_inc := var_inc;
  ms_var_decay := var_decay;
  ms_cla_inc := cla_inc;
  ms_cla_decay := cla_decay;
  ms_random_seed := ms_random_seed M;
  ms_progress := progress;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M;
  ms_stats := stats
|}.

Definition msolver_resume (M : msolver) : msolver :=
  msolver_propagation_update M (ms_cap M) (ms_qtail M) (0) (mt_set_qhead (ms_core M) (ms_capacity_pending_qhead
    M)) (ms_reason_words M) (ms_reason_of M) (ms_prob M) (ms_learnt M) (ms_binary_lits M) (ms_wm M)
    (ms_simpdb_props M) (ms_stats M).

(** The mutable ghost projection while [solver_propagate] is scanning one
    watcher vector.  The source vector is spatially open during the scan, so
    callers supply the evolving trail/reason, database, watcher-map and
    bookkeeping components; every field outside propagation's footprint is
    definitionally inherited from the state at the outer-iteration entry. *)
Definition msolver_propagation_scan
    (M : msolver) (core : mtrail) (qtail : Z)
    (reason_words : list Z) (reason_of : Z -> option clause)
    (prob learnt : dbmap) (wm : wmap)
    (simpdb_props propagation_count : Z) : msolver :=
  msolver_propagation_update M (ms_cap M) (qtail) (ms_capacity_root_propagation_pending M) (core) (reason_words)
    (reason_of) (prob) (learnt) (ms_binary_lits M) (wm) (simpdb_props) (stats_set_propagations
    propagation_count (ms_stats M)).

Definition msolver_propagation_scan_begin
    (M : msolver) (simpdb_props propagation_count : Z) : msolver :=
  msolver_propagation_scan M
    (mt_set_qhead (ms_core M) (mt_qhead (ms_core M) + 1))
    (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    (ms_prob M) (ms_learnt M) (ms_wm M)
    simpdb_props propagation_count.

Definition msolver_propagation_enqueue_success
    (M : msolver) (l reason_word : Z) (reason_clause : clause) : msolver :=
  let v := lit_var_c l in
  if Znth v (mt_assigns (ms_core M)) 0 =? 0 then
    msolver_propagation_overlay M
      (mt_enqueue (ms_core M) l) (ms_qtail M + 1)
      (replace_Znth v reason_word (ms_reason_words M))
      (sat_function_update (ms_reason_of M) v (Some reason_clause))
      (ms_prob M) (ms_learnt M) (ms_binary_lits M)
      (ms_wm M) (ms_stats M)
  else M.

(** Exact bookkeeping projection after [act_clause_bump] and the two
    unsigned learned-clause counters.  Every semantic field, including the
    saved model and its capacity, is inherited from [M]. *)
Definition msolver_with_cla_inc_stats
    (M : msolver) (cla_inc : fp32) (stats : list Z) : msolver := {|
  ms_size := ms_size M; ms_cap := ms_cap M; ms_qtail := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending :=
    ms_capacity_root_propagation_pending M;
  ms_core := ms_core M; ms_root_level := ms_root_level M;
  ms_reason_words := ms_reason_words M; ms_reason_of := ms_reason_of M;
  ms_prob := ms_prob M; ms_learnt := ms_learnt M;
  ms_binary := ms_binary M; ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M; 
  ms_activity := ms_activity M; ms_orderpos := ms_orderpos M;
  ms_order := ms_order M; 
  ms_model := ms_model M;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M; 
  ms_stack := ms_stack M; 
  ms_var_inc := ms_var_inc M; ms_var_decay := ms_var_decay M;
  ms_cla_inc := cla_inc; ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M; ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M; ms_stats := stats
|}.

Definition msolver_with_model
    (M : msolver) (model : list Z) : msolver := {|
  ms_size := ms_size M; ms_cap := ms_cap M; ms_qtail := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending :=
    ms_capacity_root_propagation_pending M;
  ms_core := ms_core M; ms_root_level := ms_root_level M;
  ms_reason_words := ms_reason_words M; ms_reason_of := ms_reason_of M;
  ms_prob := ms_prob M; ms_learnt := ms_learnt M;
  ms_binary := ms_binary M; ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M; 
  ms_activity := ms_activity M; ms_orderpos := ms_orderpos M;
  ms_order := ms_order M; 
  ms_model := model;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M; 
  ms_stack := ms_stack M; 
  ms_var_inc := ms_var_inc M; ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M; ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M; ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M; ms_stats := ms_stats M
|}.

(** Exact transient after the search decision counter and [order_select].
    Only heap metadata, random seed, and fact-free statistics may differ. *)
Definition msolver_search_select
    (M : msolver) (orderpos order : list Z)
    (seed : fp64) (stats : list Z) : msolver := {|
  ms_size := ms_size M; ms_cap := ms_cap M; ms_qtail := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending :=
    ms_capacity_root_propagation_pending M;
  ms_core := ms_core M; ms_root_level := ms_root_level M;
  ms_reason_words := ms_reason_words M; ms_reason_of := ms_reason_of M;
  ms_prob := ms_prob M; ms_learnt := ms_learnt M;
  ms_binary := ms_binary M; ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M; 
  ms_activity := ms_activity M; ms_orderpos := orderpos;
  ms_order := order; 
  ms_model := ms_model M;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M; 
  ms_stack := ms_stack M; 
  ms_var_inc := ms_var_inc M; ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M; ms_cla_decay := ms_cla_decay M;
  ms_random_seed := seed; ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M; ms_stats := stats
|}.

Definition msolver_reorder_learnts (M : msolver) (learnt : dbmap) : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    (ms_prob M) learnt (ms_binary_lits M)
    (ms_wm M) (ms_stats M).

Definition msolver_set_root (M : msolver) (root : Z) : msolver :=
  msolver_core_heap_update M (ms_core M) (ms_qtail M)
    (ms_reason_words M) (ms_reason_of M)
    (ms_orderpos M) (ms_order M) root.

Definition msolver_heap_project
    (M : msolver) (orderpos order : list Z) : msolver :=
  msolver_core_heap_update M (ms_core M) (ms_qtail M)
    (ms_reason_words M) (ms_reason_of M) orderpos order
    (ms_root_level M).

(* Analysis updates preserve the database and trail while replacing scratch and heap components. *)
Definition msolver_analysis_update (M : msolver)
    (activity : list fp64)
    (orderpos : list Z)
    (order : list Z)
    (tags : list Z)
    (tagged : list Z)
    (stack : list Z)
    (var_inc : fp64) : msolver := {|
  ms_size := ms_size M;
  ms_cap := ms_cap M;
  ms_qtail := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending := ms_capacity_root_propagation_pending M;
  ms_core := ms_core M;
  ms_root_level := ms_root_level M;
  ms_reason_words := ms_reason_words M;
  ms_reason_of := ms_reason_of M;
  ms_prob := ms_prob M;
  ms_learnt := ms_learnt M;
  ms_binary := ms_binary M;
  ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M;
  ms_activity := activity;
  ms_orderpos := orderpos;
  ms_order := order;
  ms_model := ms_model M;
  ms_tags := tags;
  ms_tagged := tagged;
  ms_stack := stack;
  ms_var_inc := var_inc;
  ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M;
  ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M;
  ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M;
  ms_stats := ms_stats M
|}.

Definition msolver_scratch_update
    (M : msolver) (tags tagged : list Z)
    (stack : list Z) : msolver :=
  msolver_analysis_update M (ms_activity M) (ms_orderpos M) (ms_order M) (tags) (tagged) (stack) (ms_var_inc M).

(** A tagging step changes tags, the tagged vector and activity/heap state.
    It preserves the CDCL view, database, core and analysis frame.
*)
Definition analyze_tag_step_msolver
    (M : msolver) (tags tagged : list Z)
    (activity : list fp64) (orderpos order : list Z)
    (var_inc : fp64) : msolver :=
  msolver_analysis_update M (activity) (orderpos) (order) (tags) (tagged) (ms_stack M) (var_inc).

Lemma analyze_tag_step_msolver_proj :
  forall M tags tagged activity orderpos order var_inc,
    let M' := analyze_tag_step_msolver M tags tagged
                activity orderpos order var_inc in
    ms_tags M' = tags /\ ms_tagged M' = tagged /\
    ms_activity M' = activity /\
    ms_orderpos M' = orderpos /\ ms_order M' = order /\
    ms_var_inc M' = var_inc /\
    ms_size M' = ms_size M /\ ms_cap M' = ms_cap M /\
    ms_qtail M' = ms_qtail M /\ ms_core M' = ms_core M /\
    ms_reason_words M' = ms_reason_words M /\
    ms_reason_of M' = ms_reason_of M /\
    ms_stack M' = ms_stack M /\
    ms_stats M' = ms_stats M /\ ms_cla_inc M' = ms_cla_inc M.
Proof. intros. repeat split; reflexivity. Qed.

(** The identity law: retagging with the fields already in place is a no-op.
    This is what collapses a constructed [Mtag] back to [Mcur] on the
    fall-through arms of the analysis loop. *)
Lemma analyze_tag_step_msolver_id : forall M : msolver,
  analyze_tag_step_msolver M (ms_tags M) (ms_tagged M)
    (ms_activity M) (ms_orderpos M) (ms_order M) (ms_var_inc M) = M.
Proof. intros M. destruct M. reflexivity. Qed.

Definition msolver_simpdb_update
    (M : msolver) (simpdb_assigns simpdb_props : Z) : msolver := {|
  ms_size := ms_size M; ms_cap := ms_cap M; ms_qtail := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending :=
    ms_capacity_root_propagation_pending M;
  ms_core := ms_core M; ms_root_level := ms_root_level M;
  ms_reason_words := ms_reason_words M; ms_reason_of := ms_reason_of M;
  ms_prob := ms_prob M; ms_learnt := ms_learnt M;
  ms_binary := ms_binary M; ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M; 
  ms_activity := ms_activity M; ms_orderpos := ms_orderpos M;
  ms_order := ms_order M; 
  ms_model := ms_model M;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M; 
  ms_stack := ms_stack M; 
  ms_var_inc := ms_var_inc M; ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M; ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M; ms_progress := ms_progress M;
  ms_simpdb_assigns := simpdb_assigns;
  ms_simpdb_props := simpdb_props;
  ms_verbosity := ms_verbosity M; ms_stats := ms_stats M
|}.

Fixpoint clear_indices (xs tags : list Z) : list Z :=
  match xs with
  | [] => tags
  | x :: rest => clear_indices rest (replace_Znth x 0 tags)
  end.

Definition analysis_tags_exact
    (n : Z) (tags tagged : list Z) : Prop :=
  Zlength tags = n /\ NoDup tagged /\
  Forall (fun v => 0 <= v < n) tagged /\
  Forall (fun z => z = 0 \/ z = 1) tags /\
  (forall v, 0 <= v < n ->
     (Znth v tags 0 = 1 <-> In v tagged)).

(** Parent-owned freed-hole state for learned-database compaction.  The live
    database is exactly the already-kept prefix plus the unvisited suffix of
    the still-full vector.  Cells in [[j,i)) may contain stale freed pointers
    but are never dereferenced again and are discarded by the final resize. *)
Definition db_compaction_inv
    (M : msolver) (words : list Z) (i j : Z) : Prop :=
  0 <= j /\ j <= i /\ i <= Zlength words /\
  map fst (ms_learnt M) =
    sublist 0 j words ++ sublist i (Zlength words) words.

Definition db_compaction_step (M : msolver) (c : Z) (M' : msolver) : Prop :=
  (M' = M \/
   exists wm stats,
     M' = msolver_remove_clause M true c wm stats) /\
  ms_model M' = ms_model M /\
  ms_cla_decay M' = ms_cla_decay M.

(** Downward clearing progress for the first cancellation loop. *)
Definition cancel_clear_loop_inv
    (M : msolver) (level c : Z) (assigns reasons : list Z) : Prop :=
  let trail := mt_trail (ms_core M) in
  let qtail := ms_qtail M in
  let bound := Znth level (mt_lim (ms_core M)) 0 in
  0 <= level < Zlength (mt_lim (ms_core M)) /\
  bound - 1 <= c < qtail /\
  assigns = clear_vars (sublist (c + 1) qtail trail)
                        (mt_assigns (ms_core M)) /\
  reasons = clear_vars (sublist (c + 1) qtail trail)
                        (ms_reason_words M).

(** Progress of the second loop: the cleared arrays are already final and
    [[c+1,qhead)) has been restored to the heap. *)
Definition cancel_reinsert_loop_inv
    (M : msolver) (level c : Z)
    (assigns reasons order orderpos : list Z)
    : Prop :=
  let trail := mt_trail (ms_core M) in
  let qhead := mt_qhead (ms_core M) in
  let bound := Znth level (mt_lim (ms_core M)) 0 in
  assigns = clear_vars (zdrop bound trail) (mt_assigns (ms_core M)) /\
  reasons = clear_vars (zdrop bound trail) (ms_reason_words M) /\
  0 <= level < Zlength (mt_lim (ms_core M)) /\
  bound - 1 <= c < qhead /\
  heap_wf (ms_size M) (heap_of_lists order orderpos) /\
  incl (ms_order M) order /\
  cancel_reinserted (heap_of_lists order orderpos)
                      trail (c + 1) qhead.

Definition cancel_bound_ready (M : msolver) (level : Z) : Prop :=
  Zlength (mt_lim (ms_core M)) <= level \/
  Znth level (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M).

Definition msolver_propagation_binary_conflict
    (M : msolver) (implied propagator : Z) : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    (ms_prob M) (ms_learnt M) [implied; lit_neg_c propagator]
    (ms_wm M) (ms_stats M).

(** The common scan exit changes only the accumulated inspect statistic. *)
Definition msolver_propagation_scan_finish
    (M : msolver) (inspect_delta : Z) : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    (ms_prob M) (ms_learnt M) (ms_binary_lits M)
    (ms_wm M)
    (stats_set_inspects (MiniSatTarget.lo64
                    (stats_inspects (ms_stats M) + inspect_delta)) (ms_stats M)).

Lemma msolver_propagation_scan_begin_qhead :
  forall M simpdb_props propagation_count,
    mt_qhead (ms_core
      (msolver_propagation_scan_begin M simpdb_props propagation_count)) =
    mt_qhead (ms_core M) + 1.
Proof. reflexivity. Qed.

(** Of the six fields a tagging step mutates, only [ms_orderpos],
    [ms_activity] and [ms_tags] occur in [solver_shape]; [ms_tagged],
    [ms_order] and [ms_var_inc] do not appear at all.  The
    shape obligation at the tagged state is therefore exactly three length
    side conditions. *)
Lemma solver_shape_analyze_tag_step :
  forall M tags tagged activity orderpos order var_inc,
    solver_shape M ->
    Zlength tags = ms_size M ->
    Zlength activity = ms_size M ->
    Zlength orderpos = ms_size M ->
    solver_shape (analyze_tag_step_msolver M tags tagged
                    activity orderpos order var_inc).
Proof.
  intros M tags tagged activity orderpos order var_inc
         Hshape Htags Hact Hopos.
  unfold solver_shape, analyze_tag_step_msolver, msolver_analysis_update in *. cbn in *. tauto.
Qed.

Definition solver_size_cell (s n : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> n.

Definition solver_conflict_count_cell (s conflicts : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts") # UInt64 |-> conflicts.

(** The vector of resident problem clauses holds [l]. The contract of
    [solver_nclauses] in solver_qcp.h names [s->clauses] through this predicate,
    because it precedes the definition of [struct solver_t]. *)
Definition solver_clauses_rep (s : Z) (l : list Z) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "clauses") l.

Definition solver_ptrs_rep
    (s wl act asg opos rsn lvl trl bin tgs : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "wlists")   # Ptr |-> wl **
  &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
  &( s # "solver_t" ->ₛ "assigns")  # Ptr |-> asg **
  &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
  &( s # "solver_t" ->ₛ "reasons")  # Ptr |-> rsn **
  &( s # "solver_t" ->ₛ "levels")   # Ptr |-> lvl **
  &( s # "solver_t" ->ₛ "trail")    # Ptr |-> trl **
  &( s # "solver_t" ->ₛ "binary")   # Ptr |-> bin **
  &( s # "solver_t" ->ₛ "tags")     # Ptr |-> tgs.

(* Keep the outer watcher-table address public; inner vector allocations
   remain existential inside the existing representation. *)
Definition solver_rep_wl (s : Z) (M : msolver) (wl : Z) : Assertion :=
  EX lvl : Z, solver_rep_levels_wl_at s M wl lvl.

Definition solver_scalars_without_size_rep
    (s : Z) (M : msolver) : Assertion :=
  clause_new_scalars_frame s M.

Definition solver_vecs_without_model_rep
    (s : Z) (M : msolver) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)).

Definition solver_vecs_without_clauses_rep
    (s : Z) (M : msolver) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
           (ms_model M).

(** Exact full-solver remainder after removing only the assignment pointer
    and its live/undefined slices.  Supplying smaller scalar/vector bundles
    specializes the same footprint for model copying without a second large
    representation. *)
Definition solver_without_assigns_cells_at
    (s : Z) (M : msolver) (wl act opos rsn trl tgs lvl : Z) : Assertion :=
      (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
       &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
       &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
       &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
       &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
       &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
       &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
      (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
       solver_double_tail act (ms_size M) (ms_cap M) **
       IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
       solver_int_tail opos (ms_size M) (ms_cap M) **
       PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
       solver_ptr_tail rsn (ms_size M) (ms_cap M) **
       CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
       solver_char_tail tgs (ms_size M) (ms_cap M)) **
      solver_trail_array_rep M trl **
      wlists_rep wl (ms_size M) (ms_wm M) **
      clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
      binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
      stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M) **
      solver_levels_slice_at s M lvl.

Definition solver_without_assigns_frame_wl_at
    (s : Z) (M : msolver) (wl lvl : Z)
    (scalars vectors : Assertion) : Assertion :=
  “ solver_shape M ” &&
  (scalars ** solver_fp_rep s M ** vectors **
   (EX act opos rsn trl tgs : Z,
    solver_without_assigns_cells_at s M wl act opos rsn trl tgs lvl)).


Definition solver_solve_entry_rest_at
    (s : Z) (M : msolver) (lvl : Z) (wl : Z) : Assertion :=
  solver_without_assigns_frame_wl_at
    s M wl lvl (solver_scalars_rep s M)
    (solver_vecs_without_clauses_rep s M).

Definition solver_model_copy_frame_at
    (s : Z) (M : msolver) (lvl : Z) (wl : Z) : Assertion :=
  solver_without_assigns_frame_wl_at
    s M wl lvl (solver_scalars_without_size_rep s M)
    (solver_vecs_without_model_rep s M).

Definition solver_scalars_without_root_rep
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "simpdb_assigns")
    # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M.

Definition solver_simplify_lim_frame_at
    (s : Z) (M : msolver) (asg lvl : Z) (wl : Z) : Assertion :=
  solver_without_assigns_frame_wl_at
    s M wl lvl (solver_scalars_rep s M)
    (solver_vecs_without_lim_rep s M) **
  &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  solver_char_tail asg (ms_size M) (ms_cap M).

Definition solver_simplify_control_scalars_frame
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M.

(** Exact complement of the three simplify guard cells and the cached
    reasons pointer.  The reasons array remains owned by this frame. *)
Definition solver_simplify_control_frame_at
    (s : Z) (M : msolver) (asg lvl rsn : Z) (wl : Z) : Assertion :=
  “ solver_shape M ” &&
  (solver_simplify_control_scalars_frame s M **
   solver_fp_rep s M ** solver_vecs_rep s M **
   (EX act opos trl tgs : Z,
      (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
       &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
       &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
       &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
       &( s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
       &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
       &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
       &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
      solver_var_arrays_rep M act asg opos rsn lvl tgs **
      solver_trail_array_rep M trl **
      wlists_rep wl (ms_size M) (ms_wm M) **
      clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
      binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
      stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M))).

(** Exact remainder while installing the completed assumption prefix as the
    search root.  [root_level] and [trail_lim] stay visible for the single C
    assignment and its [solver_dlevel] read. *)
Definition solver_root_install_frame_at
    (s : Z) (M : msolver) (asg lvl : Z) (wl : Z) : Assertion :=
  solver_without_assigns_frame_wl_at
    s M wl lvl (solver_scalars_without_root_rep s M)
    (solver_vecs_without_lim_rep s M) **
  &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  solver_char_tail asg (ms_size M) (ms_cap M).

(** Pointer-indexed arrays and clauses kept stable while search updates its
    embedded scalar, vector and statistics bundles. *)
Definition solver_payload_cells (s : Z) (M : msolver) (wl : Z) : Assertion :=
  (EX act asg opos rsn trl tgs : Z,
      (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
       &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
       &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
       &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
       &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
       &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
       &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
       &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
      (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
       solver_double_tail act (ms_size M) (ms_cap M) **
       CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
       solver_char_tail asg (ms_size M) (ms_cap M) **
       IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
       solver_int_tail opos (ms_size M) (ms_cap M) **
       PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
       solver_ptr_tail rsn (ms_size M) (ms_cap M) **
       CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
       solver_char_tail tgs (ms_size M) (ms_cap M)) **
      solver_trail_array_rep M trl **
      wlists_rep wl (ms_size M) (ms_wm M) **
      clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
      binary_scratch_rep (ms_binary M) (ms_binary_lits M)).

Definition solver_search_payload
    (s : Z) (M : msolver)
    (wl : Z) (scalars fps vectors statistics : Assertion) : Assertion :=
  “ solver_shape M ” &&
  (scalars ** fps ** vectors ** statistics **
   solver_payload_cells s M wl).

Definition solver_search_bundle_at
    (s : Z) (M : msolver) (lvl wl : Z)
    (scalars fps vectors statistics : Assertion) : Assertion :=
  solver_search_payload s M wl scalars fps vectors statistics **
  solver_levels_slice_at s M lvl.

Definition solver_fp_without_decays_rep (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "var_inc") # Double |-> ms_var_inc M **
  &( s # "solver_t" ->ₛ "cla_inc") # Float |-> ms_cla_inc M **
  &( s # "solver_t" ->ₛ "random_seed") # Double |-> ms_random_seed M **
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M.

Definition stats_without_starts_rep (p : Z) (st : list Z) : Assertion :=
  “ Zlength st = 11 ” &&
  (&( p # "stats_t" ->ₛ "decisions") # UInt64 |-> stats_decisions st **
   &( p # "stats_t" ->ₛ "propagations") # UInt64 |-> stats_propagations st **
   &( p # "stats_t" ->ₛ "inspects") # UInt64 |-> stats_inspects st **
   &( p # "stats_t" ->ₛ "conflicts") # UInt64 |-> stats_conflicts st **
   &( p # "stats_t" ->ₛ "clauses") # UInt64 |-> stats_clauses st **
   &( p # "stats_t" ->ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
   &( p # "stats_t" ->ₛ "learnts") # UInt64 |-> stats_learnts st **
   &( p # "stats_t" ->ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st **
   &( p # "stats_t" ->ₛ "max_literals") # UInt64 |-> stats_max_literals st **
   &( p # "stats_t" ->ₛ "tot_literals") # UInt64 |-> stats_tot_literals st).

Definition stats_without_conflicts_rep (p : Z) (st : list Z) : Assertion :=
  “ Zlength st = 11 ” &&
  (&( p # "stats_t" ->ₛ "starts") # UInt64 |-> stats_starts st **
   &( p # "stats_t" ->ₛ "decisions") # UInt64 |-> stats_decisions st **
   &( p # "stats_t" ->ₛ "propagations") # UInt64 |-> stats_propagations st **
   &( p # "stats_t" ->ₛ "inspects") # UInt64 |-> stats_inspects st **
   &( p # "stats_t" ->ₛ "clauses") # UInt64 |-> stats_clauses st **
   &( p # "stats_t" ->ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
   &( p # "stats_t" ->ₛ "learnts") # UInt64 |-> stats_learnts st **
   &( p # "stats_t" ->ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st **
   &( p # "stats_t" ->ₛ "max_literals") # UInt64 |-> stats_max_literals st **
   &( p # "stats_t" ->ₛ "tot_literals") # UInt64 |-> stats_tot_literals st).

Definition stats_without_decisions_rep (p : Z) (st : list Z) : Assertion :=
  “ Zlength st = 11 ” &&
  (&( p # "stats_t" ->ₛ "starts") # UInt64 |-> stats_starts st **
   &( p # "stats_t" ->ₛ "propagations") # UInt64 |-> stats_propagations st **
   &( p # "stats_t" ->ₛ "inspects") # UInt64 |-> stats_inspects st **
   &( p # "stats_t" ->ₛ "conflicts") # UInt64 |-> stats_conflicts st **
   &( p # "stats_t" ->ₛ "clauses") # UInt64 |-> stats_clauses st **
   &( p # "stats_t" ->ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
   &( p # "stats_t" ->ₛ "learnts") # UInt64 |-> stats_learnts st **
   &( p # "stats_t" ->ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st **
   &( p # "stats_t" ->ₛ "max_literals") # UInt64 |-> stats_max_literals st **
   &( p # "stats_t" ->ₛ "tot_literals") # UInt64 |-> stats_tot_literals st).

Definition solver_fp_without_decay_incs_rep
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "random_seed") # Double |-> ms_random_seed M **
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M.

Definition solver_fp_without_seed_rep (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "var_inc") # Double |-> ms_var_inc M **
  &( s # "solver_t" ->ₛ "var_decay") # Double |-> ms_var_decay M **
  &( s # "solver_t" ->ₛ "cla_inc") # Float |-> ms_cla_inc M **
  &( s # "solver_t" ->ₛ "cla_decay") # Float |-> ms_cla_decay M **
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M.

Definition solver_fp_without_progress_rep
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "var_inc") # Double |-> ms_var_inc M **
  &( s # "solver_t" ->ₛ "var_decay") # Double |-> ms_var_decay M **
  &( s # "solver_t" ->ₛ "cla_inc") # Float |-> ms_cla_inc M **
  &( s # "solver_t" ->ₛ "cla_decay") # Float |-> ms_cla_decay M **
  &( s # "solver_t" ->ₛ "random_seed") # Double |-> ms_random_seed M.

Definition solver_vecs_without_order_rep
    (s : Z) (M : msolver) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
    (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
    (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
    (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
    (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
    (mt_lim (ms_core M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
    (ms_model M).


(* Shared peel/join rules expose the required fields and retain the
   remaining state as one bundle. [sep_apply] matches the folded remainder
   spatially; [fold] need not find it as a literal subterm. *)

Lemma peel_scalars_root : forall s M,
  solver_scalars_rep s M |--
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  solver_scalars_without_root_rep s M.
Proof. intros. unfold solver_scalars_rep, solver_scalars_without_root_rep. msat_entailer_with lia. Qed.

Lemma join_scalars_root : forall s M,
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  solver_scalars_without_root_rep s M |--
  solver_scalars_rep s M.
Proof. intros. unfold solver_scalars_rep, solver_scalars_without_root_rep. msat_entailer_with lia. Qed.

Lemma peel_vecs_trail_lim : forall s M,
  solver_vecs_rep s M |--
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)) **
  solver_vecs_without_lim_rep s M.
Proof. intros. unfold solver_vecs_rep, solver_vecs_without_lim_rep. msat_entailer_with lia. Qed.

Lemma join_vecs_trail_lim : forall s M,
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)) **
  solver_vecs_without_lim_rep s M |--
  solver_vecs_rep s M.
Proof. intros. unfold solver_vecs_rep, solver_vecs_without_lim_rep. msat_entailer_with lia. Qed.

Lemma peel_scalars_size : forall s M,
  solver_scalars_rep s M |--
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  clause_new_scalars_frame s M.
Proof. intros. unfold solver_scalars_rep, clause_new_scalars_frame. msat_entailer_with lia. Qed.

Lemma peel_fp_progress : forall s M,
  solver_fp_rep s M |--
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> (ms_progress M) **
  solver_fp_without_progress_rep s M.
Proof. intros. unfold solver_fp_rep, solver_fp_without_progress_rep. msat_entailer_with lia. Qed.

Lemma peel_fp_decays : forall s M,
  solver_fp_rep s M |--
  &( s # "solver_t" ->ₛ "var_decay") # Double |-> (ms_var_decay M) **
  &( s # "solver_t" ->ₛ "cla_decay") # Float |-> (ms_cla_decay M) **
  solver_fp_without_decays_rep s M.
Proof. intros. unfold solver_fp_rep, solver_fp_without_decays_rep. msat_entailer_with lia. Qed.

Lemma peel_vecs_model : forall s M,
  solver_vecs_rep s M |--
  Veci.rep &( s # "solver_t" ->ₛ "model") (ms_model M) **
  solver_vecs_without_model_rep s M.
Proof. intros. unfold solver_vecs_rep, solver_vecs_without_model_rep. msat_entailer_with lia. Qed.

Lemma peel_scalars_qtail : forall s M,
  solver_scalars_rep s M |--
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  solver_scalars_without_qtail_rep s M.
Proof. intros. unfold solver_scalars_rep, solver_scalars_without_qtail_rep. msat_entailer_with lia. Qed.

Lemma join_scalars_qtail : forall s M,
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  solver_scalars_without_qtail_rep s M |--
  solver_scalars_rep s M.
Proof. intros. unfold solver_scalars_rep, solver_scalars_without_qtail_rep. msat_entailer_with lia. Qed.

Lemma peel_vecs_learnts : forall s M,
  solver_vecs_rep s M |--
  Vecp.rep &( s # "solver_t" ->ₛ "learnts") (map fst (ms_learnt M)) **
  solver_vecs_without_learnts_rep s M.
Proof. intros. unfold solver_vecs_rep, solver_vecs_without_learnts_rep. msat_entailer_with lia. Qed.

Lemma join_vecs_learnts : forall s M,
  Vecp.rep &( s # "solver_t" ->ₛ "learnts") (map fst (ms_learnt M)) **
  solver_vecs_without_learnts_rep s M |--
  solver_vecs_rep s M.
Proof. intros. unfold solver_vecs_rep, solver_vecs_without_learnts_rep. msat_entailer_with lia. Qed.

Lemma peel_scalars_simplify_control : forall s M,
  solver_scalars_rep s M |--
  &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  solver_simplify_control_scalars_frame s M.
Proof. intros. unfold solver_scalars_rep, solver_simplify_control_scalars_frame. msat_entailer_with lia. Qed.

Lemma join_scalars_size : forall s M,
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  clause_new_scalars_frame s M |--
  solver_scalars_rep s M.
Proof. intros. unfold solver_scalars_rep, clause_new_scalars_frame. msat_entailer_with lia. Qed.

Lemma join_vecs_full : forall s M,
  Vecp.rep &( s # "solver_t" ->ₛ "clauses") (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts") (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "order") (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model") (ms_model M) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged") (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack") (ms_stack M) |--
  solver_vecs_rep s M.
Proof. intros. unfold solver_vecs_rep. msat_entailer_with lia. Qed.


Definition solver_search_init_frame_at
    (s : Z) (M : msolver) (lvl wl : Z) : Assertion :=
  solver_search_bundle_at s M lvl wl
    (solver_scalars_rep s M) (solver_fp_without_decays_rep s M)
    (solver_vecs_without_model_rep s M)
    (stats_without_starts_rep &( s # "solver_t" ->ₛ "stats")
                              (ms_stats M)).

Definition solver_search_root_frame_at
    (s : Z) (M : msolver) (lvl wl : Z) : Assertion :=
  solver_search_bundle_at s M lvl wl
    (solver_scalars_without_root_rep s M) (solver_fp_rep s M)
    (solver_vecs_without_lim_rep s M)
    (stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M)).

Definition solver_search_root_payload
    (s : Z) (M : msolver) (wl : Z) : Assertion :=
  solver_search_payload s M wl
    (solver_scalars_without_root_rep s M) (solver_fp_rep s M)
    (solver_vecs_without_lim_rep s M)
    (stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M)).

Definition solver_search_conflict_frame_at
    (s : Z) (M : msolver) (lvl wl : Z) : Assertion :=
  solver_search_bundle_at s M lvl wl
    (solver_scalars_without_root_rep s M) (solver_fp_rep s M)
    (solver_vecs_without_lim_rep s M)
    (stats_without_conflicts_rep &( s # "solver_t" ->ₛ "stats")
                                 (ms_stats M)).

Definition solver_search_decay_frame_at
    (s : Z) (M : msolver) (lvl wl : Z) : Assertion :=
  solver_search_bundle_at s M lvl wl
    (solver_scalars_rep s M) (solver_fp_without_decay_incs_rep s M)
    (solver_vecs_rep s M)
    (stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M)).

Definition solver_search_reducedb_frame_at
    (s : Z) (M : msolver) (lvl wl : Z) : Assertion :=
  solver_search_bundle_at s M lvl wl
    (solver_scalars_without_qtail_rep s M) (solver_fp_rep s M)
    (solver_vecs_without_learnts_rep s M)
    (stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M)).

(** Complement of [order_select]'s concrete footprint plus the one decisions
    counter increment performed immediately before it. *)
Definition solver_search_order_frame_at
    (s : Z) (M : msolver) (lvl act asg opos : Z) (wl : Z) : Assertion :=
  “ solver_shape M ” &&
  (clause_new_scalars_frame s M ** solver_fp_without_seed_rep s M **
   solver_vecs_without_order_rep s M **
   stats_without_decisions_rep &( s # "solver_t" ->ₛ "stats")
                               (ms_stats M) **
   solver_double_tail act (ms_size M) (ms_cap M) **
   solver_char_tail asg (ms_size M) (ms_cap M) **
   solver_int_tail opos (ms_size M) (ms_cap M) **
   (EX rsn trl tgs : Z,
      (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
       &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
       &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
       &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
       &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
      PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
      solver_ptr_tail rsn (ms_size M) (ms_cap M) **
      CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
      solver_char_tail tgs (ms_size M) (ms_cap M) **
      solver_trail_array_rep M trl **
      wlists_rep wl (ms_size M) (ms_wm M) **
      clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
      binary_scratch_rep (ms_binary M) (ms_binary_lits M)) **
   solver_levels_slice_at s M lvl).

Definition solver_search_progress_frame_at
    (s : Z) (M : msolver) (asg lvl : Z) (wl : Z) : Assertion :=
  “ solver_shape M ” &&
  (clause_new_scalars_frame s M ** solver_fp_without_progress_rep s M **
   solver_vecs_rep s M **
   solver_char_tail asg (ms_size M) (ms_cap M) **
   solver_int_tail lvl (ms_size M) (ms_cap M) **
   (EX act opos rsn trl tgs : Z,
      (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
       &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
       &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
       &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
       &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
       &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
       &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
      DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
      solver_double_tail act (ms_size M) (ms_cap M) **
      IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
      solver_int_tail opos (ms_size M) (ms_cap M) **
      PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
      solver_ptr_tail rsn (ms_size M) (ms_cap M) **
      CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
      solver_char_tail tgs (ms_size M) (ms_cap M) **
      solver_trail_array_rep M trl **
      wlists_rep wl (ms_size M) (ms_wm M) **
      clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
      binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
      stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M))).

Definition solver_enqueue_frame_with_scalars_wl
    (s : Z) (M : msolver) (wl : Z) (scalars : Assertion) : Assertion :=
  EX act opos tgs : Z,
    solver_enqueue_cells_at s M wl act opos tgs scalars.

Definition solver_enqueue_frame_wl (s : Z) (M : msolver) (wl : Z) : Assertion :=
  solver_enqueue_frame_with_scalars_wl s M wl (solver_scalars_without_qtail_rep s M).


Definition solver_assume_frame_wl (s : Z) (M : msolver) (wl : Z) : Assertion :=
  solver_enqueue_frame_with_scalars_wl s M wl (solver_assume_scalars_frame s M).

(** The nine statistic cells framed while record increments slots 7 and 8. *)
Definition stats_record_frame (p : Z) (st : list Z) : Assertion :=
  &( p # "stats_t" ->ₛ "starts") # UInt64 |-> stats_starts st **
  &( p # "stats_t" ->ₛ "decisions") # UInt64 |-> stats_decisions st **
  &( p # "stats_t" ->ₛ "propagations") # UInt64 |-> stats_propagations st **
  &( p # "stats_t" ->ₛ "inspects") # UInt64 |-> stats_inspects st **
  &( p # "stats_t" ->ₛ "conflicts") # UInt64 |-> stats_conflicts st **
  &( p # "stats_t" ->ₛ "clauses") # UInt64 |-> stats_clauses st **
  &( p # "stats_t" ->ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
  &( p # "stats_t" ->ₛ "max_literals") # UInt64 |-> stats_max_literals st **
  &( p # "stats_t" ->ₛ "tot_literals") # UInt64 |-> stats_tot_literals st.

(** Complement used by the non-unary record arm: the learned vector and
    learned objects, [cla_inc], and statistic slots 7/8 stay exposed. *)
Definition solver_record_finish_frame_at
    (s : Z) (M : msolver) (lvl wl : Z) : Assertion :=
  EX act asg opos rsn trl tgs : Z,
    “ solver_shape M ” &&
    (solver_scalars_rep s M **
     (&( s # "solver_t" ->ₛ "var_inc") # Double |-> ms_var_inc M **
      &( s # "solver_t" ->ₛ "var_decay") # Double |-> ms_var_decay M **
      &( s # "solver_t" ->ₛ "cla_decay") # Float |-> ms_cla_decay M **
      &( s # "solver_t" ->ₛ "random_seed") # Double |-> ms_random_seed M **
      &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M) **
     (Vecp.rep &( s # "solver_t" ->ₛ "clauses")
        (map fst (ms_prob M)) **
      Veci.rep &( s # "solver_t" ->ₛ "tagged")
        (ms_tagged M) **
      Veci.rep &( s # "solver_t" ->ₛ "stack")
        (ms_stack M) **
      Veci.rep &( s # "solver_t" ->ₛ "order")
        (ms_order M) **
      Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
        (mt_lim (ms_core M)) **
      Veci.rep &( s # "solver_t" ->ₛ "model")
        (ms_model M)) **
     solver_ptrs_rep s wl act asg opos rsn lvl trl (ms_binary M) tgs **
     solver_var_arrays_rep M act asg opos rsn lvl tgs **
     solver_trail_array_rep M trl **
     wlists_rep wl (ms_size M) (ms_wm M) **
     clause_db_rep (ms_prob M) **
     binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
     stats_record_frame &( s # "solver_t" ->ₛ "stats") (ms_stats M)).

(** Remainder while a parent database-compaction loop exposes one database
    vector, its clause objects, the watcher table, reasons, [cla_inc], and
    statistics.  No fourth database representation is introduced: the
    omitted components are precisely the ones threaded explicitly by the
    loop invariant. *)
Definition solver_db_mutation_frame_at
    (s : Z) (M : msolver) (lvl : Z) : Assertion :=
  clause_new_scalars_frame s M **
  (&( s # "solver_t" ->ₛ "var_inc") # Double |-> ms_var_inc M **
   &( s # "solver_t" ->ₛ "var_decay") # Double |-> ms_var_decay M **
   &( s # "solver_t" ->ₛ "cla_decay") # Float |-> ms_cla_decay M **
   &( s # "solver_t" ->ₛ "random_seed") # Double |-> ms_random_seed M **
   &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M) **
  solver_vecs_without_learnts_rep s M **
  (EX act asg opos trl tgs : Z,
    &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
    &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
    DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
    solver_double_tail act (ms_size M) (ms_cap M) **
    CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
    solver_char_tail asg (ms_size M) (ms_cap M) **
    IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
    solver_int_tail opos (ms_size M) (ms_cap M) **
    CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
    solver_char_tail tgs (ms_size M) (ms_cap M) **
    solver_trail_array_rep M trl) **
  solver_levels_slice_at s M lvl **
  clause_db_rep (ms_prob M) **
  binary_scratch_rep (ms_binary M) (ms_binary_lits M).

(** Cancellation preserves the activity, assigns, orderpos and reasons
    tails above [ms_size M], and the trail tail above [ms_qtail M].
    The level tail remains in [solver_levels_slice_at]. *)
Definition solver_cancel_undef_tail (M : msolver) (act asg opos rsn trl : Z)
    : Assertion :=
  solver_double_tail act (ms_size M) (ms_cap M) **
  solver_char_tail asg (ms_size M) (ms_cap M) **
  solver_int_tail opos (ms_size M) (ms_cap M) **
  solver_ptr_tail rsn (ms_size M) (ms_cap M) **
  solver_int_tail trl (ms_qtail M) (ms_cap M).

(** Remainder while cancellation exposes the queue cursors, trail core,
    reasons, and variable heap.  It deliberately excludes the untouched
    level slice.  The activity array is exposed separately because each
    [order_unassigned] call may invoke [order_update]. *)
Definition solver_cancel_frame (s : Z) (M : msolver) (wl : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M **
  solver_fp_rep s M **
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) **
  (EX tgs : Z,
    &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
    &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
    CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
    solver_char_tail tgs (ms_size M) (ms_cap M) **
    wlists_rep wl (ms_size M) (ms_wm M) **
    clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M)) **
  stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

Definition solver_cancel_open_at (s : Z) (M : msolver)
    (act asg opos rsn trl : Z) (asg_l opos_l rsn_l ord_l : list Z)
    (wl : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
  &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
  &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
  &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
  DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
  CharArray.seg asg 0 (ms_size M) asg_l **
  IntArray.seg opos 0 (ms_size M) opos_l **
  PtrArray.seg rsn 0 (ms_size M) rsn_l **
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  solver_cancel_undef_tail M act asg opos rsn trl **
  Veci.rep &( s # "solver_t" ->ₛ "order") ord_l **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  solver_cancel_frame s M wl.

Lemma solver_analyze_frame_analyze_tag_step :
  forall s M tags tagged activity orderpos order var_inc wl,
    solver_analyze_frame s (analyze_tag_step_msolver M tags tagged
                              activity orderpos order var_inc) wl
    = solver_analyze_frame s M wl.
Proof. intros. reflexivity. Qed.

(** Analysis preserves six uninitialised tails, the unused stack vector,
    and two literal counters until its epilogue. [qtail] and the open tagged
    vector stay outside this bundle, which is disjoint from [solver_analyze_frame]. *)
Definition solver_analyze_inert_at (s : Z) (M : msolver)
    (n act opos rsn lvl trl tgs : Z) : Assertion :=
  solver_double_tail act n (ms_cap M) **
  solver_int_tail opos n (ms_cap M) **
  solver_ptr_tail rsn n (ms_cap M) **
  solver_int_tail lvl n (ms_cap M) **
  solver_int_tail trl (ms_qtail M) (ms_cap M) **
  solver_char_tail tgs n (ms_cap M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack") (ms_stack M) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals")
    # UInt64 |-> stats_max_literals (ms_stats M) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals")
    # UInt64 |-> stats_tot_literals (ms_stats M).

Definition solver_analyze_open_at (s : Z) (M : msolver)
    (n act opos rsn lvl trl tgs : Z) (wl : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> n **
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
  &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
  &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
  &( s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
  &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
  &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
  DoubleArray.seg act 0 n (ms_activity M) **
  IntArray.seg opos 0 n (ms_orderpos M) **
  PtrArray.seg rsn 0 n (ms_reason_words M) **
  IntArray.seg lvl 0 n (mt_levels (ms_core M)) **
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  CharArray.seg tgs 0 n (ms_tags M) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (db_words (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged") (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "order") (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  &( s # "solver_t" ->ₛ "var_inc") # Double |-> ms_var_inc M **
  &( s # "solver_t" ->ₛ "cla_inc") # Float |-> ms_cla_inc M **
  solver_analyze_inert_at s M n act opos rsn lvl trl tgs **
  solver_analyze_frame s M wl.

Lemma solver_analyze_inert_at_tag_step :
  forall s M tags tagged activity orderpos order var_inc
         n act opos rsn lvl trl tgs,
    solver_analyze_inert_at s
      (analyze_tag_step_msolver M tags tagged activity orderpos
         order var_inc) n act opos rsn lvl trl tgs
    = solver_analyze_inert_at s M n act opos rsn lvl trl tgs.
Proof. intros. reflexivity. Qed.

Lemma solver_analyze_inert_at_cla_inc :
  forall s M cla_inc n act opos rsn lvl trl tgs,
    solver_analyze_inert_at s (msolver_with_cla_inc_stats M cla_inc (ms_stats M))
      n act opos rsn lvl trl tgs
    = solver_analyze_inert_at s M n act opos rsn lvl trl tgs.
Proof. intros. reflexivity. Qed.

Definition solver_tags_tagged_frame_at
    (s : Z) (M : msolver) (reasons_ptr levels_ptr trl : Z) (wl : Z) : Assertion :=
    &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
    &( s # "solver_t" ->ₛ "reasons") # Ptr |-> reasons_ptr **
    &( s # "solver_t" ->ₛ "levels") # Ptr |-> levels_ptr **
    PtrArray.seg reasons_ptr 0 (ms_size M) (ms_reason_words M) **
    solver_ptr_tail reasons_ptr (ms_size M) (ms_cap M) **
    IntArray.seg levels_ptr 0 (ms_size M) (mt_levels (ms_core M)) **
    solver_int_tail levels_ptr (ms_size M) (ms_cap M) **
    Veci.rep &( s # "solver_t" ->ₛ "stack")
             (ms_stack M) **
    clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
    solver_removable_frame_at s M trl wl.

Definition solver_literal_stats_frame_at
    (s : Z) (M : msolver) (rsn lvl trl tgs : Z) (wl : Z) : Assertion :=
  “ solver_shape M ” &&
  (EX act asg opos : Z,
     solver_scalars_rep s M ** solver_fp_rep s M ** solver_vecs_rep s M **
     solver_ptrs_rep s wl act asg opos rsn lvl trl (ms_binary M) tgs **
     solver_var_arrays_rep M act asg opos rsn lvl tgs **
     solver_trail_array_rep M trl **
     wlists_rep wl (ms_size M) (ms_wm M) **
     clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
     binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
     stats_analyze_frame &( s # "solver_t" ->ₛ "stats") (ms_stats M)).

Definition solver_propagate_open_at (s : Z) (M : msolver)
    (wl asg rsn lvl trl : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
  &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
  &( s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
  &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
  &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  solver_char_tail asg (ms_size M) (ms_cap M) **
  PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
  solver_ptr_tail rsn (ms_size M) (ms_cap M) **
  IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
  solver_int_tail lvl (ms_size M) (ms_cap M) **
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  solver_int_tail trl (ms_qtail M) (ms_cap M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  wlists_rep wl (ms_size M) (ms_wm M) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "propagations") # UInt64 |-> stats_propagations (ms_stats M) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "inspects") # UInt64 |-> stats_inspects (ms_stats M) **
  solver_propagate_frame s M.

Definition solver_propagation_nonwatch_rest_at
    (s : Z) (M : msolver) (asg lvl : Z) : Assertion :=
  EX rsn trl : Z,
    &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
    &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
    &( s # "solver_t" ->ₛ "simpdb_props")
      # Int |-> ms_simpdb_props M **
    &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    &( s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
    &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
    &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
    CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
    solver_char_tail asg (ms_size M) (ms_cap M) **
    IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
    solver_int_tail lvl (ms_size M) (ms_cap M) **
    PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
    solver_ptr_tail rsn (ms_size M) (ms_cap M) **
    IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
    solver_int_tail trl (ms_qtail M) (ms_cap M) **
    Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
      (mt_lim (ms_core M)) **
    &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
    solver_binary_rep M **
    &( s # "solver_t" ->ₛ "stats" .ₛ "propagations")
      # UInt64 |-> stats_propagations (ms_stats M) **
    &( s # "solver_t" ->ₛ "stats" .ₛ "inspects")
      # UInt64 |-> stats_inspects (ms_stats M) **
    solver_propagate_frame s M.

Definition tagged_word (word : Z) : Prop := is_tag word = true.

Definition clause_is_lit_result (word ret : Z) : Prop :=
  (ret = 1 /\ is_tag word = true) \/
  (ret = 0 /\ is_tag word = false).

(** Named source-scan fragments prevent the symbolic executor from eagerly
    recombining the isolated current watcher with an adjacent array segment.
    They are definitionally the ordinary pointer-array segment. *)
Definition propagation_ptr_segment
    (base lo hi : Z) (words : list Z) : Assertion :=
  PtrArray.seg base lo hi words.

(** Keep the selected literal cell open across the three native reads that
    classify and route a replacement candidate.  The symbolic executor's
    ordinary [IntArray.missing_i] close rule otherwise rewrites the tail as a
    [replace_Znth] after the first read and loses the exact selected value
    needed by the next read. *)
Definition propagation_int_missing
    (base index lo hi : Z) (words : list Z) : Assertion :=
  IntArray.missing_i base index lo hi words.

Lemma propagation_normalized_clause_length : forall watch0 false_lit old,
  2 <= Zlength old ->
  Zlength (propagation_normalized_clause watch0 false_lit old) = Zlength old.
Proof.
  intros watch0 false_lit old Hlen.
  unfold propagation_normalized_clause.
  rewrite !Zlength_cons, Zlength_sublist by lia. lia.
Qed.

Definition propagation_migrated_clause
    (watch0 candidate false_lit offset : Z) (old : list Z) : list Z :=
  replace_Znth offset false_lit
    (watch0 :: candidate :: sublist 2 (Zlength old) old).

Lemma propagation_migrated_clause_length :
  forall watch0 candidate false_lit offset old,
    2 <= Zlength old ->
    Zlength (propagation_migrated_clause
      watch0 candidate false_lit offset old) = Zlength old.
Proof.
  intros. unfold propagation_migrated_clause.
  rewrite Zlength_replace_Znth, !Zlength_cons, Zlength_sublist by lia. lia.
Qed.

(** Exact forward-copy progress for the conflict paths that compact the
    current watcher vector in place.  [words] is the vector at entry to the
    current watcher iteration; slot [jj] has already received [current], and
    [copied] is the prefix of [suffix] subsequently moved from [ii+1] to
    [jj+1].  The relation records the concrete list after those writes, so a
    loop invariant cannot forget or invent watcher words. *)
Fixpoint binary_watch_write
    (dst : Z) (copied memory : list Z) : list Z :=
  match copied with
  | nil => memory
  | x :: copied' =>
      binary_watch_write (dst + 1) copied'
        (replace_Znth dst x memory)
  end.

Definition binary_watch_copy_progress
    (words kept : list Z) (current : Z) (suffix : list Z)
    (ii jj src dst : Z) (memory : list Z) : Prop :=
  exists copied rest,
    words = kept ++ (current :: suffix) /\
    Zlength kept = ii /\
    0 <= jj <= ii /\
    suffix = copied ++ rest /\
    src = ii + 1 + Zlength copied /\
    dst = jj + 1 + Zlength copied /\
    memory = binary_watch_write (jj + 1) copied
               (replace_Znth jj current words) /\
    Zlength memory = Zlength words.

Definition enqueue_input
    (n l qtail : Z) (assigns levels reasons trail : list Z) : Prop :=
  lit_wf_c n l /\ 2 * n <= INT_MAX /\
  Zlength assigns = n /\ Zlength levels = n /\ Zlength reasons = n /\
  Zlength trail = qtail /\ 0 <= qtail <= n /\
  (Znth (lit_var_c l) assigns 0 = 0 -> qtail < n) /\
  Forall (fun x => -1 <= x <= 1) assigns.


Definition solver_rep_assigns_levels_at
    (s : Z) (M : msolver) (asg lvl wl : Z) : Assertion :=
  EX act opos rsn trl tgs : Z,
    solver_rep_at s M wl act asg opos rsn lvl trl tgs.
(* Preserve the watcher-table address while a simplifier caches its reasons
   and levels pointers; the other backing arrays remain existential. *)
Definition solver_rep_reasons_levels_wl_at
    (s : Z) (M : msolver) (rsn lvl wl : Z) : Assertion :=
  EX act asg opos trl tgs : Z,
    solver_rep_at s M wl act asg opos rsn lvl trl tgs.

Lemma solver_rep_analyze_join_levels_at : forall s M rsn lvl trl tgs wl,
  solver_rep_analyze_at s M rsn lvl trl tgs wl
  |-- solver_rep_levels_wl_at s M wl lvl.
Proof.
  intros. unfold solver_rep_analyze_at.
  Intros act asg opos.
  unfold solver_rep_at, solver_rep_levels_wl_at.
  Exists act asg opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

(** Cancellation touches every component except the level slice.  These
    structural equivalences justify the narrowly registered split/refold
    strategies used at native call boundaries. *)
Lemma solver_rep_cancel_split : forall s M wl,
  solver_rep_wl s M wl
  |-- EX lvl : Z, solver_cancel_owned s M wl ** solver_levels_slice_at s M lvl.
Proof.
  intros s M wl.
  unfold solver_rep_wl, solver_rep_levels_wl_at, solver_cancel_owned.
  Intros lvl act asg opos rsn trl tgs.
  Exists lvl act asg opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_cancel_join_rep : forall s M lvl wl,
  solver_cancel_owned s M wl ** solver_levels_slice_at s M lvl
  |-- solver_rep_wl s M wl.
Proof.
  intros s M lvl wl.
  unfold solver_rep_wl, solver_rep_levels_wl_at, solver_cancel_owned.
  Intros act asg opos rsn trl tgs.
  Exists lvl act asg opos rsn trl tgs.
  msat_entailer_with lia.
Qed.


Lemma solver_cancel_join_rep_levels_at : forall s M lvl wl,
  solver_cancel_owned s M wl ** solver_levels_slice_at s M lvl
  |-- solver_rep_levels_wl_at s M wl lvl.
Proof. msat_rep_levels_cancel_split. Qed.

Lemma solver_rep_assigns_levels_at_levels_at : forall s M asg lvl wl,
  solver_rep_assigns_levels_at s M asg lvl wl
  |-- solver_rep_levels_wl_at s M wl lvl.
Proof.
  intros s M asg lvl wl.
  unfold solver_rep_assigns_levels_at, solver_rep_at, solver_rep_levels_wl_at.
  Intros act opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_rep_assigns_levels_cancel_split : forall s M asg lvl wl,
  solver_rep_assigns_levels_at s M asg lvl wl
  |-- solver_cancel_owned s M wl ** solver_levels_slice_at s M lvl.
Proof.
  intros s M asg lvl wl.
  unfold solver_rep_assigns_levels_at, solver_rep_at, solver_cancel_owned.
  Intros act opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_levels_slice_cancel_project :
  forall s M lvl level orderpos order root,
    solver_levels_slice_at s M lvl
    |-- solver_levels_slice_at s
          (msolver_cancel_project M level orderpos order root) lvl.
Proof.
  intros. unfold solver_levels_slice_at, msolver_cancel_project,
    msolver_core_heap_update. simpl.
  cancel.
Qed.

Lemma solver_cancel_project_join_rep :
  forall s M lvl level orderpos order root wl,
    solver_cancel_owned s
      (msolver_cancel_project M level orderpos order root) wl **
    solver_levels_slice_at s M lvl
    |-- solver_rep_wl s
      (msolver_cancel_project M level orderpos order root) wl.
Proof.
  intros s M0 lvl level orderpos order root wl.
  sep_apply (solver_levels_slice_cancel_project
    s M0 lvl level orderpos order root).
  sep_apply (solver_cancel_join_rep s
    (msolver_cancel_project M0 level orderpos order root) lvl wl).
  msat_entailer_with lia.
Qed.

Lemma solver_cancel_project_join_rep_levels_at :
  forall s M lvl level orderpos order root wl,
    solver_cancel_owned s
      (msolver_cancel_project M level orderpos order root) wl **
    solver_levels_slice_at s M lvl
    |-- solver_rep_levels_wl_at s
      (msolver_cancel_project M level orderpos order root) wl lvl.
Proof.
  intros s M0 lvl level orderpos order root wl.
  sep_apply (solver_levels_slice_cancel_project
    s M0 lvl level orderpos order root).
  sep_apply (solver_cancel_join_rep_levels_at s
    (msolver_cancel_project M0 level orderpos order root) lvl wl).
  msat_entailer_with lia.
Qed.


Lemma solver_shape_assigns_len : forall M,
  solver_shape M -> Zlength (mt_assigns (ms_core M)) = ms_size M.
Proof. intros M H. unfold solver_shape in H. tauto. Qed.

Lemma solver_shape_reasons_len : forall M,
  solver_shape M -> Zlength (ms_reason_words M) = ms_size M.
Proof. intros M H. unfold solver_shape in H. tauto. Qed.

Lemma solver_shape_binary_nonnull : forall M,
  solver_shape M -> ms_binary M <> 0.
Proof. intros M H. unfold solver_shape in H. tauto. Qed.

Lemma solver_shape_binary_not_tag : forall M,
  solver_shape M -> is_tag (ms_binary M) = false.
Proof.
  intros M H. unfold solver_shape in H. apply even_not_tag. tauto.
Qed.

Lemma lit_denote_even_var : forall v, 0 <= v -> lit_denote (2 * v) = Pos v.
Proof.
  intros v Hv. unfold lit_denote.
  assert (Ho : Z.odd (2 * v) = false) by (rewrite Z.odd_mul; reflexivity).
  assert (Hd : (2 * v) / 2 = v).
  { replace (2 * v) with (v * 2) by lia. apply Z_div_mult_full. lia. }
  rewrite Ho, Hd. reflexivity.
Qed.

Lemma lit_denote_odd_var : forall v, 0 <= v -> lit_denote (2 * v + 1) = Neg v.
Proof.
  intros v Hv. unfold lit_denote.
  assert (Ho : Z.odd (2 * v + 1) = true).
  { replace (2 * v + 1) with (Z.succ (2 * v)) by lia.
    rewrite Z.odd_succ, Z.even_mul. reflexivity. }
  assert (Hd : (2 * v + 1) / 2 = v).
  { replace (2 * v + 1) with (1 + v * 2) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rewrite Ho, Hd. reflexivity.
Qed.

Lemma trail_lit_of_nonneg : forall t v, 0 <= v -> 0 <= trail_lit_of t v.
Proof.
  intros t v Hv. unfold trail_lit_of.
  destruct (Znth v (mt_assigns t) 0 =? -1); lia.
Qed.

Lemma trail_lit_of_wf : forall n t v,
  0 <= v < n -> lit_wf_c n (trail_lit_of t v).
Proof.
  intros n t v Hv. unfold lit_wf_c, trail_lit_of.
  destruct (Znth v (mt_assigns t) 0 =? -1); lia.
Qed.

Lemma trail_lit_of_var : forall t v,
  0 <= v -> lit_var_c (trail_lit_of t v) = v.
Proof.
  intros t v Hv. unfold trail_lit_of, lit_var_c.
  destruct (Znth v (mt_assigns t) 0 =? -1).
  - replace (2 * v + 1) with (1 + v * 2) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  - replace (2 * v) with (v * 2) by lia. apply Z_div_mult_full. lia.
Qed.

Lemma trail_lit_of_denote : forall t v b,
  0 <= v -> mt_pv t v = Some b ->
  lit_denote (trail_lit_of t v) = satisfying_literal v b.
Proof.
  intros t v b Hv Hpv.
  rewrite (mt_pv_nonneg t v Hv) in Hpv.
  unfold lbool_val in Hpv. unfold trail_lit_of, satisfying_literal.
  destruct (Znth v (mt_assigns t) 0 =? 1) eqn:E1.
  - inversion Hpv. subst b.
    apply Z.eqb_eq in E1. rewrite E1.
    assert (E2 : (1 =? -1) = false) by reflexivity. rewrite E2.
    apply lit_denote_even_var; lia.
  - destruct (Znth v (mt_assigns t) 0 =? -1) eqn:E2.
    + inversion Hpv. subst b. apply lit_denote_odd_var; lia.
    + discriminate.
Qed.

Lemma reason_word_ok_null : forall t v db r,
  reason_word_ok t v db 0 r -> r = None.
Proof. intros t v db r H. unfold reason_word_ok in H. simpl in H. auto. Qed.

Lemma reason_word_ok_tag : forall t v db w r,
  0 < w -> is_tag w = true -> reason_word_ok t v db w r ->
  r = Some [lit_denote (trail_lit_of t v);
            literal_neg (lit_denote (tag_lit w))].
Proof.
  intros t v db w r Hw Ht H. unfold reason_word_ok in H.
  destruct (w =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - rewrite Ht in H. tauto.
Qed.

(** Every live reason word belongs to an assigned variable.  MiniSat installs
    assignment and reason together at enqueue and clears both cells together
    at cancellation.  This global form is necessary: a stale tag at an
    unassigned owner could name a second unassigned variable whose later
    enqueue overwrites its level, invalidating [binary_reason_same_level]. *)
Lemma reason_word_ok_nonzero_assigned : forall t v db w r,
  w <> 0 -> reason_word_ok t v db w r ->
  Znth v (mt_assigns t) 0 <> 0.
Proof.
  intros t v db w r Hw H. unfold reason_word_ok in H.
  destruct (w =? 0) eqn:E.
  - apply Z.eqb_eq in E. contradiction.
  - tauto.
Qed.

Lemma reason_word_of_tag : forall t v db p,
  0 <= p -> Znth v (mt_assigns t) 0 <> 0 ->
  reason_word_ok t v db (tag_of_lit p)
    (Some [lit_denote (trail_lit_of t v); literal_neg (lit_denote p)]).
Proof.
  intros t v db p Hp Hassigned. unfold reason_word_ok.
  assert (tag_of_lit p =? 0 = false) as E.
  { apply Z.eqb_neq. unfold tag_of_lit. lia. }
  rewrite E. split; [exact Hassigned |].
  rewrite is_tag_of, tag_lit_of. reflexivity.
Qed.


(** A tag in [wm[p]] yields a resident binary clause via [wmap_tag_witness].
    Denotation and permutation give the entailed reason clause [q; ~p]. *)
Lemma tagged_reason_entailed : forall n F db wm l w,
  db_wf n db -> wmap_exact n db wm ->
  0 <= l < 2 * n -> In w (Znth l wm nil) -> is_tag w = true ->
  (forall p co, In (p, co) db -> entails_clause F (denote_obj co)) ->
  entails_clause F [lit_denote (tag_lit w); literal_neg (lit_denote l)].
Proof.
  intros n F db wm l w Hdb Hwm Hl Hin Ht Hent.
  destruct (wmap_tag_witness n db wm l w Hdb Hwm Hl Hin Ht)
    as [p [co [Hco [_ Hperm]]]].
  apply (entails_clause_perm F (denote_obj co)); [| exact (Hent p co Hco)].
  unfold denote_obj.
  eapply Permutation_trans; [apply lits_denote_perm; exact Hperm |].
  change (lits_denote [lit_neg_c l; tag_lit w])
    with [lit_denote (lit_neg_c l); lit_denote (tag_lit w)].
  rewrite (lit_denote_neg l ltac:(lia)).
  apply perm_swap.
Qed.

(** ** Loop-transient focus on one watch list.

    [solver_propagate] compacts [wm[p]] in place while it pushes watchers onto
    other lists.  The loop holds the table with slot [p] taken out,
    [VecpArray.missing_i wl p 0 (2 * n) wm], where the entry of [wm] at [p] is
    stale: the live contents of slot [p] are tracked separately, and
    [ms_wm M = replace_Znth p words wm].  While it pushes onto a destination
    [t], slot [t] is out as well ([VecpArray.missing2]). *)

(** The watch table after the current watcher was pushed onto [target], with
    [source] back in the open slot [hole]. *)
Definition propagation_move_wmap
    (hole target : Z) (wm : wmap) (source : list Z) (current : Z) : wmap :=
  replace_Znth target (Znth target wm nil ++ [current])
    (replace_Znth hole source wm).

(** The destination watcher index selected while the current source watcher
    is already open.  Naming this pure fact keeps QCP from unfolding the full
    propagation invariant during the accessor call. *)
Definition propagation_destination_ok
    (bound hole target : Z) : Prop :=
  0 <= hole /\ 0 <= target < bound /\ target <> hole.

Definition clause_remove_pre
    (s c n cap wl rsn : Z) (wm : wmap)
    (is_learnt : bool) (lits stats reasons : list Z) : Assertion :=
  “ 0 <= n /\ n <= cap /\ 2 * n <= INT_MAX /\ Zlength reasons = n /\
    clause_remove_ready n c lits wm stats /\
    clause_unlocked_words c reasons ” &&
  (&( s # "solver_t" ->ₛ "size") # Int |-> n **
   &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
   PtrArray.seg rsn 0 n reasons ** solver_ptr_tail rsn n cap **
   solver_wlists_handle s wl ** wlists_rep wl n wm **
   MiniSatClause.rep c is_learnt lits **
   stats_rep &( s # "solver_t" ->ₛ "stats") stats).

Definition clause_remove_open_at (s n cap wl rsn : Z)
    (wm : wmap) (stats reasons : list Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> n **
  &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
  PtrArray.seg rsn 0 n reasons ** solver_ptr_tail rsn n cap **
  solver_wlists_handle s wl ** wlists_rep wl n wm **
  stats_rep &( s # "solver_t" ->ₛ "stats") stats.

Definition clause_remove_post
    (s c n cap wl rsn : Z) (wm : wmap)
    (lits stats reasons : list Z) : Assertion :=
  EX wm' : wmap, EX stats' : list Z,
    “ clause_remove_result c lits wm wm' /\ Zlength stats' = 11 /\
      Zlength reasons = n /\ clause_unlocked_words c reasons ” &&
    (&( s # "solver_t" ->ₛ "size") # Int |-> n **
     &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
     PtrArray.seg rsn 0 n reasons ** solver_ptr_tail rsn n cap **
     solver_wlists_handle s wl ** wlists_rep wl n wm' **
     stats_rep &( s # "solver_t" ->ₛ "stats") stats').

(** The successful replacement-watch path opens the canonical destination
    vector before leaving the inner scan. This inductive certificate lets the
    spatial match choose the raw physical witnesses first and then records their
    exact index, address, and appended contents for the isolated tagged exit. *)
Inductive propagation_real_migrated_physical_alias
    (wl target current destination_index destination_ptr : Z)
    (wm : wmap) (destination_words : list Z) : Prop :=
| propagation_real_migrated_physical_alias_intro :
    destination_index = target ->
    destination_ptr = Vecp.slot wl destination_index ->
    destination_words = Znth destination_index wm nil ++ [current] ->
    propagation_real_migrated_physical_alias
      wl target current destination_index destination_ptr
      wm destination_words.


Lemma db_clauses_app : forall db1 db2,
  db_clauses (db1 ++ db2) = db_clauses db1 ++ db_clauses db2.
Proof. intros. unfold db_clauses. apply map_app. Qed.

(** A tagging step names its heap directly by the two arguments
    [act_var_bump] returned, so [heap_wf] / [heap_covers] obligations at the
    tagged state can be stated without unfolding the 39-field literal. *)
Lemma msolver_heap_analyze_tag_step :
  forall M tags tagged activity orderpos order var_inc,
    msolver_heap (analyze_tag_step_msolver M tags tagged
                    activity orderpos order var_inc)
    = {| mh_heap := order; mh_orderpos := orderpos |}.
Proof. intros. reflexivity. Qed.

Lemma msolver_view_installed : forall n M,
  installed_clauses (msolver_view n M) = msolver_clauses M.
Proof. reflexivity. Qed.

Lemma msolver_view_assignment : forall n M,
  assignment (msolver_view n M) = mt_pv (ms_core M).
Proof. reflexivity. Qed.

Lemma msolver_view_current_level : forall n M,
  current_level (msolver_view n M) = Zlength (mt_lim (ms_core M)).
Proof. reflexivity. Qed.

Lemma msolver_view_analyze_tag_step :
  forall n M tags tagged activity orderpos order var_inc,
    msolver_view n (analyze_tag_step_msolver M tags tagged
                      activity orderpos order var_inc)
    = msolver_view n M.
Proof. intros. reflexivity. Qed.

Lemma msolver_seed_shadow_analyze_tag_step :
  forall M tags tagged activity orderpos order var_inc,
    msolver_seed_shadow (analyze_tag_step_msolver M tags tagged
                           activity orderpos order var_inc)
    <-> msolver_seed_shadow M.
Proof. intros. split; intro H; exact H. Qed.

Definition msi_size {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_size (msi_weak H).

Definition msi_n_range {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_n_range (msi_weak H).

Definition msi_shape {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_shape (msi_weak H).


Definition msi_trail_wf {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_trail_wf (msi_weak H).


Definition msi_root_range {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_root_range (msi_weak H).


Definition msi_trail_impl {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_trail_impl (msi_weak H).

Definition msi_db_wf {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_db_wf (msi_weak H).


Definition msi_learnt_db {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_learnt_db (msi_weak H).


Definition msi_reasons_mem {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_reasons_mem (msi_weak H).


Definition msi_wmap_exact {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_wmap_exact (msi_weak H).


Definition msi_heap_wf {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_heap_wf (msi_weak H).

Definition msi_cla_inc_nonnegative
    {n F A_arr A_inst M} (H : msolver_inv n F A_arr A_inst M) :=
  msw_cla_inc_nonnegative (msi_weak H).


