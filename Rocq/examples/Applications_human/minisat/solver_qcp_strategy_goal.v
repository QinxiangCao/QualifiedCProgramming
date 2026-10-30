From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.vec_qcp_lib.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.

Definition solver_qcp_strategy72 :=
  forall (index : Z) (hi : Z) (cursor : Z) (base : Z) (arr : (@list Z)),
    TT &&
    (“ (cursor = (base + (index * sizeof(INT)))) ”) &&
    (“ (base < cursor) ”) &&
    (“ (index <= hi) ”) &&
    emp **
    ((IntArray.seg base 0 hi arr))
    |--
    (
    TT &&
    (“ (cursor = (base + (index * sizeof(INT)))) ”) &&
    (“ (0 < index) ”) &&
    emp **
    ((IntArray.missing_i base (index - 1) 0 hi arr))
    ) ** (
    ALL (value : Z),
      TT &&
      (“ (value = (Znth (index - 1) arr  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (cursor + ((- 1) * sizeof(INT))) value))
      ).

Definition solver_qcp_strategy73 :=
  forall (index : Z) (hi : Z) (cursor : Z) (base : Z) (arr : (@list Z)),
    TT &&
    (“ (cursor = (base + (index * sizeof(INT)))) ”) &&
    (“ (0 < index) ”) &&
    (“ (index <= hi) ”) &&
    emp **
    ((IntArray.missing_i base (index - 1) 0 hi arr)) **
    ((poly_store FET_int (cursor + ((- 1) * sizeof(INT))) (Znth (index - 1) arr  0)))
    |--
    (
    TT &&
    (“ (cursor = (base + (index * sizeof(INT)))) ”) &&
    emp **
    ((IntArray.seg base 0 hi arr))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy12 :=
  forall (i : Z) (hi : Z) (lo : Z) (p : Z) (l : (@list fp64)),
    TT &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((DoubleArray.seg p lo hi l))
    |--
    (
    TT &&
    emp **
    ((DoubleArray.missing_i p i lo hi l))
    ) ** (
    ALL (v : fp64),
      TT &&
      (“ (v = (double_Znth (i - lo) l)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_double (p + (i * sizeof(DOUBLE))) v))
      ).

Definition solver_qcp_strategy36 :=
  forall (hi : Z) (lo : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (lo <= 0) ”) &&
    (“ (0 < hi) ”) &&
    emp **
    ((IntArray.seg p lo hi l))
    |--
    (
    TT &&
    emp **
    ((IntArray.missing_i p 0 lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (0 - lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int p v))
      ).

Definition solver_qcp_strategy69 :=
  forall (hi : Z) (q : Z) (p : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    (“ (lo <= 0) ”) &&
    (“ (0 < hi) ”) &&
    emp **
    ((IntArray.seg p lo hi l))
    |--
    (
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    emp **
    ((IntArray.missing_i p 0 lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (0 - lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int q v))
      ).

Definition solver_qcp_strategy37 :=
  forall (i : Z) (hi : Z) (q : Z) (p : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((IntArray.seg p lo hi l))
    |--
    (
    TT &&
    emp **
    ((IntArray.missing_i p i lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (i - lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (q + (i * sizeof(INT))) v))
      ).

Definition solver_qcp_strategy39 :=
  forall (xp : Z) (xr : Z) (yp : Z) (w : Z) (db : dbmap) (xa : fp32) (xw : (@list Z)) (activities : (@list fp32)),
    TT &&
    (“ (xp = yp) ”) &&
    (“ (xp = xr) ”) &&
    emp **
    ((poly_store FET_int (clause_hdr_addr xp) w)) **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    |--
    (
    TT &&
    emp **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = w) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (clause_hdr_addr yp) v))
      ).

Definition solver_qcp_strategy40 :=
  forall (xp : Z) (xr : Z) (yp : Z) (size : Z) (a : fp32) (db : dbmap) (xa : fp32) (xw : (@list Z)) (activities : (@list fp32)),
    TT &&
    (“ (xp = yp) ”) &&
    (“ (xp = xr) ”) &&
    emp **
    ((poly_store FET_float (clause_act_addr xp size) a)) **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    |--
    (
    TT &&
    emp **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    ) ** (
    ALL (other_size : Z) (b : fp32),
      TT &&
      (“ (b = a) ”) &&
      (“ (other_size = size) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_float (clause_act_addr yp other_size) b))
      ).

Definition solver_qcp_strategy41 :=
  forall (hi : Z) (q : Z) (cp : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = (clause_lits_addr cp)) ”) &&
    (“ (lo <= 0) ”) &&
    (“ (0 < hi) ”) &&
    emp **
    ((IntArray.seg (clause_lits_addr cp) lo hi l))
    |--
    (
    TT &&
    emp **
    ((IntArray.missing_i (clause_lits_addr cp) 0 lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (0 - lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int q v))
      ).

Definition solver_qcp_strategy61 :=
  forall (i : Z) (n : Z) (p : Z) (words : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((PtrArray.missing_i p i 0 n (@replace_Znth Z i (@Znth Z i words 0) (@replace_Znth Z i (@Znth Z i words 0) words))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PtrArray.missing_i p i 0 n words))
    ).

Definition solver_qcp_strategy75 :=
  forall (level : Z) (wl : Z) (M : msolver) (s : Z),
    TT &&
    emp **
    ((solver_cancel_root_frame s level M wl)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_cancel_pre s level M wl))
    ).

Definition solver_qcp_strategy93 :=
  forall (i : Z) (n : Z) (wm : (@list (@list Z))) (b : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < (2 * n)) ”) &&
    emp **
    ((wlists_rep b n wm))
    |--
    (
    TT &&
    (“ ((@Zlength (@list Z) wm) = (2 * n)) ”) &&
    emp **
    ((VecpArray.full b (2 * n) wm))
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      emp **
      ((Vecp.rep (Vecp.slot b i) l) || (Vecp.rep_ptr (Vecp.slot b i) p l)) -*
      TT &&
      emp **
      ((Vecp.rep (Vecp.slot b i) l) || (Vecp.rep_ptr (Vecp.slot b i) p l))
      ).

Definition solver_qcp_strategy94 :=
  forall (i : Z) (n : Z) (b : Z) (w : Z) (wm : (@list (@list Z))),
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < (2 * n)) ”) &&
    emp **
    ((wlists_rep b n wm))
    |--
    (
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    (“ ((@Zlength (@list Z) wm) = (2 * n)) ”) &&
    emp **
    ((VecpArray.full b (2 * n) wm))
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      emp **
      ((Vecp.rep w l) || (Vecp.rep_ptr w p l)) -*
      TT &&
      emp **
      ((Vecp.rep w l) || (Vecp.rep_ptr w p l))
      ).

Definition solver_qcp_strategy13 :=
  forall (i : Z) (hi : Z) (lo : Z) (l : (@list fp64)) (p : Z),
    TT &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((DoubleArray.missing_i p i lo hi l)) **
    ((poly_store FET_double (p + (i * sizeof(DOUBLE))) (double_Znth (i - lo) l)))
    |--
    (
    TT &&
    emp **
    ((DoubleArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy67 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((IntArray.missing_i p i lo hi l)) **
    ((poly_store FET_int (q + (j * sizeof(INT))) (Znth (i - lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy42 :=
  forall (i : Z) (hi : Z) (cp : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = (clause_lits_addr cp)) ”) &&
    (“ (i = 0) ”) &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((IntArray.missing_i (clause_lits_addr cp) i lo hi l)) **
    ((poly_store FET_int q (Znth (i - lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg (clause_lits_addr cp) lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy58 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((PtrArray.missing_i p i lo hi l)) **
    ((poly_store FET_ptr (q + (j * sizeof(PTR))) (Znth (i - lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((PtrArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy57 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((CharArray.missing_i p i lo hi l)) **
    ((poly_store FET_char (q + (j * sizeof(CHAR))) (Znth (i - lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((CharArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy76 :=
  forall (q : Z) (cp : Z),
    TT &&
    (“ (q = (clause_lits_addr cp)) ”) &&
    emp **
    ((poly_undef_store FET_int ((clause_lits_addr cp) + sizeof(INT))))
    |--
    (
    TT &&
    (“ (q = (clause_lits_addr cp)) ”) &&
    emp **
    ((poly_undef_store FET_int (q + (1 * sizeof(INT)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy77 :=
  forall (q : Z) (cp : Z),
    TT &&
    (“ (q = (clause_lits_addr cp)) ”) &&
    emp **
    ((poly_undef_store FET_int (clause_lits_addr cp)))
    |--
    (
    TT &&
    (“ (q = (clause_lits_addr cp)) ”) &&
    emp **
    ((poly_undef_store FET_int (q + (0 * sizeof(INT)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy16 :=
  forall (y : Z) (s : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y))
    ) ** (
    ALL (qtail : Z) (cap : Z) (trail : (@list Z)) (levels : (@list Z)) (assigns : (@list Z)) (n : Z) (reasons : (@list Z)) (trl : Z) (rsn : Z) (lvl : Z) (asg : Z) (lim : (@list Z)),
      TT &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ ((@Zlength Z assigns) = n) ”) &&
      (“ ((@Zlength Z levels) = n) ”) &&
      (“ ((@Zlength Z reasons) = n) ”) &&
      (“ ((@Zlength Z trail) = qtail) ”) &&
      (“ (0 <= qtail) ”) &&
      (“ (qtail <= cap) ”) &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") qtail)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
      ((CharArray.seg asg 0 n assigns)) **
      ((solver_char_tail asg n cap)) **
      ((IntArray.seg lvl 0 n levels)) **
      ((solver_int_tail lvl n cap)) **
      ((PtrArray.seg rsn 0 n reasons)) **
      ((solver_ptr_tail rsn n cap)) **
      ((IntArray.seg trl 0 qtail trail)) **
      ((solver_int_tail trl qtail cap)) **
      ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") lim)) -*
      TT &&
      emp **
      ((enqueue_state_at s asg lvl n cap qtail assigns levels reasons trail lim))
      ).

Definition solver_qcp_strategy23 :=
  forall (s : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_levels_slice_at s M lvl))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (order : (@list Z)) (orderpos : (@list Z)),
      TT &&
      emp -*
      TT &&
      emp **
      ((solver_levels_slice_at s (msolver_heap_project M orderpos order) lvl))
      ).

Definition solver_qcp_strategy29 :=
  forall (i : Z) (j : Z) (n : Z) (words : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (i = j) ”) &&
    emp **
    ((removable_reason_array_hole p i n words)) **
    ((poly_store FET_ptr (p + (j * sizeof(PTR))) (@Znth Z i words 0)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PtrArray.seg p 0 n words))
    ).

Definition solver_qcp_strategy33 :=
  forall (s : Z) (l : (@list Z)),
    TT &&
    emp **
    ((solver_clauses_rep s l))
    |--
    (
    TT &&
    emp **
    ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") l))
    ) ** (
    ALL (p : Z) (w : (@list Z)),
      TT &&
      emp **
      ((Vecp.rep_ptr &( ((s)) # "solver_t" ->ₛ "clauses") p w) || (Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") w)) -*
      TT &&
      emp **
      ((Vecp.rep_ptr &( ((s)) # "solver_t" ->ₛ "clauses") p w) || (Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") w))
      ).

Definition solver_qcp_strategy34 :=
  forall (s : Z) (w : (@list Z)) (p : Z),
    TT &&
    emp **
    ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") w) || (Vecp.rep_ptr &( ((s)) # "solver_t" ->ₛ "clauses") p w))
    |--
    (
    TT &&
    emp **
    ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") w) || (Vecp.rep_ptr &( ((s)) # "solver_t" ->ₛ "clauses") p w))
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      emp **
      ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") l)) -*
      TT &&
      emp **
      ((solver_clauses_rep s l))
      ).

Definition solver_qcp_strategy43 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_root_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy44 :=
  forall (lvl : Z) (wl : Z) (s : Z) (M : msolver),
    TT &&
    emp **
    ((solver_search_root_frame_at s M lvl wl)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    ).

Definition solver_qcp_strategy45 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)))) **
    ((solver_int_tail lvl (ms_size M) (ms_cap M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_root_payload s M wl))
    ).

Definition solver_qcp_strategy46 :=
  forall (wl : Z) (s : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_search_root_payload s M wl)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)))) **
    ((solver_int_tail lvl (ms_size M) (ms_cap M)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    ).

Definition solver_qcp_strategy47 :=
  forall (s : Z) (asg : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_assigns_levels_at s M asg lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_root_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy48 :=
  forall (s : Z) (asg : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_assigns_levels_at s M asg lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") (stats_conflicts (ms_stats M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_conflict_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy49 :=
  forall (s : Z) (asg : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_assigns_levels_at s M asg lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") (ms_size M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)))) **
    ((poly_store FET_double &( ((s)) # "solver_t" ->ₛ "progress_estimate") (ms_progress M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_progress_frame_at s M asg lvl wl))
    ).

Definition solver_qcp_strategy50 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") (stats_starts (ms_stats M)))) **
    ((poly_store FET_double &( ((s)) # "solver_t" ->ₛ "var_decay") (ms_var_decay M))) **
    ((poly_store FET_float &( ((s)) # "solver_t" ->ₛ "cla_decay") (ms_cla_decay M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "model") (ms_model M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_init_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy51 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") (ms_qtail M))) **
    ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "learnts") (db_words (ms_learnt M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_reducedb_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy52 :=
  forall (lvl : Z) (wl : Z) (s : Z) (M : msolver),
    TT &&
    emp **
    ((solver_search_reducedb_frame_at s M lvl wl)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") (ms_qtail M))) **
    ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "learnts") (db_words (ms_learnt M))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    ).

Definition solver_qcp_strategy53 :=
  forall (s : Z) (rsn : Z) (trl : Z) (wl : Z) (tgs : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_analyze_at s M rsn lvl trl tgs wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") (stats_max_literals (ms_stats M)))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") (stats_tot_literals (ms_stats M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_literal_stats_frame_at s M rsn lvl trl tgs wl))
    ).

Definition solver_qcp_strategy54 :=
  forall (s : Z) (rsn : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_reasons_levels_wl_at s M rsn lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") (mt_qhead (ms_core M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_assigns") (ms_simpdb_assigns M))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") (ms_simpdb_props M))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") (stats_clauses_literals (ms_stats M)))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") (stats_learnts_literals (ms_stats M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_simplify_finish_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy55 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    EX (values_ptr : Z),
      (
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") (ms_size M))) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") values_ptr)) **
      ((CharArray.seg values_ptr 0 (ms_size M) (mt_assigns (ms_core M)))) **
      ((solver_char_tail values_ptr (ms_size M) (ms_cap M))) **
      ((Veci.rep &( ((s)) # "solver_t" ->ₛ "model") (ms_model M)))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp **
      ((solver_model_copy_frame_at s M lvl wl))
      ).

Definition solver_qcp_strategy56 :=
  forall (M : msolver) (rsn : Z) (trl : Z) (wl : Z) (tgs : Z) (s : Z) (lvl : Z) (n : Z),
    TT &&
    (“ (solver_shape M) ”) &&
    emp **
    ((solver_reason_levels_frame_at s M trl tgs wl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((PtrArray.seg rsn 0 n (ms_reason_words M))) **
    ((solver_ptr_tail rsn n (ms_cap M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 n (mt_levels (ms_core M)))) **
    ((solver_int_tail lvl n (ms_cap M)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_analyze_at s M rsn lvl trl tgs wl))
    ).

Definition solver_qcp_strategy62 :=
  forall (s : Z) (sz : Z) (act : Z) (opos : Z) (lvl : Z) (tgs : Z) (trl : Z) (rsn : Z) (asg : Z) (wl : Z) (M : msolver),
    TT &&
    emp **
    ((setnvars_arrays_at s M sz wl act asg opos rsn lvl trl tgs))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") (ms_qtail M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") wl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") act)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") opos)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") tgs)) **
    ((DoubleArray.seg act 0 sz (ms_activity M))) **
    ((solver_double_tail act sz (ms_cap M))) **
    ((CharArray.seg asg 0 sz (mt_assigns (ms_core M)))) **
    ((solver_char_tail asg sz (ms_cap M))) **
    ((IntArray.seg opos 0 sz (ms_orderpos M))) **
    ((solver_int_tail opos sz (ms_cap M))) **
    ((PtrArray.seg rsn 0 sz (ms_reason_words M))) **
    ((solver_ptr_tail rsn sz (ms_cap M))) **
    ((IntArray.seg lvl 0 sz (mt_levels (ms_core M)))) **
    ((solver_int_tail lvl sz (ms_cap M))) **
    ((CharArray.seg tgs 0 sz (ms_tags M))) **
    ((solver_char_tail tgs sz (ms_cap M))) **
    ((IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)))) **
    ((solver_int_tail trl (ms_qtail M) (ms_cap M))) **
    ((wlists_rep wl sz (ms_wm M))) **
    ((solver_wlists_tail wl (2 * sz) (2 * (ms_cap M))))
    ) ** (
    ALL (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y))
      ).

Definition solver_qcp_strategy63 :=
  forall (s : Z) (n : Z) (opos : Z) (lvl : Z) (tgs : Z) (wl : Z) (trl : Z) (rsn : Z) (act : Z) (M : msolver),
    TT &&
    emp **
    ((solver_analyze_open_at s M n act opos rsn lvl trl tgs wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") n)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") (ms_qtail M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") act)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") opos)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") tgs)) **
    ((DoubleArray.seg act 0 n (ms_activity M))) **
    ((IntArray.seg opos 0 n (ms_orderpos M))) **
    ((PtrArray.seg rsn 0 n (ms_reason_words M))) **
    ((IntArray.seg lvl 0 n (mt_levels (ms_core M)))) **
    ((IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)))) **
    ((CharArray.seg tgs 0 n (ms_tags M))) **
    ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "learnts") (db_words (ms_learnt M)))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "tagged") (ms_tagged M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "order") (ms_order M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)))) **
    ((poly_store FET_double &( ((s)) # "solver_t" ->ₛ "var_inc") (ms_var_inc M))) **
    ((poly_store FET_float &( ((s)) # "solver_t" ->ₛ "cla_inc") (ms_cla_inc M))) **
    ((solver_analyze_inert_at s M n act opos rsn lvl trl tgs)) **
    ((solver_analyze_frame s M wl))
    ) ** (
    ALL (dl : (@list fp64)) (yd : fp64) (yf : fp32) (hi : Z) (l : (@list Z)) (lo : Z) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y) || (poly_store FET_double &( ((s)) # "solver_t" ->ₛ "var_inc") yd) || (poly_store FET_float &( ((s)) # "solver_t" ->ₛ "cla_inc") yf) || (Vecp.rep &( ((s)) # "solver_t" ->ₛ "learnts") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "tagged") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "order") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l) || (DoubleArray.seg act lo hi dl) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg lvl lo hi l) || (IntArray.seg trl lo hi l) || (CharArray.seg tgs lo hi l) || (poly_store FET_char (tgs + (i * sizeof(CHAR))) y) || (poly_store FET_int (lvl + (i * sizeof(INT))) y) || (poly_store FET_int (trl + (i * sizeof(INT))) y) || (poly_store FET_ptr (rsn + (i * sizeof(PTR))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y) || (poly_store FET_double &( ((s)) # "solver_t" ->ₛ "var_inc") yd) || (poly_store FET_float &( ((s)) # "solver_t" ->ₛ "cla_inc") yf) || (Vecp.rep &( ((s)) # "solver_t" ->ₛ "learnts") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "tagged") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "order") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l) || (DoubleArray.seg act lo hi dl) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg lvl lo hi l) || (IntArray.seg trl lo hi l) || (CharArray.seg tgs lo hi l) || (poly_store FET_char (tgs + (i * sizeof(CHAR))) y) || (poly_store FET_int (lvl + (i * sizeof(INT))) y) || (poly_store FET_int (trl + (i * sizeof(INT))) y) || (poly_store FET_ptr (rsn + (i * sizeof(PTR))) y))
      ).

Definition solver_qcp_strategy64 :=
  forall (s : Z) (act : Z) (opos : Z) (trl : Z) (opos_l : (@list Z)) (ord_l : (@list Z)) (wl : Z) (rsn_l : (@list Z)) (asg_l : (@list Z)) (rsn : Z) (asg : Z) (M : msolver),
    TT &&
    emp **
    ((solver_cancel_open_at s M act asg opos rsn trl asg_l opos_l rsn_l ord_l wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") (ms_size M))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") (mt_qhead (ms_core M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") (ms_qtail M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") act)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") opos)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((DoubleArray.seg act 0 (ms_size M) (ms_activity M))) **
    ((CharArray.seg asg 0 (ms_size M) asg_l)) **
    ((IntArray.seg opos 0 (ms_size M) opos_l)) **
    ((PtrArray.seg rsn 0 (ms_size M) rsn_l)) **
    ((IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)))) **
    ((solver_cancel_undef_tail M act asg opos rsn trl)) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "order") ord_l)) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)))) **
    ((solver_cancel_frame s M wl))
    ) ** (
    ALL (lo : Z) (l : (@list Z)) (hi : Z) (dl : (@list fp64)) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "order") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l) || (DoubleArray.seg act lo hi dl) || (CharArray.seg asg lo hi l) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg trl lo hi l) || (poly_store FET_int (trl + (i * sizeof(INT))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "order") l) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l) || (DoubleArray.seg act lo hi dl) || (CharArray.seg asg lo hi l) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg trl lo hi l) || (poly_store FET_int (trl + (i * sizeof(INT))) y))
      ).

Definition solver_qcp_strategy65 :=
  forall (s : Z) (cap : Z) (rsn : Z) (stats0 : (@list Z)) (reasons0 : (@list Z)) (wm : (@list (@list Z))) (wl : Z) (n : Z),
    TT &&
    emp **
    ((clause_remove_open_at s n cap wl rsn wm stats0 reasons0))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") n)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((PtrArray.seg rsn 0 n reasons0)) **
    ((solver_ptr_tail rsn n cap)) **
    ((solver_wlists_handle s wl)) **
    ((wlists_rep wl n wm)) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") (stats_starts stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "decisions") (stats_decisions stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") (stats_propagations stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") (stats_inspects stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") (stats_conflicts stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses") (stats_clauses stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") (stats_clauses_literals stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts") (stats_learnts stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") (stats_learnts_literals stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") (stats_max_literals stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") (stats_tot_literals stats0)))
    ) ** (
    ALL (lo : Z) (hi : Z) (wn : Z) (wmd : (@list (@list Z))) (l : (@list Z)) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "decisions") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") y) || (wlists_rep wl wn wmd) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (poly_store FET_ptr (rsn + (i * sizeof(PTR))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "decisions") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") y) || (wlists_rep wl wn wmd) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (poly_store FET_ptr (rsn + (i * sizeof(PTR))) y))
      ).

Definition solver_qcp_strategy66 :=
  forall (s : Z) (wl : Z) (rsn : Z) (trl : Z) (lvl : Z) (asg : Z) (M : msolver),
    TT &&
    emp **
    ((solver_propagate_open_at s M wl asg rsn lvl trl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") (mt_qhead (ms_core M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") (ms_qtail M))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") (ms_simpdb_props M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") wl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "binary") (ms_binary M))) **
    ((CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)))) **
    ((solver_char_tail asg (ms_size M) (ms_cap M))) **
    ((PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M))) **
    ((solver_ptr_tail rsn (ms_size M) (ms_cap M))) **
    ((IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)))) **
    ((solver_int_tail lvl (ms_size M) (ms_cap M))) **
    ((IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)))) **
    ((solver_int_tail trl (ms_qtail M) (ms_cap M))) **
    ((Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") (mt_lim (ms_core M)))) **
    ((wlists_rep wl (ms_size M) (ms_wm M))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") (stats_propagations (ms_stats M)))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") (stats_inspects (ms_stats M)))) **
    ((solver_propagate_frame s M))
    ) ** (
    ALL (l : (@list Z)) (wmd : (@list (@list Z))) (wn : Z) (hi : Z) (lo : Z) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "binary") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l) || (wlists_rep wl wn wmd) || (CharArray.seg asg lo hi l) || (CharArray.undef_seg asg lo hi) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (IntArray.seg lvl lo hi l) || (IntArray.undef_seg lvl lo hi) || (IntArray.seg trl lo hi l) || (IntArray.undef_seg trl lo hi) || (poly_store FET_char (asg + (i * sizeof(CHAR))) y) || (poly_store FET_ptr (rsn + (i * sizeof(PTR))) y) || (poly_store FET_int (lvl + (i * sizeof(INT))) y) || (poly_store FET_int (trl + (i * sizeof(INT))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "binary") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (Veci.rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l) || (wlists_rep wl wn wmd) || (CharArray.seg asg lo hi l) || (CharArray.undef_seg asg lo hi) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (IntArray.seg lvl lo hi l) || (IntArray.undef_seg lvl lo hi) || (IntArray.seg trl lo hi l) || (IntArray.undef_seg trl lo hi) || (poly_store FET_char (asg + (i * sizeof(CHAR))) y) || (poly_store FET_ptr (rsn + (i * sizeof(PTR))) y) || (poly_store FET_int (lvl + (i * sizeof(INT))) y) || (poly_store FET_int (trl + (i * sizeof(INT))) y))
      ).

Definition solver_qcp_strategy74 :=
  forall (s : Z) (M : msolver) (wl : Z) (level : Z),
    TT &&
    emp **
    ((solver_cancel_pre s level M wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") (ms_root_level M))) **
    ((solver_cancel_root_frame s level M wl))
    ) ** (
    ALL (value : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") value)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") value))
      ).

Definition solver_qcp_strategy78 :=
  forall (p : Z) (cap : Z) (lo : Z),
    TT &&
    emp **
    ((solver_int_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((IntArray.undef_seg p lo physical))
      ) ** (
      ALL (hi : Z),
        TT &&
        emp **
        ((IntArray.undef_seg p lo hi)) -*
        TT &&
        emp **
        ((IntArray.undef_seg p lo hi))
        ).

Definition solver_qcp_strategy79 :=
  forall (p : Z) (physical : Z) (lo : Z),
    TT &&
    emp **
    ((IntArray.undef_seg p lo physical))
    |--
    (
    TT &&
    emp **
    ((IntArray.undef_seg p lo physical))
    ) ** (
    ALL (cap : Z),
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((IntArray.undef_seg p lo physical)) -*
      TT &&
      emp **
      ((solver_int_tail p lo cap))
      ).

Definition solver_qcp_strategy80 :=
  forall (p : Z) (cap : Z) (lo : Z),
    TT &&
    emp **
    ((solver_ptr_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((PtrArray.undef_seg p lo physical))
      ) ** (
      ALL (hi : Z),
        TT &&
        emp **
        ((PtrArray.undef_seg p lo hi)) -*
        TT &&
        emp **
        ((PtrArray.undef_seg p lo hi))
        ).

Definition solver_qcp_strategy81 :=
  forall (p : Z) (physical : Z) (lo : Z),
    TT &&
    emp **
    ((PtrArray.undef_seg p lo physical))
    |--
    (
    TT &&
    emp **
    ((PtrArray.undef_seg p lo physical))
    ) ** (
    ALL (cap : Z),
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((PtrArray.undef_seg p lo physical)) -*
      TT &&
      emp **
      ((solver_ptr_tail p lo cap))
      ).

Definition solver_qcp_strategy82 :=
  forall (p : Z) (cap : Z) (lo : Z),
    TT &&
    emp **
    ((solver_char_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((CharArray.undef_seg p lo physical))
      ) ** (
      ALL (hi : Z),
        TT &&
        emp **
        ((CharArray.undef_seg p lo hi)) -*
        TT &&
        emp **
        ((CharArray.undef_seg p lo hi))
        ).

Definition solver_qcp_strategy83 :=
  forall (p : Z) (physical : Z) (lo : Z),
    TT &&
    emp **
    ((CharArray.undef_seg p lo physical))
    |--
    (
    TT &&
    emp **
    ((CharArray.undef_seg p lo physical))
    ) ** (
    ALL (cap : Z),
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((CharArray.undef_seg p lo physical)) -*
      TT &&
      emp **
      ((solver_char_tail p lo cap))
      ).

Definition solver_qcp_strategy84 :=
  forall (p : Z) (cap : Z) (lo : Z),
    TT &&
    emp **
    ((solver_double_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((DoubleArray.undef_seg p lo physical))
      ) ** (
      ALL (hi : Z),
        TT &&
        emp **
        ((DoubleArray.undef_seg p lo hi)) -*
        TT &&
        emp **
        ((DoubleArray.undef_seg p lo hi))
        ).

Definition solver_qcp_strategy85 :=
  forall (p : Z) (physical : Z) (lo : Z),
    TT &&
    emp **
    ((DoubleArray.undef_seg p lo physical))
    |--
    (
    TT &&
    emp **
    ((DoubleArray.undef_seg p lo physical))
    ) ** (
    ALL (cap : Z),
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((DoubleArray.undef_seg p lo physical)) -*
      TT &&
      emp **
      ((solver_double_tail p lo cap))
      ).

Definition solver_qcp_strategy86 :=
  forall (p : Z) (cap : Z) (lo : Z),
    TT &&
    emp **
    ((solver_wlists_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((VecpArray.undef_seg p lo physical))
      ) ** (
      ALL (hi : Z),
        TT &&
        emp **
        ((VecpArray.undef_seg p lo hi)) -*
        TT &&
        emp **
        ((VecpArray.undef_seg p lo hi))
        ).

Definition solver_qcp_strategy87 :=
  forall (p : Z) (physical : Z) (lo : Z),
    TT &&
    emp **
    ((VecpArray.undef_seg p lo physical))
    |--
    (
    TT &&
    emp **
    ((VecpArray.undef_seg p lo physical))
    ) ** (
    ALL (cap : Z),
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((VecpArray.undef_seg p lo physical)) -*
      TT &&
      emp **
      ((solver_wlists_tail p lo cap))
      ).

Definition solver_qcp_strategy88 :=
  forall (i : Z) (cap : Z) (p : Z) (lo : Z),
    TT &&
    (“ (lo <= i) ”) &&
    (“ (i < cap) ”) &&
    emp **
    ((solver_int_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((IntArray.undef_seg p lo physical))
      ) ** (
      ALL (value : Z),
        TT &&
        emp **
        ((poly_store FET_int (p + (i * sizeof(INT))) value) || (poly_undef_store FET_int (p + (i * sizeof(INT))))) -*
        TT &&
        emp **
        ((poly_store FET_int (p + (i * sizeof(INT))) value) || (poly_undef_store FET_int (p + (i * sizeof(INT)))))
        ).

Definition solver_qcp_strategy89 :=
  forall (i : Z) (cap : Z) (p : Z) (lo : Z),
    TT &&
    (“ (lo <= i) ”) &&
    (“ (i < cap) ”) &&
    emp **
    ((solver_ptr_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((PtrArray.undef_seg p lo physical))
      ) ** (
      ALL (value : Z),
        TT &&
        emp **
        ((poly_store FET_ptr (p + (i * sizeof(PTR))) value) || (poly_undef_store FET_ptr (p + (i * sizeof(PTR))))) -*
        TT &&
        emp **
        ((poly_store FET_ptr (p + (i * sizeof(PTR))) value) || (poly_undef_store FET_ptr (p + (i * sizeof(PTR)))))
        ).

Definition solver_qcp_strategy90 :=
  forall (i : Z) (cap : Z) (p : Z) (lo : Z),
    TT &&
    (“ (lo <= i) ”) &&
    (“ (i < cap) ”) &&
    emp **
    ((solver_char_tail p lo cap))
    |--
    EX (physical : Z),
      (
      TT &&
      (“ (cap <= physical) ”) &&
      (“ (physical <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok physical p) ”) &&
      emp **
      ((CharArray.undef_seg p lo physical))
      ) ** (
      ALL (value : Z),
        TT &&
        emp **
        ((poly_store FET_char (p + (i * sizeof(CHAR))) value) || (poly_undef_store FET_char (p + (i * sizeof(CHAR))))) -*
        TT &&
        emp **
        ((poly_store FET_char (p + (i * sizeof(CHAR))) value) || (poly_undef_store FET_char (p + (i * sizeof(CHAR)))))
        ).

Definition solver_qcp_strategy92 :=
  forall (words : (@list Z)) (F : cnf) (A_inst : (@list literal)) (root : Z) (A_arr : (@list literal)) (n : Z) (M : msolver) (c : Z) (s : Z) (lvl : Z) (wl : Z) (begin : Z),
    TT &&
    emp **
    ((clause_new_pending_at_root s begin lvl n F A_arr A_inst M words c 0 wl root))
    |--
    (
    TT &&
    (“ (n = (ms_size M)) ”) &&
    (“ (clause_new_stage_ready_root n F A_arr A_inst M M words 0 root) ”) &&
    (“ (clause_allocator_fresh M c) ”) &&
    (“ ((lit_neg_c (@Znth Z 0 words 0)) <> (lit_neg_c (@Znth Z 1 words 0))) ”) &&
    emp **
    ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") (db_words (ms_prob M)))) **
    ((Vecp.rep (Vecp.slot wl (lit_neg_c (@Znth Z 0 words 0))) (@app Z (@Znth (@list Z) (lit_neg_c (@Znth Z 0 words 0)) (ms_wm M) (@nil Z)) (@cons Z (clause_watch_word c words (@Znth Z 1 words 0)) (@nil Z))))) **
    ((Vecp.rep (Vecp.slot wl (lit_neg_c (@Znth Z 1 words 0))) (@app Z (@Znth (@list Z) (lit_neg_c (@Znth Z 1 words 0)) (ms_wm M) (@nil Z)) (@cons Z (clause_watch_word c words (@Znth Z 0 words 0)) (@nil Z))))) **
    ((MiniSatClause.rep c (msat_false) words)) **
    ((clause_db_rep (ms_prob M))) **
    ((clause_new_transaction_rest_at_gen s wl (lit_neg_c (@Znth Z 0 words 0)) (lit_neg_c (@Znth Z 1 words 0)) M lvl 0)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") n)) **
    ((IntArray.seg begin 0 (@Zlength Z words) words))
    ) ** (
    ALL (target_l : (@list Z)),
      TT &&
      emp **
      ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") target_l)) -*
      TT &&
      emp **
      ((Vecp.rep &( ((s)) # "solver_t" ->ₛ "clauses") target_l))
      ).

Definition solver_qcp_strategy14 :=
  forall (i : Z) (hi : Z) (lo : Z) (l : (@list fp64)) (v : fp64) (p : Z),
    TT &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((DoubleArray.missing_i p i lo hi l)) **
    ((poly_store FET_double (p + (i * sizeof(DOUBLE))) v))
    |--
    (
    TT &&
    emp **
    ((DoubleArray.seg p lo hi (@replace_Znth fp64 (i - lo) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy59 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    emp **
    ((CharArray.missing_i p i lo hi l)) **
    ((poly_store FET_char (q + (j * sizeof(CHAR))) v))
    |--
    (
    TT &&
    emp **
    ((CharArray.seg p lo hi (@replace_Znth Z (i - lo) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy38 :=
  forall (i : Z) (j : Z) (lo : Z) (p : Z) (q : Z) (hi : Z) (l : (@list Z)) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    (“ (lo <= i) ”) &&
    (“ (i < hi) ”) &&
    (“ (i = j) ”) &&
    emp **
    ((IntArray.missing_i p i lo hi l)) **
    ((poly_store FET_int (q + (j * sizeof(INT))) v))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg p lo hi (@replace_Znth Z (i - lo) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type solver_qcp_Strategy_Correct.

  Axiom solver_qcp_strategy72_correctness : solver_qcp_strategy72.
  Axiom solver_qcp_strategy73_correctness : solver_qcp_strategy73.
  Axiom solver_qcp_strategy12_correctness : solver_qcp_strategy12.
  Axiom solver_qcp_strategy36_correctness : solver_qcp_strategy36.
  Axiom solver_qcp_strategy69_correctness : solver_qcp_strategy69.
  Axiom solver_qcp_strategy37_correctness : solver_qcp_strategy37.
  Axiom solver_qcp_strategy39_correctness : solver_qcp_strategy39.
  Axiom solver_qcp_strategy40_correctness : solver_qcp_strategy40.
  Axiom solver_qcp_strategy41_correctness : solver_qcp_strategy41.
  Axiom solver_qcp_strategy61_correctness : solver_qcp_strategy61.
  Axiom solver_qcp_strategy75_correctness : solver_qcp_strategy75.
  Axiom solver_qcp_strategy93_correctness : solver_qcp_strategy93.
  Axiom solver_qcp_strategy94_correctness : solver_qcp_strategy94.
  Axiom solver_qcp_strategy13_correctness : solver_qcp_strategy13.
  Axiom solver_qcp_strategy67_correctness : solver_qcp_strategy67.
  Axiom solver_qcp_strategy42_correctness : solver_qcp_strategy42.
  Axiom solver_qcp_strategy58_correctness : solver_qcp_strategy58.
  Axiom solver_qcp_strategy57_correctness : solver_qcp_strategy57.
  Axiom solver_qcp_strategy76_correctness : solver_qcp_strategy76.
  Axiom solver_qcp_strategy77_correctness : solver_qcp_strategy77.
  Axiom solver_qcp_strategy16_correctness : solver_qcp_strategy16.
  Axiom solver_qcp_strategy23_correctness : solver_qcp_strategy23.
  Axiom solver_qcp_strategy29_correctness : solver_qcp_strategy29.
  Axiom solver_qcp_strategy33_correctness : solver_qcp_strategy33.
  Axiom solver_qcp_strategy34_correctness : solver_qcp_strategy34.
  Axiom solver_qcp_strategy43_correctness : solver_qcp_strategy43.
  Axiom solver_qcp_strategy44_correctness : solver_qcp_strategy44.
  Axiom solver_qcp_strategy45_correctness : solver_qcp_strategy45.
  Axiom solver_qcp_strategy46_correctness : solver_qcp_strategy46.
  Axiom solver_qcp_strategy47_correctness : solver_qcp_strategy47.
  Axiom solver_qcp_strategy48_correctness : solver_qcp_strategy48.
  Axiom solver_qcp_strategy49_correctness : solver_qcp_strategy49.
  Axiom solver_qcp_strategy50_correctness : solver_qcp_strategy50.
  Axiom solver_qcp_strategy51_correctness : solver_qcp_strategy51.
  Axiom solver_qcp_strategy52_correctness : solver_qcp_strategy52.
  Axiom solver_qcp_strategy53_correctness : solver_qcp_strategy53.
  Axiom solver_qcp_strategy54_correctness : solver_qcp_strategy54.
  Axiom solver_qcp_strategy55_correctness : solver_qcp_strategy55.
  Axiom solver_qcp_strategy56_correctness : solver_qcp_strategy56.
  Axiom solver_qcp_strategy62_correctness : solver_qcp_strategy62.
  Axiom solver_qcp_strategy63_correctness : solver_qcp_strategy63.
  Axiom solver_qcp_strategy64_correctness : solver_qcp_strategy64.
  Axiom solver_qcp_strategy65_correctness : solver_qcp_strategy65.
  Axiom solver_qcp_strategy66_correctness : solver_qcp_strategy66.
  Axiom solver_qcp_strategy74_correctness : solver_qcp_strategy74.
  Axiom solver_qcp_strategy78_correctness : solver_qcp_strategy78.
  Axiom solver_qcp_strategy79_correctness : solver_qcp_strategy79.
  Axiom solver_qcp_strategy80_correctness : solver_qcp_strategy80.
  Axiom solver_qcp_strategy81_correctness : solver_qcp_strategy81.
  Axiom solver_qcp_strategy82_correctness : solver_qcp_strategy82.
  Axiom solver_qcp_strategy83_correctness : solver_qcp_strategy83.
  Axiom solver_qcp_strategy84_correctness : solver_qcp_strategy84.
  Axiom solver_qcp_strategy85_correctness : solver_qcp_strategy85.
  Axiom solver_qcp_strategy86_correctness : solver_qcp_strategy86.
  Axiom solver_qcp_strategy87_correctness : solver_qcp_strategy87.
  Axiom solver_qcp_strategy88_correctness : solver_qcp_strategy88.
  Axiom solver_qcp_strategy89_correctness : solver_qcp_strategy89.
  Axiom solver_qcp_strategy90_correctness : solver_qcp_strategy90.
  Axiom solver_qcp_strategy92_correctness : solver_qcp_strategy92.
  Axiom solver_qcp_strategy14_correctness : solver_qcp_strategy14.
  Axiom solver_qcp_strategy59_correctness : solver_qcp_strategy59.
  Axiom solver_qcp_strategy38_correctness : solver_qcp_strategy38.

End solver_qcp_Strategy_Correct.
