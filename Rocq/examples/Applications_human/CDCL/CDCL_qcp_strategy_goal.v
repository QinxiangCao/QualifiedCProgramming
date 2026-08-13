Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.CDCL.CDCL_qcp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition CDCL_qcp_strategy7 :=
  forall (j : Z) (live : Z) (n : Z) (original_count : Z) (snap : dense_snapshot) (F : cnf) (old : cdcl_view) (after_clear : cdcl_view) (target : Z) (cap : Z) (st : (@list Z)) (un : (@list Z)) (tc : (@list Z)) (dl : Z) (ranks : (Z -> (@option nat))) (n2 : Z) (variable : Z) (current : cdcl_view) (un_ptr : Z),
    TT &&
    (“ (backtrack_inner old current after_clear n target variable j live cap ( installed_clauses ( cdcl_view_of_snapshot n2 snap ranks dl)) st tc un) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (Z.le 0 j) ”) &&
    (“ (Z.lt j live) ”) &&
    emp **
    ((IntArray.full un_ptr live un))
    |--
    (
    TT &&
    (“ (backtrack_inner old current after_clear n target variable j live cap ( installed_clauses ( cdcl_view_of_snapshot n2 snap ranks dl)) st tc un) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (Z.le 0 (@Znth Z j un 0)) ”) &&
    (“ (Z.le (@Znth Z j un 0) n) ”) &&
    (“ (Z.le 0 (@Znth Z j tc 0)) ”) &&
    (“ (Z.le (@Znth Z j tc 0) n) ”) &&
    (“ (Z.le (Z.sub 0 n) (@Znth Z j st 0)) ”) &&
    (“ (Z.le (@Znth Z j st 0) 2) ”) &&
    emp **
    ((IntArray.full un_ptr live un))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy8 :=
  forall (j : Z) (live : Z) (n : Z) (original_count : Z) (snap : dense_snapshot) (F : cnf) (old : cdcl_view) (x : Z) (n2 : Z) (ranks : (Z -> (@option nat))) (dl : Z) (tc : (@list Z)) (un : (@list Z)) (st : (@list Z)) (cap : Z) (new : cdcl_view) (un_ptr : Z),
    TT &&
    (“ (decision_update old new x j live cap ( installed_clauses ( cdcl_view_of_snapshot n2 snap ranks dl)) st tc un) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (Z.le 0 j) ”) &&
    (“ (Z.lt j live) ”) &&
    emp **
    ((IntArray.full un_ptr live un))
    |--
    (
    TT &&
    (“ (decision_update old new x j live cap ( installed_clauses ( cdcl_view_of_snapshot n2 snap ranks dl)) st tc un) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (Z.le 0 (@Znth Z j un 0)) ”) &&
    (“ (Z.le (@Znth Z j un 0) n) ”) &&
    (“ (Z.le 0 (@Znth Z j tc 0)) ”) &&
    (“ (Z.le (@Znth Z j tc 0) n) ”) &&
    (“ (Z.le (Z.sub 0 n) (@Znth Z j st 0)) ”) &&
    (“ (Z.le (@Znth Z j st 0) 2) ”) &&
    emp **
    ((IntArray.full un_ptr live un))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy9 :=
  forall (j : Z) (live : Z) (n : Z) (original_count : Z) (snap : dense_snapshot) (F : cnf) (old : cdcl_view) (x : Z) (d : Z) (n2 : Z) (ranks : (Z -> (@option nat))) (dl : Z) (tc : (@list Z)) (un : (@list Z)) (st : (@list Z)) (cap : Z) (exempt : Z) (reason : Z) (b : bool) (new : cdcl_view) (un_ptr : Z),
    TT &&
    (“ (bcp_clause_scan old new x b d reason j exempt live cap ( installed_clauses ( cdcl_view_of_snapshot n2 snap ranks dl)) st tc un) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (Z.le 0 j) ”) &&
    (“ (Z.lt j live) ”) &&
    emp **
    ((IntArray.full un_ptr live un))
    |--
    (
    TT &&
    (“ (bcp_clause_scan old new x b d reason j exempt live cap ( installed_clauses ( cdcl_view_of_snapshot n2 snap ranks dl)) st tc un) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (Z.le 0 (@Znth Z j un 0)) ”) &&
    (“ (Z.le (@Znth Z j un 0) n) ”) &&
    (“ (Z.le 0 (@Znth Z j tc 0)) ”) &&
    (“ (Z.le (@Znth Z j tc 0) n) ”) &&
    (“ (Z.le (Z.sub 0 n) (@Znth Z j st 0)) ”) &&
    (“ (Z.le (@Znth Z j st 0) 2) ”) &&
    emp **
    ((IntArray.full un_ptr live un))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy10 :=
  forall (i : Z) (live2 : Z) (new : cdcl_view) (b : bool) (reason : Z) (exempt : Z) (cap : Z) (st : (@list Z)) (un : (@list Z)) (tc : (@list Z)) (rows : cnf) (live : Z) (j : Z) (d : Z) (x : Z) (old : cdcl_view) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (bcp_clause_scan old new x b d reason j exempt live cap rows st tc un) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i live2) ”) &&
    emp **
    ((IntArray.full p live2 (@replace_Znth Z i v l)))
    |--
    (
    TT &&
    (“ (bcp_clause_scan old new x b d reason j exempt live cap rows st tc un) ”) &&
    (“ ((@Znth Z i (@replace_Znth Z i v l) 0) = v) ”) &&
    emp **
    ((IntArray.full p live2 (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy3 :=
  forall (i : Z) (live : Z) (__default_app1_Z : (@list Z)) (p : Z) (cap : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i live) ”) &&
    emp **
    ((installed_rows_capacity_rep p live cap rows))
    |--
    EX (row_ptr : Z),
      (
      TT &&
      emp **
      ((IntPtrArray2.missing_i p live i row_ptr rows)) **
      ((IntArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
      ((PtrArray.undef_seg p live cap))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = row_ptr) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
        ).

Definition CDCL_qcp_strategy5 :=
  forall (live : Z) (cap : Z) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (Z.lt live cap) ”) &&
    emp **
    ((installed_rows_capacity_rep p live cap rows))
    |--
    (
    TT &&
    emp **
    ((IntPtrArray2.full p live rows)) **
    ((PtrArray.undef_seg p (Z.add live 1) cap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr (Z.add p (Z.mul live (@sizeof_front_end_type FET_ptr)))))
    ).

Definition CDCL_qcp_strategy11 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (rp : Z) (vp : Z) (lp : Z) (snap : dense_snapshot) (n : Z),
    TT &&
    emp **
    ((IntArray.full vp n ( snap_values snap))) **
    ((IntArray.full rp n ( snap_reasons snap))) **
    ((IntArray.full lp n ( snap_levels snap))) -*
    TT &&
    emp **
    ((variable_arrays_rep vp rp lp n snap))
    ).

Definition CDCL_qcp_strategy12 :=
  forall (vp : Z) (lp : Z) (snap : dense_snapshot) (n : Z) (rp : Z),
    TT &&
    emp **
    ((variable_arrays_rep vp rp lp n snap))
    |--
    (
    TT &&
    emp **
    ((IntArray.full vp n ( snap_values snap))) **
    ((IntArray.full rp n ( snap_reasons snap))) **
    ((IntArray.full lp n ( snap_levels snap)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy13 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (un : Z) (tc : Z) (st : Z) (rt : Z) (cap : Z) (snap : dense_snapshot) (live : Z),
    TT &&
    emp **
    ((IntArray.seg st 0 live ( snap_states snap))) **
    ((IntArray.seg_shape st live cap)) **
    ((IntArray.seg tc 0 live ( snap_true_counts snap))) **
    ((IntArray.seg_shape tc live cap)) **
    ((IntArray.seg un 0 live ( snap_unassigned snap))) **
    ((IntArray.seg_shape un live cap)) **
    ((installed_rows_capacity_rep rt live cap ( snap_rows snap))) -*
    TT &&
    emp **
    ((solver_arrays_rep st tc un rt live cap snap))
    ).

Definition CDCL_qcp_strategy14 :=
  forall (st : Z) (un : Z) (live : Z) (snap : dense_snapshot) (cap : Z) (rt : Z) (tc : Z),
    TT &&
    emp **
    ((solver_arrays_rep st tc un rt live cap snap))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg st 0 live ( snap_states snap))) **
    ((IntArray.seg_shape st live cap)) **
    ((IntArray.seg tc 0 live ( snap_true_counts snap))) **
    ((IntArray.seg_shape tc live cap)) **
    ((IntArray.seg un 0 live ( snap_unassigned snap))) **
    ((IntArray.seg_shape un live cap)) **
    ((installed_rows_capacity_rep rt live cap ( snap_rows snap)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy15 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (reasons : Z) (values : Z) (levels : Z) (v_data : Z),
    TT &&
    emp **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "value") values)) **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "ancient") reasons)) **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "dl") levels)) -*
    TT &&
    emp **
    ((var_header_rep v_data values reasons levels))
    ).

Definition CDCL_qcp_strategy16 :=
  forall (v_data : Z) (reasons : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((var_header_rep v_data values reasons levels))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "value") values)) **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "ancient") reasons)) **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "dl") levels))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy17 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (unassigned : Z) (states : Z) (true_counts : Z) (rows : Z) (cl_data : Z),
    TT &&
    emp **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "state") states)) **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "lit_state") true_counts)) **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "unassign_num") unassigned)) **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "value") rows)) -*
    TT &&
    emp **
    ((clause_header_rep cl_data states true_counts unassigned rows))
    ).

Definition CDCL_qcp_strategy18 :=
  forall (cl_data : Z) (true_counts : Z) (rows : Z) (unassigned : Z) (states : Z),
    TT &&
    emp **
    ((clause_header_rep cl_data states true_counts unassigned rows))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "state") states)) **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "lit_state") true_counts)) **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "unassign_num") unassigned)) **
    ((poly_store FET_ptr &( ((cl_data)) # "clause_data" ->ₛ "value") rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy19 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (v_data : Z) (cap : Z) (n : Z) (live : Z) (logical_dl : Z) (cl_data : Z) (s : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "v_size") n)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_size") live)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_maxsize") cap)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cur_dl") logical_dl)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "v_data") v_data)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "cl_data") cl_data)) -*
    TT &&
    emp **
    ((sat_header_rep s n live cap logical_dl v_data cl_data))
    ).

Definition CDCL_qcp_strategy20 :=
  forall (s : Z) (live : Z) (logical_dl : Z) (cl_data : Z) (v_data : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((sat_header_rep s n live cap logical_dl v_data cl_data))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "v_size") n)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_size") live)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_maxsize") cap)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cur_dl") logical_dl)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "v_data") v_data)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "cl_data") cl_data))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy21 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (v_data : Z) (cap : Z) (n : Z) (live : Z) (cl_data : Z) (s : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "v_size") n)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_size") live)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_maxsize") cap)) **
    ((poly_undef_store FET_int &( ((s)) # "sat_data" ->ₛ "cur_dl"))) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "v_data") v_data)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "cl_data") cl_data)) -*
    TT &&
    emp **
    ((sat_entry_header_rep s n live cap v_data cl_data))
    ).

Definition CDCL_qcp_strategy22 :=
  forall (s : Z) (live : Z) (v_data : Z) (cl_data : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((sat_entry_header_rep s n live cap v_data cl_data))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "v_size") n)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_size") live)) **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "cl_maxsize") cap)) **
    ((poly_undef_store FET_int &( ((s)) # "sat_data" ->ₛ "cur_dl"))) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "v_data") v_data)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "cl_data") cl_data))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy23 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (true_counts : Z) (cur_states : (@list Z)) (cur_unassigned : (@list Z)) (cur_true : (@list Z)) (unassigned : Z) (states : Z) (row_table : Z) (cap : Z) (rows : (@list (@list Z))) (live : Z),
    TT &&
    emp **
    ((clause_summaries_explicit_rep states true_counts unassigned live cap cur_states cur_true cur_unassigned)) **
    ((installed_rows_capacity_rep row_table live cap rows)) -*
    TT &&
    emp **
    ((clause_arrays_explicit_rep states true_counts unassigned row_table live cap rows cur_states cur_true cur_unassigned))
    ).

Definition CDCL_qcp_strategy24 :=
  forall (states : Z) (unassigned : Z) (live : Z) (rows : (@list (@list Z))) (cur_true : (@list Z)) (cur_unassigned : (@list Z)) (cur_states : (@list Z)) (cap : Z) (row_table : Z) (true_counts : Z),
    TT &&
    emp **
    ((clause_arrays_explicit_rep states true_counts unassigned row_table live cap rows cur_states cur_true cur_unassigned))
    |--
    (
    TT &&
    emp **
    ((clause_summaries_explicit_rep states true_counts unassigned live cap cur_states cur_true cur_unassigned)) **
    ((installed_rows_capacity_rep row_table live cap rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy25 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (wj : Z) (wi : Z) (result_row : Z) (right_row : (@list Z)) (left_row : (@list Z)) (n : Z),
    TT &&
    emp **
    ((IntArray.full wi n left_row)) **
    ((IntArray.full wj n right_row)) **
    ((IntArray.full result_row n ( dense_cancel_union left_row right_row))) -*
    TT &&
    emp **
    ((resolution_rows_rep wi wj result_row n left_row right_row))
    ).

Definition CDCL_qcp_strategy26 :=
  forall (wi : Z) (result_row : Z) (left_row : (@list Z)) (right_row : (@list Z)) (n : Z) (wj : Z),
    TT &&
    emp **
    ((resolution_rows_rep wi wj result_row n left_row right_row))
    |--
    (
    TT &&
    emp **
    ((IntArray.full wi n left_row)) **
    ((IntArray.full wj n right_row)) **
    ((IntArray.full result_row n ( dense_cancel_union left_row right_row)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy27 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (row : (@list Z)) (clause : Z) (s : Z) (v_data : Z) (levels : Z) (snap : dense_snapshot) (n : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "v_size") n)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "v_data") v_data)) **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "dl") levels)) **
    ((IntArray.full clause n row)) **
    ((IntArray.full levels n ( snap_levels snap))) -*
    TT &&
    emp **
    ((conflict_levels_rep s clause n v_data levels row snap))
    ).

Definition CDCL_qcp_strategy28 :=
  forall (s : Z) (n : Z) (levels : Z) (snap : dense_snapshot) (row : (@list Z)) (v_data : Z) (clause : Z),
    TT &&
    emp **
    ((conflict_levels_rep s clause n v_data levels row snap))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "sat_data" ->ₛ "v_size") n)) **
    ((poly_store FET_ptr &( ((s)) # "sat_data" ->ₛ "v_data") v_data)) **
    ((poly_store FET_ptr &( ((v_data)) # "var_data" ->ₛ "dl") levels)) **
    ((IntArray.full clause n row)) **
    ((IntArray.full levels n ( snap_levels snap)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy29 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (cur_unassigned : (@list Z)) (cur_true : (@list Z)) (cur_states : (@list Z)) (states : Z) (true_counts : Z) (unassigned : Z) (cap : Z) (live : Z),
    TT &&
    emp **
    ((IntArray.full states live cur_states)) **
    ((IntArray.seg_shape states live cap)) **
    ((IntArray.full true_counts live cur_true)) **
    ((IntArray.seg_shape true_counts live cap)) **
    ((IntArray.full unassigned live cur_unassigned)) **
    ((IntArray.seg_shape unassigned live cap)) -*
    TT &&
    emp **
    ((clause_summaries_explicit_rep states true_counts unassigned live cap cur_states cur_true cur_unassigned))
    ).

Definition CDCL_qcp_strategy30 :=
  forall (states : Z) (unassigned : Z) (cap : Z) (cur_true : (@list Z)) (cur_unassigned : (@list Z)) (cur_states : (@list Z)) (live : Z) (true_counts : Z),
    TT &&
    emp **
    ((clause_summaries_explicit_rep states true_counts unassigned live cap cur_states cur_true cur_unassigned))
    |--
    (
    TT &&
    emp **
    ((IntArray.full states live cur_states)) **
    ((IntArray.seg_shape states live cap)) **
    ((IntArray.full true_counts live cur_true)) **
    ((IntArray.seg_shape true_counts live cap)) **
    ((IntArray.full unassigned live cur_unassigned)) **
    ((IntArray.seg_shape unassigned live cap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy31 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (i : Z) (rows : (@list (@list Z))) (row_ptr : Z) (live : Z),
    TT &&
    emp **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) row_ptr)) **
    ((IntArray.full row_ptr (@Zlength Z (@Znth (@list Z) i rows (@nil Z))) (@Znth (@list Z) i rows (@nil Z)))) **
    ((IntPtrArray2.missing_i p live i row_ptr rows)) -*
    TT &&
    emp **
    ((installed_row_focus_rep p live i row_ptr rows))
    ).

Definition CDCL_qcp_strategy32 :=
  forall (p : Z) (i : Z) (rows : (@list (@list Z))) (row_ptr : Z) (live : Z),
    TT &&
    emp **
    ((installed_row_focus_rep p live i row_ptr rows))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) row_ptr)) **
    ((IntArray.full row_ptr (@Zlength Z (@Znth (@list Z) i rows (@nil Z))) (@Znth (@list Z) i rows (@nil Z)))) **
    ((IntPtrArray2.missing_i p live i row_ptr rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy33 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (n : Z) (original_count : Z) (snap : dense_snapshot) (live : Z) (F : cnf) (states : Z) (unassigned : Z) (cap : Z) (row_table : Z) (true_counts : Z),
    TT &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    emp **
    ((solver_arrays_rep states true_counts unassigned row_table live cap snap)) -*
    TT &&
    emp **
    ((store_cnf F n original_count states true_counts unassigned row_table live cap snap))
    ).

Definition CDCL_qcp_strategy34 :=
  forall (n : Z) (original_count : Z) (snap : dense_snapshot) (live : Z) (F : cnf) (true_counts : Z) (row_table : Z) (cap : Z) (unassigned : Z) (states : Z),
    TT &&
    emp **
    ((store_cnf F n original_count states true_counts unassigned row_table live cap snap))
    |--
    (
    TT &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    emp **
    ((solver_arrays_rep states true_counts unassigned row_table live cap snap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy35 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (snap : dense_snapshot) (n : Z) (values : Z) (levels : Z) (reasons : Z),
    TT &&
    (“ (all_unassigned_cells n snap) ”) &&
    emp **
    ((variable_arrays_rep values reasons levels n snap)) -*
    TT &&
    emp **
    ((uninitialized_Assignment values reasons levels n snap))
    ).

Definition CDCL_qcp_strategy36 :=
  forall (snap : dense_snapshot) (n : Z) (values : Z) (levels : Z) (reasons : Z),
    TT &&
    emp **
    ((uninitialized_Assignment values reasons levels n snap))
    |--
    (
    TT &&
    (“ (all_unassigned_cells n snap) ”) &&
    emp **
    ((variable_arrays_rep values reasons levels n snap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy37 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (J : Assignment) (n : Z) (snap : dense_snapshot) (values : Z) (levels : Z) (reasons : Z),
    TT &&
    (“ (J = ( rho_of_values n ( snap_values snap))) ”) &&
    emp **
    ((variable_arrays_rep values reasons levels n snap)) -*
    TT &&
    emp **
    ((store_Assignment values reasons levels n snap J))
    ).

Definition CDCL_qcp_strategy38 :=
  forall (J : Assignment) (n : Z) (snap : dense_snapshot) (values : Z) (levels : Z) (reasons : Z),
    TT &&
    emp **
    ((store_Assignment values reasons levels n snap J))
    |--
    (
    TT &&
    (“ (J = ( rho_of_values n ( snap_values snap))) ”) &&
    emp **
    ((variable_arrays_rep values reasons levels n snap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy39 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (values : Z) (levels : Z) (snap : dense_snapshot) (n : Z) (reasons : Z),
    TT &&
    emp **
    ((variable_arrays_rep values reasons levels n snap)) -*
    TT &&
    emp **
    ((unconstrained_Assignment values reasons levels n snap))
    ).

Definition CDCL_qcp_strategy40 :=
  forall (values : Z) (levels : Z) (snap : dense_snapshot) (n : Z) (reasons : Z),
    TT &&
    emp **
    ((unconstrained_Assignment values reasons levels n snap))
    |--
    (
    TT &&
    emp **
    ((variable_arrays_rep values reasons levels n snap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy41 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (n : Z) (snap : dense_snapshot) (ranks : (Z -> (@option nat))) (original_count : Z) (F : cnf) (live : Z) (cap : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (v_data : Z) (s : Z) (cl_data : Z) (values : Z) (levels : Z) (reasons : Z),
    TT &&
    (“ (Z.le 0 n) ”) &&
    (“ (Z.lt n ( INT_MAX)) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (original_count = live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (stable_search_facts n snap ranks 0) ”) &&
    (“ (fresh_formula F n original_count ( cdcl_view_of_snapshot n snap ranks 0)) ”) &&
    emp **
    ((sat_entry_header_rep s n live cap v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((store_cnf F n original_count states true_counts unassigned row_table live cap snap)) **
    ((uninitialized_Assignment values reasons levels n snap)) -*
    TT &&
    emp **
    ((solver_input_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap))
    ).

Definition CDCL_qcp_strategy42 :=
  forall (n : Z) (snap : dense_snapshot) (ranks : (Z -> (@option nat))) (original_count : Z) (F : cnf) (live : Z) (cap : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_input_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      (“ (Z.le 0 n) ”) &&
      (“ (Z.lt n ( INT_MAX)) ”) &&
      (“ (Z.le 0 original_count) ”) &&
      (“ (original_count = live) ”) &&
      (“ (Z.le 0 live) ”) &&
      (“ (Z.le live cap) ”) &&
      (“ (stable_search_facts n snap ranks 0) ”) &&
      (“ (fresh_formula F n original_count ( cdcl_view_of_snapshot n snap ranks 0)) ”) &&
      emp **
      ((sat_entry_header_rep s n live cap v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((store_cnf F n original_count states true_counts unassigned row_table live cap snap)) **
      ((uninitialized_Assignment values reasons levels n snap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy43 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (final_live : Z) (cap : Z) (original_count : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (F : cnf) (v_data : Z) (snap : dense_snapshot) (live : Z) (ranks : (Z -> (@option nat))) (s : Z) (final_dl : Z) (cl_data : Z) (values : Z) (levels : Z) (final_snap : dense_snapshot) (J : Assignment) (n : Z) (reasons : Z),
    TT &&
    (“ (Z.le original_count final_live) ”) &&
    (“ (Z.le final_live cap) ”) &&
    emp **
    ((sat_header_rep s n final_live cap final_dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((store_cnf F n original_count states true_counts unassigned row_table final_live cap final_snap)) **
    ((store_Assignment values reasons levels n final_snap J)) -*
    TT &&
    emp **
    ((solver_sat_arm_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap J))
    ).

Definition CDCL_qcp_strategy44 :=
  forall (cap : Z) (original_count : Z) (s : Z) (ranks : (Z -> (@option nat))) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (J : Assignment) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z) (snap : dense_snapshot) (F : cnf),
    TT &&
    emp **
    ((solver_sat_arm_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap J))
    |--
    EX (final_snap : dense_snapshot) (final_dl : Z) (final_live : Z) (v_data : Z) (cl_data : Z),
      (
      TT &&
      (“ (Z.le original_count final_live) ”) &&
      (“ (Z.le final_live cap) ”) &&
      emp **
      ((sat_header_rep s n final_live cap final_dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((store_cnf F n original_count states true_counts unassigned row_table final_live cap final_snap)) **
      ((store_Assignment values reasons levels n final_snap J))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy45 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (final_live : Z) (cap : Z) (original_count : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (F : cnf) (v_data : Z) (snap : dense_snapshot) (live : Z) (ranks : (Z -> (@option nat))) (s : Z) (final_dl : Z) (cl_data : Z) (values : Z) (levels : Z) (final_snap : dense_snapshot) (n : Z) (reasons : Z),
    TT &&
    (“ (Z.le original_count final_live) ”) &&
    (“ (Z.le final_live cap) ”) &&
    emp **
    ((sat_header_rep s n final_live cap final_dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((store_cnf F n original_count states true_counts unassigned row_table final_live cap final_snap)) **
    ((unconstrained_Assignment values reasons levels n final_snap)) -*
    TT &&
    emp **
    ((solver_unsat_arm_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap))
    ).

Definition CDCL_qcp_strategy46 :=
  forall (cap : Z) (original_count : Z) (s : Z) (ranks : (Z -> (@option nat))) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z) (snap : dense_snapshot) (F : cnf),
    TT &&
    emp **
    ((solver_unsat_arm_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap))
    |--
    EX (final_snap : dense_snapshot) (final_dl : Z) (final_live : Z) (v_data : Z) (cl_data : Z),
      (
      TT &&
      (“ (Z.le original_count final_live) ”) &&
      (“ (Z.le final_live cap) ”) &&
      emp **
      ((sat_header_rep s n final_live cap final_dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((store_cnf F n original_count states true_counts unassigned row_table final_live cap final_snap)) **
      ((unconstrained_Assignment values reasons levels n final_snap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy47 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (row : (@list Z)) (n : Z) (conflict_dl : Z) (reasons : Z) (conflict_snap : dense_snapshot) (levels : Z) (values : Z) (cl_data : Z) (s : Z) (ranks : (Z -> (@option nat))) (live : Z) (snap : dense_snapshot) (v_data : Z) (F : cnf) (original_count : Z) (true_counts : Z) (row_table : Z) (cap : Z) (unassigned : Z) (states : Z) (row_ptr : Z),
    TT &&
    (“ (Z.lt 0 conflict_dl) ”) &&
    (“ (Z.le conflict_dl n) ”) &&
    (“ (row_wf n row) ”) &&
    emp **
    ((sat_header_rep s n cap cap conflict_dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((store_cnf F n original_count states true_counts unassigned row_table cap cap conflict_snap)) **
    ((unconstrained_Assignment values reasons levels n conflict_snap)) **
    ((IntArray.full row_ptr n row)) -*
    TT &&
    emp **
    ((solver_capacity_exhausted_arm_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap))
    ).

Definition CDCL_qcp_strategy48 :=
  forall (n : Z) (s : Z) (original_count : Z) (ranks : (Z -> (@option nat))) (reasons : Z) (states : Z) (unassigned : Z) (cap : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z) (snap : dense_snapshot) (F : cnf),
    TT &&
    emp **
    ((solver_capacity_exhausted_arm_core s F original_count snap ranks values reasons levels states true_counts unassigned row_table n live cap))
    |--
    EX (conflict_snap : dense_snapshot) (conflict_dl : Z) (row_ptr : Z) (row : (@list Z)) (v_data : Z) (cl_data : Z),
      (
      TT &&
      (“ (Z.lt 0 conflict_dl) ”) &&
      (“ (Z.le conflict_dl n) ”) &&
      (“ (row_wf n row) ”) &&
      emp **
      ((sat_header_rep s n cap cap conflict_dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((store_cnf F n original_count states true_counts unassigned row_table cap cap conflict_snap)) **
      ((unconstrained_Assignment values reasons levels n conflict_snap)) **
      ((IntArray.full row_ptr n row))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy49 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (reasons : Z) (n : Z) (levels : Z) (values : Z) (v_data : Z) (s : Z) (dl : Z) (cl_data : Z) (states : Z) (unassigned : Z) (live : Z) (snap : dense_snapshot) (cap : Z) (row_table : Z) (true_counts : Z),
    TT &&
    emp **
    ((sat_header_rep s n live cap dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((unconstrained_Assignment values reasons levels n snap)) **
    ((solver_arrays_rep states true_counts unassigned row_table live cap snap)) -*
    TT &&
    emp **
    ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap))
    ).

Definition CDCL_qcp_strategy50 :=
  forall (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (cap : Z) (snap : dense_snapshot) (dl : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      emp **
      ((sat_header_rep s n live cap dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((unconstrained_Assignment values reasons levels n snap)) **
      ((solver_arrays_rep states true_counts unassigned row_table live cap snap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy51 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (n : Z) (levels : Z) (states : Z) (unassigned : Z) (true_counts : Z) (cl_data : Z) (logical_dl : Z) (s : Z) (v_data : Z) (values : Z) (reasons : Z) (row_table : Z) (cap : Z) (snap : dense_snapshot) (live : Z),
    TT &&
    emp **
    ((sat_header_rep s n live cap logical_dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((IntArray.full reasons n ( snap_reasons snap))) **
    ((IntArray.full levels n ( snap_levels snap))) **
    ((installed_rows_capacity_rep row_table live cap ( snap_rows snap))) -*
    TT &&
    emp **
    ((learning_state s values reasons levels states true_counts unassigned row_table n live cap logical_dl snap))
    ).

Definition CDCL_qcp_strategy52 :=
  forall (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (cap : Z) (snap : dense_snapshot) (logical_dl : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((learning_state s values reasons levels states true_counts unassigned row_table n live cap logical_dl snap))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      emp **
      ((sat_header_rep s n live cap logical_dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((IntArray.full reasons n ( snap_reasons snap))) **
      ((IntArray.full levels n ( snap_levels snap))) **
      ((installed_rows_capacity_rep row_table live cap ( snap_rows snap)))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy53 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (true_counts : Z) (row_table : Z) (cap : Z) (live : Z) (unassigned : Z) (states : Z) (cl_data : Z) (s : Z) (original_count : Z) (v_data : Z) (values : Z) (levels : Z) (reasons : Z) (F : cnf) (conflict_snap : dense_snapshot) (conflict_ranks : (Z -> (@option nat))) (back_dl : Z) (last : Z) (learned : (@list literal)) (ranks : (Z -> (@option nat))) (snap : dense_snapshot) (n : Z) (start_ranks : (Z -> (@option nat))) (conflict_dl : Z) (start_snap : dense_snapshot),
    TT &&
    emp **
    ((sat_header_rep s n live cap back_dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((variable_arrays_rep values reasons levels n snap)) **
    ((solver_arrays_rep states true_counts unassigned row_table live cap snap)) **
    ((pending_backjump_rep F ( cdcl_view_of_snapshot n start_snap start_ranks conflict_dl) ( cdcl_view_of_snapshot n conflict_snap conflict_ranks conflict_dl) ( cdcl_view_of_snapshot n snap ranks conflict_dl) back_dl back_dl last learned)) -*
    TT &&
    emp **
    ((backjump_state s F original_count start_snap conflict_snap snap start_ranks conflict_ranks ranks conflict_dl back_dl last learned values reasons levels states true_counts unassigned row_table n live cap))
    ).

Definition CDCL_qcp_strategy54 :=
  forall (s : Z) (original_count : Z) (conflict_snap : dense_snapshot) (start_ranks : (Z -> (@option nat))) (ranks : (Z -> (@option nat))) (back_dl : Z) (learned : (@list literal)) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (cap : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z) (last : Z) (conflict_dl : Z) (conflict_ranks : (Z -> (@option nat))) (snap : dense_snapshot) (start_snap : dense_snapshot) (F : cnf),
    TT &&
    emp **
    ((backjump_state s F original_count start_snap conflict_snap snap start_ranks conflict_ranks ranks conflict_dl back_dl last learned values reasons levels states true_counts unassigned row_table n live cap))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      emp **
      ((sat_header_rep s n live cap back_dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((variable_arrays_rep values reasons levels n snap)) **
      ((solver_arrays_rep states true_counts unassigned row_table live cap snap)) **
      ((pending_backjump_rep F ( cdcl_view_of_snapshot n start_snap start_ranks conflict_dl) ( cdcl_view_of_snapshot n conflict_snap conflict_ranks conflict_dl) ( cdcl_view_of_snapshot n snap ranks conflict_dl) back_dl back_dl last learned))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy55 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (snap1 : dense_snapshot) (ranks1 : (Z -> (@option nat))) (last : Z) (n : Z) (pre_ranks : (Z -> (@option nat))) (logical_dl : Z) (pre_snap : dense_snapshot) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (cap : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks logical_dl) ( cdcl_view_of_snapshot n snap1 ranks1 logical_dl) last) ”) &&
    emp **
    ((solver_state s values reasons levels states true_counts unassigned row_table n live cap logical_dl snap1)) -*
    TT &&
    emp **
    ((propagation_result s values reasons levels states true_counts unassigned row_table n live cap logical_dl snap1 ranks1))
    ).

Definition CDCL_qcp_strategy56 :=
  forall (snap1 : dense_snapshot) (ranks1 : (Z -> (@option nat))) (n : Z) (logical_dl : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (cap : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((propagation_result s values reasons levels states true_counts unassigned row_table n live cap logical_dl snap1 ranks1))
    |--
    EX (pre_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (last : Z),
      (
      TT &&
      (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks logical_dl) ( cdcl_view_of_snapshot n snap1 ranks1 logical_dl) last) ”) &&
      emp **
      ((solver_state s values reasons levels states true_counts unassigned row_table n live cap logical_dl snap1))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy57 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (n : Z) (ranks : (Z -> (@option nat))) (dl : Z) (snap : dense_snapshot) (original_count : Z) (live : Z) (F : cnf) (cap : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    (“ (Z.le 0 dl) ”) &&
    (“ (Z.le dl n) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n snap ranks dl) ”) &&
    (“ (bcp_ready ( cdcl_view_of_snapshot n snap ranks dl)) ”) &&
    emp **
    ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap)) -*
    TT &&
    emp **
    ((solver_loop_state s F original_count values reasons levels states true_counts unassigned row_table n live cap snap ranks dl))
    ).

Definition CDCL_qcp_strategy58 :=
  forall (n : Z) (ranks : (Z -> (@option nat))) (dl : Z) (snap : dense_snapshot) (original_count : Z) (live : Z) (F : cnf) (cap : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_loop_state s F original_count values reasons levels states true_counts unassigned row_table n live cap snap ranks dl))
    |--
    (
    TT &&
    (“ (Z.le 0 dl) ”) &&
    (“ (Z.le dl n) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n snap ranks dl) ”) &&
    (“ (bcp_ready ( cdcl_view_of_snapshot n snap ranks dl)) ”) &&
    emp **
    ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy59 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (pre_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (conflict_cl : Z) (last : Z) (live : Z) (n : Z) (ranks : (Z -> (@option nat))) (dl : Z) (snap : dense_snapshot) (original_count : Z) (F : cnf) (cap : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    (“ (Z.le 0 dl) ”) &&
    (“ (Z.le dl n) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n snap ranks dl) ”) &&
    (“ (bcp_outcome ( cdcl_view_of_snapshot n snap ranks dl) ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) live conflict_cl last) ”) &&
    emp **
    ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap)) -*
    TT &&
    emp **
    ((solver_after_bcp_state s F original_count values reasons levels states true_counts unassigned row_table n live cap conflict_cl snap ranks dl))
    ).

Definition CDCL_qcp_strategy60 :=
  forall (conflict_cl : Z) (live : Z) (n : Z) (ranks : (Z -> (@option nat))) (dl : Z) (snap : dense_snapshot) (original_count : Z) (F : cnf) (cap : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_after_bcp_state s F original_count values reasons levels states true_counts unassigned row_table n live cap conflict_cl snap ranks dl))
    |--
    EX (pre_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (last : Z),
      (
      TT &&
      (“ (Z.le 0 dl) ”) &&
      (“ (Z.le dl n) ”) &&
      (“ (Z.le 0 original_count) ”) &&
      (“ (Z.le original_count live) ”) &&
      (“ (Z.le 0 live) ”) &&
      (“ (Z.le live cap) ”) &&
      (“ (coherent_snapshot F n live original_count snap) ”) &&
      (“ (stable_search_facts n snap ranks dl) ”) &&
      (“ (bcp_outcome ( cdcl_view_of_snapshot n snap ranks dl) ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) live conflict_cl last) ”) &&
      emp **
      ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy61 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (conflict_cl : Z) (n : Z) (ranks : (Z -> (@option nat))) (dl : Z) (snap : dense_snapshot) (F : cnf) (cap : Z) (live : Z) (original_count : Z) (pre_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (last : Z) (row : (@list Z)) (values : Z) (levels : Z) (true_counts : Z) (row_table : Z) (unassigned : Z) (states : Z) (reasons : Z) (s : Z) (new_cl : Z),
    TT &&
    (“ (Z.le 0 conflict_cl) ”) &&
    (“ (Z.lt conflict_cl live) ”) &&
    (“ (Z.lt 0 dl) ”) &&
    (“ (Z.le dl n) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n snap ranks dl) ”) &&
    (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) ( cdcl_view_of_snapshot n snap ranks dl) last) ”) &&
    (“ (current_learning_exit_cert F ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
    (“ (row_wf n row) ”) &&
    (“ (learning_ready_conflict ( cdcl_view_of_snapshot n snap ranks dl) conflict_cl) ”) &&
    emp **
    ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap)) **
    ((IntArray.full new_cl n row)) -*
    TT &&
    emp **
    ((solver_learning_state s F original_count values reasons levels states true_counts unassigned row_table n live cap conflict_cl new_cl row snap ranks dl))
    ).

Definition CDCL_qcp_strategy62 :=
  forall (conflict_cl : Z) (n : Z) (ranks : (Z -> (@option nat))) (dl : Z) (snap : dense_snapshot) (F : cnf) (cap : Z) (live : Z) (original_count : Z) (row : (@list Z)) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (new_cl : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_learning_state s F original_count values reasons levels states true_counts unassigned row_table n live cap conflict_cl new_cl row snap ranks dl))
    |--
    EX (pre_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (last : Z),
      (
      TT &&
      (“ (Z.le 0 conflict_cl) ”) &&
      (“ (Z.lt conflict_cl live) ”) &&
      (“ (Z.lt 0 dl) ”) &&
      (“ (Z.le dl n) ”) &&
      (“ (Z.le 0 original_count) ”) &&
      (“ (Z.le original_count live) ”) &&
      (“ (Z.le 0 live) ”) &&
      (“ (Z.le live cap) ”) &&
      (“ (coherent_snapshot F n live original_count snap) ”) &&
      (“ (stable_search_facts n snap ranks dl) ”) &&
      (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) ( cdcl_view_of_snapshot n snap ranks dl) last) ”) &&
      (“ (current_learning_exit_cert F ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
      (“ (row_wf n row) ”) &&
      (“ (learning_ready_conflict ( cdcl_view_of_snapshot n snap ranks dl) conflict_cl) ”) &&
      emp **
      ((solver_state s values reasons levels states true_counts unassigned row_table n live cap dl snap)) **
      ((IntArray.full new_cl n row))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy63 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (snap : dense_snapshot) (dl : Z) (ranks : (Z -> (@option nat))) (n : Z) (cap : Z) (live : Z) (row : (@list Z)) (F : cnf) (last : Z) (pre_ranks : (Z -> (@option nat))) (pre_snap : dense_snapshot) (original_count : Z) (slot : Z) (conflict_cl : Z) (row_table : Z) (old_unassigned : Z) (true_counts : Z) (old_state : Z) (reasons : Z) (levels : Z) (values : Z) (v_data : Z) (s : Z) (cl_data : Z) (states : Z) (old_true_count : Z) (unassigned : Z) (new_cl : Z),
    TT &&
    (“ (slot_at slot live) ”) &&
    (“ (Z.le 0 conflict_cl) ”) &&
    (“ (Z.lt conflict_cl live) ”) &&
    (“ (Z.lt 0 dl) ”) &&
    (“ (Z.le dl n) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.lt live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n snap ranks dl) ”) &&
    (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) ( cdcl_view_of_snapshot n snap ranks dl) last) ”) &&
    (“ (current_learning_exit_cert F ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
    (“ (installing_clause F ( cdcl_view_of_snapshot n snap ranks dl) n cap row ( dense_decode row) live (Z.add live 1)) ”) &&
    emp **
    ((sat_header_rep s n slot cap dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((variable_arrays_rep values reasons levels n snap)) **
    ((IntArray.seg states 0 live ( snap_states snap))) **
    ((poly_store FET_int (Z.add states (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_int))) old_state)) **
    ((IntArray.seg_shape states (Z.add live 1) cap)) **
    ((IntArray.seg true_counts 0 live ( snap_true_counts snap))) **
    ((poly_store FET_int (Z.add true_counts (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_int))) old_true_count)) **
    ((IntArray.seg_shape true_counts (Z.add live 1) cap)) **
    ((IntArray.seg unassigned 0 live ( snap_unassigned snap))) **
    ((poly_store FET_int (Z.add unassigned (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_int))) old_unassigned)) **
    ((IntArray.seg_shape unassigned (Z.add live 1) cap)) **
    ((IntPtrArray2.full row_table live ( snap_rows snap))) **
    ((poly_undef_store FET_ptr (Z.add row_table (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_ptr))))) **
    ((PtrArray.undef_seg row_table (Z.add live 1) cap)) **
    ((IntArray.full new_cl n row)) -*
    TT &&
    emp **
    ((solver_install_slot_state s F original_count values reasons levels states true_counts unassigned row_table n live cap slot conflict_cl new_cl row snap ranks dl))
    ).

Definition CDCL_qcp_strategy64 :=
  forall (snap : dense_snapshot) (dl : Z) (ranks : (Z -> (@option nat))) (n : Z) (cap : Z) (live : Z) (row : (@list Z)) (F : cnf) (original_count : Z) (slot : Z) (conflict_cl : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (new_cl : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_install_slot_state s F original_count values reasons levels states true_counts unassigned row_table n live cap slot conflict_cl new_cl row snap ranks dl))
    |--
    EX (pre_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (last : Z) (old_state : Z) (old_true_count : Z) (old_unassigned : Z) (v_data : Z) (cl_data : Z),
      (
      TT &&
      (“ (slot_at slot live) ”) &&
      (“ (Z.le 0 conflict_cl) ”) &&
      (“ (Z.lt conflict_cl live) ”) &&
      (“ (Z.lt 0 dl) ”) &&
      (“ (Z.le dl n) ”) &&
      (“ (Z.le 0 original_count) ”) &&
      (“ (Z.le original_count live) ”) &&
      (“ (Z.le 0 live) ”) &&
      (“ (Z.lt live cap) ”) &&
      (“ (coherent_snapshot F n live original_count snap) ”) &&
      (“ (stable_search_facts n snap ranks dl) ”) &&
      (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) ( cdcl_view_of_snapshot n snap ranks dl) last) ”) &&
      (“ (current_learning_exit_cert F ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
      (“ (installing_clause F ( cdcl_view_of_snapshot n snap ranks dl) n cap row ( dense_decode row) live (Z.add live 1)) ”) &&
      emp **
      ((sat_header_rep s n slot cap dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((variable_arrays_rep values reasons levels n snap)) **
      ((IntArray.seg states 0 live ( snap_states snap))) **
      ((poly_store FET_int (Z.add states (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_int))) old_state)) **
      ((IntArray.seg_shape states (Z.add live 1) cap)) **
      ((IntArray.seg true_counts 0 live ( snap_true_counts snap))) **
      ((poly_store FET_int (Z.add true_counts (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_int))) old_true_count)) **
      ((IntArray.seg_shape true_counts (Z.add live 1) cap)) **
      ((IntArray.seg unassigned 0 live ( snap_unassigned snap))) **
      ((poly_store FET_int (Z.add unassigned (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_int))) old_unassigned)) **
      ((IntArray.seg_shape unassigned (Z.add live 1) cap)) **
      ((IntPtrArray2.full row_table live ( snap_rows snap))) **
      ((poly_undef_store FET_ptr (Z.add row_table (Z.mul (Z.sub slot 1) (@sizeof_front_end_type FET_ptr))))) **
      ((PtrArray.undef_seg row_table (Z.add live 1) cap)) **
      ((IntArray.full new_cl n row))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy65 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (snap : dense_snapshot) (dl : Z) (ranks : (Z -> (@option nat))) (n : Z) (cap : Z) (live : Z) (row : (@list Z)) (F : cnf) (conflict_cl : Z) (installed_snap : dense_snapshot) (original_count : Z) (pre_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (last : Z) (new_cl : Z) (reasons : Z) (levels : Z) (values : Z) (v_data : Z) (s : Z) (cl_data : Z) (states : Z) (unassigned : Z) (true_counts : Z) (row_table : Z),
    TT &&
    (“ (snapshot_installs row snap installed_snap) ”) &&
    (“ (Z.le 0 conflict_cl) ”) &&
    (“ (Z.lt conflict_cl live) ”) &&
    (“ (Z.lt 0 dl) ”) &&
    (“ (Z.le dl n) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.lt live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n snap ranks dl) ”) &&
    (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) ( cdcl_view_of_snapshot n snap ranks dl) last) ”) &&
    (“ (current_learning_exit_cert F ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
    (“ (clause_vars_assigned ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
    (“ (installing_clause F ( cdcl_view_of_snapshot n snap ranks dl) n cap row ( dense_decode row) live (Z.add live 1)) ”) &&
    emp **
    ((sat_header_rep s n (Z.add live 1) cap dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((variable_arrays_rep values reasons levels n snap)) **
    ((clause_summaries_explicit_rep states true_counts unassigned (Z.add live 1) cap ( snap_states installed_snap) ( snap_true_counts installed_snap) ( snap_unassigned installed_snap))) **
    ((IntPtrArray2.missing_i row_table (Z.add live 1) live new_cl ( snap_rows installed_snap))) **
    ((poly_store FET_ptr (Z.add row_table (Z.mul live (@sizeof_front_end_type FET_ptr))) new_cl)) **
    ((IntArray.full new_cl n row)) **
    ((PtrArray.undef_seg row_table (Z.add live 1) cap)) -*
    TT &&
    emp **
    ((solver_installed_row_state s F original_count values reasons levels states true_counts unassigned row_table n live cap conflict_cl new_cl row snap ranks dl))
    ).

Definition CDCL_qcp_strategy66 :=
  forall (snap : dense_snapshot) (dl : Z) (ranks : (Z -> (@option nat))) (n : Z) (cap : Z) (live : Z) (row : (@list Z)) (F : cnf) (conflict_cl : Z) (original_count : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (new_cl : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_installed_row_state s F original_count values reasons levels states true_counts unassigned row_table n live cap conflict_cl new_cl row snap ranks dl))
    |--
    EX (pre_snap : dense_snapshot) (installed_snap : dense_snapshot) (pre_ranks : (Z -> (@option nat))) (last : Z) (v_data : Z) (cl_data : Z),
      (
      TT &&
      (“ (snapshot_installs row snap installed_snap) ”) &&
      (“ (Z.le 0 conflict_cl) ”) &&
      (“ (Z.lt conflict_cl live) ”) &&
      (“ (Z.lt 0 dl) ”) &&
      (“ (Z.le dl n) ”) &&
      (“ (Z.le 0 original_count) ”) &&
      (“ (Z.le original_count live) ”) &&
      (“ (Z.le 0 live) ”) &&
      (“ (Z.lt live cap) ”) &&
      (“ (coherent_snapshot F n live original_count snap) ”) &&
      (“ (stable_search_facts n snap ranks dl) ”) &&
      (“ (dense_conflict_batch ( cdcl_view_of_snapshot n pre_snap pre_ranks dl) ( cdcl_view_of_snapshot n snap ranks dl) last) ”) &&
      (“ (current_learning_exit_cert F ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
      (“ (clause_vars_assigned ( cdcl_view_of_snapshot n snap ranks dl) ( dense_decode row)) ”) &&
      (“ (installing_clause F ( cdcl_view_of_snapshot n snap ranks dl) n cap row ( dense_decode row) live (Z.add live 1)) ”) &&
      emp **
      ((sat_header_rep s n (Z.add live 1) cap dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((variable_arrays_rep values reasons levels n snap)) **
      ((clause_summaries_explicit_rep states true_counts unassigned (Z.add live 1) cap ( snap_states installed_snap) ( snap_true_counts installed_snap) ( snap_unassigned installed_snap))) **
      ((IntPtrArray2.missing_i row_table (Z.add live 1) live new_cl ( snap_rows installed_snap))) **
      ((poly_store FET_ptr (Z.add row_table (Z.mul live (@sizeof_front_end_type FET_ptr))) new_cl)) **
      ((IntArray.full new_cl n row)) **
      ((PtrArray.undef_seg row_table (Z.add live 1) cap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy69 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (snap : dense_snapshot) (logical_dl : Z) (ranks : (Z -> (@option nat))) (n : Z) (focus : Z) (cap : Z) (F : cnf) (live : Z) (original_count : Z) (row_ptr : Z) (reasons : Z) (values : Z) (v_data : Z) (s : Z) (cl_data : Z) (true_counts : Z) (unassigned : Z) (states : Z) (levels : Z) (row_table : Z),
    TT &&
    (“ (Z.lt 0 n) ”) &&
    (“ (Z.lt n ( INT_MAX)) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (Z.lt 0 logical_dl) ”) &&
    (“ (Z.le 0 focus) ”) &&
    (“ (Z.lt focus live) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n snap ranks logical_dl) ”) &&
    emp **
    ((sat_header_rep s n live cap logical_dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((IntArray.full reasons n ( snap_reasons snap))) **
    ((IntArray.full levels n ( snap_levels snap))) **
    ((installed_row_focus_rep row_table live focus row_ptr ( snap_rows snap))) **
    ((PtrArray.undef_seg row_table live cap)) -*
    TT &&
    emp **
    ((learning_focus_state s F original_count values reasons levels states true_counts unassigned row_table n live cap focus row_ptr snap ranks logical_dl))
    ).

Definition CDCL_qcp_strategy70 :=
  forall (snap : dense_snapshot) (logical_dl : Z) (ranks : (Z -> (@option nat))) (n : Z) (focus : Z) (cap : Z) (F : cnf) (live : Z) (original_count : Z) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (row_ptr : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((learning_focus_state s F original_count values reasons levels states true_counts unassigned row_table n live cap focus row_ptr snap ranks logical_dl))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      (“ (Z.lt 0 n) ”) &&
      (“ (Z.lt n ( INT_MAX)) ”) &&
      (“ (Z.le 0 original_count) ”) &&
      (“ (Z.le original_count live) ”) &&
      (“ (Z.le 0 live) ”) &&
      (“ (Z.le live cap) ”) &&
      (“ (Z.lt 0 logical_dl) ”) &&
      (“ (Z.le 0 focus) ”) &&
      (“ (Z.lt focus live) ”) &&
      (“ (coherent_snapshot F n live original_count snap) ”) &&
      (“ (stable_search_facts n snap ranks logical_dl) ”) &&
      emp **
      ((sat_header_rep s n live cap logical_dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((IntArray.full reasons n ( snap_reasons snap))) **
      ((IntArray.full levels n ( snap_levels snap))) **
      ((installed_row_focus_rep row_table live focus row_ptr ( snap_rows snap))) **
      ((PtrArray.undef_seg row_table live cap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy71 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (n : Z) (vlevs : (@list Z)) (levels : Z) (vvals : (@list Z)) (values : Z) (v_data : Z) (s : Z) (dl : Z) (cl_data : Z) (reasons : Z) (vreas : (@list Z)) (states : Z) (unassigned : Z) (live : Z) (rows : (@list (@list Z))) (cur_true : (@list Z)) (cur_unassigned : (@list Z)) (cur_states : (@list Z)) (cap : Z) (row_table : Z) (true_counts : Z),
    TT &&
    emp **
    ((sat_header_rep s n live cap dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((IntArray.full values n vvals)) **
    ((IntArray.full reasons n vreas)) **
    ((IntArray.full levels n vlevs)) **
    ((clause_arrays_explicit_rep states true_counts unassigned row_table live cap rows cur_states cur_true cur_unassigned)) -*
    TT &&
    emp **
    ((solver_explicit_state s values reasons levels states true_counts unassigned row_table n live cap dl vvals vreas vlevs rows cur_states cur_true cur_unassigned))
    ).

Definition CDCL_qcp_strategy72 :=
  forall (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (cap : Z) (vvals : (@list Z)) (vlevs : (@list Z)) (cur_states : (@list Z)) (cur_unassigned : (@list Z)) (cur_true : (@list Z)) (rows : (@list (@list Z))) (vreas : (@list Z)) (dl : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_explicit_state s values reasons levels states true_counts unassigned row_table n live cap dl vvals vreas vlevs rows cur_states cur_true cur_unassigned))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      emp **
      ((sat_header_rep s n live cap dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((IntArray.full values n vvals)) **
      ((IntArray.full reasons n vreas)) **
      ((IntArray.full levels n vlevs)) **
      ((clause_arrays_explicit_rep states true_counts unassigned row_table live cap rows cur_states cur_true cur_unassigned))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy75 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (current_snap : dense_snapshot) (snap : dense_snapshot) (i : Z) (original_count : Z) (F : cnf) (back_dl : Z) (cap : Z) (conflict_ranks : (Z -> (@option nat))) (conflict_dl : Z) (conflict_snap : dense_snapshot) (n : Z) (live : Z) (after_snap : dense_snapshot) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (cur_states : (@list Z)) (cur_unassigned : (@list Z)) (cur_true : (@list Z)) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (Z.le 0 back_dl) ”) &&
    (“ (Z.lt back_dl conflict_dl) ”) &&
    (“ (Z.le 0 n) ”) &&
    (“ (Z.lt n ( INT_MAX)) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n conflict_snap conflict_ranks conflict_dl) ”) &&
    (“ (snapshot_lengths n live current_snap) ”) &&
    (“ (snapshot_cells_wf n live current_snap) ”) &&
    (“ (snapshot_lengths n live after_snap) ”) &&
    (“ (snapshot_cells_wf n live after_snap) ”) &&
    (“ (( snap_values after_snap) = (@replace_Znth Z i (Z.sub 0 1) ( snap_values current_snap))) ”) &&
    (“ (( snap_reasons after_snap) = (@replace_Znth Z i (Z.sub 0 1) ( snap_reasons current_snap))) ”) &&
    (“ (( snap_levels after_snap) = (@replace_Znth Z i (Z.sub 0 1) ( snap_levels current_snap))) ”) &&
    (“ (( snap_rows after_snap) = ( snap_rows current_snap)) ”) &&
    (“ (( snap_rows current_snap) = ( snap_rows snap)) ”) &&
    emp **
    ((solver_explicit_state s values reasons levels states true_counts unassigned row_table n live cap back_dl ( snap_values current_snap) ( snap_reasons current_snap) ( snap_levels current_snap) ( snap_rows current_snap) cur_states cur_true cur_unassigned)) -*
    TT &&
    emp **
    ((backtrack_inner_state s F original_count snap conflict_snap current_snap after_snap conflict_ranks conflict_dl back_dl i values reasons levels states true_counts unassigned row_table n live cap cur_states cur_true cur_unassigned))
    ).

Definition CDCL_qcp_strategy76 :=
  forall (current_snap : dense_snapshot) (snap : dense_snapshot) (i : Z) (original_count : Z) (F : cnf) (back_dl : Z) (cap : Z) (conflict_ranks : (Z -> (@option nat))) (conflict_dl : Z) (conflict_snap : dense_snapshot) (n : Z) (live : Z) (after_snap : dense_snapshot) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (cur_true : (@list Z)) (cur_unassigned : (@list Z)) (cur_states : (@list Z)) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((backtrack_inner_state s F original_count snap conflict_snap current_snap after_snap conflict_ranks conflict_dl back_dl i values reasons levels states true_counts unassigned row_table n live cap cur_states cur_true cur_unassigned))
    |--
    (
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (Z.le 0 back_dl) ”) &&
    (“ (Z.lt back_dl conflict_dl) ”) &&
    (“ (Z.le 0 n) ”) &&
    (“ (Z.lt n ( INT_MAX)) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n conflict_snap conflict_ranks conflict_dl) ”) &&
    (“ (snapshot_lengths n live current_snap) ”) &&
    (“ (snapshot_cells_wf n live current_snap) ”) &&
    (“ (snapshot_lengths n live after_snap) ”) &&
    (“ (snapshot_cells_wf n live after_snap) ”) &&
    (“ (( snap_values after_snap) = (@replace_Znth Z i (Z.sub 0 1) ( snap_values current_snap))) ”) &&
    (“ (( snap_reasons after_snap) = (@replace_Znth Z i (Z.sub 0 1) ( snap_reasons current_snap))) ”) &&
    (“ (( snap_levels after_snap) = (@replace_Znth Z i (Z.sub 0 1) ( snap_levels current_snap))) ”) &&
    (“ (( snap_rows after_snap) = ( snap_rows current_snap)) ”) &&
    (“ (( snap_rows current_snap) = ( snap_rows snap)) ”) &&
    emp **
    ((solver_explicit_state s values reasons levels states true_counts unassigned row_table n live cap back_dl ( snap_values current_snap) ( snap_reasons current_snap) ( snap_levels current_snap) ( snap_rows current_snap) cur_states cur_true cur_unassigned))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy73 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (row_ptr : Z) (rows : (@list (@list Z))) (focus : Z) (n : Z) (vlevs : (@list Z)) (levels : Z) (vvals : (@list Z)) (values : Z) (v_data : Z) (s : Z) (dl : Z) (cl_data : Z) (reasons : Z) (vreas : (@list Z)) (states : Z) (unassigned : Z) (cur_true : (@list Z)) (cur_unassigned : (@list Z)) (cur_states : (@list Z)) (true_counts : Z) (row_table : Z) (cap : Z) (live : Z),
    TT &&
    emp **
    ((sat_header_rep s n live cap dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((IntArray.full values n vvals)) **
    ((IntArray.full reasons n vreas)) **
    ((IntArray.full levels n vlevs)) **
    ((clause_summaries_explicit_rep states true_counts unassigned live cap cur_states cur_true cur_unassigned)) **
    ((installed_row_focus_rep row_table live focus row_ptr rows)) **
    ((PtrArray.undef_seg row_table live cap)) -*
    TT &&
    emp **
    ((solver_row_focus_state s values reasons levels states true_counts unassigned row_table n live cap dl focus row_ptr vvals vreas vlevs rows cur_states cur_true cur_unassigned))
    ).

Definition CDCL_qcp_strategy74 :=
  forall (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (cap : Z) (focus : Z) (vvals : (@list Z)) (vlevs : (@list Z)) (cur_states : (@list Z)) (cur_unassigned : (@list Z)) (cur_true : (@list Z)) (rows : (@list (@list Z))) (vreas : (@list Z)) (row_ptr : Z) (dl : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((solver_row_focus_state s values reasons levels states true_counts unassigned row_table n live cap dl focus row_ptr vvals vreas vlevs rows cur_states cur_true cur_unassigned))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      emp **
      ((sat_header_rep s n live cap dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((IntArray.full values n vvals)) **
      ((IntArray.full reasons n vreas)) **
      ((IntArray.full levels n vlevs)) **
      ((clause_summaries_explicit_rep states true_counts unassigned live cap cur_states cur_true cur_unassigned)) **
      ((installed_row_focus_rep row_table live focus row_ptr rows)) **
      ((PtrArray.undef_seg row_table live cap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy77 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (current_snap : dense_snapshot) (snap : dense_snapshot) (i : Z) (original_count : Z) (F : cnf) (back_dl : Z) (cap : Z) (conflict_ranks : (Z -> (@option nat))) (conflict_dl : Z) (conflict_snap : dense_snapshot) (n : Z) (live : Z) (after_snap : dense_snapshot) (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (j : Z) (cur_states : (@list Z)) (cur_unassigned : (@list Z)) (cur_true : (@list Z)) (row_ptr : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (Z.le 0 back_dl) ”) &&
    (“ (Z.lt back_dl conflict_dl) ”) &&
    (“ (Z.le 0 n) ”) &&
    (“ (Z.lt n ( INT_MAX)) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n conflict_snap conflict_ranks conflict_dl) ”) &&
    (“ (snapshot_lengths n live current_snap) ”) &&
    (“ (snapshot_cells_wf n live current_snap) ”) &&
    (“ (snapshot_lengths n live after_snap) ”) &&
    (“ (snapshot_cells_wf n live after_snap) ”) &&
    (“ (( snap_values after_snap) = (@replace_Znth Z i (Z.opp 1) ( snap_values current_snap))) ”) &&
    (“ (( snap_reasons after_snap) = (@replace_Znth Z i (Z.opp 1) ( snap_reasons current_snap))) ”) &&
    (“ (( snap_levels after_snap) = (@replace_Znth Z i (Z.opp 1) ( snap_levels current_snap))) ”) &&
    (“ (( snap_rows after_snap) = ( snap_rows current_snap)) ”) &&
    (“ (( snap_rows current_snap) = ( snap_rows snap)) ”) &&
    emp **
    ((solver_row_focus_state s values reasons levels states true_counts unassigned row_table n live cap back_dl j row_ptr ( snap_values current_snap) ( snap_reasons current_snap) ( snap_levels current_snap) ( snap_rows current_snap) cur_states cur_true cur_unassigned)) -*
    TT &&
    emp **
    ((backtrack_row_focus_state s F original_count snap conflict_snap current_snap after_snap conflict_ranks conflict_dl back_dl i j values reasons levels states true_counts unassigned row_table n live cap row_ptr cur_states cur_true cur_unassigned))
    ).

Definition CDCL_qcp_strategy78 :=
  forall (current_snap : dense_snapshot) (snap : dense_snapshot) (i : Z) (original_count : Z) (F : cnf) (back_dl : Z) (cap : Z) (conflict_ranks : (Z -> (@option nat))) (conflict_dl : Z) (conflict_snap : dense_snapshot) (n : Z) (live : Z) (after_snap : dense_snapshot) (s : Z) (values : Z) (levels : Z) (true_counts : Z) (row_table : Z) (row_ptr : Z) (cur_true : (@list Z)) (cur_unassigned : (@list Z)) (cur_states : (@list Z)) (unassigned : Z) (states : Z) (reasons : Z) (j : Z),
    TT &&
    emp **
    ((backtrack_row_focus_state s F original_count snap conflict_snap current_snap after_snap conflict_ranks conflict_dl back_dl i j values reasons levels states true_counts unassigned row_table n live cap row_ptr cur_states cur_true cur_unassigned))
    |--
    (
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (Z.le 0 back_dl) ”) &&
    (“ (Z.lt back_dl conflict_dl) ”) &&
    (“ (Z.le 0 n) ”) &&
    (“ (Z.lt n ( INT_MAX)) ”) &&
    (“ (Z.le 0 original_count) ”) &&
    (“ (Z.le original_count live) ”) &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.le live cap) ”) &&
    (“ (coherent_snapshot F n live original_count snap) ”) &&
    (“ (stable_search_facts n conflict_snap conflict_ranks conflict_dl) ”) &&
    (“ (snapshot_lengths n live current_snap) ”) &&
    (“ (snapshot_cells_wf n live current_snap) ”) &&
    (“ (snapshot_lengths n live after_snap) ”) &&
    (“ (snapshot_cells_wf n live after_snap) ”) &&
    (“ (( snap_values after_snap) = (@replace_Znth Z i (Z.opp 1) ( snap_values current_snap))) ”) &&
    (“ (( snap_reasons after_snap) = (@replace_Znth Z i (Z.opp 1) ( snap_reasons current_snap))) ”) &&
    (“ (( snap_levels after_snap) = (@replace_Znth Z i (Z.opp 1) ( snap_levels current_snap))) ”) &&
    (“ (( snap_rows after_snap) = ( snap_rows current_snap)) ”) &&
    (“ (( snap_rows current_snap) = ( snap_rows snap)) ”) &&
    emp **
    ((solver_row_focus_state s values reasons levels states true_counts unassigned row_table n live cap back_dl j row_ptr ( snap_values current_snap) ( snap_reasons current_snap) ( snap_levels current_snap) ( snap_rows current_snap) cur_states cur_true cur_unassigned))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy79 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (row_ptr : Z) (snap : dense_snapshot) (focus : Z) (cur_unassigned : (@list Z)) (cur_true : (@list Z)) (cur_states : (@list Z)) (reasons : Z) (n : Z) (new_snap : dense_snapshot) (levels : Z) (values : Z) (v_data : Z) (s : Z) (dl : Z) (cl_data : Z) (current_state : Z) (states : Z) (true_counts : Z) (unassigned : Z) (row_table : Z) (cap : Z) (live : Z),
    TT &&
    emp **
    ((sat_header_rep s n live cap dl v_data cl_data)) **
    ((var_header_rep v_data values reasons levels)) **
    ((clause_header_rep cl_data states true_counts unassigned row_table)) **
    ((variable_arrays_rep values reasons levels n new_snap)) **
    ((poly_store FET_int (Z.add states (Z.mul focus (@sizeof_front_end_type FET_int))) current_state)) **
    ((IntArray.missing_i states focus 0 live cur_states)) **
    ((IntArray.seg_shape states live cap)) **
    ((IntArray.full true_counts live cur_true)) **
    ((IntArray.seg_shape true_counts live cap)) **
    ((IntArray.full unassigned live cur_unassigned)) **
    ((IntArray.seg_shape unassigned live cap)) **
    ((installed_row_focus_rep row_table live focus row_ptr ( snap_rows snap))) **
    ((PtrArray.undef_seg row_table live cap)) -*
    TT &&
    emp **
    ((bcp_clause_update_state s values reasons levels states true_counts unassigned row_table n live cap dl focus row_ptr current_state snap new_snap cur_states cur_true cur_unassigned))
    ).

Definition CDCL_qcp_strategy80 :=
  forall (s : Z) (reasons : Z) (states : Z) (unassigned : Z) (n : Z) (cap : Z) (focus : Z) (current_state : Z) (new_snap : dense_snapshot) (cur_true : (@list Z)) (cur_unassigned : (@list Z)) (cur_states : (@list Z)) (snap : dense_snapshot) (row_ptr : Z) (dl : Z) (live : Z) (row_table : Z) (true_counts : Z) (levels : Z) (values : Z),
    TT &&
    emp **
    ((bcp_clause_update_state s values reasons levels states true_counts unassigned row_table n live cap dl focus row_ptr current_state snap new_snap cur_states cur_true cur_unassigned))
    |--
    EX (v_data : Z) (cl_data : Z),
      (
      TT &&
      emp **
      ((sat_header_rep s n live cap dl v_data cl_data)) **
      ((var_header_rep v_data values reasons levels)) **
      ((clause_header_rep cl_data states true_counts unassigned row_table)) **
      ((variable_arrays_rep values reasons levels n new_snap)) **
      ((poly_store FET_int (Z.add states (Z.mul focus (@sizeof_front_end_type FET_int))) current_state)) **
      ((IntArray.missing_i states focus 0 live cur_states)) **
      ((IntArray.seg_shape states live cap)) **
      ((IntArray.full true_counts live cur_true)) **
      ((IntArray.seg_shape true_counts live cap)) **
      ((IntArray.full unassigned live cur_unassigned)) **
      ((IntArray.seg_shape unassigned live cap)) **
      ((installed_row_focus_rep row_table live focus row_ptr ( snap_rows snap))) **
      ((PtrArray.undef_seg row_table live cap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition CDCL_qcp_strategy4 :=
  forall (i : Z) (live : Z) (row_ptr : Z) (__default_app1_Z : (@list Z)) (rows : (@list (@list Z))) (p : Z) (cap : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i live) ”) &&
    emp **
    ((IntPtrArray2.missing_i p live i row_ptr rows)) **
    ((IntArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) row_ptr)) **
    ((PtrArray.undef_seg p live cap))
    |--
    (
    TT &&
    emp **
    ((installed_rows_capacity_rep p live cap rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition CDCL_qcp_strategy6 :=
  forall (live : Z) (cap : Z) (row : (@list Z)) (newp : Z) (rows : (@list (@list Z))) (p : Z),
    TT &&
    (“ (Z.le 0 live) ”) &&
    (“ (Z.lt live cap) ”) &&
    emp **
    ((IntPtrArray2.full p live rows)) **
    ((poly_store FET_ptr (Z.add p (Z.mul live (@sizeof_front_end_type FET_ptr))) newp)) **
    ((IntArray.full newp (@Zlength Z row) row)) **
    ((PtrArray.undef_seg p (Z.add live 1) cap))
    |--
    (
    TT &&
    emp **
    ((installed_rows_capacity_rep p (Z.add live 1) cap (@app (@list Z) rows (@cons (@list Z) row (@nil (@list Z))))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type CDCL_qcp_Strategy_Correct.

  Axiom CDCL_qcp_strategy7_correctness : CDCL_qcp_strategy7.
  Axiom CDCL_qcp_strategy8_correctness : CDCL_qcp_strategy8.
  Axiom CDCL_qcp_strategy9_correctness : CDCL_qcp_strategy9.
  Axiom CDCL_qcp_strategy10_correctness : CDCL_qcp_strategy10.
  Axiom CDCL_qcp_strategy3_correctness : CDCL_qcp_strategy3.
  Axiom CDCL_qcp_strategy5_correctness : CDCL_qcp_strategy5.
  Axiom CDCL_qcp_strategy11_correctness : CDCL_qcp_strategy11.
  Axiom CDCL_qcp_strategy12_correctness : CDCL_qcp_strategy12.
  Axiom CDCL_qcp_strategy13_correctness : CDCL_qcp_strategy13.
  Axiom CDCL_qcp_strategy14_correctness : CDCL_qcp_strategy14.
  Axiom CDCL_qcp_strategy15_correctness : CDCL_qcp_strategy15.
  Axiom CDCL_qcp_strategy16_correctness : CDCL_qcp_strategy16.
  Axiom CDCL_qcp_strategy17_correctness : CDCL_qcp_strategy17.
  Axiom CDCL_qcp_strategy18_correctness : CDCL_qcp_strategy18.
  Axiom CDCL_qcp_strategy19_correctness : CDCL_qcp_strategy19.
  Axiom CDCL_qcp_strategy20_correctness : CDCL_qcp_strategy20.
  Axiom CDCL_qcp_strategy21_correctness : CDCL_qcp_strategy21.
  Axiom CDCL_qcp_strategy22_correctness : CDCL_qcp_strategy22.
  Axiom CDCL_qcp_strategy23_correctness : CDCL_qcp_strategy23.
  Axiom CDCL_qcp_strategy24_correctness : CDCL_qcp_strategy24.
  Axiom CDCL_qcp_strategy25_correctness : CDCL_qcp_strategy25.
  Axiom CDCL_qcp_strategy26_correctness : CDCL_qcp_strategy26.
  Axiom CDCL_qcp_strategy27_correctness : CDCL_qcp_strategy27.
  Axiom CDCL_qcp_strategy28_correctness : CDCL_qcp_strategy28.
  Axiom CDCL_qcp_strategy29_correctness : CDCL_qcp_strategy29.
  Axiom CDCL_qcp_strategy30_correctness : CDCL_qcp_strategy30.
  Axiom CDCL_qcp_strategy31_correctness : CDCL_qcp_strategy31.
  Axiom CDCL_qcp_strategy32_correctness : CDCL_qcp_strategy32.
  Axiom CDCL_qcp_strategy33_correctness : CDCL_qcp_strategy33.
  Axiom CDCL_qcp_strategy34_correctness : CDCL_qcp_strategy34.
  Axiom CDCL_qcp_strategy35_correctness : CDCL_qcp_strategy35.
  Axiom CDCL_qcp_strategy36_correctness : CDCL_qcp_strategy36.
  Axiom CDCL_qcp_strategy37_correctness : CDCL_qcp_strategy37.
  Axiom CDCL_qcp_strategy38_correctness : CDCL_qcp_strategy38.
  Axiom CDCL_qcp_strategy39_correctness : CDCL_qcp_strategy39.
  Axiom CDCL_qcp_strategy40_correctness : CDCL_qcp_strategy40.
  Axiom CDCL_qcp_strategy41_correctness : CDCL_qcp_strategy41.
  Axiom CDCL_qcp_strategy42_correctness : CDCL_qcp_strategy42.
  Axiom CDCL_qcp_strategy43_correctness : CDCL_qcp_strategy43.
  Axiom CDCL_qcp_strategy44_correctness : CDCL_qcp_strategy44.
  Axiom CDCL_qcp_strategy45_correctness : CDCL_qcp_strategy45.
  Axiom CDCL_qcp_strategy46_correctness : CDCL_qcp_strategy46.
  Axiom CDCL_qcp_strategy47_correctness : CDCL_qcp_strategy47.
  Axiom CDCL_qcp_strategy48_correctness : CDCL_qcp_strategy48.
  Axiom CDCL_qcp_strategy49_correctness : CDCL_qcp_strategy49.
  Axiom CDCL_qcp_strategy50_correctness : CDCL_qcp_strategy50.
  Axiom CDCL_qcp_strategy51_correctness : CDCL_qcp_strategy51.
  Axiom CDCL_qcp_strategy52_correctness : CDCL_qcp_strategy52.
  Axiom CDCL_qcp_strategy53_correctness : CDCL_qcp_strategy53.
  Axiom CDCL_qcp_strategy54_correctness : CDCL_qcp_strategy54.
  Axiom CDCL_qcp_strategy55_correctness : CDCL_qcp_strategy55.
  Axiom CDCL_qcp_strategy56_correctness : CDCL_qcp_strategy56.
  Axiom CDCL_qcp_strategy57_correctness : CDCL_qcp_strategy57.
  Axiom CDCL_qcp_strategy58_correctness : CDCL_qcp_strategy58.
  Axiom CDCL_qcp_strategy59_correctness : CDCL_qcp_strategy59.
  Axiom CDCL_qcp_strategy60_correctness : CDCL_qcp_strategy60.
  Axiom CDCL_qcp_strategy61_correctness : CDCL_qcp_strategy61.
  Axiom CDCL_qcp_strategy62_correctness : CDCL_qcp_strategy62.
  Axiom CDCL_qcp_strategy63_correctness : CDCL_qcp_strategy63.
  Axiom CDCL_qcp_strategy64_correctness : CDCL_qcp_strategy64.
  Axiom CDCL_qcp_strategy65_correctness : CDCL_qcp_strategy65.
  Axiom CDCL_qcp_strategy66_correctness : CDCL_qcp_strategy66.
  Axiom CDCL_qcp_strategy69_correctness : CDCL_qcp_strategy69.
  Axiom CDCL_qcp_strategy70_correctness : CDCL_qcp_strategy70.
  Axiom CDCL_qcp_strategy71_correctness : CDCL_qcp_strategy71.
  Axiom CDCL_qcp_strategy72_correctness : CDCL_qcp_strategy72.
  Axiom CDCL_qcp_strategy75_correctness : CDCL_qcp_strategy75.
  Axiom CDCL_qcp_strategy76_correctness : CDCL_qcp_strategy76.
  Axiom CDCL_qcp_strategy73_correctness : CDCL_qcp_strategy73.
  Axiom CDCL_qcp_strategy74_correctness : CDCL_qcp_strategy74.
  Axiom CDCL_qcp_strategy77_correctness : CDCL_qcp_strategy77.
  Axiom CDCL_qcp_strategy78_correctness : CDCL_qcp_strategy78.
  Axiom CDCL_qcp_strategy79_correctness : CDCL_qcp_strategy79.
  Axiom CDCL_qcp_strategy80_correctness : CDCL_qcp_strategy80.
  Axiom CDCL_qcp_strategy4_correctness : CDCL_qcp_strategy4.
  Axiom CDCL_qcp_strategy6_correctness : CDCL_qcp_strategy6.

End CDCL_qcp_Strategy_Correct.
