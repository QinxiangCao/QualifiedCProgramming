#ifndef KOSARAJU_DFS1_H
#define KOSARAJU_DFS1_H

#include "safeexecE_def.h"

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.dfs1_lib */

/*@ Extern Coq (KSt :: *) (AdjGraph :: *) (unit :: *) */
/*@ Extern Coq
      (dfs1_high_level_post: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (dfs_finish: AdjGraph -> Z -> program KSt unit)
      (dfs_finish_from: AdjGraph -> list Z -> list Z -> Z -> Z -> program KSt unit)
      (dfs_finish_fromK: AdjGraph -> list Z -> list Z -> Z -> Z -> unit -> program KSt unit)
      (pre_dfs1_sequence: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> KSt -> Prop)
      (dfs1_sequence_state_ready: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (dfs1_sequence_extension: AdjGraph -> list Z -> list Z -> Z -> list Z -> list Z -> Z -> Z -> Prop)
      (dfs1_active_sequence_extension: AdjGraph -> list Z -> list Z -> Z -> list Z -> list Z -> Z -> Z -> Prop)
      (dfs1_finish_prefix_marked: list Z -> list Z -> Z -> Z -> Prop)
      (dfs1_timer_surplus_preserved: list Z -> list Z -> Z -> Z -> Prop)
      (dfs1_active_timer_surplus: list Z -> list Z -> Z -> Z -> Prop)
      (csr_wf1: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Prop)
      (csr1_faithful: AdjGraph -> list Z -> list Z -> Prop)
      (adj_verts: AdjGraph -> Z)
      (m_of: list Z -> Z)
      (csr_lo: Z -> list Z -> Z)
      (csr_hi: Z -> list Z -> Z)
      (count_nonzero: list Z -> Z)
      (Znth: {A} -> Z -> list A -> A -> A)
   */

#ifndef KOSARAJU_DFS1_IMPLEMENTATION
void dfs1(int const u, int const n,
          int const *const radj_col, int const *const radj_row,
          int *const vis1, int *const fin, int *const timer_p)
/*@ low_level_spec
    With g radj_col_l radj_row_l vis1_l fin_l timer_v X
    Require
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l, fin_l) &&
      csr1_faithful(g, radj_col_l, radj_row_l) &&
      adj_verts(g) == n &&
      dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_l, fin_l, timer_v) &&
      dfs1_finish_prefix_marked(fin_l, vis1_l, timer_v, n) &&
      safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l,
                                 vis1_l, fin_l, timer_v),
               dfs_finish(g, u), X) &&
      0 <= u && u < n && n <= 2147483646 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v && timer_v <= count_nonzero(vis1_l) &&
      timer_v < n &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      store_int(timer_p, timer_v)
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l_, fin_l_) &&
      adj_verts(g) == n &&
      dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_) &&
      dfs1_sequence_extension(g, vis1_l, fin_l, timer_v,
                              vis1_l_, fin_l_, timer_v_, u) &&
      dfs1_finish_prefix_marked(fin_l_, vis1_l_, timer_v_, n) &&
      safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_),
               return(tt), X) &&
      0 <= timer_v_ && timer_v_ <= count_nonzero(vis1_l_) &&
      timer_v <= timer_v_ &&
      dfs1_timer_surplus_preserved(vis1_l, vis1_l_, timer_v, timer_v_) &&
      (forall w, 0 <= w && w < n &&
         Znth(w, vis1_l, 0) != 0 =>
         Znth(w, vis1_l_, 0) != 0) &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      store_int(timer_p, timer_v_)
*/;
#endif

void dfs1(int const u, int const n,
          int const *const radj_col, int const *const radj_row,
          int *const vis1, int *const fin, int *const timer_p)
/*@ high_level_spec <= low_level_spec
    With g radj_col_l radj_row_l vis1_l fin_l timer_v X
    Require
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l, fin_l) &&
      csr1_faithful(g, radj_col_l, radj_row_l) &&
      adj_verts(g) == n &&
      dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_l, fin_l, timer_v) &&
      dfs1_finish_prefix_marked(fin_l, vis1_l, timer_v, n) &&
      safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l,
                                 vis1_l, fin_l, timer_v),
               dfs_finish(g, u), X) &&
      0 <= u && u < n && n <= 2147483646 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v && timer_v <= count_nonzero(vis1_l) &&
      timer_v < n &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      store_int(timer_p, timer_v)
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_) &&
      dfs1_sequence_extension(g, vis1_l, fin_l, timer_v,
                              vis1_l_, fin_l_, timer_v_, u) &&
      dfs1_finish_prefix_marked(fin_l_, vis1_l_, timer_v_, n) &&
      safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_),
               return(tt), X) &&
      adj_verts(g) == n &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      store_int(timer_p, timer_v_)
*/;

void dfs1(int const u, int const n,
          int const *const radj_col, int const *const radj_row,
          int *const vis1, int *const fin, int *const timer_p)
/*@ bind_spec <= low_level_spec
    With {B} g radj_col_l radj_row_l vis1_l fin_l timer_v X (f: unit -> program KSt B)
    Require
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l, fin_l) &&
      csr1_faithful(g, radj_col_l, radj_row_l) &&
      adj_verts(g) == n &&
      dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_l, fin_l, timer_v) &&
      dfs1_finish_prefix_marked(fin_l, vis1_l, timer_v, n) &&
      safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l,
                                 vis1_l, fin_l, timer_v),
               bind(dfs_finish(g, u), f), X) &&
      0 <= u && u < n && n <= 2147483646 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v && timer_v <= count_nonzero(vis1_l) &&
      timer_v < n &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      store_int(timer_p, timer_v)
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l_, fin_l_) &&
      adj_verts(g) == n &&
      dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_) &&
      dfs1_sequence_extension(g, vis1_l, fin_l, timer_v,
                              vis1_l_, fin_l_, timer_v_, u) &&
      dfs1_finish_prefix_marked(fin_l_, vis1_l_, timer_v_, n) &&
      safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_),
               applyf(f, tt), X) &&
      0 <= timer_v_ && timer_v_ <= count_nonzero(vis1_l_) &&
      timer_v <= timer_v_ &&
      dfs1_timer_surplus_preserved(vis1_l, vis1_l_, timer_v, timer_v_) &&
      (forall w, 0 <= w && w < n &&
         Znth(w, vis1_l, 0) != 0 =>
         Znth(w, vis1_l_, 0) != 0) &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      store_int(timer_p, timer_v_)
*/;

#endif
