#ifndef KOSARAJU_DFS2_H
#define KOSARAJU_DFS2_H

#include "safeexecE_def.h"

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.dfs2_lib */

/*@ Extern Coq (KSt :: *) (AdjGraph :: *) (unit :: *) */
/*@ Extern Coq
      (dfs2_high_level_post: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (dfs2_phase2_post: AdjGraph -> Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (AdjGraphValid: AdjGraph -> Prop)
      (dfs_scc: AdjGraph -> Z -> Z -> program KSt unit)
      (dfs_scc_from: AdjGraph -> list Z -> list Z -> Z -> Z -> Z -> program KSt unit)
      (dfs_scc_fromK: AdjGraph -> list Z -> list Z -> Z -> Z -> Z -> unit -> program KSt unit)
      (pre_dfs2: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> KSt -> Prop)
      (phase2_sequence_residual_refinement: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (csr_wf2: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Prop)
      (csr_wf2_core: AdjGraph -> list Z -> list Z -> Prop)
      (csr2_faithful: AdjGraph -> list Z -> list Z -> Prop)
      (adj_verts: AdjGraph -> Z)
      (m_of: list Z -> Z)
      (csr_lo: Z -> list Z -> Z)
      (csr_hi: Z -> list Z -> Z)
      (Znth: {A} -> Z -> list A -> A -> A)
      (replace_Znth: {A} -> Z -> A -> list A -> list A)
   */

#ifndef KOSARAJU_DFS2_IMPLEMENTATION
void dfs2(int const root, int const u, int const n,
          int const *const fadj_col, int const *const fadj_row,
          int *const vis2, int *const sid)
/*@ low_level_spec
    With g fadj_col_l fadj_row_l vis2_l sid_l root_v X root0 n0 u0 fadj_col0 fadj_row0 vis20 sid0
    Require
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l, root_v),
               dfs_scc(g, root, u), X) &&
      0 <= u && u < n && 0 <= root && root < n && root0 == root && n <= 2147483646 &&
      Znth(u, vis2_l, 0) == 0 &&
      n0 == n && u0 == u &&
      fadj_col0 == fadj_col && fadj_row0 == fadj_row &&
      vis20 == vis2 && sid0 == sid &&
      (u == root || Znth(root, vis2_l, 0) != 0) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_) &&
      adj_verts(g) == n0 &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_, root_v),
               return(tt), X) &&
      Znth(u0, vis2_l_, 0) != 0 &&
      (forall (w: Z), (0 <= w && w < n0) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_l_, 0) != 0)) &&
      (forall (w: Z), (0 <= w && w < n0) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, sid_l_, 0) == Znth(w, sid_l, 0))) &&
      (forall (w: Z), (0 <= w && w < n0) =>
                  (Znth(w, vis2_l_, 0) != 0 =>
                   (Znth(w, vis2_l, 0) == 0 => Znth(w, sid_l_, 0) == Znth(root0, sid_l, 0)))) &&
      IntArray::full(fadj_col0, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row0, n0 + 1, fadj_row_l) *
      IntArray::full(vis20, n0, vis2_l_) *
      IntArray::full(sid0, n0, sid_l_)
*/;
#endif

void dfs2(int const root, int const u, int const n,
          int const *const fadj_col, int const *const fadj_row,
          int *const vis2, int *const sid)
/*@ high_level_spec <= low_level_spec
    With g fadj_col_l fadj_row_l vis2_l sid_l
    Require
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      adj_verts(g) == n &&
      0 <= u && u < n && 0 <= root && root < n && n <= 2147483646 &&
      Znth(u, vis2_l, 0) == 0 &&
      (u == root || Znth(root, vis2_l, 0) != 0) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      dfs2_high_level_post(g, fadj_col_l, fadj_row_l,
                              vis2_l, sid_l, vis2_l_, sid_l_,
                              root, u, n) &&
      adj_verts(g) == n &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_)
*/;

void dfs2(int const root, int const u, int const n,
          int const *const fadj_col, int const *const fadj_row,
          int *const vis2, int *const sid)
/*@ phase2_spec <= low_level_spec
    With g fadj_col_l fadj_row_l vis1_l vis2_l sid_before_l sid_l
         fin_l order_l timer_v k
    Require
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) && adj_verts(g) == n &&
      csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
      csr_lo(0, fadj_row_l) == 0 &&
      1 <= n && n <= 2147483646 &&
      0 <= k && k < n &&
      0 <= root && root < n && u == root && root == Znth(k, order_l, 0) &&
      Znth(u, vis2_l, 0) == 0 &&
      Znth(root, vis2_l, 0) == 0 &&
      Znth(root, sid_l, 0) == root &&
      sid_l == replace_Znth(root, root, sid_before_l) &&
      phase2_sequence_residual_refinement(g, fin_l, order_l, vis1_l,
                                           vis2_l, sid_before_l,
                                           timer_v, n, k) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      dfs2_high_level_post(g, fadj_col_l, fadj_row_l,
                              vis2_l, sid_l, vis2_l_, sid_l_,
                              root, root, n) &&
      dfs2_phase2_post(g, n, vis2_l, sid_l, vis2_l_, sid_l_, root) &&
      phase2_sequence_residual_refinement(g, fin_l, order_l, vis1_l,
                                           vis2_l_, sid_l_,
                                           timer_v, n, k + 1) &&
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) && adj_verts(g) == n &&
      csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
      csr_lo(0, fadj_row_l) == 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_)
*/;

void dfs2(int const root, int const u, int const n,
          int const *const fadj_col, int const *const fadj_row,
          int *const vis2, int *const sid)
/*@ bind_spec <= low_level_spec
    With {B} g fadj_col_l fadj_row_l vis2_l sid_l root_v root0 X (f: unit -> program KSt B)
    Require
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l, root_v),
               bind(dfs_scc(g, root, u), f), X) &&
      0 <= u && u < n && 0 <= root && root < n && root0 == root && n <= 2147483646 &&
      Znth(u, vis2_l, 0) == 0 &&
      Znth(root, vis2_l, 0) != 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_, root_v),
               applyf(f, tt), X) &&
      Znth(u, vis2_l_, 0) != 0 &&
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_l_, 0) != 0)) &&
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, sid_l_, 0) == Znth(w, sid_l, 0))) &&
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l_, 0) != 0 =>
                   (Znth(w, vis2_l, 0) == 0 => Znth(w, sid_l_, 0) == Znth(root0, sid_l, 0)))) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_)
*/;

#endif
