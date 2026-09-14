#define KOSARAJU_DFS2_IMPLEMENTATION
#include "dfs2.h"

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
 */
{
  vis2[u] = 1;
  sid[u] = sid[root];
  int lo = fadj_row[u];
  int hi = fadj_row[u + 1];
  int i = lo;

  /*@ Inv Assert
      exists vis2_m sid_m,
        csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m, root_v),
                 dfs_scc_from(g, fadj_col_l, fadj_row_l, root, u, i), X) &&
        n0 == n && u0 == u &&
        fadj_col0 == fadj_col && fadj_row0 == fadj_row &&
        vis20 == vis2 && sid0 == sid &&
        lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
        0 <= lo && lo <= i && i <= hi && hi <= m_of(fadj_row_l) &&
        0 <= u && u < n && 0 <= root && root < n && root0 == root && n <= 2147483646 &&
        Znth(u, vis2_l, 0) == 0 &&
        Znth(u, vis2_m, 0) != 0 &&
        (forall (j: Z), (lo <= j && j < i) =>
                    (Znth(Znth(j, fadj_col_l, 0), vis2_m, 0) != 0)) &&
        Znth(root, vis2_m, 0) != 0 &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_m, 0) != 0)) &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, sid_m, 0) == Znth(w, sid_l, 0))) &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_m, 0) != 0 =>
                     (Znth(w, vis2_l, 0) == 0 => Znth(w, sid_m, 0) == Znth(root0, sid_l, 0)))) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(sid, n, sid_m)
  */
  while (i < hi) {
    /*@ Given vis2_m sid_m */
    int v;
    v = fadj_col[i];

    /*@ Assert
        csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m, root_v),
                 dfs_scc_from(g, fadj_col_l, fadj_row_l, root, u, i), X) &&
        n0 == n && u0 == u &&
        fadj_col0 == fadj_col && fadj_row0 == fadj_row &&
        vis20 == vis2 && sid0 == sid &&
        lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
        0 <= lo && lo <= i && i < hi && hi <= m_of(fadj_row_l) &&
        0 <= u && u < n && 0 <= root && root < n && root0 == root && n <= 2147483646 &&
        Znth(u, vis2_l, 0) == 0 &&
        Znth(u, vis2_m, 0) != 0 &&
        (forall (j: Z), (lo <= j && j < i) =>
                    (Znth(Znth(j, fadj_col_l, 0), vis2_m, 0) != 0)) &&
        Znth(root, vis2_m, 0) != 0 &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_m, 0) != 0)) &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, sid_m, 0) == Znth(w, sid_l, 0))) &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_m, 0) != 0 =>
                     (Znth(w, vis2_l, 0) == 0 => Znth(w, sid_m, 0) == Znth(root0, sid_l, 0)))) &&
        0 <= v && v < n && v == Znth(i, fadj_col_l, 0) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(sid, n, sid_m)
    */
    if (vis2[v] == 0) {
      dfs2(root, v, n, fadj_col, fadj_row, vis2, sid)
          /*@ where(bind_spec)
                g = g,
                fadj_col_l = fadj_col_l, fadj_row_l = fadj_row_l,
                vis2_l = vis2_m, sid_l = sid_m, root_v = root_v, root0 = root0,
                X = X,
                f = dfs_scc_fromK(g, fadj_col_l, fadj_row_l, root, u, i + 1); B = unit */;
    }
    i = i + 1;
  }
}
