#define KOSARAJU_DFS1_IMPLEMENTATION
#include "dfs1.h"

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
 */
{
  vis1[u] = 1;
  int const lo = radj_row[u];
  int const hi = radj_row[u + 1];
  int i = lo;

  /*@ Inv Assert
      exists vis1_m fin_m timer_m,
        csr_wf1(g, radj_col_l, radj_row_l, vis1_m, fin_m) &&
        csr1_faithful(g, radj_col_l, radj_row_l) &&
        adj_verts(g) == n &&
        dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_m, fin_m, timer_m) &&
        dfs1_finish_prefix_marked(fin_m, vis1_m, timer_m, n) &&
        dfs1_active_sequence_extension(g, vis1_l, fin_l, timer_v,
                                       vis1_m, fin_m, timer_m, u) &&
        safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l,
                                   vis1_m, fin_m, timer_m),
                 dfs_finish_from(g, radj_col_l, radj_row_l, u, i), X) &&
        u == u@pre && n == n@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        vis1 == vis1@pre && fin == fin@pre && timer_p == timer_p@pre &&
        lo == csr_lo(u, radj_row_l) && hi == csr_hi(u, radj_row_l) &&
        0 <= lo && lo <= i && i <= hi && hi <= m_of(radj_row_l) &&
        0 <= u && u < n && n <= 2147483646 &&
        0 <= timer_m && timer_m <= count_nonzero(vis1_m) &&
        timer_m < n &&
        timer_v <= timer_m &&
        timer_m + 1 <= count_nonzero(vis1_m) &&
        Znth(u, vis1_l, 0) == 0 &&
        Znth(u, vis1_m, 0) != 0 &&
        (forall w, 0 <= w && w < n &&
           Znth(w, vis1_l, 0) != 0 =>
           Znth(w, vis1_m, 0) != 0) &&
        dfs1_active_timer_surplus(vis1_l, vis1_m, timer_v, timer_m) &&
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        store_int(timer_p, timer_m)
  */
  while (i < hi) {
    /*@ Given vis1_m fin_m timer_m */
    int const v = radj_col[i];

    /*@ Assert
        csr_wf1(g, radj_col_l, radj_row_l, vis1_m, fin_m) &&
        csr1_faithful(g, radj_col_l, radj_row_l) &&
        adj_verts(g) == n &&
        dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_m, fin_m, timer_m) &&
        dfs1_finish_prefix_marked(fin_m, vis1_m, timer_m, n) &&
        dfs1_active_sequence_extension(g, vis1_l, fin_l, timer_v,
                                       vis1_m, fin_m, timer_m, u) &&
        safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l,
                                   vis1_m, fin_m, timer_m),
                 dfs_finish_from(g, radj_col_l, radj_row_l, u, i), X) &&
        u == u@pre && n == n@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        vis1 == vis1@pre && fin == fin@pre && timer_p == timer_p@pre &&
        lo == csr_lo(u, radj_row_l) && hi == csr_hi(u, radj_row_l) &&
        0 <= lo && lo <= i && i < hi && hi <= m_of(radj_row_l) &&
        0 <= u && u < n && n <= 2147483646 &&
        0 <= timer_m && timer_m <= count_nonzero(vis1_m) &&
        timer_m < n &&
        timer_v <= timer_m &&
        timer_m + 1 <= count_nonzero(vis1_m) &&
        Znth(u, vis1_l, 0) == 0 &&
        Znth(u, vis1_m, 0) != 0 &&
        (forall w, 0 <= w && w < n &&
           Znth(w, vis1_l, 0) != 0 =>
           Znth(w, vis1_m, 0) != 0) &&
        dfs1_active_timer_surplus(vis1_l, vis1_m, timer_v, timer_m) &&
        0 <= v && v < n && v == Znth(i, radj_col_l, 0) &&
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        store_int(timer_p, timer_m)
        */

    if (vis1[v] == 0) {
      dfs1(v, n, radj_col, radj_row, vis1, fin, timer_p)
          /*@ where(bind_spec)
                g = g,
                radj_col_l = radj_col_l, radj_row_l = radj_row_l,
                vis1_l = vis1_m, fin_l = fin_m, timer_v = timer_m,
                X = X,
                f = dfs_finish_fromK(g, radj_col_l, radj_row_l, u, i + 1); B = unit */;
    }
    i = i + 1;
  }

  fin[*timer_p] = u;
  *timer_p = *timer_p + 1;
}
