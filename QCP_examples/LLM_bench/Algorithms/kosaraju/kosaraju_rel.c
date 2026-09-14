#include "safeexecE_def.h"
#include "dfs1.h"
#include "dfs2.h"

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.kosaraju_rel_lib */

/*@ Extern Coq (KSt :: *) (AdjGraph :: *) (unit :: *) */
/*@ Extern Coq
               (mutually_reachable: AdjGraph -> Z -> Z -> Prop)
               (fin_values_in_int_range: list Z -> Z -> Prop)
               (order_spec: list Z -> list Z -> Z -> Prop)
               (phase2_sequence_order_spec: list Z -> list Z -> Z -> Prop)
               (phase2_order_spec: list Z -> list Z -> Z -> Prop)
               (phase1_order_graph: AdjGraph -> list Z -> Z -> Prop)
               (base_order: Z -> list Z)
               (Permutation: list Z -> list Z -> Prop)
               (fin_upperbound: list Z -> Z -> list Z -> Prop)
               (fin_nonincreasing: list Z -> list Z -> Prop)
               (fin_prefix_suffix_sorted: list Z -> list Z -> list Z -> Prop)
               (order_init_prefix: Z -> Z -> list Z -> Prop)
               (order_entries_in_range: Z -> list Z -> Prop)
               (order_covers_range: Z -> list Z -> Prop)
               (all_order_prefix_marked: Z -> Z -> list Z -> list Z -> Prop)
               (phase2_prefix_complete: AdjGraph -> Z -> Z -> list Z -> list Z -> Prop)
               (sid_correct_on_marked: AdjGraph -> Z -> list Z -> list Z -> Prop)
               (sid_labels_in_order_prefix: Z -> Z -> list Z -> list Z -> list Z -> Prop)
               (transpose_spec: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
               (dfs1_high_level_post: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
               (dfs2_high_level_post: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
               (dfs2_phase2_post: AdjGraph -> Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
               (AdjGraphValid: AdjGraph -> Prop)
                */
/*@ Extern Coq
               (dfs_finish: AdjGraph -> Z -> program KSt unit)
               (dfs_finish_schedule: AdjGraph -> Z -> Z -> program KSt unit)
               (dfs_finish_scheduleK: AdjGraph -> Z -> Z -> unit -> program KSt unit)
               (dfs_scc: AdjGraph -> Z -> Z -> program KSt unit)
               (dfs_finish_from: AdjGraph -> list Z -> list Z -> Z -> Z -> program KSt unit)
               (dfs_scc_from: AdjGraph -> list Z -> list Z -> Z -> Z -> Z -> program KSt unit)
               (dfs_finish_fromK: AdjGraph -> list Z -> list Z -> Z -> Z -> unit -> program KSt unit)
               (dfs_scc_fromK: AdjGraph -> list Z -> list Z -> Z -> Z -> Z -> unit -> program KSt unit)
               (result_state: {A} -> (KSt -> Prop) -> program KSt A -> A -> KSt -> Prop)
               (pre_dfs1_sequence: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> KSt -> Prop)
               (pre_dfs1_sequence_initial: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> KSt -> Prop)
               (dfs1_sequence_state_ready: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
               (dfs1_sequence_extension: AdjGraph -> list Z -> list Z -> Z -> list Z -> list Z -> Z -> Z -> Prop)
               (dfs1_finish_prefix_marked: list Z -> list Z -> Z -> Z -> Prop)
               (phase1_sequence_refinement: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
               (phase2_sequence_residual_refinement: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
               (dfs_finish_phase1_checked: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> program KSt unit)
               (pre_dfs2: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> KSt -> Prop)
               (dfs1_timer_surplus_preserved: list Z -> list Z -> Z -> Z -> Prop)
               (dfs1_active_timer_surplus: list Z -> list Z -> Z -> Z -> Prop)
               (csr_wf1: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Prop)
               (csr_wf2: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Prop)
               (csr_wf2_core: AdjGraph -> list Z -> list Z -> Prop)
               (radj_col_particular: AdjGraph -> list Z -> Prop)
               (csr1_faithful: AdjGraph -> list Z -> list Z -> Prop)
               (csr2_faithful: AdjGraph -> list Z -> list Z -> Prop)
               (adj_verts: AdjGraph -> Z)
               (m_of: list Z -> Z)
               (csr_lo: Z -> list Z -> Z)
               (csr_hi: Z -> list Z -> Z)
               (count_nonzero: list Z -> Z)
               (transpose_count_ready: Z -> Z -> list Z -> Prop)
               (transpose_prefix_inv: Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
               (transpose_count_values: Z -> Z -> list Z -> list Z -> Prop)
               (transpose_prefix_offsets: Z -> Z -> list Z -> list Z -> list Z -> Prop)
               (transpose_scatter_inv: Z -> Z -> Z -> list Z -> list Z -> list Z -> Prop)
               (transpose_scatter_rows: Z -> Z -> list Z -> list Z -> Prop)
               (transpose_scatter_contents: AdjGraph -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
                */

/* Working-array allocator / deallocator */
int * malloc_int_array(int n)
  /*@ Require n > 0 && emp
      Ensure exists l, Zlength(l) == n && IntArray::full(__return, n, l)
   */
  ;

void free_int_array(int *a)
  /*@ With n l
      Require IntArray::full(a, n, l)
      Ensure emp
   */
  ;

/* DFS phases are implemented and specified in dfs1.c/dfs1.h and dfs2.c/dfs2.h. */

/* ==================================================================== */
/* transpose: counting-sort CSR transpose of the forward graph.        */
/*   Inputs : fadj_col[fadj_row[u] .. fadj_row[u+1]-1] = out-neighbours*/
/*            of u, i.e. forward edges (u -> v) packed in CSR.         */
/*   Outputs: radj_col/radj_row = reverse CSR, where radj_col          */
/*            [radj_row[v] .. radj_row[v+1]-1] = in-neighbours of v    */
/*            = { u | edge u->v }.                                      */
/*   pos   : scratch cursor array of length n (malloc'd by caller),    */
/*           used as the moving write head during the scatter pass so  */
/*           radj_row stays in prefix-sum (offset) form.               */
/*   Algorithm (standard CSR transpose):                                */
/*     pass 1: count in-degree of each v into radj_row[0..n-1]          */
/*     pass 2: prefix-sum radj_row (radj_row[v]=bucket start of v);    */
/*             radj_row[n] = m.  Copy radj_row -> pos (write heads).    */
/*     pass 3: for each vertex u, scan its forward neighbour range; for */
/*             each edge (u,v) write u at radj_col[pos[v]], pos[v]++.   */
/*             The outer loop carries u, so no CSR inverse lookup.     */
/*   Postcondition: transpose_spec (csr1_faithful + csr_wf1).          */
/*   high_level_spec <= low_level_spec (no monad; pure arrays).         */
/* ==================================================================== */
void transpose(int n, int m,
               int *fadj_col, int *fadj_row,
               int *radj_col, int *radj_row, int *pos)
/*@ high_level_spec <= low_level_spec
    With g fadj_col_l fadj_row_l radj_col_l radj_row_l pos_l
    Require
      1 <= n && n <= 2147483646 &&
      0 <= m && m == m_of(fadj_row_l) &&
      m <= 2147483646 &&
      csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
      csr_lo(0, fadj_row_l) == 0 &&
	      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
	      AdjGraphValid(g) &&
	      adj_verts(g) == n &&
	      Zlength(radj_col_l) == m &&
	      Zlength(radj_row_l) == n + 1 &&
	      Zlength(pos_l) == n &&
	      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(pos, n, pos_l)
    Ensure
      exists radj_col_l_ radj_row_l_ pos_l_,
      transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l_, radj_row_l_, n) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l_) *
      IntArray::full(radj_row, n + 1, radj_row_l_) *
      IntArray::full(pos, n, pos_l_)
*/;
void transpose(int n, int m,
               int *fadj_col, int *fadj_row,
               int *radj_col, int *radj_row, int *pos)
/*@ low_level_spec
    With g fadj_col_l fadj_row_l radj_col_l radj_row_l pos_l
    Require
      1 <= n && n <= 2147483646 &&
      0 <= m && m == m_of(fadj_row_l) &&
      m <= 2147483646 &&
      csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
      csr_lo(0, fadj_row_l) == 0 &&
	      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
	      AdjGraphValid(g) &&
	      adj_verts(g) == n &&
	      Zlength(radj_col_l) == m &&
	      Zlength(radj_row_l) == n + 1 &&
	      Zlength(pos_l) == n &&
	      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(pos, n, pos_l)
    Ensure
      exists radj_col_l_ radj_row_l_ pos_l_,
      transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l_, radj_row_l_, n) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l_) *
      IntArray::full(radj_row, n + 1, radj_row_l_) *
      IntArray::full(pos, n, pos_l_)
*/
{
  /* pass 1: zero the in-degree counters in radj_row[0..n-1] */
    /*@ Inv Assert
      exists rr_m,
        0 <= v && v <= n && 1 <= n && n <= 2147483646 &&
        n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        pos == pos@pre &&
        0 <= m && m == m_of(fadj_row_l) && m <= 2147483646 &&
	        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
	        csr_lo(0, fadj_row_l) == 0 &&
	        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
	        AdjGraphValid(g) && adj_verts(g) == n &&
	        Zlength(radj_col_l) == m &&
	        Zlength(pos_l) == n &&
	        Zlength(rr_m) == n + 1 &&
	        (forall (k : Z), (0 <= k && k < v) => Znth(k, rr_m, 0) == 0) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_l)
  */
  for (int v = 0; v < n; v++) {
    /*@ Given rr_m */
    radj_row[v] = 0;
  }
  /* pass 2: count in-degrees: for each forward edge (u, v=fadj_col[j]),
     increment radj_row[v] */
  /*@ Inv Assert
      exists rr_m,
        0 <= m && m == m_of(fadj_row_l) && 0 <= j && j <= m && 1 <= n && n <= 2147483646 &&
        n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        pos == pos@pre &&
        m <= 2147483646 &&
	        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
	        csr_lo(0, fadj_row_l) == 0 &&
	        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
	        AdjGraphValid(g) && adj_verts(g) == n &&
	        Zlength(radj_col_l) == m &&
	        Zlength(pos_l) == n &&
	        Zlength(rr_m) == n + 1 &&
	        transpose_count_ready(n, j, rr_m) &&
        transpose_count_values(n, j, fadj_col_l, rr_m) &&
        (forall (k : Z), (0 <= k && k < n) => 0 <= Znth(k, rr_m, 0) && Znth(k, rr_m, 0) <= j) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_l)
  */
  for (int j = 0; j < m; j++) {
    /*@ Given rr_m */
    int v = fadj_col[j];
    /*@ Assert
        0 <= m && 0 <= j && j < m_of(fadj_row_l) && m == m_of(fadj_row_l) &&
        1 <= n && n <= 2147483646 &&
        n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        pos == pos@pre &&
        0 <= v && v < n && v == Znth(j, fadj_col_l, 0) &&
        m <= 2147483646 &&
	        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
	        csr_lo(0, fadj_row_l) == 0 &&
	        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
	        AdjGraphValid(g) && adj_verts(g) == n &&
	        Zlength(radj_col_l) == m &&
	        Zlength(pos_l) == n &&
	        Zlength(rr_m) == n + 1 &&
	        transpose_count_ready(n, j, rr_m) &&
        transpose_count_values(n, j, fadj_col_l, rr_m) &&
        (forall (k : Z), (0 <= k && k < n) => 0 <= Znth(k, rr_m, 0) && Znth(k, rr_m, 0) <= j) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_l)
    */
    radj_row[v] = radj_row[v] + 1;
  }
  /* pass 3: prefix-sum: radj_row[v] = offset of v's in-bucket;
     radj_row[n] = total edge count = m.  Copy offsets into pos. */
  int sum = 0;
  /*@ Inv Assert
      exists rr_m pos_m cnt_m,
        0 <= v && v <= n && 1 <= n && n <= 2147483646 &&
        n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        pos == pos@pre &&
        0 <= m && m == m_of(fadj_row_l) && m <= 2147483646 &&
	        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
	        csr_lo(0, fadj_row_l) == 0 &&
	        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
	        AdjGraphValid(g) && adj_verts(g) == n &&
	        Zlength(radj_col_l) == m &&
	        Zlength(pos_m) == n &&
	        transpose_prefix_inv(n, m, v, sum, rr_m, cnt_m) &&
        transpose_count_values(n, m, fadj_col_l, cnt_m) &&
        transpose_prefix_offsets(n, v, rr_m, pos_m, cnt_m) &&
        Zlength(rr_m) == n + 1 &&
        (0 < v => csr_lo(0, rr_m) == 0) &&
        0 <= sum && sum <= m &&
        (v < n => sum + Znth(v, rr_m, 0) <= m) &&
        (forall (k : Z), (0 <= k && k < n) => 0 <= Znth(k, rr_m, 0) && Znth(k, rr_m, 0) <= m) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_m)
  */
  for (int v = 0; v < n; v++) {
    /*@ Given rr_m pos_m cnt_m */
    int deg = radj_row[v];
    radj_row[v] = sum;
    pos[v] = sum;
    sum = sum + deg;
  }
  radj_row[n] = sum;
  /* pass 4: scatter.  Outer loop over source vertex u; inner loop over
     u's forward neighbour range [fadj_row[u], fadj_row[u+1]).  For each
     edge (u,v): radj_col[pos[v]] := u; pos[v]++.  radj_row is untouched
     and stays in offset form. */
  /*@ Inv Assert
      exists rc_m rr_m pos_m,
        0 <= u && u <= n && 1 <= n && n <= 2147483646 &&
        n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        pos == pos@pre &&
	        0 <= m && m == m_of(fadj_row_l) && m <= 2147483646 && sum == m &&
	        Zlength(rc_m) == m_of(fadj_row_l) &&
	        Zlength(radj_col_l) == m &&
	        Zlength(pos_m) == n &&
	        Zlength(rr_m) == n + 1 &&
	        csr_lo(0, rr_m) == 0 &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        transpose_scatter_inv(n, m, csr_lo(u, fadj_row_l), fadj_col_l, rr_m, pos_m) &&
        transpose_scatter_rows(n, m, fadj_col_l, rr_m) &&
        transpose_scatter_contents(g, n, csr_lo(u, fadj_row_l), fadj_row_l, fadj_col_l, rr_m, rc_m) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_m)
  */
  for (int u = 0; u < n; u++) {
    /*@ Given rc_m rr_m pos_m */
    int lo = fadj_row[u];
    int hi = fadj_row[u + 1];
    int j = lo;
    /*@ Inv Assert
        exists rc_m rr_m pos_m,
          0 <= u && u < n && 1 <= n && n <= 2147483646 &&
          n == n@pre &&
          fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
          radj_col == radj_col@pre && radj_row == radj_row@pre &&
          pos == pos@pre &&
	          0 <= m && m == m_of(fadj_row_l) && m <= 2147483646 && sum == m &&
	          Zlength(rc_m) == m_of(fadj_row_l) &&
	          Zlength(radj_col_l) == m &&
	          Zlength(pos_m) == n &&
	          csr_lo(0, rr_m) == 0 &&
	        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
	        csr_lo(0, fadj_row_l) == 0 &&
	        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
	        AdjGraphValid(g) && adj_verts(g) == n &&
	        Zlength(radj_col_l) == m &&
	        Zlength(pos_m) == n &&
	        lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
          0 <= lo && lo <= j && j <= hi && hi <= m_of(fadj_row_l) &&
          transpose_scatter_inv(n, m, j, fadj_col_l, rr_m, pos_m) &&
          transpose_scatter_rows(n, m, fadj_col_l, rr_m) &&
          transpose_scatter_contents(g, n, j, fadj_row_l, fadj_col_l, rr_m, rc_m) &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
          IntArray::full(radj_row, n + 1, rr_m) *
          IntArray::full(pos, n, pos_m)
    */
    while (j < hi) {
      int v = fadj_col[j];
      /*@ Assert
          exists rc_m rr_m pos_m,
          0 <= j && j < hi &&
          0 <= v && v < n && v == Znth(j, fadj_col_l, 0) &&
          0 <= u && u < n && 1 <= n && n <= 2147483646 &&
          n == n@pre &&
          fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
          radj_col == radj_col@pre && radj_row == radj_row@pre &&
          pos == pos@pre &&
	          0 <= m && m == m_of(fadj_row_l) && m <= 2147483646 && sum == m &&
	          Zlength(rc_m) == m_of(fadj_row_l) &&
	          Zlength(radj_col_l) == m &&
	          Zlength(pos_m) == n &&
	          csr_lo(0, rr_m) == 0 &&
          csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
          csr_lo(0, fadj_row_l) == 0 &&
          csr2_faithful(g, fadj_col_l, fadj_row_l) &&
          AdjGraphValid(g) && adj_verts(g) == n &&
          lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
          0 <= lo && lo <= j && j <= hi && hi <= m_of(fadj_row_l) &&
          transpose_scatter_inv(n, m, j, fadj_col_l, rr_m, pos_m) &&
          transpose_scatter_rows(n, m, fadj_col_l, rr_m) &&
          transpose_scatter_contents(g, n, j, fadj_row_l, fadj_col_l, rr_m, rc_m) &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
          IntArray::full(radj_row, n + 1, rr_m) *
          IntArray::full(pos, n, pos_m)
      */
      int p = pos[v];
      /*@ Assert
          exists rc_m rr_m pos_m,
          0 <= j && j < hi && 0 <= p && p < m_of(fadj_row_l) &&
          p == Znth(v, pos_m, 0) &&
          0 <= v && v < n && v == Znth(j, fadj_col_l, 0) &&
          0 <= u && u < n && 1 <= n && n <= 2147483646 &&
          n == n@pre &&
          fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
          radj_col == radj_col@pre && radj_row == radj_row@pre &&
          pos == pos@pre &&
          0 <= m && m == m_of(fadj_row_l) && m <= 2147483646 && sum == m &&
          Zlength(rc_m) == m_of(fadj_row_l) &&
          Zlength(radj_col_l) == m &&
          Zlength(pos_m) == n &&
          csr_lo(0, rr_m) == 0 &&
          csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
          csr_lo(0, fadj_row_l) == 0 &&
          csr2_faithful(g, fadj_col_l, fadj_row_l) &&
          AdjGraphValid(g) && adj_verts(g) == n &&
          lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
          0 <= lo && lo <= j && j <= hi && hi <= m_of(fadj_row_l) &&
          transpose_scatter_inv(n, m, j, fadj_col_l, rr_m, pos_m) &&
          transpose_scatter_rows(n, m, fadj_col_l, rr_m) &&
          transpose_scatter_contents(g, n, j, fadj_row_l, fadj_col_l, rr_m, rc_m) &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
          IntArray::full(radj_row, n + 1, rr_m) *
          IntArray::full(pos, n, pos_m)
      */
      radj_col[p] = u;
      pos[v] = p + 1;
      j = j + 1;
    }
  }
  /*@ Assert
      exists rc_m rr_m pos_m,
        n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        pos == pos@pre &&
        1 <= n && n <= 2147483646 &&
	        0 <= m && m == m_of(fadj_row_l) && m <= 2147483646 && sum == m &&
	        Zlength(rc_m) == m_of(fadj_row_l) &&
	        Zlength(radj_col_l) == m &&
	        Zlength(pos_m) == n &&
	        Zlength(rr_m) == n + 1 &&
        csr_lo(0, rr_m) == 0 &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        transpose_scatter_inv(n, m, csr_lo(n, fadj_row_l), fadj_col_l, rr_m, pos_m) &&
        transpose_scatter_rows(n, m, fadj_col_l, rr_m) &&
        transpose_scatter_contents(g, n, csr_lo(n, fadj_row_l), fadj_row_l, fadj_col_l, rr_m, rc_m) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_m)
  */
}

/* ==================================================================== */
/* kosaraju: top-level SCC driver (direct-proof external interface,    */
/*   mirroring kmp_rel.c:main).  Takes the forward CSR + an output sid */
/*   buffer; mallocs all working arrays internally and frees them      */
/*   before return, so the external spec mentions only fadj_* and sid. */
/*   Composes: transpose -> phase-1 dfs1 sweep -> sort_by_fin ->       */
/*   phase-2 dfs2 sweep over the sorted order.                         */
/*   Ensure: the output sid labels vertices so that                    */
/*     sid[u] = sid[v]  <=>  mutually_reachable g u v   (same SCC).    */
/* ==================================================================== */
void kosaraju(int n, int *fadj_col, int *fadj_row, int *sid)
/*@ high_level_spec
    With g fadj_col_l fadj_row_l sid_l
    Require
      1 <= n && n <= 2147483646 &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) &&
      csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
      csr_lo(0, fadj_row_l) == 0 &&
      adj_verts(g) == n &&
      m_of(fadj_row_l) > 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists sid_l_,
      (forall (u: Z), (0 <= u && u < n) =>
         (forall (v: Z), (0 <= v && v < n) =>
            ((Znth(u, sid_l_, 0) == Znth(v, sid_l_, 0) => mutually_reachable(g, u, v))
             && (mutually_reachable(g, u, v) => Znth(u, sid_l_, 0) == Znth(v, sid_l_, 0))))) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l_)
*/
{
  int m = fadj_row[n];
  int *radj_col = malloc_int_array(m);
  int *radj_row = malloc_int_array(n + 1);
  int *pos = malloc_int_array(n);
  int *vis1 = malloc_int_array(n);
  int *fin = malloc_int_array(n);
  int *vis2 = malloc_int_array(n);
  int timer = 0;

  /* capture the arbitrary contents returned by malloc for the working
     arrays that transpose will overwrite. */
  /*@ Assert
      exists radj_col_l0 radj_row_l0 pos_l0 vis1_l0 fin_l0 vis2_l0,
        n == n@pre && m == m_of(fadj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        timer == 0 &&
        1 <= n && n <= 2147483646 &&
	        Zlength(sid_l) == n && Zlength(vis2_l0) == n &&
	        Zlength(radj_col_l0) == m_of(fadj_row_l) &&
	        Zlength(radj_row_l0) == n + 1 &&
	        Zlength(pos_l0) == n &&
	        Zlength(vis1_l0) == n &&
	        Zlength(fin_l0) == n &&
	        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l0) *
        IntArray::full(radj_row, n + 1, radj_row_l0) *
        IntArray::full(pos, n, pos_l0) *
        IntArray::full(vis1, n, vis1_l0) *
        IntArray::full(fin, n, fin_l0) *
        IntArray::full(vis2, n, vis2_l0)
  */
  /*@ Given radj_col_l0 radj_row_l0 pos_l0 vis1_l0 fin_l0 vis2_l0 */

  /* initialise vis1 and vis2 to zero */
  /*@ Inv Assert
      exists vm vm2,
        n == n@pre && m == m_of(fadj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483646 && 0 <= u && u <= n && timer == 0 &&
	        Zlength(sid_l) == n &&
	        Zlength(fin_l0) == n &&
	        Zlength(vm) == n &&
		      Zlength(vm2) == n &&
	      (forall i, 0 <= i && i < u => Znth(i, vm, 0) == 0) &&
	      (forall i, 0 <= i && i < u => Znth(i, vm2, 0) == 0) &&
	      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m, radj_col_l0) *
        IntArray::full(radj_row, n + 1, radj_row_l0) *
        IntArray::full(pos, n, pos_l0) *
        IntArray::full(vis1, n, vm) *
        IntArray::full(fin, n, fin_l0) *
        IntArray::full(vis2, n, vm2)
  */
  for (int u = 0; u < n; u++) {
    /*@ Given vm vm2 */
    vis1[u] = 0;
    vis2[u] = 0;
  }
  /* capture the zeroed working arrays (vis1_zero/vis2_zero). */
  /*@ Assert
      exists vis1_zero vis2_zero,
        n == n@pre && m == m_of(fadj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483646 && timer == 0 &&
        Zlength(sid_l) == n && Zlength(vis1_zero) == n && Zlength(vis2_zero) == n &&
        (forall i, 0 <= i && i < n => Znth(i, vis1_zero, 0) == 0) &&
        (forall i, 0 <= i && i < n => Znth(i, vis2_zero, 0) == 0) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l0) *
        IntArray::full(radj_row, n + 1, radj_row_l0) *
        IntArray::full(pos, n, pos_l0) *
        IntArray::full(vis1, n, vis1_zero) *
        IntArray::full(fin, n, fin_l0) *
        IntArray::full(vis2, n, vis2_zero)
  */
  /*@ Given vis1_zero vis2_zero */

  /* step C: build the reverse CSR from the forward CSR.  The working
     arrays' pre-call contents (radj_col_l0/radj_row_l0/pos_l0) are
     arbitrary; transpose overwrites them. */
  /*@ Assert
      n == n@pre && m == m_of(fadj_row_l) &&
      fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
      1 <= n && n <= 2147483646 && timer == 0 &&
      Zlength(sid_l) == n && Zlength(vis1_zero) == n && Zlength(vis2_zero) == n &&
      (forall i, 0 <= i && i < n => Znth(i, vis1_zero, 0) == 0) &&
      (forall i, 0 <= i && i < n => Znth(i, vis2_zero, 0) == 0) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) && adj_verts(g) == n &&
      csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
      csr_lo(0, fadj_row_l) == 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l0) *
      IntArray::full(radj_row, n + 1, radj_row_l0) *
      IntArray::full(pos, n, pos_l0) *
      IntArray::full(vis1, n, vis1_zero) *
      IntArray::full(fin, n, fin_l0) *
      IntArray::full(vis2, n, vis2_zero)
  */
  transpose(n, m, fadj_col, fadj_row, radj_col, radj_row, pos)
      /*@ where(high_level_spec)
            g = g,
            fadj_col_l = fadj_col_l, fadj_row_l = fadj_row_l,
            radj_col_l = radj_col_l0, radj_row_l = radj_row_l0,
            pos_l = pos_l0 */;
  /* step A (phase 1): for each unvisited1 vertex, run dfs1 on the
     reverse graph to assign finish times.  Loop invariant threads the
     visited1/fin/timer arrays; each dfs1 call refines them. */
  /*@ Inv Assert
      exists vis1_m fin_m radj_col_l radj_row_l pos_l,
        n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483646 && 0 <= u && u <= n &&
        Zlength(sid_l) == n && Zlength(vis1_m) == n && Zlength(vis2_zero) == n &&
        (forall i, 0 <= i && i < n => Znth(i, vis2_zero, 0) == 0) &&
        phase1_sequence_refinement(g, radj_col_l, radj_row_l, vis1_m, fin_m,
                                   vis1_zero, fin_l0, timer, n, u) &&
        dfs1_finish_prefix_marked(fin_m, vis1_m, timer, n) &&
        transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l, radj_row_l, n) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(vis2, n, vis2_zero)
  */
  for (int u = 0; u < n; u++) {
    /*@ Given vis1_m fin_m radj_col_l radj_row_l pos_l */
    if (vis1[u] == 0) {
      /*@ Assert
          n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) &&
          fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
          Zlength(sid_l) == n && Zlength(vis2_zero) == n &&
          (forall i, 0 <= i && i < n => Znth(i, vis2_zero, 0) == 0) &&
          transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l, radj_row_l, n) &&
          csr_wf1(g, radj_col_l, radj_row_l, vis1_m, fin_m) &&
          csr1_faithful(g, radj_col_l, radj_row_l) &&
          adj_verts(g) == n &&
          dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_m, fin_m, timer) &&
          phase1_sequence_refinement(g, radj_col_l, radj_row_l, vis1_m, fin_m,
                                     vis1_zero, fin_l0, timer, n, u) &&
          dfs1_finish_prefix_marked(fin_m, vis1_m, timer, n) &&
          safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l,
                                     vis1_m, fin_m, timer),
                   bind(dfs_finish(g, u),
                        dfs_finish_scheduleK(g, u + 1, n - u - 1)),
                   result_state(pre_dfs1_sequence_initial(g, radj_col_l, radj_row_l, vis1_zero, fin_l0, n),
                                dfs_finish_schedule(g, 0, n))) &&
          0 <= u && u < n && n <= 2147483646 &&
          Znth(u, vis1_m, 0) == 0 &&
          0 <= timer && timer <= count_nonzero(vis1_m) &&
          csr2_faithful(g, fadj_col_l, fadj_row_l) && AdjGraphValid(g) &&
          csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
          csr_lo(0, fadj_row_l) == 0 &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(sid, n, sid_l) *
          IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
          IntArray::full(radj_row, n + 1, radj_row_l) *
          IntArray::full(pos, n, pos_l) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(fin, n, fin_m) *
          IntArray::full(vis2, n, vis2_zero)
      */
      dfs1(u, n, radj_col, radj_row, vis1, fin, &timer)
          /*@ where(bind_spec)
                g = g,
                radj_col_l = radj_col_l, radj_row_l = radj_row_l,
                vis1_l = vis1_m, fin_l = fin_m, timer_v = timer,
                X = result_state(pre_dfs1_sequence_initial(g, radj_col_l, radj_row_l,
                                                           vis1_zero, fin_l0, n),
                                 dfs_finish_schedule(g, 0, n)),
                f = dfs_finish_scheduleK(g, u + 1, n - u - 1); B = unit */;
      /*@ Assert
          exists vis1_m_ fin_m_ timer_,
            safeExec(pre_dfs1_sequence(g, radj_col_l, radj_row_l, vis1_m_, fin_m_, timer_),
                     dfs_finish_schedule(g, u + 1, n - u - 1),
                     result_state(pre_dfs1_sequence_initial(g, radj_col_l, radj_row_l, vis1_zero, fin_l0, n),
                                  dfs_finish_schedule(g, 0, n))) &&
            adj_verts(g) == n &&
            n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) &&
            fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
            timer == timer_ &&
            Zlength(sid_l) == n && Zlength(vis2_zero) == n &&
            (forall i, 0 <= i && i < n => Znth(i, vis2_zero, 0) == 0) &&
            1 <= n && n <= 2147483646 &&
            0 <= u && u < n &&
            phase1_sequence_refinement(g, radj_col_l, radj_row_l, vis1_m_, fin_m_,
                                       vis1_zero, fin_l0, timer_, n, u + 1) &&
            dfs1_finish_prefix_marked(fin_m_, vis1_m_, timer_, n) &&
            transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l, radj_row_l, n) &&
            dfs1_sequence_state_ready(g, radj_col_l, radj_row_l, vis1_m_, fin_m_, timer_) &&
            csr2_faithful(g, fadj_col_l, fadj_row_l) && AdjGraphValid(g) &&
            csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
            csr_lo(0, fadj_row_l) == 0 &&
            IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
            IntArray::full(fadj_row, n + 1, fadj_row_l) *
            IntArray::full(sid, n, sid_l) *
            IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
            IntArray::full(radj_row, n + 1, radj_row_l) *
            IntArray::full(pos, n, pos_l) *
            IntArray::full(vis1, n, vis1_m_) *
            IntArray::full(fin, n, fin_m_) *
            IntArray::full(vis2, n, vis2_zero)
      */
      /*@ Given vis1_m_ fin_m_ timer_ */
    }
  }

  /*@ Assert
      exists vis1_m fin_m radj_col_l radj_row_l pos_l,
        phase1_sequence_refinement(g, radj_col_l, radj_row_l, vis1_m, fin_m,
                                   vis1_zero, fin_l0, timer, n, n) &&
        dfs1_finish_prefix_marked(fin_m, vis1_m, timer, n) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483646 &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        Zlength(sid_l) == n && Zlength(vis2_zero) == n &&
        (forall i, 0 <= i && i < n => Znth(i, vis2_zero, 0) == 0) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(vis2, n, vis2_zero) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m)
  */

  /* Reuse pos, which transpose no longer needs, as the decreasing
     finish-time traversal order required by phase 2. */
  /*@ Inv Assert
      exists fin_m order_l vis1_m vis2_m sid_m timer_m radj_col_l radj_row_l,
        n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) && m == m &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483646 && 0 <= i && i <= n &&
        timer == timer_m &&
        Zlength(fin_m) == n && Zlength(order_l) == n &&
        Zlength(vis1_m) == n && Zlength(vis2_m) == n && Zlength(sid_m) == n &&
        (forall (u0: Z), (0 <= u0 && u0 < n) => Znth(u0, vis2_m, 0) == 0) &&
        (forall (u: Z), (0 <= u && u < i) => Znth(u, order_l, 0) == Znth(n - 1 - u, fin_m, 0)) &&
        phase1_sequence_refinement(g, radj_col_l, radj_row_l, vis1_m, fin_m,
                                   vis1_zero, fin_l0, timer_m, n, n) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, order_l) *
        IntArray::full(vis1, n, vis1_m)
  */
  for (int i = 0; i < n; i++) {
    pos[i] = fin[n - 1 - i];
  }

  /* step B (phase 2): sweep the sorted order; for each unvisited2 root,
     run dfs2(root, root, ...) to label its whole SCC. */
  /*@ Inv Assert
      exists fin_m order_l vis1_m vis2_m sid_m timer_m radj_col_l radj_row_l,
        n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) && m == m &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483646 && 0 <= k && k <= n &&
        timer == timer_m &&
        phase2_sequence_residual_refinement(g, fin_m, order_l, vis1_m, vis2_m, sid_m,
                                            timer_m, n, k) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m) &&
        (k == n =>
          (forall (u: Z), (0 <= u && u < n) =>
            (forall (v: Z), (0 <= v && v < n) =>
              ((Znth(u, sid_m, 0) == Znth(v, sid_m, 0) => mutually_reachable(g, u, v))
               && (mutually_reachable(g, u, v) => Znth(u, sid_m, 0) == Znth(v, sid_m, 0)))))) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, order_l) *
        IntArray::full(vis1, n, vis1_m)
  */
  for (int k = 0; k < n; k++) {
    /*@ Given fin_m order_l vis1_m vis2_m sid_m timer_m radj_col_l radj_row_l */
    int root = pos[k];
    /*@ Assert
        n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) && m == m &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483646 && 0 <= k && k < n &&
        0 <= root && root < n && root == Znth(k, order_l, 0) && timer == timer_m &&
        phase2_sequence_residual_refinement(g, fin_m, order_l, vis1_m, vis2_m, sid_m,
                                            timer_m, n, k) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        AdjGraphValid(g) && adj_verts(g) == n &&
        csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
        csr_lo(0, fadj_row_l) == 0 &&
        csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, order_l) *
        IntArray::full(vis1, n, vis1_m)
    */
    if (vis2[root] == 0) {
      /* Pre-set sid[root] = root.  dfs2 itself performs the visited2 write;
         keeping root unvisited at the call boundary matches the abstract
         Kosaraju phase-2 theorem for a fresh SCC round. */
      /* pre-mark: sid[root] = root.  dfs2 reads sid[root] and labels
         every vertex in root's SCC with sid[root]; setting sid[root]=root
         BEFORE the call makes the SCC representative equal to root itself
         (standard Kosaraju structure).  Same write-before pattern. */
      sid[root] = root;
      /* dfs2 pre-call Assert: expose the POST-write sid state while keeping
         vis2[root] == 0.  phase2_spec is the top-level phase-2 entry for
         dfs2(root, root, ...). */
      /*@ Assert
          exists sid_m1,
            csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m1) &&
            csr2_faithful(g, fadj_col_l, fadj_row_l) &&
            AdjGraphValid(g) && adj_verts(g) == n &&
            csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
            csr_lo(0, fadj_row_l) == 0 &&
            n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) && m == m &&
            fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre && timer == timer_m &&
            1 <= n && n <= 2147483646 && 0 <= k && k < n &&
            0 <= root && root < n && root == Znth(k, order_l, 0) &&
            Znth(root, vis2_m, 0) == 0 &&
            Znth(root, sid_m1, 0) == root &&
            sid_m1 == replace_Znth(root, root, sid_m) &&
            phase2_sequence_residual_refinement(g, fin_m, order_l, vis1_m, vis2_m, sid_m,
                                                timer_m, n, k) &&
            IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
            IntArray::full(fadj_row, n + 1, fadj_row_l) *
            IntArray::full(vis2, n, vis2_m) *
            IntArray::full(sid, n, sid_m1) *
            IntArray::full(fin, n, fin_m) *
            IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
            IntArray::full(radj_row, n + 1, radj_row_l) *
            IntArray::full(pos, n, order_l) *
            IntArray::full(vis1, n, vis1_m)
      */
      /*@ Given sid_m1 */
      dfs2(root, root, n, fadj_col, fadj_row, vis2, sid)
          /*@ where(phase2_spec)
                g = g,
                fadj_col_l = fadj_col_l, fadj_row_l = fadj_row_l,
                vis1_l = vis1_m, vis2_l = vis2_m,
                sid_before_l = sid_m, sid_l = sid_m1,
                fin_l = fin_m, order_l = order_l,
                timer_v = timer_m, k = k */;
      /* post-call Assert: capture phase2_spec's high-level and SCC facts. */
      /*@ Assert
          exists vis2_m_ sid_m_,
            dfs2_high_level_post(g, fadj_col_l, fadj_row_l,
                                    vis2_m, sid_m1, vis2_m_, sid_m_,
                                    root, root, n) &&
            dfs2_phase2_post(g, n, vis2_m, sid_m1, vis2_m_, sid_m_, root) &&
            csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m_, sid_m_) &&
            csr2_faithful(g, fadj_col_l, fadj_row_l) &&
            AdjGraphValid(g) && adj_verts(g) == n &&
            csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
            csr_lo(0, fadj_row_l) == 0 &&
            n == n@pre && m == m_of(fadj_row_l) && m == m_of(radj_row_l) && m == m &&
            fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre && timer == timer_m &&
            1 <= n && n <= 2147483646 && 0 <= k && k < n &&
            0 <= root && root < n && root == Znth(k, order_l, 0) &&
            Znth(root, vis2_m, 0) == 0 &&
            sid_m1 == replace_Znth(root, root, sid_m) &&
            phase2_sequence_residual_refinement(g, fin_m, order_l, vis1_m,
                                                vis2_m_, sid_m_, timer_m, n, k + 1) &&
            IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
            IntArray::full(fadj_row, n + 1, fadj_row_l) *
            IntArray::full(vis2, n, vis2_m_) *
            IntArray::full(sid, n, sid_m_) *
            IntArray::full(fin, n, fin_m) *
            IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
            IntArray::full(radj_row, n + 1, radj_row_l) *
            IntArray::full(pos, n, order_l) *
            IntArray::full(vis1, n, vis1_m)
      */
      /*@ Given vis2_m_ sid_m_ */
    }
  }

  /* post-phase-2: re-expose all working arrays with their lengths in the
     form free_int_array expects (radj_col length = m, others length n). */
  /*@ Assert
      exists sid_m vis2_m fin_m order_l vis1_m timer_m radj_col_l radj_row_l,
        1 <= n && n <= 2147483646 &&
        n == n@pre && timer == timer_m &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        m == m_of(fadj_row_l) && m == m_of(radj_row_l) && m == m &&
        (forall (u: Z), (0 <= u && u < n) =>
          (forall (v: Z), (0 <= v && v < n) =>
            ((Znth(u, sid_m, 0) == Znth(v, sid_m, 0) => mutually_reachable(g, u, v))
             && (mutually_reachable(g, u, v) => Znth(u, sid_m, 0) == Znth(v, sid_m, 0))))) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(radj_col, m, radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, order_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(vis2, n, vis2_m)
  */
  /*@ Given sid_m vis2_m fin_m order_l vis1_m timer_m radj_col_l radj_row_l */

  /* free all working arrays.  The final sid array carries the SCC
     labeling (sid_m final); the external Ensure's sid_l_ is sid_m. */
  free_int_array(radj_col) /*@ where n = m, l = radj_col_l */;
  free_int_array(radj_row) /*@ where n = n + 1, l = radj_row_l */;
  free_int_array(pos)      /*@ where n = n, l = order_l */;
  free_int_array(vis1)     /*@ where n = n, l = vis1_m */;
  free_int_array(fin)      /*@ where n = n, l = fin_m */;
  free_int_array(vis2)     /*@ where n = n, l = vis2_m */;
}
