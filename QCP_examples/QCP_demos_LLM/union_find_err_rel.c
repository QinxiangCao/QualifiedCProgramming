


#include "safeexecE_def.h"

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.union_find_err_rel_lib */
/*@ Import Coq Local Open Scope monad */
/*@ Extern Coq (uf_state :: *) */
/*@ Extern Coq
      (uf_state_of: Z -> list Z -> list Z -> uf_state)
      (uf_find: Z -> program uf_state Z)
      (uf_union: Z -> Z -> program uf_state unit)
      (uf_find_after_read: Z -> Z -> program uf_state Z)
      (uf_find_after_rec: Z -> Z -> program uf_state Z)
      (uf_union_after_find_x: Z -> Z -> program uf_state unit)
      (uf_union_after_find_y: Z -> Z -> program uf_state unit)
      (uf_union_after_rank_rx: Z -> Z -> Z -> program uf_state unit)
      (uf_union_after_rank_ry: Z -> Z -> Z -> Z -> program uf_state unit)
      (bump_rank: Z -> program uf_state unit)
      (equiv: {A} -> A -> A -> Prop)
      (uf_abstract: uf_state -> (Z -> Z) -> Prop)
      (valid: uf_state -> Z -> Prop)
      (merge: (Z -> Prop) -> (Z -> Z) -> Z -> Z -> (Z -> Z) -> Prop)
      (tt: unit)
*/

int uf_find_c(int n, int *parent, int *rank, int x)
  /*@ high_level_spec <= low_level_spec
      With ps rs (repr_of: Z -> Z)
      Require 0 <= n && n <= INT_MAX &&
              0 <= x && x < n &&
              uf_abstract(uf_state_of(n, ps, rs), repr_of) &&
              IntArray::full(parent, n, ps) *
              IntArray::full(rank, n, rs)
      Ensure exists ps1,
              __return == repr_of(x) &&
              uf_abstract(uf_state_of(n, ps1, rs), repr_of) &&
              IntArray::full(parent, n, ps1) *
              IntArray::full(rank, n, rs)
   */
;

int uf_find_c(int n, int *parent, int *rank, int x)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} ps rs (c: Z -> program uf_state B) X
      Require 0 <= n && n <= INT_MAX &&
              0 <= x && x < n &&
              safeExec(equiv(uf_state_of(n, ps, rs)), bind(uf_find(x), c), X) &&
              IntArray::full(parent, n, ps) *
              IntArray::full(rank, n, rs)
      Ensure exists ps1,
              0 <= __return && __return < n &&
              safeExec(equiv(uf_state_of(n, ps1, rs)), applyf(c, __return), X) &&
              IntArray::full(parent, n, ps1) *
              IntArray::full(rank, n, rs)
   */
;

int uf_find_c(int n, int *parent, int *rank, int x)
  /*@ low_level_spec
      With ps rs X
      Require 0 <= n && n <= INT_MAX &&
              0 <= x && x < n &&
              safeExec(equiv(uf_state_of(n, ps, rs)), uf_find(x), X) &&
              IntArray::full(parent, n, ps) *
              IntArray::full(rank, n, rs)
      Ensure exists ps1,
              0 <= __return && __return < n &&
              safeExec(equiv(uf_state_of(n, ps1, rs)), return(__return), X) &&
              IntArray::full(parent, n, ps1) *
              IntArray::full(rank, n, rs)
  */
{
  int p;
  p = parent[x];
  /*@ Assert
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre &&
      0 <= x && x < n &&
      p == Znth(x, ps, 0) &&
      safeExec(equiv(uf_state_of(n, ps, rs)), uf_find_after_read(x, p), X) &&
      IntArray::full(parent, n, ps) *
      IntArray::full(rank, n, rs)
   */
  if (p == x) {
    return x;
  }
  /*@ Assert
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre &&
      0 <= x && x < n &&
      0 <= p && p < n &&
      p == Znth(x, ps, 0) &&
      safeExec(equiv(uf_state_of(n, ps, rs)), bind(uf_find(p), uf_find_after_rec(x)), X) &&
      IntArray::full(parent, n, ps) *
      IntArray::full(rank, n, rs)
   */
  int r;
  r = uf_find_c(n, parent, rank, p) /*@ where(low_level_spec_aux) ps = ps, rs = rs, c = uf_find_after_rec(x), X = X; B = Z */;
  /*@ Assert
      exists ps1,
      0 <= n@pre && n@pre <= INT_MAX &&
	      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre &&
	      0 <= x && x < n &&
	      0 <= r && r < n &&
	      p == Znth(x, ps, 0) &&
      safeExec(equiv(uf_state_of(n, ps1, rs)), applyf(uf_find_after_rec(x), r), X) &&
      IntArray::full(parent, n, ps1) *
      IntArray::full(rank, n, rs)
   */
  parent[x] = r;
  /*@ Assert
      exists ps1,
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre &&
      p == Znth(x, ps, 0) &&
      0 <= r && r < n &&
      safeExec(equiv(uf_state_of(n, replace_Znth(x, r, ps1), rs)), return(r), X) &&
      IntArray::full(parent, n, replace_Znth(x, r, ps1)) *
      IntArray::full(rank, n, rs)
   */
  return r;
}

void uf_union_c(int n, int *parent, int *rank, int x, int y)
  /*@ high_level_spec <= low_level_spec
      With ps rs (repr_of: Z -> Z)
      Require 0 <= n && n <= INT_MAX &&
              0 <= x && x < n &&
              0 <= y && y < n &&
              uf_abstract(uf_state_of(n, ps, rs), repr_of) &&
              IntArray::full(parent, n, ps) *
              IntArray::full(rank, n, rs)
      Ensure exists ps1 rs1 (repr_of1 : Z -> Z),
              uf_abstract(uf_state_of(n, ps1, rs1), repr_of1) &&
              merge(valid(uf_state_of(n, ps1, rs1)), repr_of, x, y, repr_of1) &&
              IntArray::full(parent, n, ps1) *
              IntArray::full(rank, n, rs1)
   */
;

void uf_union_c(int n, int *parent, int *rank, int x, int y)
  /*@ low_level_spec
      With ps rs X
      Require 0 <= n && n <= INT_MAX &&
              0 <= x && x < n &&
              0 <= y && y < n &&
              safeExec(equiv(uf_state_of(n, ps, rs)), uf_union(x, y), X) &&
              IntArray::full(parent, n, ps) *
              IntArray::full(rank, n, rs)
      Ensure exists ps1 rs1,
              safeExec(equiv(uf_state_of(n, ps1, rs1)), return(tt), X) &&
              IntArray::full(parent, n, ps1) *
              IntArray::full(rank, n, rs1)
  */
{
  int rx;
  /*@ Assert
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
      0 <= x && x < n &&
      0 <= y && y < n &&
      safeExec(equiv(uf_state_of(n, ps, rs)), bind(uf_find(x), uf_union_after_find_x(y)), X) &&
      has_permission(&rx) *
      IntArray::full(parent, n, ps) *
      IntArray::full(rank, n, rs)
   */
  rx = uf_find_c(n, parent, rank, x) /*@ where(low_level_spec_aux) ps = ps, rs = rs, c = uf_union_after_find_x(y), X = X; B = unit */;
  /*@ Assert
      exists ps1 rs1,
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
      0 <= rx && rx < n &&
      0 <= y && y < n &&
      safeExec(equiv(uf_state_of(n, ps1, rs1)), applyf(uf_union_after_find_x(y), rx), X) &&
      IntArray::full(parent, n, ps1) *
      IntArray::full(rank, n, rs1)
   */
  int ry;
  ry = uf_find_c(n, parent, rank, y) /*@ where(low_level_spec_aux) c = uf_union_after_find_y(rx), X = X; B = unit */;
  /*@ Assert
      exists ps2 rs2,
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
      0 <= rx && rx < n &&
      0 <= ry && ry < n &&
      safeExec(equiv(uf_state_of(n, ps2, rs2)), applyf(uf_union_after_find_y(rx), ry), X) &&
      IntArray::full(parent, n, ps2) *
      IntArray::full(rank, n, rs2)
   */
  if (rx == ry) {
    /*@ Assert
        exists ps2 rs2,
        parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
        0 <= rx && rx < n &&
        ry == rx &&
        safeExec(equiv(uf_state_of(n, ps2, rs2)), return(tt), X) &&
        IntArray::full(parent, n, ps2) *
        IntArray::full(rank, n, rs2)
     */
    return;
  }

  int rx_rank;
  rx_rank = rank[rx];
  /*@ Assert
      exists ps2 rs2,
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
      0 <= rx && rx < n &&
      0 <= ry && ry < n &&
      rx != ry &&
      rx_rank == Znth(rx, rs2, 0) &&
      safeExec(equiv(uf_state_of(n, ps2, rs2)), uf_union_after_rank_rx(rx, ry, rx_rank), X) &&
      IntArray::full(parent, n, ps2) *
      IntArray::full(rank, n, rs2)
   */
  int ry_rank;
  ry_rank = rank[ry];
  /*@ Assert
      exists ps2 rs2,
      0 <= n@pre && n@pre <= INT_MAX &&
      parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
      0 <= rx && rx < n &&
      0 <= ry && ry < n &&
      rx != ry &&
      rx_rank == Znth(rx, rs2, 0) &&
      ry_rank == Znth(ry, rs2, 0) &&
      safeExec(equiv(uf_state_of(n, ps2, rs2)), uf_union_after_rank_ry(rx, ry, rx_rank, ry_rank), X) &&
      IntArray::full(parent, n, ps2) *
      IntArray::full(rank, n, rs2)
   */
  if (ry_rank < rx_rank) {
    parent[ry] = rx;
    /*@ Assert
        exists ps2 rs2,
        parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
        0 <= rx && rx < n &&
        0 <= ry && ry < n &&
        rx != ry &&
        ry_rank < rx_rank &&
        safeExec(equiv(uf_state_of(n, replace_Znth(ry, rx, ps2), rs2)), return(tt), X) &&
        IntArray::full(parent, n, replace_Znth(ry, rx, ps2)) *
        IntArray::full(rank, n, rs2)
     */
  } else {
    if (rx_rank < ry_rank) {
      parent[rx] = ry;
      /*@ Assert
          exists ps2 rs2,
          parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
          0 <= rx && rx < n &&
          0 <= ry && ry < n &&
          rx != ry &&
          rx_rank < ry_rank &&
          safeExec(equiv(uf_state_of(n, replace_Znth(rx, ry, ps2), rs2)), return(tt), X) &&
          IntArray::full(parent, n, replace_Znth(rx, ry, ps2)) *
          IntArray::full(rank, n, rs2)
       */
    } else {
      parent[rx] = ry;
      /*@ Assert
          exists ps2 rs2,
          parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
          0 <= rx && rx < n &&
          0 <= ry && ry < n &&
          rx != ry &&
          rx_rank == ry_rank &&
          ry_rank == Znth(ry, rs2, 0) &&
          ry_rank + 1 <= INT_MAX &&
          safeExec(equiv(uf_state_of(n, replace_Znth(rx, ry, ps2), rs2)), bump_rank(ry), X) &&
          IntArray::full(parent, n, replace_Znth(rx, ry, ps2)) *
          IntArray::full(rank, n, rs2)
       */
      rank[ry] = ry_rank + 1;
      /*@ Assert
          exists ps2 rs2,
          parent == parent@pre && rank == rank@pre && n == n@pre && x == x@pre && y == y@pre &&
          0 <= rx && rx < n &&
          0 <= ry && ry < n &&
          rx != ry &&
          rx_rank == ry_rank &&
          safeExec(equiv(uf_state_of(n, replace_Znth(rx, ry, ps2), replace_Znth(ry, ry_rank + 1, rs2))), return(tt), X) &&
          IntArray::full(parent, n, replace_Znth(rx, ry, ps2)) *
          IntArray::full(rank, n, replace_Znth(ry, ry_rank + 1, rs2))
       */
    }
  }
}
