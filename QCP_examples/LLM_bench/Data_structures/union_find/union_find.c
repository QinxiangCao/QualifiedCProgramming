#include "union_find_def.h"
#include "verification_list.h"
#include "int_array_def.h"

/*
 * Demonstration-only implementation sketch.
 *
 * This file is intentionally not wired into the build.  It shows the intended
 * struct boundary: clients include union_find_def.h and see only UF;
 * this implementation file opens UF into parent/rank arrays and ps/rs lists.
 *
 * Efficiency policy: uf_find_raw fully compresses the visited find path, and
 * uf_union_raw uses union by rank. Rank is neither recomputed tree depth nor
 * component size.
 */

struct union_find {
  int n;
  int *parent;
  int *rank;
};

/* Private implementation-side specification vocabulary. */
/*@ Extern Coq (Zrange : Z -> Z -> list Z) */
/*@ Extern Coq (uf_state :: *) */
/*@ Extern Coq
      (uf_state_of : Z -> list Z -> list Z -> uf_state)
      (uf_abstract : uf_state -> (Z -> Z) -> Prop)
      (uf_parent_indices_valid : Z -> list Z -> Prop)
      (uf_rank_values_valid : Z -> list Z -> Prop)
      (UF_raw :
        Z -> Z -> Z -> Z -> list Z -> list Z -> (Z -> Z) -> Assertion)
 */

static struct union_find *malloc_union_find()
/*@ Require emp
    Ensure
      __return != 0 &&
      has_permission(&(__return -> n)) *
      has_permission(&(__return -> parent)) *
      has_permission(&(__return -> rank))
 */
;

static int *malloc_int_array(int n)
/*@ Require n > 0 && emp
    Ensure IntArray::undef_full(__return, n)
 */
;

static void free_int_array(int *a)
/*@ With n l
    Require IntArray::full(a, n, l)
    Ensure emp
 */
;

static void free_union_find(struct union_find *uf)
/*@ Require
      has_permission(&(uf -> n)) *
      has_permission(&(uf -> parent)) *
      has_permission(&(uf -> rank))
    Ensure emp
 */
;

static int uf_find_raw(int n, int *parent, int *rank, int x)
/*@ With ps rs (repr_of : Z -> Z)
    Require
      0 <= n && n <= INT_MAX &&
      0 <= x && x < n &&
      uf_parent_indices_valid(n, ps) &&
      uf_rank_values_valid(n, rs) &&
      uf_abstract(uf_state_of(n, ps, rs), repr_of) &&
      IntArray::full(parent, n, ps) *
      IntArray::full(rank, n, rs)
    Ensure exists ps1,
      0 <= __return && __return < n &&
      __return == repr_of(x) &&
      uf_parent_indices_valid(n, ps1) &&
      uf_rank_values_valid(n, rs) &&
      uf_abstract(uf_state_of(n, ps1, rs), repr_of) &&
      IntArray::full(parent, n, ps1) *
      IntArray::full(rank, n, rs)
 */
{
  int p = parent[x];

  if (p == x) {
    return x;
  }

  int r = uf_find_raw(n, parent, rank, p);
  /* Each recursive caller rewires its vertex directly to the root. */
  parent[x] = r;
  return r;
}

static void uf_union_raw(int n, int *parent, int *rank, int x, int y)
/*@ With ps rs (repr_of : Z -> Z)
    Require
      0 <= n && n <= INT_MAX &&
      0 <= x && x < n &&
      0 <= y && y < n &&
      uf_parent_indices_valid(n, ps) &&
      uf_rank_values_valid(n, rs) &&
      uf_abstract(uf_state_of(n, ps, rs), repr_of) &&
      IntArray::full(parent, n, ps) *
      IntArray::full(rank, n, rs)
    Ensure exists ps1 rs1 (repr_of1 : Z -> Z),
      uf_parent_indices_valid(n, ps1) &&
      uf_rank_values_valid(n, rs1) &&
      uf_abstract(uf_state_of(n, ps1, rs1), repr_of1) &&
      uf_merge(n, repr_of, x, y, repr_of1) &&
      IntArray::full(parent, n, ps1) *
      IntArray::full(rank, n, rs1)
 */
{
  int rx = uf_find_raw(n, parent, rank, x);
  int ry = uf_find_raw(n, parent, rank, y);

  if (rx == ry) {
    return;
  }

  /* Union by rank: rank is a maintained height upper bound. */
  int rx_rank = rank[rx];
  int ry_rank = rank[ry];

  if (rx_rank < ry_rank) {
    parent[rx] = ry;
  } else if (rx_rank > ry_rank) {
    parent[ry] = rx;
  } else {
    parent[ry] = rx;
    rank[rx] = rx_rank + 1;
  }
}

struct union_find *uf_create(int n)
/*@ Require
      0 < n && n <= INT_MAX && emp
    Ensure exists repr_of,
      __return != 0 &&
      uf_initial(n, repr_of) &&
      UF(__return, n, repr_of)
 */
{
  struct union_find *uf = malloc_union_find();
  int *parent = malloc_int_array(n);
  int *rank = malloc_int_array(n);

  uf->n = n;
  uf->parent = parent;
  uf->rank = rank;

  int i = 0;
  /*@ Inv Assert
      0 <= i && i <= n &&
      IntArray::seg(parent, 0, i, Zrange(0, i)) *
      IntArray::undef_seg(parent, i, n) *
      IntArray::seg(rank, 0, i, repeat_Z(0, i)) *
      IntArray::undef_seg(rank, i, n)
   */
  while (i < n) {
    parent[i] = i;
    rank[i] = 0;
    i++;
  }

  /*
   * Close the concrete representation into the public UF predicate before
   * returning.  The caller never receives parent, rank, ps, or rs.
   */
  /*@ Assert exists ps rs repr_of,
      ps == Zrange(0, n) &&
      rs == repeat_Z(0, n) &&
      uf_initial(n, repr_of) &&
      UF_raw(uf, n, parent, rank, ps, rs, repr_of) &&
      UF(uf, n, repr_of)
   */
  return uf;
}

int uf_find(struct union_find *uf, int x)
/*@ With n (repr_of : Z -> Z)
    Require
      0 <= x && x < n &&
      UF(uf, n, repr_of)
    Ensure
      0 <= __return && __return < n &&
      __return == repr_of(x) &&
      UF(uf, n, repr_of)
 */
{
  /*@ Assert exists parent rank ps rs,
      UF_raw(uf, n, parent, rank, ps, rs, repr_of)
   */
  int n0 = uf->n;
  int *parent = uf->parent;
  int *rank = uf->rank;

  int r = uf_find_raw(n0, parent, rank, x);

  /*
   * Path compression changes the concrete parent list but preserves the
   * abstract partition, so the public UF predicate closes with repr_of again.
   */
  /*@ Assert exists ps1 rs,
      n0 == n &&
      r == repr_of(x) &&
      uf_abstract(uf_state_of(n, ps1, rs), repr_of) &&
      UF_raw(uf, n, parent, rank, ps1, rs, repr_of) &&
      UF(uf, n, repr_of)
   */
  return r;
}

void uf_union(struct union_find *uf, int x, int y)
/*@ With n (repr_of : Z -> Z)
    Require
      0 <= x && x < n &&
      0 <= y && y < n &&
      UF(uf, n, repr_of)
    Ensure exists repr_of1,
      uf_merge(n, repr_of, x, y, repr_of1) &&
      UF(uf, n, repr_of1)
 */
{
  /*@ Assert exists parent rank ps rs,
      UF_raw(uf, n, parent, rank, ps, rs, repr_of)
   */
  int n0 = uf->n;
  int *parent = uf->parent;
  int *rank = uf->rank;

  uf_union_raw(n0, parent, rank, x, y);

  /*@ Assert exists ps1 rs1 repr_of1,
      n0 == n &&
      uf_merge(n, repr_of, x, y, repr_of1) &&
      uf_abstract(uf_state_of(n, ps1, rs1), repr_of1) &&
      UF_raw(uf, n, parent, rank, ps1, rs1, repr_of1) &&
      UF(uf, n, repr_of1)
   */
}

int uf_connected(struct union_find *uf, int x, int y)
/*@ With n (repr_of : Z -> Z)
    Require
      0 <= x && x < n &&
      0 <= y && y < n &&
      UF(uf, n, repr_of)
    Ensure
      ((__return != 0 && uf_same_class(repr_of, x, y)) ||
       (__return == 0 && uf_different_class(repr_of, x, y))) &&
      UF(uf, n, repr_of)
 */
{
  int rx = uf_find(uf, x);
  int ry = uf_find(uf, y);
  return rx == ry;
}

void uf_free(struct union_find *uf)
/*@ With n (repr_of : Z -> Z)
    Require UF(uf, n, repr_of)
    Ensure emp
 */
{
  /*@ Assert exists parent rank ps rs,
      UF_raw(uf, n, parent, rank, ps, rs, repr_of)
   */
  int *parent = uf->parent;
  int *rank = uf->rank;

  free_int_array(parent);
  free_int_array(rank);
  free_union_find(uf);
}
