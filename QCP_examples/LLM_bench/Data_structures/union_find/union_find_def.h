#ifndef UNION_FIND_DEF_H
#define UNION_FIND_DEF_H

#include "verification_stdlib.h"

/*
 * Public Union-Find interface, designed as an encapsulated ADT.
 *
 * Clients can name "struct union_find *", but they cannot see the fields.
 * The only representation predicate exposed to clients is UF(uf, n, repr_of).
 * Concrete arrays, logical lists, ranks, and implementation-side predicates
 * are private to the implementation file.
 *
 * The intended implementation uses full path compression on each find path
 * and union by rank. Rank is a maintained upper bound used for balancing; it
 * is not the current depth after compression and not the component size.
 */

struct union_find;

/*@ Extern Coq
      (uf_initial : Z -> (Z -> Z) -> Prop)
      (uf_merge : Z -> (Z -> Z) -> Z -> Z -> (Z -> Z) -> Prop)
      (uf_same_class : (Z -> Z) -> Z -> Z -> Prop)
      (uf_different_class : (Z -> Z) -> Z -> Z -> Prop)
      (UF : Z -> Z -> (Z -> Z) -> Assertion)
*/

struct union_find *uf_create(int n)
/*@ Require
      0 < n && n <= INT_MAX && emp
    Ensure exists repr_of,
      __return != 0 &&
      uf_initial(n, repr_of) &&
      UF(__return, n, repr_of)
 */
;

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
;

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
;

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
;

void uf_free(struct union_find *uf)
/*@ With n (repr_of : Z -> Z)
    Require UF(uf, n, repr_of)
    Ensure emp
 */
;

#endif
