/*
 * Codeforces 1316/E - Team Building  (rating 2300, BITMASK DP)
 *
 * Sort people by audience strength descending and sweep.  With i people seen
 * and a set mask of positions already filled, exactly i - |mask| of them were
 * audience candidates, so the audience is always the strongest available
 * people: dp[i][mask] extends by making person i+1 audience (while a seat is
 * free), a player in any empty position, or by skipping them.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P080-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P080_1316E_team_building_lib */
/*@ Extern Coq
      (Pre : Z -> list Z -> list(list Z) -> Prop)
      (Spec : Z -> list Z -> list(list Z) -> Z -> Prop)
      (concat : list(list Z) -> list Z)
*/
/* QCP_INSERT_END:shard09-P080-solver-support */

/*@ Extern Coq
      (BitCount : Z -> Z -> Prop)
      (PeoplePermutation : list Z -> list Z -> list Z -> list Z -> Prop)
      (PeopleHeapParentsFrom : list Z -> Z -> Z -> Prop)
      (PeopleHeapOrderedExceptAt : list Z -> Z -> Z -> Z -> Prop)
      (increasing : list Z -> Prop)
*/

/*@ Extern Coq
      (BitCountProgress : Z -> Z -> Z -> Prop)
      (PeopleSiftProgress : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (PeopleSelectedLargerChild : list Z -> Z -> Z -> Z -> Prop)
      (PeopleHeapBuildState : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (PeopleHeapSortState : list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (SortedPeopleState : list Z -> list Z -> list Z -> list Z -> Prop)
      (TeamNegInf : Z)
      (AllTeamNegInf : list Z -> Prop)
      (TeamDPTable : list Z -> list(list Z) -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (TeamNextRowProgress : list Z -> list Z -> list(list Z) -> Z -> Z -> Z -> list Z -> list Z -> Z -> Prop)
      (TeamRoleUpdateProgress : list Z -> list Z -> list(list Z) -> Z -> Z -> Z -> list Z -> list Z -> Z -> Z -> Prop)
      (TeamCopyPrefix : list Z -> list Z -> Z -> Prop)
*/

/*@ Extern Coq
      (BoundedTeamDPTable : list Z -> list(list Z) -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (BoundedTeamNextRowProgress : list Z -> list Z -> list(list Z) -> Z -> Z -> Z -> list Z -> list Z -> Z -> Prop)
      (BoundedTeamRoleUpdateProgress : list Z -> list Z -> list(list Z) -> Z -> Z -> Z -> list Z -> list Z -> Z -> Z -> Prop)
      (BoundedTeamCopyPrefix : list Z -> list Z -> Z -> Prop)
*/


/* popcount: number of 1-bits in v.  Replaces the compiler builtin, which has no
 * body.  p <= 7, so v < 128 here. */
static int popcount(unsigned int v)
/*@ Require
      0 <= v && v < 128 && emp
    Ensure
      BitCount(v@pre, __return) && 0 <= __return && __return <= 7 && emp
*/
{
    int c = 0;
    /*@ Inv Assert
          0 <= v@pre && v@pre < 128 &&
          0 <= v && v < 128 &&
          0 <= c && c <= 7 &&
          BitCountProgress(v@pre, v, c) && emp
    */
    while (v) {
        c = c + (int)(v & 1u);
        v >>= 1;
    }
    return c;
}

static void sift_people(long long *audience, int *order, int root, int hi)
/*@ With (audience_values order_values : list Z) (n : Z)
    Require
      2 <= n && n <= 100000 &&
      Zlength(audience_values) == n && Zlength(order_values) == n &&
      0 <= root && root <= hi && hi < n &&
      PeopleHeapOrderedExceptAt(audience_values, root, hi, root) &&
      Int64Array::full(audience, n, audience_values) *
      IntArray::full(order, n, order_values)
    Ensure
      exists (audience_after : list Z) (order_after : list Z),
        Zlength(audience_after) == n && Zlength(order_after) == n &&
        PeoplePermutation(audience_values, order_values,
                          audience_after, order_after) &&
        PeopleHeapParentsFrom(audience_after, root@pre, hi) &&
        sublist(hi + 1, n, audience_after) ==
          sublist(hi + 1, n, audience_values) &&
        sublist(hi + 1, n, order_after) ==
          sublist(hi + 1, n, order_values) &&
        Int64Array::full(audience, n, audience_after) *
        IntArray::full(order, n, order_after)
*/
{
    /*@ Inv Assert
          exists (audience_now : list Z) (order_now : list Z),
            audience == audience@pre && order == order@pre && hi == hi@pre &&
            2 <= n && n <= 100000 &&
            Zlength(audience_values) == n && Zlength(order_values) == n &&
            Zlength(audience_now) == n && Zlength(order_now) == n &&
            0 <= root@pre && root@pre <= root && root <= hi && hi < n &&
            0 <= 2 * root + 1 && 2 * root + 1 <= INT_MAX &&
            PeopleSiftProgress(audience_values, order_values,
                               audience_now, order_now,
                               root@pre, root, hi, n) &&
            Int64Array::full(audience, n, audience_now) *
            IntArray::full(order, n, order_now)
    */
    while (2 * root + 1 <= hi) {
        int child = 2 * root + 1;
        if (child + 1 <= hi && audience[child] < audience[child + 1])
            child++;
        /*@ Assert
              exists (audience_now : list Z) (order_now : list Z),
                audience == audience@pre && order == order@pre && hi == hi@pre &&
                2 <= n && n <= 100000 &&
                Zlength(audience_values) == n && Zlength(order_values) == n &&
                Zlength(audience_now) == n && Zlength(order_now) == n &&
                0 <= root@pre && root@pre <= root && root <= hi && hi < n &&
                0 <= child && child <= hi &&
                PeopleSiftProgress(audience_values, order_values,
                                   audience_now, order_now,
                                   root@pre, root, hi, n) &&
                PeopleSelectedLargerChild(audience_now, root, hi, child) &&
                Int64Array::full(audience, n, audience_now) *
                IntArray::full(order, n, order_now)
        */
        if (audience[root] >= audience[child])
            return;
        long long t = audience[root]; audience[root] = audience[child];
        audience[child] = t;
        int q = order[root]; order[root] = order[child]; order[child] = q;
        /*@ Assert
              exists (audience_now : list Z) (order_now : list Z),
                audience == audience@pre && order == order@pre && hi == hi@pre &&
                2 <= n && n <= 100000 &&
                Zlength(audience_values) == n && Zlength(order_values) == n &&
                Zlength(audience_now) == n && Zlength(order_now) == n &&
                0 <= root@pre && root@pre <= root && root < child &&
                child <= hi && hi < n &&
                PeopleSiftProgress(audience_values, order_values,
                                   audience_now, order_now,
                                   root@pre, child, hi, n) &&
                Int64Array::full(audience, n, audience_now) *
                IntArray::full(order, n, order_now) *
                has_permission(&t) * has_permission(&q)
        */
        root = child;
    }
}

static void sort_people(long long *audience, int *order, int n)
/*@ With (audience_values order_values : list Z)
    Require
      2 <= n && n <= 100000 &&
      Zlength(audience_values) == n && Zlength(order_values) == n &&
      Int64Array::full(audience, n, audience_values) *
      IntArray::full(order, n, order_values)
    Ensure
      exists (audience_after : list Z) (order_after : list Z),
        Zlength(audience_after) == n && Zlength(order_after) == n &&
        PeoplePermutation(audience_values, order_values,
                          audience_after, order_after) &&
        increasing(audience_after) &&
        Int64Array::full(audience, n, audience_after) *
        IntArray::full(order, n, order_after)
*/
{
    /*@ Inv Assert
          exists (audience_now : list Z) (order_now : list Z),
            audience == audience@pre && order == order@pre && n == n@pre &&
            2 <= n && n <= 100000 &&
            Zlength(audience_values) == n && Zlength(order_values) == n &&
            Zlength(audience_now) == n && Zlength(order_now) == n &&
            -1 <= root && root <= n / 2 - 1 &&
            PeopleHeapBuildState(audience_values, order_values,
                                 audience_now, order_now, root, n) &&
            Int64Array::full(audience, n, audience_now) *
            IntArray::full(order, n, order_now)
    */
    for (int root = n / 2 - 1; root >= 0; root--)
    {
        /*@ Assert
              exists (audience_now : list Z) (order_now : list Z),
                audience == audience@pre && order == order@pre && n == n@pre &&
                2 <= n && n <= 100000 &&
                Zlength(audience_values) == n && Zlength(order_values) == n &&
                Zlength(audience_now) == n && Zlength(order_now) == n &&
                0 <= root && root <= n / 2 - 1 &&
                PeopleHeapBuildState(audience_values, order_values,
                                     audience_now, order_now, root, n) &&
                PeopleHeapOrderedExceptAt(audience_now, root, n - 1, root) &&
                Int64Array::full(audience, n, audience_now) *
                IntArray::full(order, n, order_now)
        */
        sift_people(audience, order, root, n - 1) /*@ where n = n */;
    }
    /*@ Inv Assert
          exists (audience_now : list Z) (order_now : list Z),
            audience == audience@pre && order == order@pre && n == n@pre &&
            2 <= n && n <= 100000 &&
            Zlength(audience_values) == n && Zlength(order_values) == n &&
            Zlength(audience_now) == n && Zlength(order_now) == n &&
            0 <= hi && hi <= n - 1 &&
            PeopleHeapSortState(audience_values, order_values,
                                audience_now, order_now, hi) &&
            Int64Array::full(audience, n, audience_now) *
            IntArray::full(order, n, order_now)
    */
    for (int hi = n - 1; hi > 0; hi--) {
        long long t = audience[0]; audience[0] = audience[hi];
        audience[hi] = t;
        int q = order[0]; order[0] = order[hi]; order[hi] = q;
        /*@ Assert
              exists (audience_now : list Z) (order_now : list Z),
                audience == audience@pre && order == order@pre && n == n@pre &&
                2 <= n && n <= 100000 &&
                Zlength(audience_values) == n && Zlength(order_values) == n &&
                Zlength(audience_now) == n && Zlength(order_now) == n &&
                1 <= hi && hi <= n - 1 &&
                PeoplePermutation(audience_values, order_values,
                                  audience_now, order_now) &&
                PeopleHeapOrderedExceptAt(audience_now, 0, hi - 1, 0) &&
                increasing(sublist(hi, n, audience_now)) &&
                (forall left right,
                   (0 <= left && left < hi && hi <= right && right < n) =>
                   audience_now[left] <= audience_now[right]) &&
                Int64Array::full(audience, n, audience_now) *
                IntArray::full(order, n, order_now) *
                has_permission(&t) * has_permission(&q)
        */
        sift_people(audience, order, 0, hi - 1) /*@ where n = n */;
    }
}

/* solver: maximum total strength.  s is row-major n x p. */
static long long solver(long long *audience, int *order,
                        const long long *s, int n, int p, int k,
                        long long *dp, long long *ndp)
/* QCP_INSERT_BEGIN:shard09-P080-normalized-solver-contract */
/*@ With (aud : list Z) (skill : list(list Z))
          (order_values : list Z)
    Require
      2 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (1 <= aud[i] && aud[i] <= 1000000000)) && 1 <= p && p <= 7 && 1 <= k && (forall idx, (0 <= idx && idx < n * p) => (1 <= concat(skill)[idx] && concat(skill)[idx] <= 1000000000)) && Pre(k, aud, skill) &&
      n == Zlength(aud) &&
      p == Zlength(skill[0]) &&
      Zlength(order_values) == n &&
      (forall i, (0 <= i && i < n) => order_values[i] == i) &&
      Int64Array::full(audience, n, aud) *
      IntArray::full(order, n, order_values) *
      Int64Array::full(s, n * p, concat(skill)) *
      Int64Array::full_shape(dp, 128) *
      Int64Array::full_shape(ndp, 128)
    Ensure
      Spec(k, aud, skill, __return) &&
      exists (aud_after : list Z) (order_after : list Z),
        Zlength(aud_after) == n && Zlength(order_after) == n &&
        Int64Array::full(audience, n, aud_after) *
        IntArray::full(order, n, order_after) *
        Int64Array::full(s, n * p, concat(skill)) *
        Int64Array::full_shape(dp, 128) *
        Int64Array::full_shape(ndp, 128)
*/
/* QCP_INSERT_END:shard09-P080-normalized-solver-contract */
{
    sort_people(audience, order, n)
        /*@ where audience_values = aud, order_values = order_values */;
    /*@ Assert
          exists (audience_sorted : list Z) (order_sorted : list Z),
            audience == audience@pre && order == order@pre && s == s@pre &&
            n == n@pre && p == p@pre && k == k@pre &&
            dp == dp@pre && ndp == ndp@pre &&
            2 <= n@pre && n@pre <= 100000 &&
            1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
            n@pre == Zlength(aud) && p@pre == Zlength(skill[0]) &&
            Zlength(order_values) == n@pre &&
            (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
            Zlength(audience_sorted) == n@pre &&
            Zlength(order_sorted) == n@pre &&
            Zlength(concat(skill)) == n@pre * p@pre &&
            Pre(k@pre, aud, skill) &&
            SortedPeopleState(aud, order_values,
                              audience_sorted, order_sorted) &&
            (forall q, (0 <= q && q < n@pre) =>
               (1 <= audience_sorted[q] &&
                audience_sorted[q] <= 1000000000)) &&
            (forall q, (0 <= q && q < n@pre) =>
               (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
            (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
            (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
               (1 <= concat(skill)[idx] &&
                concat(skill)[idx] <= 1000000000)) &&
            Int64Array::full(audience, n@pre, audience_sorted) *
            IntArray::full(order, n@pre, order_sorted) *
            Int64Array::full(s, n@pre * p@pre, concat(skill)) *
            Int64Array::full_shape(dp, 128) *
            Int64Array::full_shape(ndp, 128)
    */
    int full = 1 << p;
    /*@ Inv Assert
          exists (audience_sorted : list Z) (order_sorted : list Z)
                 (dp_values : list Z),
            audience == audience@pre && order == order@pre && s == s@pre &&
            n == n@pre && p == p@pre && k == k@pre &&
            dp == dp@pre && ndp == ndp@pre &&
            2 <= n@pre && n@pre <= 100000 &&
            1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
            n@pre == Zlength(aud) && p@pre == Zlength(skill[0]) &&
            Zlength(order_values) == n@pre &&
            Zlength(audience_sorted) == n@pre &&
            Zlength(order_sorted) == n@pre &&
            Zlength(concat(skill)) == n@pre * p@pre &&
            full == (1 << p@pre) && 2 <= full && full <= 128 &&
            0 <= m && m <= full && Zlength(dp_values) == 128 &&
            Pre(k@pre, aud, skill) &&
            SortedPeopleState(aud, order_values,
                              audience_sorted, order_sorted) &&
            AllTeamNegInf(sublist(0, m, dp_values)) &&
            (forall q, (0 <= q && q < n@pre) =>
               (1 <= audience_sorted[q] &&
                audience_sorted[q] <= 1000000000)) &&
            (forall q, (0 <= q && q < n@pre) =>
               (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
            (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
            (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
               (1 <= concat(skill)[idx] &&
                concat(skill)[idx] <= 1000000000)) &&
            Int64Array::full(audience, n@pre, audience_sorted) *
            IntArray::full(order, n@pre, order_sorted) *
            Int64Array::full(s, n@pre * p@pre, concat(skill)) *
            Int64Array::full(dp, 128, dp_values) *
            Int64Array::full_shape(ndp, 128)
    */
    for (int m = 0; m < full; m++)
        dp[m] = (-(1LL << 60));
    dp[0] = 0;
    /*@ Assert
          exists (audience_sorted : list Z) (order_sorted : list Z)
                 (dp_values : list Z),
            audience == audience@pre && order == order@pre && s == s@pre &&
            n == n@pre && p == p@pre && k == k@pre &&
            dp == dp@pre && ndp == ndp@pre &&
            2 <= n@pre && n@pre <= 100000 &&
            1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
            n@pre == Zlength(aud) && p@pre == Zlength(skill[0]) &&
            Zlength(order_values) == n@pre &&
            Zlength(audience_sorted) == n@pre &&
            Zlength(order_sorted) == n@pre &&
            Zlength(concat(skill)) == n@pre * p@pre &&
            full == (1 << p@pre) && 2 <= full && full <= 128 &&
            Zlength(dp_values) == 128 &&
            Pre(k@pre, aud, skill) &&
            SortedPeopleState(aud, order_values,
                              audience_sorted, order_sorted) &&
            BoundedTeamDPTable(aud, skill, order_sorted,
                               p@pre, k@pre, 0, dp_values) &&
            (forall q, (0 <= q && q < n@pre) =>
               (1 <= audience_sorted[q] &&
                audience_sorted[q] <= 1000000000)) &&
            (forall q, (0 <= q && q < n@pre) =>
               (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
            (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
            (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
               (1 <= concat(skill)[idx] &&
                concat(skill)[idx] <= 1000000000)) &&
            (forall q, (0 <= q && q < full) =>
               (-1152921504606846976 <= dp_values[q] &&
                dp_values[q] <= 100000000000000)) &&
            Int64Array::full(audience, n@pre, audience_sorted) *
            IntArray::full(order, n@pre, order_sorted) *
            Int64Array::full(s, n@pre * p@pre, concat(skill)) *
            Int64Array::full(dp, 128, dp_values) *
            Int64Array::full_shape(ndp, 128)
    */
    /*@ Inv Assert
          exists (audience_sorted : list Z) (order_sorted : list Z)
                 (dp_values : list Z),
            audience == audience@pre && order == order@pre && s == s@pre &&
            n == n@pre && p == p@pre && k == k@pre &&
            dp == dp@pre && ndp == ndp@pre &&
            2 <= n@pre && n@pre <= 100000 &&
            1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
            n@pre == Zlength(aud) && p@pre == Zlength(skill[0]) &&
            Zlength(order_values) == n@pre &&
            Zlength(audience_sorted) == n@pre &&
            Zlength(order_sorted) == n@pre &&
            Zlength(concat(skill)) == n@pre * p@pre &&
            full == (1 << p@pre) && 2 <= full && full <= 128 &&
            0 <= i && i <= n@pre && Zlength(dp_values) == 128 &&
            Pre(k@pre, aud, skill) &&
            SortedPeopleState(aud, order_values,
                              audience_sorted, order_sorted) &&
            BoundedTeamDPTable(aud, skill, order_sorted,
                               p@pre, k@pre, i, dp_values) &&
            (forall q, (0 <= q && q < n@pre) =>
               (1 <= audience_sorted[q] &&
                audience_sorted[q] <= 1000000000)) &&
            (forall q, (0 <= q && q < n@pre) =>
               (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
            (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
            (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
               (1 <= concat(skill)[idx] &&
                concat(skill)[idx] <= 1000000000)) &&
            (forall q, (0 <= q && q < full) =>
               (-1152921504606846976 <= dp_values[q] &&
                dp_values[q] <= 100000000000000)) &&
            Int64Array::full(audience, n@pre, audience_sorted) *
            IntArray::full(order, n@pre, order_sorted) *
            Int64Array::full(s, n@pre * p@pre, concat(skill)) *
            Int64Array::full(dp, 128, dp_values) *
            Int64Array::full_shape(ndp, 128)
    */
    for (int i = 0; i < n; i++) {
        /*@ Inv Assert
              exists (aud_input : list Z)
                     (audience_sorted : list Z) (order_sorted : list Z)
                     (dp_values : list Z) (ndp_values : list Z),
                audience == audience@pre && order == order@pre && s == s@pre &&
                n == n@pre && p == p@pre && k == k@pre &&
                dp == dp@pre && ndp == ndp@pre &&
                2 <= n@pre && n@pre <= 100000 &&
                1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
                aud_input == aud &&
                n@pre == Zlength(aud_input) && p@pre == Zlength(skill[0]) &&
                Zlength(order_values) == n@pre &&
                Zlength(audience_sorted) == n@pre &&
                Zlength(order_sorted) == n@pre &&
                Zlength(concat(skill)) == n@pre * p@pre &&
                full == (1 << p@pre) && 2 <= full && full <= 128 &&
                0 <= i && i < n@pre && 0 <= m && m <= full &&
                Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
                Pre(k@pre, aud_input, skill) &&
                SortedPeopleState(aud_input, order_values,
                                  audience_sorted, order_sorted) &&
                BoundedTeamDPTable(aud_input, skill, order_sorted,
                                   p@pre, k@pre, i, dp_values) &&
                AllTeamNegInf(sublist(0, m, ndp_values)) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (1 <= audience_sorted[q] &&
                    audience_sorted[q] <= 1000000000)) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
                (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
                (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
                   (1 <= concat(skill)[idx] &&
                    concat(skill)[idx] <= 1000000000)) &&
                (forall q, (0 <= q && q < full) =>
                   (-1152921504606846976 <= dp_values[q] &&
                    dp_values[q] <= 100000000000000)) &&
                Int64Array::full(audience, n@pre, audience_sorted) *
                IntArray::full(order, n@pre, order_sorted) *
                Int64Array::full(s, n@pre * p@pre, concat(skill)) *
                Int64Array::full(dp, 128, dp_values) *
                Int64Array::full(ndp, 128, ndp_values)
        */
        for (int m = 0; m < full; m++)
            ndp[m] = (-(1LL << 60));
        int rank = n - 1 - i;             /* arrays are sorted ascending */
        int person = order[rank];
        /*@ Assert
              exists (aud_input : list Z)
                     (audience_sorted : list Z) (order_sorted : list Z)
                     (dp_values : list Z) (ndp_values : list Z),
                audience == audience@pre && order == order@pre && s == s@pre &&
                n == n@pre && p == p@pre && k == k@pre &&
                dp == dp@pre && ndp == ndp@pre &&
                2 <= n@pre && n@pre <= 100000 &&
                1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
                aud_input == aud &&
                n@pre == Zlength(aud_input) && p@pre == Zlength(skill[0]) &&
                Zlength(order_values) == n@pre &&
                Zlength(audience_sorted) == n@pre &&
                Zlength(order_sorted) == n@pre &&
                Zlength(concat(skill)) == n@pre * p@pre &&
                full == (1 << p@pre) && 2 <= full && full <= 128 &&
                0 <= i && i < n@pre &&
                rank == n@pre - 1 - i && 0 <= rank && rank < n@pre &&
                person == order_sorted[rank] &&
                0 <= person && person < n@pre &&
                Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
                Pre(k@pre, aud_input, skill) &&
                SortedPeopleState(aud_input, order_values,
                                  audience_sorted, order_sorted) &&
                BoundedTeamDPTable(aud_input, skill, order_sorted,
                                   p@pre, k@pre, i, dp_values) &&
                BoundedTeamNextRowProgress(audience_sorted, order_sorted, skill,
                                           p@pre, k@pre, i,
                                           dp_values, ndp_values, 0) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (1 <= audience_sorted[q] &&
                    audience_sorted[q] <= 1000000000)) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
                (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
                (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
                   (1 <= concat(skill)[idx] &&
                    concat(skill)[idx] <= 1000000000)) &&
                (forall q, (0 <= q && q < full) =>
                   (-1152921504606846976 <= dp_values[q] &&
                    dp_values[q] <= 100000000000000 &&
                    -1152921504606846976 <= ndp_values[q] &&
                    ndp_values[q] <= 100000000000000)) &&
                Int64Array::full(audience, n@pre, audience_sorted) *
                IntArray::full(order, n@pre, order_sorted) *
                Int64Array::full(s, n@pre * p@pre, concat(skill)) *
                Int64Array::full(dp, 128, dp_values) *
                Int64Array::full(ndp, 128, ndp_values)
        */
        /*@ Inv Assert
              exists (aud_input : list Z)
                     (audience_sorted : list Z) (order_sorted : list Z)
                     (dp_values : list Z) (ndp_values : list Z),
                audience == audience@pre && order == order@pre && s == s@pre &&
                n == n@pre && p == p@pre && k == k@pre &&
                dp == dp@pre && ndp == ndp@pre &&
                2 <= n@pre && n@pre <= 100000 &&
                1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
                aud_input == aud &&
                n@pre == Zlength(aud_input) && p@pre == Zlength(skill[0]) &&
                Zlength(order_values) == n@pre &&
                Zlength(audience_sorted) == n@pre &&
                Zlength(order_sorted) == n@pre &&
                Zlength(concat(skill)) == n@pre * p@pre &&
                full == (1 << p@pre) && 2 <= full && full <= 128 &&
                0 <= i && i < n@pre && 0 <= m && m <= full &&
                rank == n@pre - 1 - i && 0 <= rank && rank < n@pre &&
                person == order_sorted[rank] &&
                0 <= person && person < n@pre &&
                Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
                Pre(k@pre, aud_input, skill) &&
                SortedPeopleState(aud_input, order_values,
                                  audience_sorted, order_sorted) &&
                BoundedTeamDPTable(aud_input, skill, order_sorted,
                                   p@pre, k@pre, i, dp_values) &&
                BoundedTeamNextRowProgress(audience_sorted, order_sorted, skill,
                                           p@pre, k@pre, i,
                                           dp_values, ndp_values, m) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (1 <= audience_sorted[q] &&
                    audience_sorted[q] <= 1000000000)) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
                (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
                (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
                   (1 <= concat(skill)[idx] &&
                    concat(skill)[idx] <= 1000000000)) &&
                (forall q, (0 <= q && q < full) =>
                   (-1152921504606846976 <= dp_values[q] &&
                    dp_values[q] <= 100000000000000 &&
                    -1152921504606846976 <= ndp_values[q] &&
                    ndp_values[q] <= 100000000000000)) &&
                Int64Array::full(audience, n@pre, audience_sorted) *
                IntArray::full(order, n@pre, order_sorted) *
                Int64Array::full(s, n@pre * p@pre, concat(skill)) *
                Int64Array::full(dp, 128, dp_values) *
                Int64Array::full(ndp, 128, ndp_values)
        */
        for (int m = 0; m < full; m++) {
            /*@ Given aud_input */
            /*@ 0 <= m && m < 128 by local */
            if (dp[m] == (-(1LL << 60)))
                continue;
            int used = popcount((unsigned int)m);
            int aud = i - used;           /* audience members chosen so far */
            if (dp[m] > ndp[m])           /* skip this person */
                ndp[m] = dp[m];
            if (aud < k) {                /* seat them in the audience */
                long long v = dp[m] + audience[rank];
                if (v > ndp[m])
                    ndp[m] = v;
            }
            /*@ exists (audience_sorted : list Z) (order_sorted : list Z)
                         (dp_values : list Z) (ndp_values : list Z),
                    audience == audience@pre && order == order@pre && s == s@pre &&
                    n == n@pre && p == p@pre && k == k@pre &&
                    dp == dp@pre && ndp == ndp@pre &&
                    2 <= n@pre && n@pre <= 100000 &&
                    1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
                    full == (1 << p@pre) && 2 <= full && full <= 128 &&
                    0 <= i && i < n@pre && 0 <= m && m < full &&
                    rank == n@pre - 1 - i && 0 <= rank && rank < n@pre &&
                    person == order_sorted[rank] &&
                    0 <= person && person < n@pre &&
                    BitCount(m, used) && 0 <= used && used <= 7 &&
                    aud == i - used &&
                    dp_values[m] != -1152921504606846976 &&
                    n@pre == Zlength(aud_input) && p@pre == Zlength(skill[0]) &&
                    Zlength(order_values) == n@pre &&
                    Zlength(audience_sorted) == n@pre &&
                    Zlength(order_sorted) == n@pre &&
                    Zlength(concat(skill)) == n@pre * p@pre &&
                    Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
                    Pre(k@pre, aud_input, skill) &&
                    SortedPeopleState(aud_input, order_values,
                                      audience_sorted, order_sorted) &&
                    BoundedTeamDPTable(aud_input, skill, order_sorted,
                                       p@pre, k@pre, i, dp_values) &&
                    BoundedTeamRoleUpdateProgress(audience_sorted, order_sorted, skill,
                                                  p@pre, k@pre, i,
                                                  dp_values, ndp_values, m, 0) &&
                    (forall q, (0 <= q && q < n@pre) =>
                       (1 <= audience_sorted[q] &&
                        audience_sorted[q] <= 1000000000)) &&
                    (forall q, (0 <= q && q < n@pre) =>
                       (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
                    (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
                    (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
                       (1 <= concat(skill)[idx] &&
                        concat(skill)[idx] <= 1000000000)) &&
                    (forall q, (0 <= q && q < full) =>
                       (-1152921504606846976 <= dp_values[q] &&
                        dp_values[q] <= 100000000000000 &&
                        -1152921504606846976 <= ndp_values[q] &&
                        ndp_values[q] <= 100000000000000)) &&
                    Int64Array::full(audience, n@pre, audience_sorted) *
                    IntArray::full(order, n@pre, order_sorted) *
                    Int64Array::full(s, n@pre * p@pre, concat(skill)) *
                    Int64Array::full(dp, 128, dp_values) *
                    Int64Array::full(ndp, 128, ndp_values)
            */
            /*@ Inv
                  exists (audience_sorted : list Z) (order_sorted : list Z)
                         (dp_values : list Z) (ndp_values : list Z),
                    audience == audience@pre && order == order@pre && s == s@pre &&
                    n == n@pre && p == p@pre && k == k@pre &&
                    dp == dp@pre && ndp == ndp@pre &&
                    2 <= n@pre && n@pre <= 100000 &&
                    1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
                    full == (1 << p@pre) && 2 <= full && full <= 128 &&
                    0 <= i && i < n@pre && 0 <= m && m < full &&
                    0 <= j && j <= p@pre &&
                    rank == n@pre - 1 - i && 0 <= rank && rank < n@pre &&
                    person == order_sorted[rank] &&
                    0 <= person && person < n@pre &&
                    BitCount(m, used) && 0 <= used && used <= 7 &&
                    aud == i - used &&
                    dp_values[m] != -1152921504606846976 &&
                    n@pre == Zlength(aud_input) && p@pre == Zlength(skill[0]) &&
                    Zlength(order_values) == n@pre &&
                    Zlength(audience_sorted) == n@pre &&
                    Zlength(order_sorted) == n@pre &&
                    Zlength(concat(skill)) == n@pre * p@pre &&
                    Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
                    Pre(k@pre, aud_input, skill) &&
                    SortedPeopleState(aud_input, order_values,
                                      audience_sorted, order_sorted) &&
                    BoundedTeamDPTable(aud_input, skill, order_sorted,
                                       p@pre, k@pre, i, dp_values) &&
                    BoundedTeamRoleUpdateProgress(audience_sorted, order_sorted, skill,
                                                  p@pre, k@pre, i,
                                                  dp_values, ndp_values, m, j) &&
                    (forall q, (0 <= q && q < n@pre) =>
                       (1 <= audience_sorted[q] &&
                        audience_sorted[q] <= 1000000000)) &&
                    (forall q, (0 <= q && q < n@pre) =>
                       (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
                    (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
                    (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
                       (1 <= concat(skill)[idx] &&
                        concat(skill)[idx] <= 1000000000)) &&
                    (forall q, (0 <= q && q < full) =>
                       (-1152921504606846976 <= dp_values[q] &&
                        dp_values[q] <= 100000000000000 &&
                        -1152921504606846976 <= ndp_values[q] &&
                        ndp_values[q] <= 100000000000000)) &&
                    Int64Array::full(audience, n@pre, audience_sorted) *
                    IntArray::full(order, n@pre, order_sorted) *
                    Int64Array::full(s, n@pre * p@pre, concat(skill)) *
                    Int64Array::full(dp, 128, dp_values) *
                    Int64Array::full(ndp, 128, ndp_values)
            */
            for (int j = 0; j < p; j++)
                if (!(m & (1 << j))) {
                    /*@ 0 <= (long long)person * p + j &&
                        (long long)person * p + j < n@pre * p@pre by local */
                    long long v = dp[m] + s[(long long)person * p + j];
                    int nm = m | (1 << j);
                    /*@ 0 <= nm && nm < full by local */
                    if (v > ndp[nm])
                        ndp[nm] = v;
                }
        }
        /*@ Assert
              exists (audience_sorted : list Z) (order_sorted : list Z)
                     (dp_values : list Z) (ndp_values : list Z),
                audience == audience@pre && order == order@pre && s == s@pre &&
                n == n@pre && p == p@pre && k == k@pre &&
                dp == dp@pre && ndp == ndp@pre &&
                2 <= n@pre && n@pre <= 100000 &&
                1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
                full == (1 << p@pre) && 2 <= full && full <= 128 &&
                0 <= i && i < n@pre &&
                rank == n@pre - 1 - i && 0 <= rank && rank < n@pre &&
                person == order_sorted[rank] &&
                0 <= person && person < n@pre &&
                Zlength(audience_sorted) == n@pre &&
                Zlength(order_sorted) == n@pre &&
                n@pre == Zlength(aud) && p@pre == Zlength(skill[0]) &&
                Zlength(order_values) == n@pre &&
                Zlength(concat(skill)) == n@pre * p@pre &&
                Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
                Pre(k@pre, aud, skill) &&
                SortedPeopleState(aud, order_values,
                                  audience_sorted, order_sorted) &&
                BoundedTeamDPTable(aud, skill, order_sorted,
                                   p@pre, k@pre, i + 1, ndp_values) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (1 <= audience_sorted[q] &&
                    audience_sorted[q] <= 1000000000)) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
                (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
                (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
                   (1 <= concat(skill)[idx] &&
                    concat(skill)[idx] <= 1000000000)) &&
                (forall q, (0 <= q && q < full) =>
                   (-1152921504606846976 <= dp_values[q] &&
                    dp_values[q] <= 100000000000000 &&
                    -1152921504606846976 <= ndp_values[q] &&
                    ndp_values[q] <= 100000000000000)) &&
                Int64Array::full(audience, n@pre, audience_sorted) *
                IntArray::full(order, n@pre, order_sorted) *
                Int64Array::full(s, n@pre * p@pre, concat(skill)) *
                Int64Array::full(dp, 128, dp_values) *
                Int64Array::full(ndp, 128, ndp_values)
        */
        /*@ Inv Assert
              exists (audience_sorted : list Z) (order_sorted : list Z)
                     (dp_values : list Z) (ndp_values : list Z),
                audience == audience@pre && order == order@pre && s == s@pre &&
                n == n@pre && p == p@pre && k == k@pre &&
                dp == dp@pre && ndp == ndp@pre &&
                2 <= n@pre && n@pre <= 100000 &&
                1 <= p@pre && p@pre <= 7 && 1 <= k@pre &&
                full == (1 << p@pre) && 2 <= full && full <= 128 &&
                0 <= i && i < n@pre && 0 <= m && m <= full &&
                rank == n@pre - 1 - i && 0 <= rank && rank < n@pre &&
                person == order_sorted[rank] &&
                0 <= person && person < n@pre &&
                Zlength(audience_sorted) == n@pre &&
                Zlength(order_sorted) == n@pre &&
                n@pre == Zlength(aud) && p@pre == Zlength(skill[0]) &&
                Zlength(order_values) == n@pre &&
                Zlength(concat(skill)) == n@pre * p@pre &&
                Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
                Pre(k@pre, aud, skill) &&
                SortedPeopleState(aud, order_values,
                                  audience_sorted, order_sorted) &&
                BoundedTeamDPTable(aud, skill, order_sorted,
                                   p@pre, k@pre, i + 1, ndp_values) &&
                BoundedTeamCopyPrefix(ndp_values, dp_values, m) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (1 <= audience_sorted[q] &&
                    audience_sorted[q] <= 1000000000)) &&
                (forall q, (0 <= q && q < n@pre) =>
                   (0 <= order_sorted[q] && order_sorted[q] < n@pre)) &&
                (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
                (forall idx, (0 <= idx && idx < n@pre * p@pre) =>
                   (1 <= concat(skill)[idx] &&
                    concat(skill)[idx] <= 1000000000)) &&
                (forall q, (0 <= q && q < full) =>
                   (-1152921504606846976 <= dp_values[q] &&
                    dp_values[q] <= 100000000000000 &&
                    -1152921504606846976 <= ndp_values[q] &&
                    ndp_values[q] <= 100000000000000)) &&
                Int64Array::full(audience, n@pre, audience_sorted) *
                IntArray::full(order, n@pre, order_sorted) *
                Int64Array::full(s, n@pre * p@pre, concat(skill)) *
                Int64Array::full(dp, 128, dp_values) *
                Int64Array::full(ndp, 128, ndp_values)
        */
        for (int m = 0; m < full; m++)
            dp[m] = ndp[m];
    }
    /*@ Assert
          exists (audience_sorted : list Z) (order_sorted : list Z)
                 (dp_values : list Z) (ndp_values : list Z),
            audience == audience@pre && order == order@pre && s == s@pre &&
            n == n@pre && p == p@pre && k == k@pre &&
            dp == dp@pre && ndp == ndp@pre &&
            full == (1 << p@pre) && 2 <= full && full <= 128 &&
            Zlength(audience_sorted) == n@pre &&
            Zlength(order_sorted) == n@pre &&
            Zlength(dp_values) == 128 && Zlength(ndp_values) == 128 &&
            Pre(k@pre, aud, skill) &&
            SortedPeopleState(aud, order_values,
                              audience_sorted, order_sorted) &&
            BoundedTeamDPTable(aud, skill, order_sorted,
                               p@pre, k@pre, n@pre, dp_values) &&
            (forall q, (0 <= q && q < n@pre) => order_values[q] == q) &&
            Spec(k@pre, aud, skill, dp_values[full - 1]) &&
            Int64Array::full(audience, n@pre, audience_sorted) *
            IntArray::full(order, n@pre, order_sorted) *
            Int64Array::full(s, n@pre * p@pre, concat(skill)) *
            Int64Array::full(dp, 128, dp_values) *
            Int64Array::full(ndp, 128, ndp_values)
    */
    return dp[full - 1];
}

// int main(void)
// {
//     int n, p, k;
//     if (scanf("%d %d %d", &n, &p, &k) != 3)
//         return 0;
//     long long *audience = malloc(sizeof(long long) * n);
//     int *order = malloc(sizeof(int) * n);
//     for (int i = 0; i < n; i++) {
//         scanf("%lld", &audience[i]);
//         order[i] = i;
//     }
//     long long *s = malloc(sizeof(long long) * (size_t)n * p);
//     for (long long i = 0; i < (long long)n * p; i++)
//         scanf("%lld", &s[i]);
//     static long long dp[128], ndp[128];
//     printf("%lld\n", solver(audience, order, s, n, p, k, dp, ndp));
//     return 0;
// }
