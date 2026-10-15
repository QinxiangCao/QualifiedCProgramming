/*
 * Codeforces 1569/D - Inconvenient Pairs  (rating 1900, SORTINGS)
 *
 * A person standing on a crossing is never inconvenient.  Otherwise the person
 * is stuck strictly between two parallel streets: two people trapped in the
 * same horizontal strip must detour unless they share the same x (and
 * symmetrically for vertical strips).  So per strip count all pairs and
 * subtract the pairs sharing a coordinate.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P063-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P063_1569D_inconvenient_pairs_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Pre : list Z -> list Z -> list(Z*Z) -> Prop)
      (Spec : list Z -> list Z -> list(Z*Z) -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P063-solver-support */

/*@ Import Coq Require Import AUXLib.MonotonicList */

/*@ Extern Coq
      (SiftChildrenBelowParentItems : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (ValueRunBoundary : list Z -> Z -> Prop)
      (RangeRunBoundary : list Z -> Z -> Z -> Z -> Prop)
      (ExtractionFrameItems : list Z -> list Z -> Z -> Prop)
      (ClassifiedCountsCorrect : list Z -> list Z -> list(Z*Z) -> Z ->
                                 list Z -> list Z -> list Z -> list Z -> Prop)
*/

/*@ Extern Coq
      (StripIndex : list Z -> Z -> Z -> Prop)
      (mono_inc : list Z -> Prop)
      (ItemLe : (Z*Z) -> (Z*Z) -> Prop)
      (ItemLe4 : Z -> Z -> Z -> Z -> Prop)
      (ParallelPermutation : list Z -> list Z -> list Z -> list Z -> Prop)
      (ItemsIncreasing : list Z -> list Z -> Prop)
      (HeapParentsFromItems : list Z -> list Z -> Z -> Z -> Prop)
      (HeapOrderedExceptAtFromItems : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (SelectedLargerChildItems : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (HeapSortItemsState : list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (PairCountPrefix : list Z -> list Z -> Z -> Z -> Prop)
      (CountGroupPhase : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (SameValueRange : list Z -> Z -> Z -> Prop)
      (ClassifiedPrefix : list Z -> list Z -> list(Z*Z) -> Z ->
                          list Z -> list Z -> list Z -> list Z -> Prop)
      (ClassifiedPairCounts : list Z -> list Z -> list(Z*Z) ->
                              list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (StreetCoordinateBounds : list Z -> Prop)
      (PeopleCoordinateBounds : list(Z*Z) -> Prop)
*/

/* strip: index of the gap of the sorted street list that v falls into, or -1
 * if v is exactly on a street. */
static int strip(const int *s, int n, int v)
/*@ With (streets : list Z)
    Require
      2 <= n && n <= 200000 && Zlength(streets) == n &&
      mono_inc(streets) && streets[0] == 0 && streets[n - 1] == 1000000 &&
      0 <= v && v <= 1000000 && IntArray::full(s, n, streets)
    Ensure
      StripIndex(streets, v, __return) &&
      IntArray::full(s, n, streets)
*/
{
    int lo = 0, hi = n - 1;
    /*@ Inv Assert
        s == s@pre && n == n@pre && v == v@pre &&
        2 <= n && n <= 200000 && Zlength(streets) == n &&
        mono_inc(streets) && streets[0] == 0 && streets[n - 1] == 1000000 &&
        0 <= v && v <= 1000000 &&
        0 <= lo && lo <= hi && hi < n &&
        streets[lo] <= v &&
        (v == streets[hi] || hi == n - 1 || v < streets[hi + 1]) &&
        IntArray::full(s, n, streets)
    */
    while (lo < hi) {                     /* last street <= v */
        int mid = lo + (hi - lo + 1) / 2;
        /*@ 0 <= mid && mid < n by local */
        if (s[mid] <= v)
            lo = mid;
        else
            hi = mid - 1;
    }
    return s[lo] == v ? -1 : lo;
}

static int item_less(int grp1, int key1, int grp2, int key2)
/*@ Require emp
    Ensure
      ((__return != 0 && ItemLe4(grp1, key1, grp2, key2) &&
                         (grp1 != grp2 || key1 != key2)) ||
       (__return == 0 && ItemLe4(grp2, key2, grp1, key1))) && emp
*/
{
    return grp1 < grp2 || (grp1 == grp2 && key1 < key2);
}

static void sift_items(int *grp, int *key, int root, int upper)
/*@ With (groups keys : list Z) (n cap : Z)
    Require
      0 <= upper && upper < n && n <= cap && cap <= 300000 &&
      Zlength(groups) == n && Zlength(keys) == n &&
      0 <= root && root <= upper &&
      HeapOrderedExceptAtFromItems(groups, keys, root, upper, root) &&
      ExtractionFrameItems(groups, keys, upper + 1) &&
      IntArray::full(grp, n, groups) * IntArray::full(key, n, keys)
    Ensure
      exists groups_after keys_after,
        Zlength(groups_after) == n && Zlength(keys_after) == n &&
        ParallelPermutation(groups, keys, groups_after, keys_after) &&
        HeapParentsFromItems(groups_after, keys_after, root, upper) &&
        ExtractionFrameItems(groups_after, keys_after, upper + 1) &&
        sublist(upper + 1, n, groups_after) == sublist(upper + 1, n, groups) &&
        sublist(upper + 1, n, keys_after) == sublist(upper + 1, n, keys) &&
        IntArray::full(grp, n, groups_after) * IntArray::full(key, n, keys_after)
*/
{
    /*@ Inv Assert
        exists groups_now keys_now,
          grp == grp@pre && key == key@pre && upper == upper@pre &&
          0 <= upper && upper < n && n <= cap && cap <= 300000 &&
          Zlength(groups_now) == n && Zlength(keys_now) == n &&
          0 <= root@pre && root@pre <= root && root <= upper &&
          0 <= 2 * root + 1 && 2 * root + 1 <= INT_MAX &&
          ParallelPermutation(groups, keys, groups_now, keys_now) &&
          HeapOrderedExceptAtFromItems(groups_now, keys_now,
                                       root@pre, upper, root) &&
          SiftChildrenBelowParentItems(groups_now, keys_now,
                                       root@pre, upper, root) &&
          ExtractionFrameItems(groups_now, keys_now, upper + 1) &&
          sublist(upper + 1, n, groups_now) == sublist(upper + 1, n, groups) &&
          sublist(upper + 1, n, keys_now) == sublist(upper + 1, n, keys) &&
          IntArray::full(grp, n, groups_now) * IntArray::full(key, n, keys_now)
    */
    while (2 * root + 1 <= upper) {
        int child = 2 * root + 1;
        if (child + 1 <= upper &&
            item_less(grp[child], key[child], grp[child + 1], key[child + 1]))
            child++;
        /*@ Assert
            exists groups_now keys_now,
              grp == grp@pre && key == key@pre && upper == upper@pre &&
              0 <= upper && upper < n && n <= cap && cap <= 300000 &&
              Zlength(groups_now) == n && Zlength(keys_now) == n &&
              0 <= root@pre && root@pre <= root && root <= upper &&
              0 <= child && child <= upper &&
              SelectedLargerChildItems(groups_now, keys_now, root, upper, child) &&
              ParallelPermutation(groups, keys, groups_now, keys_now) &&
              HeapOrderedExceptAtFromItems(groups_now, keys_now,
                                           root@pre, upper, root) &&
              SiftChildrenBelowParentItems(groups_now, keys_now,
                                           root@pre, upper, root) &&
              ExtractionFrameItems(groups_now, keys_now, upper + 1) &&
              sublist(upper + 1, n, groups_now) == sublist(upper + 1, n, groups) &&
              sublist(upper + 1, n, keys_now) == sublist(upper + 1, n, keys) &&
              IntArray::full(grp, n, groups_now) * IntArray::full(key, n, keys_now)
        */
        if (!item_less(grp[root], key[root], grp[child], key[child]))
            return;
        int t = grp[root]; grp[root] = grp[child]; grp[child] = t;
        t = key[root]; key[root] = key[child]; key[child] = t;
        /*@ Assert
            exists groups_now keys_now,
              grp == grp@pre && key == key@pre && upper == upper@pre &&
              0 <= upper && upper < n && n <= cap && cap <= 300000 &&
              Zlength(groups_now) == n && Zlength(keys_now) == n &&
              0 <= root@pre && root@pre <= root && root < child && child <= upper &&
              ParallelPermutation(groups, keys, groups_now, keys_now) &&
              HeapOrderedExceptAtFromItems(groups_now, keys_now,
                                           root@pre, upper, child) &&
              SiftChildrenBelowParentItems(groups_now, keys_now,
                                           root@pre, upper, child) &&
              ExtractionFrameItems(groups_now, keys_now, upper + 1) &&
              sublist(upper + 1, n, groups_now) == sublist(upper + 1, n, groups) &&
              sublist(upper + 1, n, keys_now) == sublist(upper + 1, n, keys) &&
              IntArray::full(grp, n, groups_now) * IntArray::full(key, n, keys_now) *
              has_permission(&t)
        */
        root = child;
    }
}

static void sort_items(int *grp, int *key, int cnt)
/*@ With (groups keys : list Z) (cap : Z)
    Require
      0 <= cnt && cnt <= cap && cap <= 300000 &&
      Zlength(groups) == cnt && Zlength(keys) == cnt &&
      IntArray::full(grp, cnt, groups) * IntArray::full(key, cnt, keys)
    Ensure
      exists groups_after keys_after,
        Zlength(groups_after) == cnt && Zlength(keys_after) == cnt &&
        ParallelPermutation(groups, keys, groups_after, keys_after) &&
        ItemsIncreasing(groups_after, keys_after) &&
        IntArray::full(grp, cnt, groups_after) * IntArray::full(key, cnt, keys_after)
*/
{
    /*@ Inv Assert
        exists groups_now keys_now,
          grp == grp@pre && key == key@pre && cnt == cnt@pre &&
          0 <= cnt && cnt <= cap && cap <= 300000 &&
          Zlength(groups) == cnt && Zlength(keys) == cnt &&
          Zlength(groups_now) == cnt && Zlength(keys_now) == cnt &&
          -1 <= root && root <= cnt / 2 - 1 &&
          ParallelPermutation(groups, keys, groups_now, keys_now) &&
          HeapParentsFromItems(groups_now, keys_now, root + 1, cnt - 1) &&
          IntArray::full(grp, cnt, groups_now) * IntArray::full(key, cnt, keys_now)
    */
    for (int root = cnt / 2 - 1; root >= 0; root--)
        sift_items(grp, key, root, cnt - 1) /*@ where n = cnt, cap = cap */;
    /*@ Inv Assert
        exists groups_now keys_now,
          grp == grp@pre && key == key@pre && cnt == cnt@pre &&
          0 <= cnt && cnt <= cap && cap <= 300000 &&
          Zlength(groups) == cnt && Zlength(keys) == cnt &&
          Zlength(groups_now) == cnt && Zlength(keys_now) == cnt &&
          -1 <= upper && upper < cnt &&
          HeapSortItemsState(groups, keys, groups_now, keys_now, upper) &&
          IntArray::full(grp, cnt, groups_now) * IntArray::full(key, cnt, keys_now)
    */
    for (int upper = cnt - 1; upper > 0; upper--) {
        int t = grp[0]; grp[0] = grp[upper]; grp[upper] = t;
        t = key[0]; key[0] = key[upper]; key[upper] = t;
        /*@ Assert
            exists groups_now keys_now,
              grp == grp@pre && key == key@pre && cnt == cnt@pre &&
              0 <= cnt && cnt <= cap && cap <= 300000 &&
              Zlength(groups) == cnt && Zlength(keys) == cnt &&
              Zlength(groups_now) == cnt && Zlength(keys_now) == cnt &&
              1 <= upper && upper <= cnt - 1 &&
              ParallelPermutation(groups, keys, groups_now, keys_now) &&
              HeapOrderedExceptAtFromItems(groups_now, keys_now,
                                           0, upper - 1, 0) &&
              ExtractionFrameItems(groups_now, keys_now, upper) &&
              IntArray::full(grp, cnt, groups_now) * IntArray::full(key, cnt, keys_now) *
              has_permission(&t)
        */
        sift_items(grp, key, 0, upper - 1) /*@ where
          n = cnt, cap = cap */;
    }
}

/* count_pairs: pairs inside each group that differ in key. */
static long long count_pairs(int *grp, int *key, int cnt)
/*@ With (groups keys : list Z) (cap : Z)
    Require
      0 <= cnt && cnt <= cap && cap <= 300000 &&
      Zlength(groups) == cnt && Zlength(keys) == cnt &&
      IntArray::full(grp, cnt, groups) * IntArray::full(key, cnt, keys)
    Ensure
      exists groups_after keys_after,
        Zlength(groups_after) == cnt && Zlength(keys_after) == cnt &&
        ParallelPermutation(groups, keys, groups_after, keys_after) &&
        PairCountPrefix(groups, keys, cnt, __return) &&
        IntArray::full(grp, cnt, groups_after) * IntArray::full(key, cnt, keys_after)
*/
{
    sort_items(grp, key, cnt) /*@ where cap = cap */;
    long long total = 0;
    int i = 0;
    /*@ Inv Assert
        exists groups_sorted keys_sorted,
          grp == grp@pre && key == key@pre && cnt == cnt@pre &&
          0 <= cnt && cnt <= cap && cap <= 300000 &&
          Zlength(groups_sorted) == cnt && Zlength(keys_sorted) == cnt &&
          0 <= i && i <= cnt && 0 <= total && total <= 45000000000 &&
          ParallelPermutation(groups, keys, groups_sorted, keys_sorted) &&
          ItemsIncreasing(groups_sorted, keys_sorted) &&
          PairCountPrefix(groups_sorted, keys_sorted, i, total) &&
          ValueRunBoundary(groups_sorted, i) &&
          IntArray::full(grp, cnt, groups_sorted) * IntArray::full(key, cnt, keys_sorted)
    */
    while (i < cnt) {
        int j = i;
        /*@ Inv Assert
            exists groups_sorted keys_sorted,
              grp == grp@pre && key == key@pre && cnt == cnt@pre &&
              0 <= cnt && cnt <= cap && cap <= 300000 &&
              Zlength(groups_sorted) == cnt && Zlength(keys_sorted) == cnt &&
              0 <= i && i < cnt && i <= j && j <= cnt &&
              0 <= total && total <= 45000000000 &&
              ParallelPermutation(groups, keys, groups_sorted, keys_sorted) &&
              ItemsIncreasing(groups_sorted, keys_sorted) &&
              PairCountPrefix(groups_sorted, keys_sorted, i, total) &&
              ValueRunBoundary(groups_sorted, i) &&
              SameValueRange(groups_sorted, i, j) &&
              IntArray::full(grp, cnt, groups_sorted) * IntArray::full(key, cnt, keys_sorted)
        */
        while (j < cnt && grp[j] == grp[i])
            j++;
        long long g = j - i;
        total += g * (g - 1) / 2;
        int p = i;
        /*@ Inv Assert
            exists groups_sorted keys_sorted,
              grp == grp@pre && key == key@pre && cnt == cnt@pre &&
              0 <= cnt && cnt <= cap && cap <= 300000 &&
              Zlength(groups_sorted) == cnt && Zlength(keys_sorted) == cnt &&
              0 <= i && i < j && j <= cnt && i <= p && p <= j &&
              g == j - i && 0 <= total && total <= 45000000000 &&
              ParallelPermutation(groups, keys, groups_sorted, keys_sorted) &&
              ItemsIncreasing(groups_sorted, keys_sorted) &&
              ValueRunBoundary(groups_sorted, i) &&
              ValueRunBoundary(groups_sorted, j) &&
              SameValueRange(groups_sorted, i, j) &&
              RangeRunBoundary(keys_sorted, i, j, p) &&
              CountGroupPhase(groups_sorted, keys_sorted, i, j, p, total) &&
              IntArray::full(grp, cnt, groups_sorted) * IntArray::full(key, cnt, keys_sorted)
        */
        while (p < j) {                   /* remove same-key pairs */
            int q = p;
            /*@ Inv Assert
                exists groups_sorted keys_sorted,
                  grp == grp@pre && key == key@pre && cnt == cnt@pre &&
                  0 <= cnt && cnt <= cap && cap <= 300000 &&
                  Zlength(groups_sorted) == cnt && Zlength(keys_sorted) == cnt &&
                  0 <= i && i < j && j <= cnt && i <= p && p < j &&
                  p <= q && q <= j && 0 <= p && p < cnt && 0 <= q && q <= cnt &&
                  ((q < j && q < cnt) || q == j) &&
                  g == j - i &&
                  0 <= total && total <= 45000000000 &&
                  ParallelPermutation(groups, keys, groups_sorted, keys_sorted) &&
                  ItemsIncreasing(groups_sorted, keys_sorted) &&
                  ValueRunBoundary(groups_sorted, i) &&
                  ValueRunBoundary(groups_sorted, j) &&
                  SameValueRange(groups_sorted, i, j) &&
                  SameValueRange(keys_sorted, p, q) &&
                  RangeRunBoundary(keys_sorted, i, j, p) &&
                  CountGroupPhase(groups_sorted, keys_sorted, i, j, p, total) &&
                  IntArray::full(grp, cnt, groups_sorted) * IntArray::full(key, cnt, keys_sorted)
                by local
            */
            while (q < j && key[q] == key[p])
                q++;
            long long same = q - p;
            total -= same * (same - 1) / 2;
            p = q;
        }
        i = j;
    }
    return total;
}

/* solver: number of inconvenient pairs. */
static long long solver(const int *xs, int n, const int *ys, int m,
                        const int *px, const int *py, int k,
                        int *va_grp, int *va_key,
                        int *ha_grp, int *ha_key)
/* QCP_INSERT_BEGIN:shard09-P063-normalized-solver-contract */
/*@ With (x_lines : list Z) (y_lines : list Z)
          (people : list(Z*Z))
          (person_x : list Z) (person_y : list Z)
    Require
      2 <= n && n <= 200000 && 2 <= m && m <= 200000 && 2 <= k && k <= 300000 && (forall i, (0 <= i && i < n) => (0 <= x_lines[i] && x_lines[i] <= 1000000)) && (forall i, (0 <= i && i < m) => (0 <= y_lines[i] && y_lines[i] <= 1000000)) && (forall i, (0 <= i && i < k) => (0 <= fst(people[i]) && fst(people[i]) <= 1000000 && 0 <= snd(people[i]) && snd(people[i]) <= 1000000)) && Pre(x_lines, y_lines, people) &&
      n == Zlength(x_lines) && m == Zlength(y_lines) &&
      k == Zlength(people) &&
      Zlength(person_x) == k && Zlength(person_y) == k &&
      (forall i, (0 <= i && i < k) =>
        (person_x[i] == fst(people[i]) &&
         person_y[i] == snd(people[i]))) &&
      IntArray::full(xs, n, x_lines) *
      IntArray::full(ys, m, y_lines) *
      IntArray::full(px, k, person_x) *
      IntArray::full(py, k, person_y) *
      IntArray::full_shape(va_grp, k) *
      IntArray::full_shape(va_key, k) *
      IntArray::full_shape(ha_grp, k) *
      IntArray::full_shape(ha_key, k)
    Ensure
      Spec(x_lines, y_lines, people, __return) &&
      IntArray::full(xs, n, x_lines) *
      IntArray::full(ys, m, y_lines) *
      IntArray::full(px, k, person_x) *
      IntArray::full(py, k, person_y) *
      IntArray::full_shape(va_grp, k) *
      IntArray::full_shape(va_key, k) *
      IntArray::full_shape(ha_grp, k) *
      IntArray::full_shape(ha_key, k)
*/
/* QCP_INSERT_END:shard09-P063-normalized-solver-contract */
{
    int nv = 0, nh = 0;
    /*@ Inv Assert
        exists vg vk hg hk vg_tail vk_tail hg_tail hk_tail,
          xs == xs@pre && ys == ys@pre && px == px@pre && py == py@pre &&
          va_grp == va_grp@pre && va_key == va_key@pre &&
          ha_grp == ha_grp@pre && ha_key == ha_key@pre &&
          n == n@pre && m == m@pre && k == k@pre &&
          2 <= n && n <= 200000 && 2 <= m && m <= 200000 &&
          2 <= k && k <= 300000 &&
          n == Zlength(x_lines) && m == Zlength(y_lines) &&
          k == Zlength(people) && Zlength(person_x) == k && Zlength(person_y) == k &&
          Pre(x_lines, y_lines, people) &&
          StreetCoordinateBounds(x_lines) && StreetCoordinateBounds(y_lines) &&
          PeopleCoordinateBounds(people) &&
          (forall q, (0 <= q && q < k) =>
             (person_x[q] == fst(people[q]) && person_y[q] == snd(people[q]))) &&
          0 <= p && p <= k && 0 <= nv && nv <= p && 0 <= nh && nh <= p &&
          Zlength(vg) == nv && Zlength(vk) == nv &&
          Zlength(hg) == nh && Zlength(hk) == nh &&
          Zlength(vg_tail) == k - nv && Zlength(vk_tail) == k - nv &&
          Zlength(hg_tail) == k - nh && Zlength(hk_tail) == k - nh &&
          ClassifiedPrefix(x_lines, y_lines, people, p, vg, vk, hg, hk) &&
          ClassifiedCountsCorrect(x_lines, y_lines, people, p,
                                  vg, vk, hg, hk) &&
          IntArray::full(xs, n, x_lines) * IntArray::full(ys, m, y_lines) *
          IntArray::full(px, k, person_x) * IntArray::full(py, k, person_y) *
          IntArray::full(va_grp, nv, vg) *
          IntArray::seg(va_grp, nv, k, vg_tail) *
          IntArray::full(va_key, nv, vk) *
          IntArray::seg(va_key, nv, k, vk_tail) *
          IntArray::full(ha_grp, nh, hg) *
          IntArray::seg(ha_grp, nh, k, hg_tail) *
          IntArray::full(ha_key, nh, hk) *
          IntArray::seg(ha_key, nh, k, hk_tail)
    */
    for (int p = 0; p < k; p++) {
        int sy = strip(ys, m, py[p]) /*@ where streets = y_lines */;
        int sx = strip(xs, n, px[p]) /*@ where streets = x_lines */;
        if (sy >= 0) {                    /* on a vertical street only */
            va_grp[nv] = sy;
            va_key[nv] = px[p];
            nv++;
        } else if (sx >= 0) {             /* on a horizontal street only */
            ha_grp[nh] = sx;
            ha_key[nh] = py[p];
            nh++;
        }
        /*@ Assert
            exists vg vk hg hk vg_next vk_next hg_next hk_next
                   vg_tail vk_tail hg_tail hk_tail,
              xs == xs@pre && ys == ys@pre && px == px@pre && py == py@pre &&
              va_grp == va_grp@pre && va_key == va_key@pre &&
              ha_grp == ha_grp@pre && ha_key == ha_key@pre &&
              n == n@pre && m == m@pre && k == k@pre &&
              2 <= n && n <= 200000 && 2 <= m && m <= 200000 &&
              2 <= k && k <= 300000 &&
              n == Zlength(x_lines) && m == Zlength(y_lines) &&
              k == Zlength(people) &&
              Zlength(person_x) == k && Zlength(person_y) == k &&
              Pre(x_lines, y_lines, people) &&
              StreetCoordinateBounds(x_lines) && StreetCoordinateBounds(y_lines) &&
              PeopleCoordinateBounds(people) &&
              (forall q, (0 <= q && q < k) =>
                 (person_x[q] == fst(people[q]) &&
                  person_y[q] == snd(people[q]))) &&
              0 <= p && p < k && 0 <= nv && nv <= p + 1 &&
              0 <= nh && nh <= p + 1 &&
              Zlength(vg_next) == nv && Zlength(vk_next) == nv &&
              Zlength(hg_next) == nh && Zlength(hk_next) == nh &&
              Zlength(vg_tail) == k - nv && Zlength(vk_tail) == k - nv &&
              Zlength(hg_tail) == k - nh && Zlength(hk_tail) == k - nh &&
              StripIndex(y_lines, person_y[p], sy) &&
              StripIndex(x_lines, person_x[p], sx) &&
              ClassifiedPrefix(x_lines, y_lines, people, p,
                               vg, vk, hg, hk) &&
              ClassifiedCountsCorrect(x_lines, y_lines, people, p,
                                      vg, vk, hg, hk) &&
              ((0 <= sy &&
                vg_next == app(vg, cons(sy, nil)) &&
                vk_next == app(vk, cons(person_x[p], nil)) &&
                hg_next == hg && hk_next == hk) ||
               (sy < 0 && 0 <= sx &&
                vg_next == vg && vk_next == vk &&
                hg_next == app(hg, cons(sx, nil)) &&
                hk_next == app(hk, cons(person_y[p], nil))) ||
               (sy < 0 && sx < 0 &&
                vg_next == vg && vk_next == vk &&
                hg_next == hg && hk_next == hk)) &&
              ClassifiedPrefix(x_lines, y_lines, people, p + 1,
                               vg_next, vk_next, hg_next, hk_next) &&
              ClassifiedCountsCorrect(x_lines, y_lines, people, p + 1,
                                      vg_next, vk_next, hg_next, hk_next) &&
              IntArray::full(xs, n, x_lines) * IntArray::full(ys, m, y_lines) *
              IntArray::full(px, k, person_x) * IntArray::full(py, k, person_y) *
              IntArray::full(va_grp, nv, vg_next) *
              IntArray::seg(va_grp, nv, k, vg_tail) *
              IntArray::full(va_key, nv, vk_next) *
              IntArray::seg(va_key, nv, k, vk_tail) *
              IntArray::full(ha_grp, nh, hg_next) *
              IntArray::seg(ha_grp, nh, k, hg_tail) *
              IntArray::full(ha_key, nh, hk_next) *
              IntArray::seg(ha_key, nh, k, hk_tail)
        */
    }
    /*@ Assert
        exists vg vk hg hk vg_tail vk_tail hg_tail hk_tail,
          xs == xs@pre && ys == ys@pre && px == px@pre && py == py@pre &&
          va_grp == va_grp@pre && va_key == va_key@pre &&
          ha_grp == ha_grp@pre && ha_key == ha_key@pre &&
          n == n@pre && m == m@pre && k == k@pre &&
          2 <= n && n <= 200000 && 2 <= m && m <= 200000 &&
          2 <= k && k <= 300000 &&
          n == Zlength(x_lines) && m == Zlength(y_lines) &&
          k == Zlength(people) &&
          Zlength(person_x) == k && Zlength(person_y) == k &&
          Pre(x_lines, y_lines, people) &&
          StreetCoordinateBounds(x_lines) && StreetCoordinateBounds(y_lines) &&
          PeopleCoordinateBounds(people) &&
          (forall q, (0 <= q && q < k) =>
             (person_x[q] == fst(people[q]) && person_y[q] == snd(people[q]))) &&
          Zlength(vg) == nv && Zlength(vk) == nv &&
          Zlength(hg) == nh && Zlength(hk) == nh &&
          Zlength(vg_tail) == k - nv && Zlength(vk_tail) == k - nv &&
          Zlength(hg_tail) == k - nh && Zlength(hk_tail) == k - nh &&
          ClassifiedPrefix(x_lines, y_lines, people, k, vg, vk, hg, hk) &&
          ClassifiedCountsCorrect(x_lines, y_lines, people, k,
                                  vg, vk, hg, hk) &&
          IntArray::full(xs, n, x_lines) * IntArray::full(ys, m, y_lines) *
          IntArray::full(px, k, person_x) * IntArray::full(py, k, person_y) *
          IntArray::full(va_grp, nv, vg) *
          IntArray::seg(va_grp, nv, k, vg_tail) *
          IntArray::full(va_key, nv, vk) *
          IntArray::seg(va_key, nv, k, vk_tail) *
          IntArray::full(ha_grp, nh, hg) *
          IntArray::seg(ha_grp, nh, k, hg_tail) *
          IntArray::full(ha_key, nh, hk) *
          IntArray::seg(ha_key, nh, k, hk_tail)
    */
    return count_pairs(va_grp, va_key, nv) /*@ where cap = k */ +
           count_pairs(ha_grp, ha_key, nh) /*@ where cap = k */;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int xs[200005], ys[200005], px[300005], py[300005];
//     static int va_grp[300005], va_key[300005];
//     static int ha_grp[300005], ha_key[300005];
//     while (t--) {
//         int n, m, k;
//         scanf("%d %d %d", &n, &m, &k);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &xs[i]);
//         for (int i = 0; i < m; i++)
//             scanf("%d", &ys[i]);
//         for (int p = 0; p < k; p++)
//             scanf("%d %d", &px[p], &py[p]);
//         printf("%lld\n", solver(xs, n, ys, m, px, py, k,
//                                 va_grp, va_key, ha_grp, ha_key));
//     }
//     return 0;
// }
