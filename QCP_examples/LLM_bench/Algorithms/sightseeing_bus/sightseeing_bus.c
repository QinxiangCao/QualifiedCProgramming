/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::lt : Z -> Z -> Prop)
      (sublist : {A} -> Z -> Z -> list A -> list A)
      (DestinationCounts : Z -> Z -> list Z -> list Z -> Prop)
      (SightseeingMinimumTotal : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
 */
/*@ Extern Coq
      (WorkspacesZeroPrefix : list Z -> list Z -> Z -> Prop)
      (PassengerAggregationPrefix : Z -> Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> Prop)
      (StationSummaryState : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (ArrivalSimulationPrefix : Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (CanonicalBusState : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (MarginalBenefitScan : list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (EdgeMarginalBenefit : Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (EdgeChoicePrefix : Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (BestBoostChoice : Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (ArrivalRepairProgress : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (ArrivalRepairOutcome : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (BoosterProgress : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (SelectedExchangeCertificate : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (OptimizedBusState : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (TravelSumPrefix : Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus.sightseeing_bus_lib */

int solve(int n, int m, int k, int *d, int *t, int *a, int *b)
/*@ With (dist times origins destinations : list Z)
    Require
      0 <= k && k <= 100000 &&
      2 <= n && n <= 1000 &&
        1 <= m && m <= 10000 &&
        Zlength(dist) == n - 1 &&
        Zlength(times) == m && Zlength(origins) == m &&
        Zlength(destinations) == m &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
      IntArray::full(d, n - 1, dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations)
    Ensure
      exists final_dist,
      SightseeingMinimumTotal(n, m, k@pre, dist, times, origins, destinations, __return) &&
      IntArray::full(d, n - 1, final_dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations)
*/
{
    int late[1000];
    int off[1000];
    int arr[1000];

    int i;
    int j;
    int cur;
    int best;
    int pos;
    int cnt;
    int ans;

    /*@ Inv Assert
        exists latest_prefix counts_prefix,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        0 <= i && i <= n@pre &&
        Zlength(latest_prefix) == i &&
        Zlength(counts_prefix) == i &&
        WorkspacesZeroPrefix(latest_prefix, counts_prefix, i) &&
        2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        undef_data_at(&j, int) *
        undef_data_at(&cur, int) *
        undef_data_at(&best, int) *
        undef_data_at(&pos, int) *
        undef_data_at(&cnt, int) *
        undef_data_at(&ans, int) *
        IntArray::full(d, n@pre - 1, dist) *
        IntArray::full(t, m@pre, times) *
        IntArray::full(a, m@pre, origins) *
        IntArray::full(b, m@pre, destinations) *
        IntArray::seg(late, 0, i, latest_prefix) *
        IntArray::undef_seg(late, i, n@pre) *
      IntArray::undef_seg(late, n@pre, 1000) *
        IntArray::seg(off, 0, i, counts_prefix) *
        IntArray::undef_seg(off, i, n@pre) *
      IntArray::undef_seg(off, n@pre, 1000) *
        IntArray::undef_full(arr, n@pre) *
      IntArray::undef_seg(arr, n@pre, 1000)
     */
    for (i = 0; i < n; ++i) {
        late[i] = 0;
        off[i] = 0;
    }

    /*@ Inv Assert
        exists latest counts,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        0 <= i && i <= m@pre &&
        2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
        Forall(Z::le(0), latest) &&
        Forall(Z::ge(100000), latest) &&
        Forall(Z::le(0), counts) &&
        Forall(Z::ge(i), counts) &&
        PassengerAggregationPrefix(
          n@pre, m@pre, times, origins, destinations, i, latest, counts) &&
        undef_data_at(&j, int) *
        undef_data_at(&cur, int) *
        undef_data_at(&best, int) *
        undef_data_at(&pos, int) *
        undef_data_at(&cnt, int) *
        undef_data_at(&ans, int) *
        IntArray::full(d, n@pre - 1, dist) *
        IntArray::full(t, m@pre, times) *
        IntArray::full(a, m@pre, origins) *
        IntArray::full(b, m@pre, destinations) *
        IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
        IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
        IntArray::undef_full(arr, n@pre) *
      IntArray::undef_seg(arr, n@pre, 1000)
     */
    for (i = 0; i < m; ++i) {
        int x = a[i] - 1;
        int y = b[i] - 1;
        /*@ (0 <= x && x < n@pre &&
            x == Znth(i, origins, 0) - 1) &&
                (0 <= y && y < n@pre &&
            y == Znth(i, destinations, 0) - 1) by local */
        if (late[x] < t[i]) {
            late[x] = t[i];
        }
        off[y] = off[y] + 1;
    }



    cur = 0;
    /*@ Inv Assert
        exists latest counts arrivals_prefix,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        0 <= i && i <= n@pre &&
        0 <= cur && cur <= 200000 &&
        Zlength(arrivals_prefix) == i &&
        2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        StationSummaryState(
          n@pre, m@pre, times, origins, destinations, latest, counts) &&
        Forall(Z::le(0), latest) &&
        Forall(Z::ge(100000), latest) &&
        Forall(Z::le(0), counts) &&
        Forall(Z::ge(m@pre), counts) &&
        ArrivalSimulationPrefix(
          n@pre, dist, latest, arrivals_prefix, i, cur) &&
        undef_data_at(&j, int) *
        undef_data_at(&best, int) *
        undef_data_at(&pos, int) *
        undef_data_at(&cnt, int) *
        undef_data_at(&ans, int) *
        IntArray::full(d, n@pre - 1, dist) *
        IntArray::full(t, m@pre, times) *
        IntArray::full(a, m@pre, origins) *
        IntArray::full(b, m@pre, destinations) *
        IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
        IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
        IntArray::seg(arr, 0, i, arrivals_prefix) *
        IntArray::undef_seg(arr, i, n@pre) *
      IntArray::undef_seg(arr, n@pre, 1000)
     */
    for (i = 0; i < n; ++i) {
        arr[i] = cur;
        if (cur < late[i]) {
            cur = late[i];
        }
        if (i + 1 < n) {
            cur = cur + d[i];
        }
    }

    /*@ Inv Assert
        exists current_dist latest counts arrivals,
        n == n@pre && m == m@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        0 <= k && k <= k@pre && k@pre <= 100000 &&
        2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
        Zlength(current_dist) == n@pre - 1 &&
        Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
        Zlength(arrivals) == n@pre &&
        Forall(Z::le(0), current_dist) &&
        Forall(Z::ge(100), current_dist) &&
        Forall(Z::le(0), latest) &&
        Forall(Z::ge(100000), latest) &&
        Forall(Z::le(0), counts) &&
        Forall(Z::ge(m@pre), counts) &&
        Forall(Z::le(0), arrivals) &&
        Forall(Z::ge(200000), arrivals) &&
        BoosterProgress(
          n@pre, m@pre, k@pre, k,
          dist, times, origins, destinations,
          current_dist, latest, counts, arrivals) &&
        undef_data_at(&i, int) *
        undef_data_at(&j, int) *
        undef_data_at(&cur, int) *
        undef_data_at(&best, int) *
        undef_data_at(&pos, int) *
        undef_data_at(&cnt, int) *
        undef_data_at(&ans, int) *
        IntArray::full(d, n@pre - 1, current_dist) *
        IntArray::full(t, m@pre, times) *
        IntArray::full(a, m@pre, origins) *
        IntArray::full(b, m@pre, destinations) *
        IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
        IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
        IntArray::full(arr, n@pre, arrivals) *
      IntArray::undef_seg(arr, n@pre, 1000)
     */
    while (k > 0) {
        best = 0;
        pos = -1;
        /*@ Inv Assert
            exists current_dist latest counts arrivals,
            n == n@pre && m == m@pre &&
            d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
            0 < k && k <= k@pre && k@pre <= 100000 &&
            0 <= i && i <= n@pre - 1 &&
            0 <= best && best <= m@pre &&
            -1 <= pos && pos < i &&
            2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
            Zlength(current_dist) == n@pre - 1 &&
            Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
            Zlength(arrivals) == n@pre &&
            Forall(Z::le(0), current_dist) &&
        Forall(Z::ge(100), current_dist) &&
            Forall(Z::le(0), latest) &&
        Forall(Z::ge(100000), latest) &&
        Forall(Z::le(0), counts) &&
        Forall(Z::ge(m@pre), counts) &&
        Forall(Z::le(0), arrivals) &&
        Forall(Z::ge(200000), arrivals) &&
            BoosterProgress(
              n@pre, m@pre, k@pre, k,
              dist, times, origins, destinations,
              current_dist, latest, counts, arrivals) &&
            EdgeChoicePrefix(
              n@pre, current_dist, counts, latest, arrivals,
              i, best, pos) &&
            undef_data_at(&j, int) *
            undef_data_at(&cur, int) *
            undef_data_at(&cnt, int) *
            undef_data_at(&ans, int) *
            IntArray::full(d, n@pre - 1, current_dist) *
            IntArray::full(t, m@pre, times) *
            IntArray::full(a, m@pre, origins) *
            IntArray::full(b, m@pre, destinations) *
            IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
            IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
            IntArray::full(arr, n@pre, arrivals) *
      IntArray::undef_seg(arr, n@pre, 1000)
         */
        for (i = 0; i + 1 < n; ++i) {
            if (d[i] > 0) {
                cnt = 0;
                /*@ Inv Assert
                    exists current_dist latest counts arrivals,
                    n == n@pre && m == m@pre &&
                    d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
                    0 < k && k <= k@pre && k@pre <= 100000 &&
                    0 <= i && i < n@pre - 1 &&
                    i + 1 <= j && j <= n@pre &&
                    0 <= cnt && cnt <= m@pre &&
                    0 <= best && best <= m@pre &&
                    -1 <= pos && pos < i &&
                    0 < Znth(i, current_dist, 0) &&
                    2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
                    Zlength(current_dist) == n@pre - 1 &&
                    Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
                    Zlength(arrivals) == n@pre &&
                    Forall(Z::le(0), current_dist) &&
        Forall(Z::ge(100), current_dist) &&
                    Forall(Z::le(0), latest) &&
        Forall(Z::ge(100000), latest) &&
        Forall(Z::le(0), counts) &&
        Forall(Z::ge(m@pre), counts) &&
        Forall(Z::le(0), arrivals) &&
        Forall(Z::ge(200000), arrivals) &&
                    BoosterProgress(
                      n@pre, m@pre, k@pre, k,
                      dist, times, origins, destinations,
                      current_dist, latest, counts, arrivals) &&
                    EdgeChoicePrefix(
                      n@pre, current_dist, counts, latest, arrivals,
                      i, best, pos) &&
                    MarginalBenefitScan(
                      counts, latest, arrivals, i, j, cnt) &&
                    undef_data_at(&cur, int) *
                    undef_data_at(&ans, int) *
                    IntArray::full(d, n@pre - 1, current_dist) *
                    IntArray::full(t, m@pre, times) *
                    IntArray::full(a, m@pre, origins) *
                    IntArray::full(b, m@pre, destinations) *
                    IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
                    IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
                    IntArray::full(arr, n@pre, arrivals) *
      IntArray::undef_seg(arr, n@pre, 1000)
                 */
                for (j = i + 1; j < n; ++j) {
                    cnt = cnt + off[j];
                    if (arr[j] <= late[j]) {
                        break;
                    }
                }

                /*@ Assert
                    exists current_dist latest counts arrivals,
                    n == n@pre && m == m@pre &&
                    d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
                    0 < k && k <= k@pre && k@pre <= 100000 &&
                    0 <= i && i < n@pre - 1 &&
                    0 <= cnt && cnt <= m@pre &&
                    0 <= best && best <= m@pre &&
                    -1 <= pos && pos < i &&
                    i + 1 <= j && j <= n@pre &&
                    0 < Znth(i, current_dist, 0) &&
                    2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
                    BoosterProgress(
                      n@pre, m@pre, k@pre, k,
                      dist, times, origins, destinations,
                      current_dist, latest, counts, arrivals) &&
                    EdgeChoicePrefix(
                      n@pre, current_dist, counts, latest, arrivals,
                      i, best, pos) &&
                    EdgeMarginalBenefit(
                      n@pre, counts, latest, arrivals, i, cnt) &&
                    undef_data_at(&cur, int) *
                    undef_data_at(&ans, int) *
                    IntArray::full(d, n@pre - 1, current_dist) *
                    IntArray::full(t, m@pre, times) *
                    IntArray::full(a, m@pre, origins) *
                    IntArray::full(b, m@pre, destinations) *
                    IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
                    IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
                    IntArray::full(arr, n@pre, arrivals) *
      IntArray::undef_seg(arr, n@pre, 1000)
                 */
                if (best < cnt) {
                    best = cnt;
                    pos = i;
                }
            }
        }

        if (pos < 0 || best == 0) {
            break;
        }
        d[pos] = d[pos] - 1;
        /*@ Inv Assert
            exists old_dist old_arrivals new_dist new_arrivals latest counts,
            n == n@pre && m == m@pre &&
            d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
            0 < k && k <= k@pre && k@pre <= 100000 &&
            0 <= pos && pos < n@pre - 1 &&
            0 < best && best <= m@pre &&
            pos + 1 <= i && i <= n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
            Zlength(old_dist) == n@pre - 1 &&
            Zlength(new_dist) == n@pre - 1 &&
            Zlength(old_arrivals) == n@pre &&
            Zlength(new_arrivals) == n@pre &&
            Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
            Forall(Z::le(0), new_dist) &&
        Forall(Z::ge(100), new_dist) &&
            Forall(Z::le(0), latest) &&
        Forall(Z::ge(100000), latest) &&
        Forall(Z::le(0), counts) &&
        Forall(Z::ge(m@pre), counts) &&
        Forall(Z::le(0), new_arrivals) &&
        Forall(Z::ge(200000), new_arrivals) &&
            BoosterProgress(
              n@pre, m@pre, k@pre, k,
              dist, times, origins, destinations,
              old_dist, latest, counts, old_arrivals) &&
            BestBoostChoice(
              n@pre, old_dist, counts, latest, old_arrivals, best, pos) &&
            ArrivalRepairProgress(
              n@pre, old_dist, old_arrivals,
              new_dist, new_arrivals, latest, pos, i) &&
            undef_data_at(&j, int) *
            undef_data_at(&cur, int) *
            undef_data_at(&cnt, int) *
            undef_data_at(&ans, int) *
            IntArray::full(d, n@pre - 1, new_dist) *
            IntArray::full(t, m@pre, times) *
            IntArray::full(a, m@pre, origins) *
            IntArray::full(b, m@pre, destinations) *
            IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
            IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
            IntArray::full(arr, n@pre, new_arrivals) *
      IntArray::undef_seg(arr, n@pre, 1000)
         */
        for (i = pos + 1; i < n; ++i) {
            arr[i] = arr[i] - 1;
            if (arr[i] < late[i]) {
                break;
            }
        }


        k = k - 1;
    }

    ans = 0;
    /*@ Inv Assert
        exists final_dist latest counts arrivals,
        n == n@pre && m == m@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        0 <= k && k <= k@pre && k@pre <= 100000 &&
        0 <= i && i <= m@pre &&
        0 <= ans && ans <= i * 200000 && ans <= 2000000000 &&
        2 <= n@pre && n@pre <= 1000 &&
        1 <= m@pre && m@pre <= 10000 &&
        Zlength(dist) == n@pre - 1 &&
        Zlength(times) == m@pre && Zlength(origins) == m@pre &&
        Zlength(destinations) == m@pre &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n@pre), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
        OptimizedBusState(
          n@pre, m@pre, k@pre,
          dist, times, origins, destinations,
          final_dist, latest, counts, arrivals) &&
        Zlength(arrivals) == n@pre &&
        Forall(Z::le(0), arrivals) &&
        Forall(Z::ge(200000), arrivals) &&
        Forall(Z::le(1), destinations) &&
        TravelSumPrefix(m@pre, times, destinations, arrivals, i, ans) &&
        undef_data_at(&j, int) *
        undef_data_at(&cur, int) *
        undef_data_at(&best, int) *
        undef_data_at(&pos, int) *
        undef_data_at(&cnt, int) *
        IntArray::full(d, n@pre - 1, final_dist) *
        IntArray::full(t, m@pre, times) *
        IntArray::full(a, m@pre, origins) *
        IntArray::full(b, m@pre, destinations) *
        IntArray::full(late, n@pre, latest) *
      IntArray::undef_seg(late, n@pre, 1000) *
        IntArray::full(off, n@pre, counts) *
      IntArray::undef_seg(off, n@pre, 1000) *
        IntArray::full(arr, n@pre, arrivals) *
      IntArray::undef_seg(arr, n@pre, 1000)
     */
    for (i = 0; i < m; ++i) {
        /*@ 0 <= Znth(i, destinations, 0) - 1 &&
            Znth(i, destinations, 0) - 1 < n@pre by local */
        ans = ans + arr[b[i] - 1] - t[i];
    }
    /*@ Assert
      exists final_dist,
n == n@pre && m == m@pre && d == d@pre && t == t@pre && a == a@pre && b == b@pre &&

      SightseeingMinimumTotal(n, m, k@pre, dist, times, origins, destinations, ans) &&
      IntArray::full(d, n - 1, final_dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations) *
      IntArray::undef_full(late, 1000) *
      IntArray::undef_full(off, 1000) *
      IntArray::undef_full(arr, 1000) *
      undef_data_at(&i, int) *
      undef_data_at(&j, int) *
      undef_data_at(&cur, int) *
      undef_data_at(&best, int) *
      undef_data_at(&pos, int) *
      undef_data_at(&cnt, int) *
      undef_data_at(&k, int)
     */
    return ans;
}
