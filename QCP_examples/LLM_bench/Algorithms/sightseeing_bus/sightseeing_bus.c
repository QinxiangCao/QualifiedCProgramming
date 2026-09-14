/*@ Extern Coq
      (SightseeingInputsBounded : Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (DestinationCounts : Z -> Z -> list Z -> list Z -> Prop)
      (SightseeingOptimalState : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
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
      (TracedBoosterProgress : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (SelectedDualCertificate : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (SelectedExchangeCertificate : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (OptimizedBusState : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (TravelSumPrefix : Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus.sightseeing_bus_lib */

int solve(int n, int m, int k, int *d, int *t, int *a, int *b,
          int *late, int *off, int *arr)
/*@ With (dist times origins destinations : list Z)
    Require
      0 <= k && k <= 100000 &&
      SightseeingInputsBounded(n, m, dist, times, origins, destinations) &&
      IntArray::full(d, n - 1, dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations) *
      IntArray::undef_full(late, n) *
      IntArray::undef_full(off, n) *
      IntArray::undef_full(arr, n)
    Ensure
      exists final_dist latest counts arrivals,
      SightseeingOptimalState(
        n, m, k@pre, dist, times, origins, destinations,
        final_dist, latest, arrivals, __return) &&
      DestinationCounts(n, m, destinations, counts) &&
      IntArray::full(d, n - 1, final_dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations) *
      IntArray::full(late, n, latest) *
      IntArray::full(off, n, counts) *
      IntArray::full(arr, n, arrivals)
*/
{
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
        late == late@pre && off == off@pre && arr == arr@pre &&
        0 <= i && i <= n@pre &&
        Zlength(latest_prefix) == i &&
        Zlength(counts_prefix) == i &&
        WorkspacesZeroPrefix(latest_prefix, counts_prefix, i) &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
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
        IntArray::seg(off, 0, i, counts_prefix) *
        IntArray::undef_seg(off, i, n@pre) *
        IntArray::undef_full(arr, n@pre)
     */
    for (i = 0; i < n; ++i) {
        late[i] = 0;
        off[i] = 0;
    }

    /*@ Assert
        exists latest counts,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        late == late@pre && off == off@pre && arr == arr@pre &&
        i == n@pre &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
        (forall (station : Z), 0 <= station && station < n@pre =>
          0 <= Znth(station, latest, 0) &&
          Znth(station, latest, 0) <= 100000 &&
          0 <= Znth(station, counts, 0) &&
          Znth(station, counts, 0) <= m@pre) &&
        PassengerAggregationPrefix(
          n@pre, m@pre, times, origins, destinations, 0, latest, counts) &&
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
        IntArray::full(off, n@pre, counts) *
        IntArray::undef_full(arr, n@pre)
     */

    /*@ Inv Assert
        exists latest counts,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        late == late@pre && off == off@pre && arr == arr@pre &&
        0 <= i && i <= m@pre &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
        (forall (station : Z), 0 <= station && station < n@pre =>
          0 <= Znth(station, latest, 0) &&
          Znth(station, latest, 0) <= 100000 &&
          0 <= Znth(station, counts, 0) &&
          Znth(station, counts, 0) <= i) &&
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
        IntArray::full(off, n@pre, counts) *
        IntArray::undef_full(arr, n@pre)
     */
    for (i = 0; i < m; ++i) {
        int x = a[i] - 1;
        int y = b[i] - 1;
        /*@ 0 <= x && x < n@pre &&
            x == Znth(i, origins, 0) - 1 by local */
        /*@ 0 <= y && y < n@pre &&
            y == Znth(i, destinations, 0) - 1 by local */
        if (late[x] < t[i]) {
            late[x] = t[i];
        }
        off[y] = off[y] + 1;
    }

    /*@ Assert
        exists latest counts,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        late == late@pre && off == off@pre && arr == arr@pre &&
        i == m@pre &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        StationSummaryState(
          n@pre, m@pre, times, origins, destinations, latest, counts) &&
        (forall (station : Z), 0 <= station && station < n@pre =>
          0 <= Znth(station, latest, 0) &&
          Znth(station, latest, 0) <= 100000 &&
          0 <= Znth(station, counts, 0) &&
          Znth(station, counts, 0) <= m@pre) &&
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
        IntArray::full(off, n@pre, counts) *
        IntArray::undef_full(arr, n@pre)
     */

    cur = 0;
    /*@ Inv Assert
        exists latest counts arrivals_prefix,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        late == late@pre && off == off@pre && arr == arr@pre &&
        0 <= i && i <= n@pre &&
        0 <= cur && cur <= 200000 &&
        Zlength(arrivals_prefix) == i &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        StationSummaryState(
          n@pre, m@pre, times, origins, destinations, latest, counts) &&
        (forall (station : Z), 0 <= station && station < n@pre =>
          0 <= Znth(station, latest, 0) &&
          Znth(station, latest, 0) <= 100000 &&
          0 <= Znth(station, counts, 0) &&
          Znth(station, counts, 0) <= m@pre) &&
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
        IntArray::full(off, n@pre, counts) *
        IntArray::seg(arr, 0, i, arrivals_prefix) *
        IntArray::undef_seg(arr, i, n@pre)
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

    /*@ Assert
        exists latest counts arrivals,
        n == n@pre && m == m@pre && k == k@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        late == late@pre && off == off@pre && arr == arr@pre &&
        i == n@pre && 0 <= cur && cur <= 200000 &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
        0 <= k@pre && k@pre <= 100000 &&
        CanonicalBusState(
          n@pre, m@pre, times, origins, destinations,
          dist, latest, counts, arrivals) &&
        Zlength(arrivals) == n@pre &&
        (forall (station : Z), 0 <= station && station < n@pre =>
          0 <= Znth(station, arrivals, 0) &&
          Znth(station, arrivals, 0) <= 200000) &&
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
        IntArray::full(off, n@pre, counts) *
        IntArray::full(arr, n@pre, arrivals)
     */

    /*@ Inv Assert
        exists current_dist latest counts arrivals,
        n == n@pre && m == m@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        late == late@pre && off == off@pre && arr == arr@pre &&
        0 <= k && k <= k@pre && k@pre <= 100000 &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
        Zlength(current_dist) == n@pre - 1 &&
        Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
        Zlength(arrivals) == n@pre &&
        (forall (edge : Z), 0 <= edge && edge < n@pre - 1 =>
          0 <= Znth(edge, current_dist, 0) &&
          Znth(edge, current_dist, 0) <= 100) &&
        (forall (station : Z), 0 <= station && station < n@pre =>
          0 <= Znth(station, latest, 0) &&
          Znth(station, latest, 0) <= 100000 &&
          0 <= Znth(station, counts, 0) &&
          Znth(station, counts, 0) <= m@pre &&
          0 <= Znth(station, arrivals, 0) &&
          Znth(station, arrivals, 0) <= 200000) &&
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
        IntArray::full(off, n@pre, counts) *
        IntArray::full(arr, n@pre, arrivals)
     */
    while (k > 0) {
        best = 0;
        pos = -1;
        /*@ Inv Assert
            exists current_dist latest counts arrivals,
            n == n@pre && m == m@pre &&
            d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
            late == late@pre && off == off@pre && arr == arr@pre &&
            0 < k && k <= k@pre && k@pre <= 100000 &&
            0 <= i && i <= n@pre - 1 &&
            0 <= best && best <= m@pre &&
            -1 <= pos && pos < i &&
            SightseeingInputsBounded(
              n@pre, m@pre, dist, times, origins, destinations) &&
            Zlength(current_dist) == n@pre - 1 &&
            Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
            Zlength(arrivals) == n@pre &&
            (forall (edge : Z), 0 <= edge && edge < n@pre - 1 =>
              0 <= Znth(edge, current_dist, 0) &&
              Znth(edge, current_dist, 0) <= 100) &&
            (forall (station : Z), 0 <= station && station < n@pre =>
              0 <= Znth(station, latest, 0) &&
              Znth(station, latest, 0) <= 100000 &&
              0 <= Znth(station, counts, 0) &&
              Znth(station, counts, 0) <= m@pre &&
              0 <= Znth(station, arrivals, 0) &&
              Znth(station, arrivals, 0) <= 200000) &&
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
            IntArray::full(off, n@pre, counts) *
            IntArray::full(arr, n@pre, arrivals)
         */
        for (i = 0; i + 1 < n; ++i) {
            if (d[i] > 0) {
                cnt = 0;
                /*@ Inv Assert
                    exists current_dist latest counts arrivals,
                    n == n@pre && m == m@pre &&
                    d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
                    late == late@pre && off == off@pre && arr == arr@pre &&
                    0 < k && k <= k@pre && k@pre <= 100000 &&
                    0 <= i && i < n@pre - 1 &&
                    i + 1 <= j && j <= n@pre &&
                    0 <= cnt && cnt <= m@pre &&
                    0 <= best && best <= m@pre &&
                    -1 <= pos && pos < i &&
                    0 < Znth(i, current_dist, 0) &&
                    SightseeingInputsBounded(
                      n@pre, m@pre, dist, times, origins, destinations) &&
                    Zlength(current_dist) == n@pre - 1 &&
                    Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
                    Zlength(arrivals) == n@pre &&
                    (forall (edge : Z), 0 <= edge && edge < n@pre - 1 =>
                      0 <= Znth(edge, current_dist, 0) &&
                      Znth(edge, current_dist, 0) <= 100) &&
                    (forall (station : Z), 0 <= station && station < n@pre =>
                      0 <= Znth(station, latest, 0) &&
                      Znth(station, latest, 0) <= 100000 &&
                      0 <= Znth(station, counts, 0) &&
                      Znth(station, counts, 0) <= m@pre &&
                      0 <= Znth(station, arrivals, 0) &&
                      Znth(station, arrivals, 0) <= 200000) &&
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
                    IntArray::full(off, n@pre, counts) *
                    IntArray::full(arr, n@pre, arrivals)
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
                    late == late@pre && off == off@pre && arr == arr@pre &&
                    0 < k && k <= k@pre && k@pre <= 100000 &&
                    0 <= i && i < n@pre - 1 &&
                    0 <= cnt && cnt <= m@pre &&
                    0 <= best && best <= m@pre &&
                    -1 <= pos && pos < i &&
                    i + 1 <= j && j <= n@pre &&
                    0 < Znth(i, current_dist, 0) &&
                    SightseeingInputsBounded(
                      n@pre, m@pre, dist, times, origins, destinations) &&
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
                    IntArray::full(off, n@pre, counts) *
                    IntArray::full(arr, n@pre, arrivals)
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
            late == late@pre && off == off@pre && arr == arr@pre &&
            0 < k && k <= k@pre && k@pre <= 100000 &&
            0 <= pos && pos < n@pre - 1 &&
            0 < best && best <= m@pre &&
            pos + 1 <= i && i <= n@pre &&
            SightseeingInputsBounded(
              n@pre, m@pre, dist, times, origins, destinations) &&
            Zlength(old_dist) == n@pre - 1 &&
            Zlength(new_dist) == n@pre - 1 &&
            Zlength(old_arrivals) == n@pre &&
            Zlength(new_arrivals) == n@pre &&
            Zlength(latest) == n@pre && Zlength(counts) == n@pre &&
            (forall (edge : Z), 0 <= edge && edge < n@pre - 1 =>
              0 <= Znth(edge, new_dist, 0) &&
              Znth(edge, new_dist, 0) <= 100) &&
            (forall (station : Z), 0 <= station && station < n@pre =>
              0 <= Znth(station, latest, 0) &&
              Znth(station, latest, 0) <= 100000 &&
              0 <= Znth(station, counts, 0) &&
              Znth(station, counts, 0) <= m@pre &&
              0 <= Znth(station, new_arrivals, 0) &&
              Znth(station, new_arrivals, 0) <= 200000) &&
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
            IntArray::full(off, n@pre, counts) *
            IntArray::full(arr, n@pre, new_arrivals)
         */
        for (i = pos + 1; i < n; ++i) {
            arr[i] = arr[i] - 1;
            if (arr[i] < late[i]) {
                break;
            }
        }

        /*@ Assert
            exists old_dist old_arrivals new_dist new_arrivals latest counts,
            n == n@pre && m == m@pre &&
            d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
            late == late@pre && off == off@pre && arr == arr@pre &&
            0 < k && k <= k@pre && k@pre <= 100000 &&
            0 <= pos && pos < n@pre - 1 &&
            0 < best && best <= m@pre &&
            pos + 1 <= i && i <= n@pre &&
            Zlength(new_dist) == n@pre - 1 &&
            Zlength(new_arrivals) == n@pre &&
            SightseeingInputsBounded(
              n@pre, m@pre, dist, times, origins, destinations) &&
            BoosterProgress(
              n@pre, m@pre, k@pre, k,
              dist, times, origins, destinations,
              old_dist, latest, counts, old_arrivals) &&
            BestBoostChoice(
              n@pre, old_dist, counts, latest, old_arrivals, best, pos) &&
            ArrivalRepairOutcome(
              n@pre, old_dist, old_arrivals,
              new_dist, new_arrivals, latest, pos) &&
            undef_data_at(&j, int) *
            undef_data_at(&cur, int) *
            undef_data_at(&cnt, int) *
            undef_data_at(&ans, int) *
            IntArray::full(d, n@pre - 1, new_dist) *
            IntArray::full(t, m@pre, times) *
            IntArray::full(a, m@pre, origins) *
            IntArray::full(b, m@pre, destinations) *
            IntArray::full(late, n@pre, latest) *
            IntArray::full(off, n@pre, counts) *
            IntArray::full(arr, n@pre, new_arrivals)
         */

        /*@ Assert
            exists old_dist old_arrivals new_dist new_arrivals latest counts,
            n == n@pre && m == m@pre &&
            d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
            late == late@pre && off == off@pre && arr == arr@pre &&
            0 < k && k <= k@pre && k@pre <= 100000 &&
            0 <= pos && pos < n@pre - 1 &&
            0 < best && best <= m@pre &&
            pos + 1 <= i && i <= n@pre &&
            Zlength(new_dist) == n@pre - 1 &&
            Zlength(new_arrivals) == n@pre &&
            SightseeingInputsBounded(
              n@pre, m@pre, dist, times, origins, destinations) &&
            BoosterProgress(
              n@pre, m@pre, k@pre, k,
              dist, times, origins, destinations,
              old_dist, latest, counts, old_arrivals) &&
            BestBoostChoice(
              n@pre, old_dist, counts, latest, old_arrivals, best, pos) &&
            SelectedExchangeCertificate(
              n@pre, m@pre, k@pre, k,
              dist, times, origins, destinations,
              old_dist, latest, counts, old_arrivals, best) &&
            ArrivalRepairOutcome(
              n@pre, old_dist, old_arrivals,
              new_dist, new_arrivals, latest, pos) &&
            undef_data_at(&j, int) *
            undef_data_at(&cur, int) *
            undef_data_at(&cnt, int) *
            undef_data_at(&ans, int) *
            IntArray::full(d, n@pre - 1, new_dist) *
            IntArray::full(t, m@pre, times) *
            IntArray::full(a, m@pre, origins) *
            IntArray::full(b, m@pre, destinations) *
            IntArray::full(late, n@pre, latest) *
            IntArray::full(off, n@pre, counts) *
            IntArray::full(arr, n@pre, new_arrivals)
         */
        k = k - 1;
    }

    ans = 0;
    /*@ Inv Assert
        exists final_dist latest counts arrivals,
        n == n@pre && m == m@pre &&
        d == d@pre && t == t@pre && a == a@pre && b == b@pre &&
        late == late@pre && off == off@pre && arr == arr@pre &&
        0 <= k && k <= k@pre && k@pre <= 100000 &&
        0 <= i && i <= m@pre &&
        0 <= ans && ans <= i * 200000 && ans <= 2000000000 &&
        SightseeingInputsBounded(
          n@pre, m@pre, dist, times, origins, destinations) &&
        OptimizedBusState(
          n@pre, m@pre, k@pre,
          dist, times, origins, destinations,
          final_dist, latest, counts, arrivals) &&
        Zlength(arrivals) == n@pre &&
        (forall (station : Z), 0 <= station && station < n@pre =>
          0 <= Znth(station, arrivals, 0) &&
          Znth(station, arrivals, 0) <= 200000) &&
        (forall (passenger : Z), 0 <= passenger && passenger < m@pre =>
          0 <= Znth(passenger, times, 0) &&
          Znth(passenger, times, 0) <= 100000 &&
          1 <= Znth(passenger, destinations, 0) &&
          Znth(passenger, destinations, 0) <= n@pre) &&
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
        IntArray::full(off, n@pre, counts) *
        IntArray::full(arr, n@pre, arrivals)
     */
    for (i = 0; i < m; ++i) {
        /*@ 0 <= Znth(i, destinations, 0) - 1 &&
            Znth(i, destinations, 0) - 1 < n@pre by local */
        ans = ans + arr[b[i] - 1] - t[i];
    }
    return ans;
}
