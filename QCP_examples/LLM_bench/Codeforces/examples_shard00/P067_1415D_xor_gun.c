/* Codeforces 1415/D - XOR-gun */
// #include <stdio.h>
// #include <limits.h>
/* QCP_INSERT_BEGIN:P067_1415D_xor_gun.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (NoEqualBitTriplePrefix : list Z -> Z -> Prop)
      (BitScanState : Z -> Z -> Z -> Prop)
      (PrefixXorTable : list Z -> list Z -> Z -> Prop)
      (BruteSearchState : list Z -> Z -> Z -> Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P067_1415D_xor_gun_lib */
/* QCP_INSERT_END:P067_1415D_xor_gun.support */
static int solver(const int *a, int n) /* QCP_INSERT_BEGIN:P067_1415D_xor_gun.contract */

/*@ With (values : list Z)
    Require
      2 <= Zlength(values) && Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 1000000000)) &&
      (forall i, (0 <= i && i + 1 < Zlength(values)) => values[i] <= values[i + 1]) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) && IntArray::full(a, n, values)
*/
/* QCP_INSERT_END:P067_1415D_xor_gun.contract */
{
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          n@pre == Zlength(values) &&
          2 <= n@pre && n@pre <= 100000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 1000000000)) &&
          (forall k, (0 <= k && k + 1 < n@pre) =>
            values[k] <= values[k + 1]) &&
          1 <= i && i <= n@pre - 1 &&
          NoEqualBitTriplePrefix(values, i) &&
          IntArray::full(a, n@pre, values)
    */
    for (int i = 1; i + 1 < n; ++i)
    {
        int x = a[i - 1], y = a[i], z = a[i + 1], bx = 0, by_count = 0, bz = 0;
        /*@ Inv Assert
              exists vx vy vz,
                a == a@pre && n == n@pre &&
                n@pre == Zlength(values) &&
                2 <= n@pre && n@pre <= 100000 &&
                (forall k, (0 <= k && k < n@pre) =>
                  (1 <= values[k] && values[k] <= 1000000000)) &&
                (forall k, (0 <= k && k + 1 < n@pre) =>
                  values[k] <= values[k + 1]) &&
                1 <= i && i + 1 < n@pre &&
                vx == values[i - 1] && vy == values[i] && vz == values[i + 1] &&
                y == vy && z == vz && by_count == 0 && bz == 0 &&
                1 <= vx && vx <= 1000000000 &&
                1 <= vy && vy <= 1000000000 &&
                1 <= vz && vz <= 1000000000 &&
                1 <= x && x <= vx && 0 <= bx && bx <= 30 &&
                BitScanState(vx, x, bx) &&
                NoEqualBitTriplePrefix(values, i) &&
                IntArray::full(a, n@pre, values)
        */
        while (x > 1)
        {
            x = x >> 1;
            ++bx;
        }
        /*@ Inv Assert
              exists vx vy vz,
                a == a@pre && n == n@pre &&
                n@pre == Zlength(values) &&
                2 <= n@pre && n@pre <= 100000 &&
                (forall k, (0 <= k && k < n@pre) =>
                  (1 <= values[k] && values[k] <= 1000000000)) &&
                (forall k, (0 <= k && k + 1 < n@pre) =>
                  values[k] <= values[k + 1]) &&
                1 <= i && i + 1 < n@pre &&
                vx == values[i - 1] && vy == values[i] && vz == values[i + 1] &&
                x == 1 && z == vz && bz == 0 &&
                1 <= vx && vx <= 1000000000 &&
                1 <= vy && vy <= 1000000000 &&
                1 <= vz && vz <= 1000000000 &&
                0 <= bx && bx <= 30 && BitScanState(vx, x, bx) &&
                1 <= y && y <= vy && 0 <= by_count && by_count <= 30 &&
                BitScanState(vy, y, by_count) &&
                NoEqualBitTriplePrefix(values, i) &&
                IntArray::full(a, n@pre, values)
        */
        while (y > 1)
        {
            y = y >> 1;
            ++by_count;
        }
        /*@ Inv Assert
              exists vx vy vz,
                a == a@pre && n == n@pre &&
                n@pre == Zlength(values) &&
                2 <= n@pre && n@pre <= 100000 &&
                (forall k, (0 <= k && k < n@pre) =>
                  (1 <= values[k] && values[k] <= 1000000000)) &&
                (forall k, (0 <= k && k + 1 < n@pre) =>
                  values[k] <= values[k + 1]) &&
                1 <= i && i + 1 < n@pre &&
                vx == values[i - 1] && vy == values[i] && vz == values[i + 1] &&
                x == 1 && y == 1 &&
                1 <= vx && vx <= 1000000000 &&
                1 <= vy && vy <= 1000000000 &&
                1 <= vz && vz <= 1000000000 &&
                0 <= bx && bx <= 30 && BitScanState(vx, x, bx) &&
                0 <= by_count && by_count <= 30 &&
                BitScanState(vy, y, by_count) &&
                1 <= z && z <= vz && 0 <= bz && bz <= 30 &&
                BitScanState(vz, z, bz) &&
                NoEqualBitTriplePrefix(values, i) &&
                IntArray::full(a, n@pre, values)
        */
        while (z > 1)
        {
            z = z >> 1;
            ++bz;
        }
        if (bx == by_count && by_count == bz)
            return 1;
    }
    if (n > 60)
        return 1;
    int pre[64] = {0};
    /*@ Inv Assert
          exists prefixes,
            a == a@pre && n == n@pre &&
            n@pre == Zlength(values) &&
            2 <= n@pre && n@pre <= 60 &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= values[k] && values[k] <= 1000000000)) &&
            (forall k, (0 <= k && k + 1 < n@pre) =>
              values[k] <= values[k + 1]) &&
            0 <= i && i <= n@pre &&
            PrefixXorTable(values, prefixes, i) &&
            IntArray::full(a, n@pre, values) *
            IntArray::full(pre, 64, prefixes)
    */
    for (int i = 0; i < n; ++i)
        pre[i + 1] = pre[i] ^ a[i];
    int ans = 2147483647;
    /*@ Inv Assert
          exists prefixes,
            a == a@pre && n == n@pre &&
            n@pre == Zlength(values) &&
            2 <= n@pre && n@pre <= 60 &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= values[k] && values[k] <= 1000000000)) &&
            (forall k, (0 <= k && k + 1 < n@pre) =>
              values[k] <= values[k + 1]) &&
            0 <= l && l <= n@pre &&
            0 <= ans && ans <= 2147483647 &&
            PrefixXorTable(values, prefixes, n@pre) &&
            BruteSearchState(values, l, l, l + 1, ans) &&
            IntArray::full(a, n@pre, values) *
            IntArray::full(pre, 64, prefixes)
    */
    for (int l = 0; l < n; ++l)
        /*@ Inv Assert
              exists prefixes,
                a == a@pre && n == n@pre &&
                n@pre == Zlength(values) &&
                2 <= n@pre && n@pre <= 60 &&
                (forall k, (0 <= k && k < n@pre) =>
                  (1 <= values[k] && values[k] <= 1000000000)) &&
                (forall k, (0 <= k && k + 1 < n@pre) =>
                  values[k] <= values[k + 1]) &&
                0 <= l && l < n@pre &&
                l <= mid && mid <= n@pre - 1 &&
                0 <= ans && ans <= 2147483647 &&
                PrefixXorTable(values, prefixes, n@pre) &&
                BruteSearchState(values, l, mid, mid + 1, ans) &&
                IntArray::full(a, n@pre, values) *
                IntArray::full(pre, 64, prefixes)
        */
        for (int mid = l; mid + 1 < n; ++mid)
            /*@ Inv Assert
                  exists prefixes,
                    a == a@pre && n == n@pre &&
                    n@pre == Zlength(values) &&
                    2 <= n@pre && n@pre <= 60 &&
                    (forall k, (0 <= k && k < n@pre) =>
                      (1 <= values[k] && values[k] <= 1000000000)) &&
                    (forall k, (0 <= k && k + 1 < n@pre) =>
                      values[k] <= values[k + 1]) &&
                    0 <= l && l <= mid && mid + 1 < n@pre &&
                    mid + 1 <= r && r <= n@pre &&
                    0 <= ans && ans <= 2147483647 &&
                    PrefixXorTable(values, prefixes, n@pre) &&
                    BruteSearchState(values, l, mid, r, ans) &&
                    IntArray::full(a, n@pre, values) *
                    IntArray::full(pre, 64, prefixes)
            */
            for (int r = mid + 1; r < n; ++r)
                if ((pre[mid + 1] ^ pre[l]) > (pre[r + 1] ^ pre[mid + 1]) && r - l - 1 < ans)
                    ans = r - l - 1;
    return ans == 2147483647 ? -1 : ans;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     int a[100005];
//     for (int i = 0; i < n; ++i)
//         scanf("%d", &a[i]);
//     printf("%d\n", solver(a, n));
//     return 0;
// }
