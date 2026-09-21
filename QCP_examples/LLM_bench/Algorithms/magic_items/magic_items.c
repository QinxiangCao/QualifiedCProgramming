/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (ListLib::sum : list Z -> Z)
      (MaximumMagicRevenue : Z -> list Z -> list Z -> Z -> Prop)
      (UnconstrainedRevenue : Z -> list Z -> list Z -> Z)
      (FreeCash : Z -> list Z -> list Z -> Z)
      (MinimumSacrifice : Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.magic_items.magic_items_lib */

int magic_items(int n, int c, int *a, int *b)
/*@ With (al bl : list Z)
    Require
      1 <= n && n <= 1000 && 1 <= c && c <= 5000 &&
      Forall(Z::le(1), al) && Forall2(Z::le, al, bl) &&
      Forall(Z::ge(10000), bl) &&
      IntArray::full(a, n, al) * IntArray::full(b, n, bl)
    Ensure
      MaximumMagicRevenue(c, al, bl, __return) &&
      IntArray::full(a, n, al) * IntArray::full(b, n, bl)
 */
{
    int dp[5001];
    int s = 0;
    int t = 0;
    int ans = 0;

    /*@ Inv Assert
      a == a@pre && b == b@pre && n == n@pre && c == c@pre &&
      1 <= n && n <= 1000 && 1 <= c && c <= 5000 &&
      0 <= i && i <= n &&
      Forall(Z::le(1), al) && Forall2(Z::le, al, bl) && Forall(Z::ge(10000), bl) &&
      t == ListLib::sum(sublist(0, i, al)) &&
      s == FreeCash(c, sublist(0, i, al), sublist(0, i, bl)) &&
      ans == UnconstrainedRevenue(c, sublist(0, i, al), sublist(0, i, bl)) &&
      0 <= t && t <= 10000 * i && 0 <= s && s <= 10000 * i &&
      0 <= ans && ans <= 10000 * i &&
      IntArray::full(a, n, al) * IntArray::full(b, n, bl) * IntArray::undef_full(dp, 5001)
     */
    for (int i = 0; i < n; ++i) {
        int d = b[i] - a[i] - c;
        t += a[i];
        ans += a[i];
        if (d > 0) {
            ans += d;
        } else {
            s += a[i];
        }
    }

    if (t < c) {
        return t;
    }
    if (s >= c) {
        return ans;
    }

    int k = c - s;
    dp[0] = 0;
    /*@ Inv Assert exists dl,
      a == a@pre && b == b@pre && n == n@pre && c == c@pre &&
      1 <= n && n <= 1000 && 1 <= c && c <= 5000 &&
      1 <= k && k <= c && 1 <= j && j <= k + 1 &&
      k == c - FreeCash(c, al, bl) && c <= ListLib::sum(al) &&
      ans == UnconstrainedRevenue(c, al, bl) && 0 <= ans && ans <= 10000000 &&
      Forall(Z::le(1), al) && Forall2(Z::le, al, bl) && Forall(Z::ge(10000), bl) &&
      Znth(0, dl, 0) == 0 && Forall(eq(10000001), sublist(1, j, dl)) &&
      IntArray::full(a, n, al) * IntArray::full(b, n, bl) * has_int_permission(&s) * has_int_permission(&t) *
      IntArray::seg(dp, 0, j, dl) * IntArray::undef_seg(dp, j, 5001)
     */
    for (int j = 1; j <= k; ++j) {
        dp[j] = 10000001;
    }
    /*@ Inv Assert exists dl,
      a == a@pre && b == b@pre && n == n@pre && c == c@pre &&
      1 <= n && n <= 1000 && 1 <= c && c <= 5000 &&
      1 <= k && k <= c && 0 <= i && i <= n &&
      k == c - FreeCash(c, al, bl) && c <= ListLib::sum(al) &&
      ans == UnconstrainedRevenue(c, al, bl) && 0 <= ans && ans <= 10000000 &&
      Forall(Z::le(1), al) && Forall2(Z::le, al, bl) && Forall(Z::ge(10000), bl) &&
      Forall(Z::le(0), dl) && Forall(Z::ge(10000001), dl) &&
      (forall (q : Z), 0 <= q && q <= k => MinimumSacrifice(c, al, bl, i, q, Znth(q, dl, 0))) &&
      IntArray::full(a, n, al) * IntArray::full(b, n, bl) * has_int_permission(&s) * has_int_permission(&t) *
      IntArray::full(dp, k + 1, dl) * IntArray::undef_seg(dp, k + 1, 5001)
     */
    for (int i = 0; i < n; ++i) {
        int d = b[i] - a[i] - c;
        if (d > 0) {
            /*@ Inv Assert exists dl,
              a == a@pre && b == b@pre && n == n@pre && c == c@pre &&
              1 <= n && n <= 1000 && 1 <= c && c <= 5000 &&
              1 <= k && k <= c && 0 <= i && i < n && 0 <= j && j <= k && 1 <= al[i] &&
              d == Znth(i, bl, 0) - Znth(i, al, 0) - c && 0 < d &&
              k == c - FreeCash(c, al, bl) && c <= ListLib::sum(al) &&
              ans == UnconstrainedRevenue(c, al, bl) && 0 <= ans && ans <= 10000000 &&
              Forall(Z::le(1), al) && Forall2(Z::le, al, bl) && Forall(Z::ge(10000), bl) &&
              Forall(Z::le(0), dl) && Forall(Z::ge(10000001), dl) &&
              (forall (q : Z), 0 <= q && q <= j => MinimumSacrifice(c, al, bl, i, q, Znth(q, dl, 0))) &&
              (forall (q : Z), j < q && q <= k => MinimumSacrifice(c, al, bl, i + 1, q, Znth(q, dl, 0))) &&
              IntArray::full(a, n, al) * IntArray::full(b, n, bl) * has_int_permission(&s) * has_int_permission(&t) *
              IntArray::full(dp, k + 1, dl) * IntArray::undef_seg(dp, k + 1, 5001)
             */
            for (int j = k; j > 0; --j) {
                int r = j - a[i];
                if (r < 0) {
                    r = 0;
                }
                int v = dp[r] + d;
                if (v < dp[j]) {
                    dp[j] = v;
                }
            }
        }
    }
    int result = ans - dp[k];
    /*@ Assert
      a == a@pre && b == b@pre && n == n@pre && c == c@pre &&
      MaximumMagicRevenue(c, al, bl, result) &&
      IntArray::full(a, n, al) * IntArray::full(b, n, bl) *
      IntArray::undef_full(dp, 5001) *
      has_int_permission(&s) * has_int_permission(&t) *
      has_int_permission(&ans) * has_int_permission(&k)
     */
    return result;
}
