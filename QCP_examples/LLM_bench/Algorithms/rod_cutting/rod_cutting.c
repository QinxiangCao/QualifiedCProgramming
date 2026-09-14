/*@ Extern Coq
      (RodCutOptimalRevenue : list Z -> Z -> Z -> Prop)
      (RodCutRevenueTable : list Z -> list Z -> Z -> Prop)
      (RodCutScanBest : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib */

int rod_cutting(const int *price, int *revenue, int n)
/*@ With (price_l : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(price_l) == n + 1 &&
      price_l[0] == 0 &&
      (forall (k : Z),
        (0 <= k && k <= n) => (0 <= price_l[k] && price_l[k] <= 1000000)) &&
      IntArray::full(price, n + 1, price_l) *
      IntArray::undef_full(revenue, n + 1)
    Ensure
      exists revenue_l,
      Zlength(revenue_l) == n + 1 &&
      RodCutRevenueTable(price_l, revenue_l, n + 1) &&
      __return == revenue_l[n] &&
      (forall (k : Z),
        (0 <= k && k < n + 1) =>
          (0 <= revenue_l[k] && revenue_l[k] <= k * 1000000)) &&
      IntArray::full(price, n + 1, price_l) *
      IntArray::full(revenue, n + 1, revenue_l)
 */
{
    int j;

    revenue[0] = 0;
    /*@ Inv Assert
        exists revenue_l,
        price == price@pre && revenue == revenue@pre && n == n@pre &&
        0 <= n@pre && n@pre <= 1000 &&
        Zlength(price_l) == n@pre + 1 &&
        price_l[0] == 0 &&
        (forall (k : Z),
          (0 <= k && k <= n@pre) =>
            (0 <= price_l[k] && price_l[k] <= 1000000)) &&
        1 <= j && j <= n@pre + 1 &&
        Zlength(revenue_l) == j &&
        RodCutRevenueTable(price_l, revenue_l, j) &&
        (forall (k : Z),
          (0 <= k && k < j) =>
            (0 <= revenue_l[k] && revenue_l[k] <= k * 1000000)) &&
        IntArray::full(price, n@pre + 1, price_l) *
        IntArray::seg(revenue, 0, j, revenue_l) *
        IntArray::undef_seg(revenue, j, n@pre + 1)
     */
    for (j = 1; j <= n; ++j) {
        int best = 0;
        int i;

        /*@ Inv Assert
            exists revenue_l,
            price == price@pre && revenue == revenue@pre && n == n@pre &&
            0 <= n@pre && n@pre <= 1000 &&
            Zlength(price_l) == n@pre + 1 &&
            price_l[0] == 0 &&
            (forall (k : Z),
              (0 <= k && k <= n@pre) =>
                (0 <= price_l[k] && price_l[k] <= 1000000)) &&
            1 <= j && j <= n@pre &&
            1 <= i && i <= j + 1 &&
            0 <= best && best <= j * 1000000 &&
            Zlength(revenue_l) == j &&
            RodCutRevenueTable(price_l, revenue_l, j) &&
            RodCutScanBest(price_l, revenue_l, j, i, best) &&
            (forall (k : Z),
              (0 <= k && k < j) =>
                (0 <= revenue_l[k] && revenue_l[k] <= k * 1000000)) &&
            IntArray::full(price, n@pre + 1, price_l) *
            IntArray::seg(revenue, 0, j, revenue_l) *
            IntArray::undef_seg(revenue, j, n@pre + 1)
         */
        for (i = 1; i <= j; ++i) {
            /*@ 0 <= j - i && j - i < j by local */
            int candidate = price[i] + revenue[j - i];
            if (best < candidate) {
                best = candidate;
            }
        }
        revenue[j] = best;
    }

    return revenue[n];
}
