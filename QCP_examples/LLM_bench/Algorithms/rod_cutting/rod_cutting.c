/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (RodCutOptimalRevenue : list Z -> Z -> Z -> Prop)
      (RodCutRevenueTable : list Z -> list Z -> Z -> Prop)
      (RodCutScanBest : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib */

int rod_cutting(const int *price, int n)
/*@ With (price_l : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(price_l) == n + 1 &&
      price_l[0] == 0 &&
      Forall(Z::le(0), price_l) && Forall(Z::ge(1000000), price_l) &&
      IntArray::full(price, n + 1, price_l)
    Ensure
      RodCutOptimalRevenue(price_l, n, __return) &&
      IntArray::full(price, n + 1, price_l)
 */
{
  int revenue[1001];

    int j;

    revenue[0] = 0;
    /*@ Inv Assert
        exists revenue_l,
        price == price@pre && n == n@pre &&
        n <= 1000 &&
        Forall(Z::le(0), price_l) && Forall(Z::ge(1000000), price_l) &&
        1 <= j && j <= n + 1 &&
        RodCutRevenueTable(price_l, revenue_l, j) &&
        (forall (k : Z),
          (0 <= k && k < j) =>
            (0 <= revenue_l[k] && revenue_l[k] <= k * 1000000)) &&
        IntArray::full(price, n + 1, price_l) *
        IntArray::seg(revenue, 0, j, revenue_l) *
        IntArray::undef_seg(revenue, j, 1001)
     */
    for (j = 1; j <= n; ++j) {
        int best = 0;
        int i;

        /*@ Inv Assert
            exists revenue_l,
            price == price@pre && n == n@pre &&
            n <= 1000 &&
            Forall(Z::le(0), price_l) && Forall(Z::ge(1000000), price_l) &&
            1 <= j && j <= n &&
            1 <= i && i <= j + 1 &&
            0 <= best && best <= j * 1000000 &&
            RodCutRevenueTable(price_l, revenue_l, j) &&
            RodCutScanBest(price_l, revenue_l, j, i, best) &&
            (forall (k : Z),
              (0 <= k && k < j) =>
                (0 <= revenue_l[k] && revenue_l[k] <= k * 1000000)) &&
            IntArray::full(price, n + 1, price_l) *
            IntArray::seg(revenue, 0, j, revenue_l) *
            IntArray::undef_seg(revenue, j, 1001)
         */
        for (i = 1; i <= j; ++i) {
            int candidate = price[i] + revenue[j - i];
            if (best < candidate) {
                best = candidate;
            }
        }
        revenue[j] = best;
    }

    int result = revenue[n];
    /*@ Assert
      price == price@pre && n == n@pre &&
      j == n + 1 &&
      RodCutOptimalRevenue(price_l, n@pre, result) &&
      IntArray::full(price, n@pre + 1, price_l) *
      IntArray::undef_full(revenue, 1001)
   */
  return result;
}
