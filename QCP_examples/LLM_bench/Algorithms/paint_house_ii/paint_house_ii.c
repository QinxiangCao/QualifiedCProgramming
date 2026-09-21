
#include "int_ptr_array2_def.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (eq : {A} -> A -> A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (PaintHouseIIRowMinima : list (list Z) -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PaintHouseIIColorMinima : list (list Z) -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PaintHouseIICompletedMinima : list (list Z) -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PaintHouseIIOptimalCost : list (list Z) -> Z -> Z -> Z -> Prop)
      (PaintHouseIIPrevSelection : Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.paint_house_ii.paint_house_ii_lib */

int paint_house_ii(int **costs, int n, int k)
/*@ With (costs_l : list (list Z))
    Require
      1 <= n && n <= 10000 &&
      2 <= k && k <= 1000 &&
      n * k <= 1000000 &&
      Zlength(costs_l) == n &&
      Forall(eq(k), map(Zlength, costs_l)) &&
      Forall(Forall(Z::le(0)), costs_l) && Forall(Forall(Z::ge(10000)), costs_l) &&
      IntPtrArray2::full(costs, n, costs_l)
    Ensure
      PaintHouseIIOptimalCost(costs_l, n, k, __return) &&
      IntPtrArray2::full(costs, n, costs_l)
 */
{
  int min1 = 0;
  int min2 = 0;
  int min1_color = -1;

  /*@ Inv Assert
      costs == costs@pre && n == n@pre && k == k@pre &&
      1 <= n@pre && n@pre <= 10000 &&
      2 <= k@pre && k@pre <= 1000 &&
      n@pre * k@pre <= 1000000 &&
      Zlength(costs_l) == n@pre &&
      Forall(eq(k@pre), map(Zlength, costs_l)) &&
      Forall(Forall(Z::le(0)), costs_l) && Forall(Forall(Z::ge(10000)), costs_l) &&
      0 <= i && i <= n@pre &&
      -1 <= min1_color && min1_color < k@pre &&
      0 <= min1 && min1 <= 1000000000 &&
      0 <= min2 && min2 <= 1000000000 &&
      0 <= i && i <= n@pre && PaintHouseIIRowMinima(costs_l, n@pre, k@pre, i, min1, min2, min1_color) &&
      IntPtrArray2::full(costs@pre, n@pre, costs_l)
   */
  for (int i = 0; i < n; ++i) {
    int new_min1 = 1000000000;
    int new_min2 = 1000000000;
    int new_min1_color = -1;

    /*@ Inv Assert
        exists row_ptr,
        costs == costs@pre && n == n@pre && k == k@pre &&
        1 <= n@pre && n@pre <= 10000 &&
        2 <= k@pre && k@pre <= 1000 &&
        n@pre * k@pre <= 1000000 &&
        Zlength(costs_l) == n@pre &&
        Forall(eq(k@pre), map(Zlength, costs_l)) &&
        Forall(Forall(Z::le(0)), costs_l) && Forall(Forall(Z::ge(10000)), costs_l) &&
        Zlength(costs_l[i]) == k@pre &&
        0 <= i && i < n@pre &&
        0 <= c && c <= k@pre &&
        -1 <= min1_color && min1_color < k@pre &&
        0 <= min1 && min1 <= 1000000000 &&
        0 <= min2 && min2 <= 1000000000 &&
        -1 <= new_min1_color && new_min1_color < k@pre &&
        0 <= new_min1 && new_min1 <= 1000000000 &&
        0 <= new_min2 && new_min2 <= 1000000000 &&
        0 <= i && i <= n@pre && PaintHouseIIRowMinima(costs_l, n@pre, k@pre, i, min1, min2, min1_color) &&
        0 <= i && i < n@pre && 0 <= c && c <= k@pre && PaintHouseIIColorMinima(costs_l, n@pre, k@pre, i, c, min1, min2, min1_color, new_min1, new_min2, new_min1_color) &&
        IntPtrArray2::missing_i(costs@pre, n@pre, i, row_ptr, costs_l) *
        data_at(costs@pre + (i * sizeof(int *)), int *, row_ptr) *
        IntArray::full(row_ptr, Zlength(costs_l[i]), costs_l[i])
     */
    for (int c = 0; c < k; ++c) {
      int prev;
      if (c == min1_color) {
        prev = min2;
      } else {
        prev = min1;
      }

      /*@ Assert
        exists row_ptr,
        costs == costs@pre && n == n@pre && k == k@pre &&
        1 <= n@pre && n@pre <= 10000 &&
        2 <= k@pre && k@pre <= 1000 &&
        n@pre * k@pre <= 1000000 &&
        Zlength(costs_l) == n@pre &&
        Forall(eq(k@pre), map(Zlength, costs_l)) &&
        Forall(Forall(Z::le(0)), costs_l) && Forall(Forall(Z::ge(10000)), costs_l) &&
        Zlength(costs_l[i]) == k@pre &&
        0 <= i && i < n@pre &&
        0 <= c && c < k@pre &&
        0 <= prev && prev <= 1000000000 &&
        0 <= costs_l[i][c] && costs_l[i][c] <= 10000 &&
        prev + costs_l[i][c] <= 1000000000 &&
        PaintHouseIIPrevSelection(min1, min2, min1_color, c, prev) &&
        0 <= i && i <= n@pre && PaintHouseIIRowMinima(costs_l, n@pre, k@pre, i, min1, min2, min1_color) &&
        0 <= i && i < n@pre && 0 <= c && c <= k@pre && PaintHouseIIColorMinima(costs_l, n@pre, k@pre, i, c, min1, min2, min1_color, new_min1, new_min2, new_min1_color) &&
        IntPtrArray2::missing_i(costs@pre, n@pre, i, row_ptr, costs_l) *
        data_at(costs@pre + (i * sizeof(int *)), int *, row_ptr) *
        IntArray::full(row_ptr, Zlength(costs_l[i]), costs_l[i])
       */
      int total = prev + costs[i][c];

      if (total < new_min1) {
        new_min2 = new_min1;
        new_min1 = total;
        new_min1_color = c;
      } else {
        if (total < new_min2) {
          new_min2 = total;
        }
      }

      /*@ Assert
        exists row_ptr,
        costs == costs@pre && n == n@pre && k == k@pre &&
        1 <= n@pre && n@pre <= 10000 &&
        2 <= k@pre && k@pre <= 1000 &&
        n@pre * k@pre <= 1000000 &&
        Zlength(costs_l) == n@pre &&
        Forall(eq(k@pre), map(Zlength, costs_l)) &&
        Forall(Forall(Z::le(0)), costs_l) && Forall(Forall(Z::ge(10000)), costs_l) &&
        Zlength(costs_l[i]) == k@pre &&
        0 <= i && i < n@pre &&
        0 <= c && c < k@pre &&
        0 <= prev && prev <= 1000000000 &&
        0 <= total && total <= 1000000000 &&
        total == prev + costs_l[i][c] &&
        PaintHouseIIPrevSelection(min1, min2, min1_color, c, prev) &&
        -1 <= new_min1_color && new_min1_color < k@pre &&
        0 <= new_min1 && new_min1 <= 1000000000 &&
        0 <= new_min2 && new_min2 <= 1000000000 &&
        0 <= i && i <= n@pre && PaintHouseIIRowMinima(costs_l, n@pre, k@pre, i, min1, min2, min1_color) &&
        0 <= i && i < n@pre && 0 <= c + 1 && c + 1 <= k@pre && PaintHouseIIColorMinima(costs_l, n@pre, k@pre, i, c + 1, min1, min2, min1_color, new_min1, new_min2, new_min1_color) &&
        IntPtrArray2::missing_i(costs@pre, n@pre, i, row_ptr, costs_l) *
        data_at(costs@pre + (i * sizeof(int *)), int *, row_ptr) *
        IntArray::full(row_ptr, Zlength(costs_l[i]), costs_l[i])
       */
    }


    min1 = new_min1;
    min2 = new_min2;
    min1_color = new_min1_color;


  }

  return min1;
}
