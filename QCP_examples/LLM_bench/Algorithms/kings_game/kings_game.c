#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (minister :: *) */
/*@ Extern Coq
      (mk_minister : Z -> Z -> minister)
      (default_minister : minister)
      (minister_left : minister -> Z)
      (minister_right : minister -> Z)
      (minister_product : minister -> Z)
      (FlatMinisters : list Z -> list minister -> Prop)
      (MinisterHandsBound : list minister -> Prop)
      (MinisterPermutation : list minister -> list minister -> Prop)
      (MinisterSorted : list minister -> Prop)
      (KingsGameResult : list minister -> Z -> list minister -> Prop)
      (minister_swap : list minister -> Z -> Z -> list minister)
      (minister_swap_flat : list Z -> Z -> Z -> list Z)
      (BubbleOuterProperty : list minister -> Z -> Z -> Prop)
      (BubbleScanProperty : list minister -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_lib */

/* Swap two complete flat minister records. */
void swap_ministers(int *a, int n, int i, int j)
/*@ With (flat : list Z) (ps : list minister)
    Require
      0 <= i && i < n && 0 <= j && j < n &&
      1 <= n && n <= 8 &&
      Zlength(ps) == n &&
      FlatMinisters(flat, ps) &&
      MinisterHandsBound(ps) &&
      IntArray::full(a, 2 * n, flat)
    Ensure
      Zlength(minister_swap(ps, i, j)) == n &&
      FlatMinisters(minister_swap_flat(flat, i, j), minister_swap(ps, i, j)) &&
      MinisterHandsBound(minister_swap(ps, i, j)) &&
      MinisterPermutation(ps, minister_swap(ps, i, j)) &&
      IntArray::full(a, 2 * n, minister_swap_flat(flat, i, j))
 */
{
  int tmp_left = a[2 * i];
  int tmp_right = a[2 * i + 1];
  a[2 * i] = a[2 * j];
  a[2 * i + 1] = a[2 * j + 1];
  a[2 * j] = tmp_left;
  a[2 * j + 1] = tmp_right;
}

/*
 * This verification-oriented implementation deliberately uses the bounded
 * domain 1 <= n <= 8 and hand values in [1,10].  Thus every comparison key is
 * at most 100 and king_left times all minister left hands is at most 10^9;
 * ordinary signed int arithmetic is sufficient and no high-precision code is
 * used.
 *
 * The strict comparison makes the adjacent-swap bubble sort stable for equal
 * left*right keys.  The formal result is stronger than sortedness: it says the
 * produced permutation realises the MaxMinLib minimax reward specification.
 */
void kings_game(int *ministers, int n, int king_left, int king_right, int *ans)
/*@ With (input_flat : list Z) (input : list minister)
    Require
      1 <= n && n <= 8 &&
      1 <= king_left && king_left <= 10 &&
      1 <= king_right && king_right <= 10 &&
      Zlength(input) == n &&
      FlatMinisters(input_flat, input) &&
      MinisterHandsBound(input) &&
      IntArray::full(ministers, 2 * n, input_flat) *
      IntArray::undef_full(ans, 2 * n)
    Ensure
      exists output_flat output,
        Zlength(output) == n &&
        FlatMinisters(output_flat, output) &&
        MinisterHandsBound(output) &&
        KingsGameResult(input, king_left, output) &&
        IntArray::full(ministers, 2 * n, input_flat) *
        IntArray::full(ans, 2 * n, output_flat)
 */
{
  (void)king_right;

  /* First copy the complete flat input, preserving the disjoint source. */
  /*@ Inv Assert
      ministers == ministers@pre && ans == ans@pre &&
      n == n@pre && king_left == king_left@pre &&
      king_right == king_right@pre &&
      1 <= n@pre && n@pre <= 8 &&
      1 <= king_left@pre && king_left@pre <= 10 &&
      1 <= king_right@pre && king_right@pre <= 10 &&
      Zlength(input) == n@pre &&
      Zlength(input_flat) == 2 * n@pre &&
      FlatMinisters(input_flat, input) &&
      MinisterHandsBound(input) &&
      0 <= k && k <= 2 * n@pre &&
      IntArray::full(ministers, 2 * n@pre, input_flat) *
      IntArray::seg(ans, 0, k, sublist(0, k, input_flat)) *
      IntArray::undef_seg(ans, k, 2 * n@pre)
   */
  for (int k = 0; k < 2 * n; k++) {
    ans[k] = ministers[k];
  }

  /* Bubble the largest remaining key into the next suffix position. */
  /*@ Inv Assert
      exists flat_cur cur,
        ministers == ministers@pre && ans == ans@pre &&
        n == n@pre && king_left == king_left@pre &&
        king_right == king_right@pre &&
        1 <= n@pre && n@pre <= 8 &&
        1 <= king_left@pre && king_left@pre <= 10 &&
        1 <= king_right@pre && king_right@pre <= 10 &&
        Zlength(input) == n@pre &&
        FlatMinisters(input_flat, input) &&
        MinisterHandsBound(input) &&
        0 <= pass && pass <= n@pre - 1 &&
        Zlength(cur) == n@pre &&
        FlatMinisters(flat_cur, cur) &&
        MinisterHandsBound(cur) &&
        MinisterPermutation(input, cur) &&
        BubbleOuterProperty(cur, n@pre, pass) &&
        IntArray::full(ministers, 2 * n@pre, input_flat) *
        IntArray::full(ans, 2 * n@pre, flat_cur)
   */
  for (int pass = 0; pass < n - 1; pass++) {
    /*@ Inv Assert
        exists flat_cur cur,
          ministers == ministers@pre && ans == ans@pre &&
          n == n@pre && king_left == king_left@pre &&
          king_right == king_right@pre &&
          1 <= n@pre && n@pre <= 8 &&
          1 <= king_left@pre && king_left@pre <= 10 &&
          1 <= king_right@pre && king_right@pre <= 10 &&
          Zlength(input) == n@pre &&
          FlatMinisters(input_flat, input) &&
          MinisterHandsBound(input) &&
          0 <= pass && pass < n@pre - 1 &&
          0 <= j && j <= n@pre - 1 - pass &&
          Zlength(cur) == n@pre &&
          FlatMinisters(flat_cur, cur) &&
          MinisterHandsBound(cur) &&
          MinisterPermutation(input, cur) &&
          BubbleOuterProperty(cur, n@pre, pass) &&
          BubbleScanProperty(cur, n@pre, pass, j) &&
          IntArray::full(ministers, 2 * n@pre, input_flat) *
          IntArray::full(ans, 2 * n@pre, flat_cur)
     */
    for (int j = 0; j < n - 1 - pass; j++) {
      int left1 = ans[2 * j];
      int right1 = ans[2 * j + 1];
      int left2 = ans[2 * (j + 1)];
      int right2 = ans[2 * (j + 1) + 1];
      if (left1 * right1 > left2 * right2) {
        swap_ministers(ans, n, j, j + 1);
      }
    }
  }
}
