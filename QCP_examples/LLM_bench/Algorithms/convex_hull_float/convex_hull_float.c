#include "verification_stdlib.h"
#include "verification_list.h"
#include "convex_hull_float_def.h"

/*@ Extern Coq
      (pointf_finite : PointF -> Prop)
      (pointsf_finite : list PointF -> Prop)
      (all_pointf_cross_finite : list PointF -> Prop)
      (pointf_permutation : list PointF -> list PointF -> Prop)
      (pointf_same_outside_range : list PointF -> list PointF -> Z -> Z -> Prop)
      (pointf_xy_sorted : list PointF -> Prop)
      (pointf_xy_sorted_range : list PointF -> Z -> Z -> Prop)
      (pointf_xy_partitioned_at : list PointF -> Z -> Z -> Z -> Prop)
      (pointf_xy_partition_scan_inv : list PointF -> list PointF -> Z -> Z -> PointF -> Z -> Z -> Prop)
      (pointf_lower_scan_inv : list PointF -> list PointF -> Z -> Z -> Prop)
      (pointf_lower_pop_inv : list PointF -> list PointF -> list PointF -> Z -> Z -> Prop)
      (pointf_upper_scan_inv : list PointF -> list PointF -> list PointF -> Z -> Z -> Z -> Prop)
      (pointf_upper_pop_inv : list PointF -> list PointF -> list PointF -> list PointF -> Z -> Z -> Z -> Prop)
      (is_andrew_hull_float : list PointF -> list PointF -> list PointF -> Prop)
 */

static int point_cmp_xy(float ax, float ay, float bx, float b_y)
/*@ Require
      pointf_finite(pointf_mk(ax, ay)) &&
      pointf_finite(pointf_mk(bx, b_y))
    Ensure
      ax == ax@pre && ay == ay@pre && bx == bx@pre && b_y == b_y@pre &&
      __return == pointf_cmp_xy(
        pointf_mk(ax@pre, ay@pre), pointf_mk(bx@pre, b_y@pre))
 */
{
  if (ax < bx) return -1;
  if (ax > bx) return 1;
  if (ay < b_y) return -1;
  if (ay > b_y) return 1;
  return 0;
}

static float point_cross(float ax, float ay, float bx, float b_y,
                         float cx, float cy)
/*@ Require
      pointf_finite(pointf_mk(ax, ay)) &&
      pointf_finite(pointf_mk(bx, b_y)) &&
      pointf_finite(pointf_mk(cx, cy)) &&
      pointf_cross_finite(
        pointf_mk(ax, ay), pointf_mk(bx, b_y), pointf_mk(cx, cy))
    Ensure
      ax == ax@pre && ay == ay@pre && bx == bx@pre && b_y == b_y@pre &&
      cx == cx@pre && cy == cy@pre &&
      __return == pointf_cross(
        pointf_mk(ax@pre, ay@pre), pointf_mk(bx@pre, b_y@pre),
        pointf_mk(cx@pre, cy@pre))
 */
{
  return (bx - ax) * (cy - ay) - (b_y - ay) * (cx - ax);
}

static void swap_points(struct PointF *pts, int n, int i, int j)
/*@ With (l : list PointF)
    Require
      0 <= i && i < n && 0 <= j && j < n &&
      Zlength(l) == n && PointFArray::full(pts, n, l)
    Ensure
      pts == pts@pre && n == n@pre && i == i@pre && j == j@pre &&
      PointFArray::full(pts, n, pointf_swap(l, i, j))
 */
{
  float tx = pts[i].x;
  float ty = pts[i].y;
  pts[i].x = pts[j].x;
  pts[i].y = pts[j].y;
  pts[j].x = tx;
  pts[j].y = ty;
}

static int partition_xy_points(struct PointF *pts, int n, int low, int high)
/*@ With (l : list PointF)
    Require
      0 <= low && low <= high && high < n &&
      0 <= n && n <= 50000 && Zlength(l) == n &&
      pointsf_finite(l) && all_pointf_cross_finite(l) &&
      PointFArray::full(pts, n, l)
    Ensure
      pts == pts@pre && n == n@pre && low == low@pre && high == high@pre &&
      low <= __return && __return <= high &&
      exists out,
        Zlength(out) == n && pointsf_finite(out) &&
        all_pointf_cross_finite(out) && pointf_permutation(l, out) &&
        pointf_same_outside_range(l, out, low, high) &&
        pointf_xy_partitioned_at(out, low, high, __return) &&
        PointFArray::full(pts, n, out)
 */
{
  float pivot_x = pts[high].x;
  float pivot_y = pts[high].y;
  int i = low - 1;
  /*@ Inv Assert
      exists cur,
        pts == pts@pre && n == n@pre && low == low@pre && high == high@pre &&
        0 <= n && n <= 50000 && 0 <= low && low <= high && high < n &&
        low - 1 <= i && i < j && j <= high && Zlength(cur) == n &&
        cur[high].pointf_x == pivot_x && cur[high].pointf_y == pivot_y &&
        pointsf_finite(cur) && all_pointf_cross_finite(cur) &&
        pointf_finite(pointf_mk(pivot_x, pivot_y)) &&
        pointf_xy_partition_scan_inv(
          l, cur, low, high, pointf_mk(pivot_x, pivot_y), i, j) &&
        PointFArray::full(pts, n, cur)
   */
  for (int j = low; j < high; ++j) {
    float ax = pts[j].x;
    float ay = pts[j].y;
    int c = point_cmp_xy(ax, ay, pivot_x, pivot_y);
    if (c <= 0) {
      ++i;
      if (i != j)
        swap_points(pts, n, i, j);
    }
  }
  ++i;
  if (i != high)
    swap_points(pts, n, i, high);
  return i;
}

static void quicksort_xy_points(struct PointF *pts, int n, int left, int right)
/*@ With (l : list PointF)
    Require
      0 <= n && n <= 50000 && 0 <= left && -1 <= right && right < n &&
      Zlength(l) == n && pointsf_finite(l) && all_pointf_cross_finite(l) &&
      PointFArray::full(pts, n, l)
    Ensure
      exists out,
        Zlength(out) == n && pointsf_finite(out) &&
        all_pointf_cross_finite(out) && pointf_permutation(l, out) &&
        pointf_same_outside_range(l, out, left, right) &&
        pointf_xy_sorted_range(out, left, right) &&
        PointFArray::full(pts, n, out)
 */
{
  if (left < right) {
    int p = partition_xy_points(pts, n, left, right);
    if (p > left)
      quicksort_xy_points(pts, n, left, p - 1);
    if (p < right)
      quicksort_xy_points(pts, n, p + 1, right);
  }
}

static int andrew_build_from_sorted(
    struct PointF *pts, int n, struct PointF *hull)
/*@ With (sorted hull_init : list PointF)
    Require
      2 <= n && n <= 50000 && Zlength(sorted) == n &&
      pointsf_finite(sorted) && all_pointf_cross_finite(sorted) &&
      pointf_xy_sorted(sorted) && Zlength(hull_init) == 2 * n &&
      pointsf_finite(hull_init) &&
      PointFArray::full(pts, n, sorted) *
      PointFArray::full(hull, 2 * n, hull_init)
    Ensure
      exists pts_out hull_all out,
        Zlength(pts_out) == n && Zlength(hull_all) == 2 * n &&
        out == sublist(0, __return, hull_all) && Zlength(out) == __return &&
        2 <= __return && __return <= 2 * n &&
        pointsf_finite(pts_out) && all_pointf_cross_finite(pts_out) &&
        pointsf_finite(hull_all) && pointf_permutation(sorted, pts_out) &&
        pointf_xy_sorted(pts_out) &&
        is_andrew_hull_float(sorted, pts_out, out) &&
        PointFArray::full(pts, n, pts_out) *
        PointFArray::full(hull, 2 * n, hull_all)
 */
{
  int k = 0;
  /*@ Inv Assert
      exists hull_all,
        pts == pts@pre && hull == hull@pre && n == n@pre &&
        2 <= n && n <= 50000 &&
        0 <= i && i <= n && 0 <= k && k <= i &&
        Zlength(sorted) == n && pointsf_finite(sorted) &&
        all_pointf_cross_finite(sorted) && pointf_xy_sorted(sorted) &&
        Zlength(hull_all) == 2 * n && pointsf_finite(hull_all) &&
        pointf_lower_scan_inv(sorted, sublist(0, k, hull_all), i, k) &&
        PointFArray::full(pts, n, sorted) *
        PointFArray::full(hull, 2 * n, hull_all)
   */
  for (int i = 0; i < n; ++i) {
    /*@ Inv Assert
        exists before hull_all,
          pts == pts@pre && hull == hull@pre && n == n@pre &&
          2 <= n && n <= 50000 &&
          0 <= i && i < n && 0 <= k && k <= i &&
          Zlength(sorted) == n && pointsf_finite(sorted) &&
          all_pointf_cross_finite(sorted) && pointf_xy_sorted(sorted) &&
          Zlength(hull_all) == 2 * n && pointsf_finite(hull_all) &&
          pointf_lower_pop_inv(
            sorted, before, sublist(0, k, hull_all), i, k) &&
          PointFArray::full(pts, n, sorted) *
          PointFArray::full(hull, 2 * n, hull_all)
     */
    while (k >= 2) {
      if (((hull[k - 1].x - hull[k - 2].x) *
           (pts[i].y - hull[k - 2].y) -
           (hull[k - 1].y - hull[k - 2].y) *
           (pts[i].x - hull[k - 2].x)) > 0.0f)
        break;
      --k;
    }
    hull[k].x = pts[i].x;
    hull[k].y = pts[i].y;
    ++k;
  }

  int lower_n = k;
  /*@ Inv Assert
      exists lower hull_all,
        pts == pts@pre && hull == hull@pre && n == n@pre &&
        2 <= n && n <= 50000 &&
        0 <= i + 1 && i + 1 <= n - 1 &&
        2 <= lower_n && lower_n <= k && k <= 2 * n &&
        lower_n == Zlength(lower) &&
        lower == sublist(0, lower_n, sublist(0, k, hull_all)) &&
        Zlength(sorted) == n && pointsf_finite(sorted) &&
        all_pointf_cross_finite(sorted) && pointf_xy_sorted(sorted) &&
        Zlength(hull_all) == 2 * n && pointsf_finite(hull_all) &&
        pointf_upper_scan_inv(
          sorted, lower, sublist(0, k, hull_all), i + 1, k, lower_n) &&
        PointFArray::full(pts, n, sorted) *
        PointFArray::full(hull, 2 * n, hull_all)
   */
  for (int i = n - 2; i >= 0; --i) {
    /*@ Inv Assert
        exists lower before hull_all,
          pts == pts@pre && hull == hull@pre && n == n@pre &&
          2 <= n && n <= 50000 &&
          0 <= i && i <= n - 2 && 2 <= lower_n && lower_n <= k &&
          k < 2 * n &&
          lower_n == Zlength(lower) &&
          lower == sublist(0, lower_n, sublist(0, k, hull_all)) &&
          Zlength(sorted) == n &&
          pointsf_finite(sorted) && all_pointf_cross_finite(sorted) &&
          pointf_xy_sorted(sorted) &&
          Zlength(hull_all) == 2 * n && pointsf_finite(hull_all) &&
          pointf_upper_pop_inv(
            sorted, lower, before, sublist(0, k, hull_all), i, k, lower_n) &&
          PointFArray::full(pts, n, sorted) *
          PointFArray::full(hull, 2 * n, hull_all)
     */
    while (k > lower_n) {
      if (((hull[k - 1].x - hull[k - 2].x) *
           (pts[i].y - hull[k - 2].y) -
           (hull[k - 1].y - hull[k - 2].y) *
           (pts[i].x - hull[k - 2].x)) > 0.0f)
        break;
      --k;
    }
    hull[k].x = pts[i].x;
    hull[k].y = pts[i].y;
    ++k;
  }
  --k;
  return k;
}

int convex_hull_float(struct PointF *pts, int n, struct PointF *hull)
/*@ With (input hull_init : list PointF)
    Require
      2 <= n && n <= 50000 && Zlength(input) == n &&
      pointsf_finite(input) && all_pointf_cross_finite(input) &&
      Zlength(hull_init) == 2 * n && pointsf_finite(hull_init) &&
      PointFArray::full(pts, n, input) *
      PointFArray::full(hull, 2 * n, hull_init)
    Ensure
      exists sorted hull_all out,
        pts == pts@pre && hull == hull@pre && n == n@pre &&
        Zlength(sorted) == n && Zlength(hull_all) == 2 * n &&
        out == sublist(0, __return, hull_all) && Zlength(out) == __return &&
        2 <= __return && __return <= 2 * n &&
        pointsf_finite(sorted) && all_pointf_cross_finite(sorted) &&
        pointsf_finite(hull_all) && pointf_permutation(input, sorted) &&
        pointf_xy_sorted(sorted) &&
        is_andrew_hull_float(input, sorted, out) &&
        PointFArray::full(pts, n, sorted) *
        PointFArray::full(hull, 2 * n, hull_all)
 */
{
  quicksort_xy_points(pts, n, 0, n - 1);
  /*@ Assert
      exists sorted,
        pts == pts@pre && hull == hull@pre && n == n@pre &&
        2 <= n && n <= 50000 && Zlength(sorted) == n &&
        pointsf_finite(sorted) && all_pointf_cross_finite(sorted) &&
        pointf_permutation(input, sorted) && pointf_xy_sorted(sorted) &&
        Zlength(hull_init) == 2 * n && pointsf_finite(hull_init) &&
        PointFArray::full(pts, n, sorted) *
        PointFArray::full(hull, 2 * n, hull_init)
   */
  return andrew_build_from_sorted(pts, n, hull);
}
