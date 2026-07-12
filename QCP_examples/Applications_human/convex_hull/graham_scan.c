#include "convex_hull_def.h"
#include "safeexec_def.h"

/*@ Extern Coq (leftmost : Point -> list Point -> Prop)
	             (is_convex_hull : list Point -> list Point -> Prop)
               (point_bound : Z)
               (point_in_bound : Point -> Prop)
               (points_in_bound : list Point -> Prop)
               (point_leftdown : Point -> Point -> Prop)
               (point_leftmost_prefix : list Point -> Z -> Z -> Prop)
               (point_permutation : list Point -> list Point -> Prop)
               (point_same_outside_range : list Point -> list Point -> Z -> Z -> Prop)
               (point_sorted_range : Point -> list Point -> Z -> Z -> Prop)
               (point_polar_partitioned_at : Point -> list Point -> Z -> Z -> Z -> Prop)
               (point_polar_partition_scan_inv : Point -> list Point -> list Point -> Z -> Z -> Point -> Z -> Z -> Prop)
               (point_polar_sorted : Point -> list Point -> Prop)
               (point_cmp_leftdown : Point -> Point -> Z)
               (point_cross_by_value : Z -> Z -> Z -> Z -> Z -> Z -> Z)
               (point_dot_by_value : Z -> Z -> Z -> Z -> Z -> Z -> Z)
               (point_colinear : Point -> Point -> Point -> Prop)
               (point_at_mid : Point -> Point -> Point -> Z)
               (default_point : Point)
               (empty_point_stack : list Point)
               (build_hull : Point -> list Point -> program (list Point) unit)
               (build_hull_c_iter : list Point -> Z -> program (list Point) unit)
               (build_hull_c_next : list Point -> Z -> unit -> program (list Point) unit)
               (build_hull_c_step : list Point -> Z -> program (list Point) unit)
               (build_hull_c_push : list Point -> Z -> program (list Point) unit)
*/

int leftdown(int a_x, int a_y, int b_x, int b_y)
/*@ Require emp
    Ensure a_x == a_x@pre && a_y == a_y@pre &&
           b_x == b_x@pre && b_y == b_y@pre &&
           __return == point_cmp_leftdown(point_mk(a_x@pre, a_y@pre),
                                          point_mk(b_x@pre, b_y@pre))
*/
{
  /*@ Assert
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre
  */
  if (a_x < b_x)
    return -1;
  if (a_x > b_x)
    return 1;
  if (a_y < b_y)
    return -1;
  if (a_y > b_y)
    return 1;
  return 0;
}

int cross_prod(int a_x, int a_y, int b_x, int b_y, int c_x, int c_y)
/*@ Require -point_bound <= a_x && a_x <= point_bound &&
            -point_bound <= a_y && a_y <= point_bound &&
            -point_bound <= b_x && b_x <= point_bound &&
            -point_bound <= b_y && b_y <= point_bound &&
            -point_bound <= c_x && c_x <= point_bound &&
            -point_bound <= c_y && c_y <= point_bound
    Ensure a_x == a_x@pre && a_y == a_y@pre &&
           b_x == b_x@pre && b_y == b_y@pre &&
           c_x == c_x@pre && c_y == c_y@pre &&
           __return == point_cross_by_value(a_x, a_y, b_x, b_y, c_x, c_y)
*/
{
  /*@ Assert
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre &&
        c_x == c_x@pre && c_y == c_y@pre &&
        -point_bound <= a_x && a_x <= point_bound &&
        -point_bound <= a_y && a_y <= point_bound &&
        -point_bound <= b_x && b_x <= point_bound &&
        -point_bound <= b_y && b_y <= point_bound &&
        -point_bound <= c_x && c_x <= point_bound &&
        -point_bound <= c_y && c_y <= point_bound
  */
  return (b_x - a_x) * (c_y - a_y) - (b_y - a_y) * (c_x - a_x);
}

int dot_prod(int a_x, int a_y, int b_x, int b_y, int c_x, int c_y)
/*@ Require -point_bound <= a_x && a_x <= point_bound &&
            -point_bound <= a_y && a_y <= point_bound &&
            -point_bound <= b_x && b_x <= point_bound &&
            -point_bound <= b_y && b_y <= point_bound &&
            -point_bound <= c_x && c_x <= point_bound &&
            -point_bound <= c_y && c_y <= point_bound
    Ensure a_x == a_x@pre && a_y == a_y@pre &&
           b_x == b_x@pre && b_y == b_y@pre &&
           c_x == c_x@pre && c_y == c_y@pre &&
           __return == point_dot_by_value(a_x, a_y, b_x, b_y, c_x, c_y)
*/
{
  /*@ Assert
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre &&
        c_x == c_x@pre && c_y == c_y@pre &&
        -point_bound <= a_x && a_x <= point_bound &&
        -point_bound <= a_y && a_y <= point_bound &&
        -point_bound <= b_x && b_x <= point_bound &&
        -point_bound <= b_y && b_y <= point_bound &&
        -point_bound <= c_x && c_x <= point_bound &&
        -point_bound <= c_y && c_y <= point_bound
  */
  return (b_x - a_x) * (c_x - a_x) + (b_y - a_y) * (c_y - a_y);
}


static int cmp_polar(int gp_x, int gp_y, int a_x, int a_y, int b_x, int b_y)
/*@ Require point_in_bound(point_mk(gp_x, gp_y)) &&
            point_in_bound(point_mk(a_x, a_y)) &&
            point_in_bound(point_mk(b_x, b_y))
    Ensure gp_x == gp_x@pre && gp_y == gp_y@pre &&
            a_x == a_x@pre && a_y == a_y@pre &&
            b_x == b_x@pre && b_y == b_y@pre &&
            __return == point_cmp_polar(point_mk(gp_x@pre, gp_y@pre),
                                        point_mk(a_x@pre, a_y@pre),
                                        point_mk(b_x@pre, b_y@pre))
*/
{
  /*@ Assert
        gp_x == gp_x@pre && gp_y == gp_y@pre &&
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre &&
        point_in_bound(point_mk(gp_x, gp_y)) &&
        point_in_bound(point_mk(a_x, a_y)) &&
        point_in_bound(point_mk(b_x, b_y))
  */
  int cr = cross_prod(gp_x, gp_y, a_x, a_y, b_x, b_y);
  if (cr > 0)
    return -1;
  if (cr < 0)
    return 1;

  /*@ Assert
        cr == point_cross(point_mk(gp_x, gp_y),
                          point_mk(a_x, a_y),
                          point_mk(b_x, b_y)) &&
        cr >= 0 && cr <= 0 &&
        point_colinear(point_mk(gp_x, gp_y),
                       point_mk(a_x, a_y),
                       point_mk(b_x, b_y)) &&
        gp_x == gp_x@pre && gp_y == gp_y@pre &&
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre &&
        point_in_bound(point_mk(gp_x, gp_y)) &&
        point_in_bound(point_mk(a_x, a_y)) &&
        point_in_bound(point_mk(b_x, b_y))
  */
  int mid = (b_x - a_x) * (gp_x - a_x) + (b_y - a_y) * (gp_y - a_y);
  /*@ Assert
        mid == point_at_mid(point_mk(gp_x, gp_y),
                            point_mk(a_x, a_y),
                            point_mk(b_x, b_y)) &&
        cr == point_cross(point_mk(gp_x, gp_y),
                          point_mk(a_x, a_y),
                          point_mk(b_x, b_y)) &&
        cr >= 0 && cr <= 0 &&
        point_colinear(point_mk(gp_x, gp_y),
                       point_mk(a_x, a_y),
                       point_mk(b_x, b_y)) &&
        gp_x == gp_x@pre && gp_y == gp_y@pre &&
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre &&
        point_in_bound(point_mk(gp_x, gp_y)) &&
        point_in_bound(point_mk(a_x, a_y)) &&
        point_in_bound(point_mk(b_x, b_y))
  */
  if (mid > 0)
    return 1;
  if (mid < 0)
    return -1;

  // Degenerate case: colinear(p, a, b) and at least two colocates.
  return leftdown(a_x, a_y, b_x, b_y);
}

int build_hull_from_sorted_tail(struct Point *pivot,
                                struct Point *sorted_tail,
                                int tail_n,
                                struct Point *hull)
/*@ high_level_spec <= low_level_spec
    With (pivot0 : Point) (l : list Point)
    Require 1 <= tail_n && tail_n < INT_MAX &&
            tail_n == Zlength(l) &&
            point_polar_sorted(pivot0, l) &&
            leftmost(pivot0, rev(l)) &&
            point_in_bound(pivot0) &&
            points_in_bound(l) &&
            store_point(pivot, pivot0) *
            PointArray::full(sorted_tail, tail_n, l) *
            PointArray::undef_full(hull, tail_n + 1)
    Ensure exists hull_out,
           pivot == pivot@pre &&
           sorted_tail == sorted_tail@pre &&
           tail_n == tail_n@pre &&
           hull == hull@pre &&
           __return == Zlength(hull_out) &&
           point_in_bound(pivot0) &&
           points_in_bound(l) &&
           is_convex_hull(cons(pivot0, l), hull_out) &&
           store_point(pivot, pivot0) *
           PointArray::full(sorted_tail, tail_n, l) *
           PointArray::seg(hull, 0, __return, hull_out) *
           PointArray::undef_seg(hull, __return, tail_n + 1)
*/
;

int build_hull_from_sorted_tail(struct Point *pivot,
                                struct Point *sorted_tail,
                                int tail_n,
                                struct Point *hull)
/*@ low_level_spec
    With (pivot0 : Point) (l : list Point) X
    Require 1 <= tail_n && tail_n < INT_MAX &&
            tail_n == Zlength(l) &&
            point_polar_sorted(pivot0, l) &&
            leftmost(pivot0, rev(l)) &&
            point_in_bound(pivot0) &&
            points_in_bound(l) &&
            safeExec(equiv(empty_point_stack), build_hull(pivot0, l), X) &&
            store_point(pivot, pivot0) *
            PointArray::full(sorted_tail, tail_n, l) *
            PointArray::undef_full(hull, tail_n + 1)
    Ensure exists stk,
           pivot == pivot@pre &&
           sorted_tail == sorted_tail@pre &&
           tail_n == tail_n@pre &&
           hull == hull@pre &&
           __return == Zlength(rev(stk)) &&
           point_in_bound(pivot0) &&
           points_in_bound(l) &&
           points_in_bound(rev(stk)) &&
           safeExec(equiv(stk), return(tt), X) &&
           store_point(pivot, pivot0) *
           PointArray::full(sorted_tail, tail_n, l) *
           PointArray::seg(hull, 0, __return, rev(stk)) *
           PointArray::undef_seg(hull, __return, tail_n + 1)
*/
{
  hull[0].x = pivot->x;
  hull[0].y = pivot->y;
  int top = 0;

  /*
   * The abstract stack is top-first; hull[0..top] stores it bottom-first.
   */
  /*@ Inv Assert
      exists stk,
        0 <= i && i <= tail_n &&
        top <= i &&
        0 <= tail_n && tail_n < INT_MAX &&
        tail_n == Zlength(l) &&
        pivot == pivot@pre &&
        sorted_tail == sorted_tail@pre &&
        tail_n == tail_n@pre &&
        hull == hull@pre &&
        top + 1 == Zlength(rev(stk)) &&
        point_polar_sorted(pivot0, l) &&
        point_in_bound(pivot0) &&
        points_in_bound(l) &&
        points_in_bound(rev(stk)) &&
        safeExec(equiv(stk), build_hull_c_iter(l, i), X) &&
        store_point(pivot, pivot0) *
        PointArray::full(sorted_tail, tail_n, l) *
        PointArray::seg(hull, 0, top + 1, rev(stk)) *
        PointArray::undef_seg(hull, top + 1, tail_n + 1)
  */
  for (int i = 0; i < tail_n; i++) {
    /*@ Inv Assert
        exists stk,
          0 <= i && i < tail_n &&
          top <= i &&
          0 <= tail_n && tail_n < INT_MAX &&
          tail_n == Zlength(l) &&
          pivot == pivot@pre &&
          sorted_tail == sorted_tail@pre &&
          tail_n == tail_n@pre &&
          hull == hull@pre &&
          top + 1 == Zlength(rev(stk)) &&
          point_polar_sorted(pivot0, l) &&
          point_in_bound(pivot0) &&
          points_in_bound(l) &&
          points_in_bound(rev(stk)) &&
          safeExec(equiv(stk), build_hull_c_step(l, i), X) &&
          store_point(pivot, pivot0) *
          PointArray::full(sorted_tail, tail_n, l) *
          PointArray::seg(hull, 0, top + 1, rev(stk)) *
          PointArray::undef_seg(hull, top + 1, tail_n + 1)
    */
    while (top >= 1) {
      if (cross_prod(hull[top - 1].x, hull[top - 1].y,
                      hull[top].x, hull[top].y,
                      sorted_tail[i].x, sorted_tail[i].y) > 0) {
        break;
      }
      top--;
    }
    ++top;
    hull[top].x = sorted_tail[i].x;
    hull[top].y = sorted_tail[i].y;
  }

  return top + 1;
}

/* =============================================================
 *  Sorting helpers and Graham scan
 *  Sorts points by polar angle before stack-based hull building.
 * ============================================================ */

static void swap_points(struct Point *pts, int n, int i, int j)
/*@ With (pts_l : list Point)
    Require
      0 <= i && i < n && 0 <= j && j < n &&
      i != j &&
      Zlength(pts_l) == n &&
      PointArray::full(pts, n, pts_l)
    Ensure
      pts == pts@pre &&
      n == n@pre &&
      i == i@pre &&
      j == j@pre &&
      Zlength(pts_l) == n &&
      PointArray::full(pts, n, point_swap(pts_l, i, j))
*/
{
  int tmp_x = pts[i].x;
  int tmp_y = pts[i].y;
  pts[i].x = pts[j].x;
  pts[i].y = pts[j].y;
  pts[j].x = tmp_x;
  pts[j].y = tmp_y;
}

static int partition_polar_points(struct Point *pts, int n,
                                   int low, int high,
                                   int gx, int gy)
/*@ With (pts_l : list Point)
    Require
      0 <= low && low <= high && high < n &&
      0 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      point_in_bound(point_mk(gx, gy)) &&
      leftmost(point_mk(gx, gy), pts_l) &&
      PointArray::full(pts, n, pts_l)
    Ensure
      pts == pts@pre &&
      n == n@pre &&
      low == low@pre &&
      high == high@pre &&
      gx == gx@pre &&
      gy == gy@pre &&
      low <= __return && __return <= high &&
      exists pts_out,
        Zlength(pts_out) == n &&
        points_in_bound(pts_out) &&
        leftmost(point_mk(gx, gy), pts_out) &&
        point_permutation(pts_l, pts_out) &&
        point_same_outside_range(pts_l, pts_out, low, high) &&
        point_polar_partitioned_at(point_mk(gx, gy), pts_out, low, high, __return) &&
        PointArray::full(pts, n, pts_out)
*/
{
  int pivot_x = pts[high].x;
  int pivot_y = pts[high].y;
  int i = low - 1;
  /*@ Inv Assert
      exists pts_cur,
        Zlength(pts_cur) == n &&
        pts == pts@pre &&
        n == n@pre &&
        low == low@pre &&
        high == high@pre &&
        gx == gx@pre &&
        gy == gy@pre &&
        0 <= n && n <= 50000 &&
        0 <= low && low <= high && high < n &&
        low - 1 <= i && i < j && j <= high &&
        pts_cur[high].x == pivot_x &&
        pts_cur[high].y == pivot_y &&
        points_in_bound(pts_cur) &&
        point_in_bound(point_mk(gx, gy)) &&
        point_in_bound(point_mk(pivot_x, pivot_y)) &&
        leftmost(point_mk(gx, gy), pts_l) &&
        leftmost(point_mk(gx, gy), pts_cur) &&
        point_polar_partition_scan_inv(point_mk(gx, gy), pts_l, pts_cur,
                                   low, high,
                                   point_mk(pivot_x, pivot_y), i, j) &&
        PointArray::full(pts, n, pts_cur)
  */
  for (int j = low; j < high; j++) {
    int ax = pts[j].x;
    int ay = pts[j].y;
    int c = cmp_polar(gx, gy, ax, ay, pivot_x, pivot_y);
    if (c <= 0) {
      i++;
      if (i != j) {
        swap_points(pts, n, i, j);
      }
    }
  }
  if (i + 1 != high) {
    swap_points(pts, n, i + 1, high);
  }
  return i + 1;
}

static void quicksort_polar_points(struct Point *pts, int n,
                                    int left, int right,
                                    int gx, int gy)
/*@ With (pts_l : list Point)
    Require
      0 <= n && n <= 50000 &&
      0 <= left && -1 <= right && right < n &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      point_in_bound(point_mk(gx, gy)) &&
      leftmost(point_mk(gx, gy), pts_l) &&
      PointArray::full(pts, n, pts_l)
    Ensure
      exists pts_out,
        Zlength(pts_out) == n &&
        points_in_bound(pts_out) &&
        leftmost(point_mk(gx, gy), pts_out) &&
        point_permutation(pts_l, pts_out) &&
        point_same_outside_range(pts_l, pts_out, left, right) &&
        point_sorted_range(point_mk(gx, gy), pts_out, left, right) &&
        PointArray::full(pts, n, pts_out)
*/
{
  if (left < right) {
    int p = partition_polar_points(pts, n, left, right, gx, gy);
    if (p > left)
      quicksort_polar_points(pts, n, left, p - 1, gx, gy);
    if (p < right)
      quicksort_polar_points(pts, n, p + 1, right, gx, gy);
  }
}


/**
 * graham_scan — Full Graham scan convex hull computation.
 *
 * 1. Find the leftmost-bottom point (pivot) via leftdown ordering.
 * 2. Move pivot to pts[0].
 * 3. Sort pts[1..n-1] by polar angle around the pivot (ascending).
 * 4. Call build_hull_from_sorted_tail to produce the hull.
 *
 * Returns the number of hull points written to `hull`.
 */
int graham_scan(struct Point *pts, int n, struct Point *hull)
/*@ With (pts_l : list Point)
    Require
      2 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      PointArray::full(pts, n, pts_l) *
      PointArray::undef_full(hull, n)
    Ensure
      exists pts_out hull_out,
        Zlength(pts_out) == n &&
        Zlength(hull_out) <= n &&
        Zlength(hull_out) >= 1 &&
        points_in_bound(pts_out) &&
        point_permutation(pts_l, pts_out) &&
        is_convex_hull(pts_l, hull_out) &&
        __return == Zlength(hull_out) &&
        PointArray::full(pts, n, pts_out) *
        PointArray::seg(hull, 0, __return, hull_out) *
        PointArray::undef_seg(hull, __return, n)
*/
{
  int pivot_idx = 0;
  /*@ Inv Assert
		        pts == pts@pre &&
		        hull == hull@pre &&
		        n == n@pre &&
		        2 <= n &&
		        0 <= n && n <= 50000 &&
        1 <= i && i <= n &&
        0 <= pivot_idx && pivot_idx < i &&
        point_leftmost_prefix(pts_l, pivot_idx, i) &&
        Zlength(pts_l) == n &&
        points_in_bound(pts_l) &&
        PointArray::full(pts, n, pts_l) *
        PointArray::undef_full(hull, n)
  */
  for (int i = 1; i < n; i++) {
    int ax = pts[i].x;
    int ay = pts[i].y;
    int bx = pts[pivot_idx].x;
    int b_y = pts[pivot_idx].y;
    if (leftdown(ax, ay, bx, b_y) < 0) {
      pivot_idx = i;
    }
  }

  if (pivot_idx != 0) {
    swap_points(pts, n, 0, pivot_idx);
  }

  int gx = pts[0].x;
  int gy = pts[0].y;
  quicksort_polar_points(pts, n, 1, n - 1, gx, gy);

  struct Point *tail = pts + 1;
  /*@ Assert
      exists pts_pivot pts_sorted tail_sorted pivot0,
	        pts == pts@pre &&
        tail == pts + 1 &&
	        hull == hull@pre &&
	        n == n@pre &&
	        2 <= n && n <= 50000 &&
        pivot0 == point_mk(gx, gy) &&
        pts_pivot == point_swap(pts_l, 0, pivot_idx) &&
        Zlength(pts_sorted) == n &&
        Zlength(tail_sorted) == n - 1 &&
        tail_sorted == sublist(1, n, pts_sorted) &&
        points_in_bound(pts_sorted) &&
        points_in_bound(tail_sorted) &&
        point_in_bound(pivot0) &&
        point_leftmost_prefix(pts_l, pivot_idx, n) &&
        leftmost(pivot0, pts_sorted) &&
        point_permutation(pts_pivot, pts_sorted) &&
        point_sorted_range(point_mk(gx, gy), pts_sorted, 1, n - 1) &&
        point_polar_sorted(pivot0, tail_sorted) &&
        leftmost(pivot0, rev(tail_sorted)) &&
        pts_sorted[0].x == gx &&
        pts_sorted[0].y == gy &&
        store_point(pts, pivot0) *
        PointArray::full(tail, n - 1, tail_sorted) *
        PointArray::undef_full(hull, (n - 1) + 1)
  */
  int ret = build_hull_from_sorted_tail(pts, tail, n - 1, hull)
    /*@ where(high_level_spec) */;
  return ret;
}
