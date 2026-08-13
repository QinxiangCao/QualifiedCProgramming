



struct Point {
  int x;
  int y;
};

static struct Point gp;

/*@ Extern Coq (point :: *) */
/*@ Extern Coq
      (mk_point : Z -> Z -> point)
      (point_x : point -> Z)
      (point_y : point -> Z)
      (default_point : point)
      (CoordInBounds : Z -> Prop)
      (PointCoordsBound : list point -> Prop)
      (FlatPoints : list Z -> list point -> Prop)
      (PointPermutation : list point -> list point -> Prop)
      (PolarCmpResult : point -> point -> point -> Z -> Prop)
      (PolarLt : point -> point -> point -> Prop)
      (PolarLe : point -> point -> point -> Prop)
      (PolarSorted : point -> list point -> Prop)
      (PointSortedRange : point -> list point -> Z -> Z -> Prop)
      (PointMemoryModel : point -> list Z -> Z -> Prop)
      (PointRangeSortResult : point -> list Z -> list point -> Z -> Z -> Prop)
      (PointSameOutsideRange : list point -> list point -> Z -> Z -> Prop)
      (PointPartitionedAt : point -> list point -> Z -> Z -> Z -> Prop)
      (PointPartitionScanInv : point -> list point -> list point -> Z -> Z -> point -> Z -> Z -> Prop)
      (point_swap_flat : list Z -> Z -> Z -> list Z)
      (point_swap_points : list point -> Z -> Z -> list point)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_lib */

int cmp_polar_values(int gx, int gy, int a_x, int a_y, int b_x, int b_y)
/*@ Require
      CoordInBounds(gx) && CoordInBounds(gy) &&
      CoordInBounds(a_x) && CoordInBounds(a_y) &&
      CoordInBounds(b_x) && CoordInBounds(b_y)
    Ensure
      PolarCmpResult(mk_point(gx, gy), mk_point(a_x, a_y), mk_point(b_x, b_y), __return) &&
      -1 <= __return && __return <= 1
 */
{
  int adx = a_x - gx;
  int ady = a_y - gy;
  int bdx = b_x - gx;
  int bdy = b_y - gy;
  int cr = adx * bdy - ady * bdx;
  int da = adx * adx + ady * ady;
  int db = bdx * bdx + bdy * bdy;

  int ah = 0;
  if (ady > 0) {
    ah = 1;
  } else {
    if (ady == 0) {
      if (adx >= 0) {
        ah = 1;
      }
    }
  }

  int bh = 0;
  if (bdy > 0) {
    bh = 1;
  } else {
    if (bdy == 0) {
      if (bdx >= 0) {
        bh = 1;
      }
    }
  }

  if (ah > bh)
    return -1;
  if (ah < bh)
    return 1;

  if (cr > 0)
    return -1;
  if (cr < 0)
    return 1;

  if (da < db)
    return -1;
  if (da > db)
    return 1;

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

void swap_points(int *coords, int n, int i, int j)
/*@ With (flat : list Z) (pts_l : list point)
    Require
      0 <= i && i < n && 0 <= j && j < n &&
      0 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      FlatPoints(flat, pts_l) &&
      PointCoordsBound(pts_l) &&
      IntArray::full(coords, 2 * n, flat)
    Ensure
      FlatPoints(point_swap_flat(flat, i, j), point_swap_points(pts_l, i, j)) &&
      PointPermutation(pts_l, point_swap_points(pts_l, i, j)) &&
      PointCoordsBound(point_swap_points(pts_l, i, j)) &&
      IntArray::full(coords, 2 * n, point_swap_flat(flat, i, j))
 */
{
  int tmp_x = coords[2 * i];
  int tmp_y = coords[2 * i + 1];
  coords[2 * i] = coords[2 * j];
  coords[2 * i + 1] = coords[2 * j + 1];
  coords[2 * j] = tmp_x;
  coords[2 * j + 1] = tmp_y;
}

int partition_points(int *coords, int n, int low, int high, int gx, int gy)
/*@ With (flat : list Z) (pts_l : list point)
    Require
      0 <= low && low <= high && high < n &&
      0 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      FlatPoints(flat, pts_l) &&
      PointCoordsBound(cons(mk_point(gx, gy), pts_l)) &&
      IntArray::full(coords, 2 * n, flat)
    Ensure
      low <= __return && __return <= high &&
      exists flat_out pts_out,
        FlatPoints(flat_out, pts_out) &&
        PointCoordsBound(cons(mk_point(gx, gy), pts_out)) &&
        PointPermutation(pts_l, pts_out) &&
        PointSameOutsideRange(pts_l, pts_out, low, high) &&
        PointPartitionedAt(mk_point(gx, gy), pts_out, low, high, __return) &&
        IntArray::full(coords, 2 * n, flat_out)
 */
{
  int pivot_x = coords[2 * high];
  int pivot_y = coords[2 * high + 1];
  int i = low - 1;
  /*@ Inv Assert
      exists flat_cur pts_cur,
        coords == coords@pre && n == n@pre &&
        low == low@pre && high == high@pre &&
        gx == gx@pre && gy == gy@pre &&
        0 <= low && low <= high && high < n &&
        0 <= n && n <= 50000 &&
        low - 1 <= i && i < j && j <= high &&
        Zlength(pts_l) == n &&
        Zlength(pts_cur) == n &&
        mk_point(pivot_x, pivot_y) == Znth(high, pts_cur, default_point) &&
        FlatPoints(flat_cur, pts_cur) &&
        PointCoordsBound(pts_cur) &&
        PointCoordsBound(cons(mk_point(gx, gy), pts_cur)) &&
        PointPartitionScanInv(mk_point(gx, gy), pts_l, pts_cur, low, high,
                              mk_point(pivot_x, pivot_y), i, j) &&
        IntArray::full(coords, 2 * n, flat_cur)
   */
  for (int j = low; j < high; j++) {
    int ax = coords[2 * j];
    int ay = coords[2 * j + 1];
    int c = cmp_polar_values(gx, gy, ax, ay, pivot_x, pivot_y);
    /*@ Given flat_cur pts_cur */
    if (c <= 0) {
      i++;
      swap_points(coords, n, i, j) /*@ where flat = flat_cur, pts_l = pts_cur */;
    }
  }

  /*@ Given flat_cur pts_cur */
  swap_points(coords, n, i + 1, high) /*@ where flat = flat_cur, pts_l = pts_cur */;
  return i + 1;
}

void quicksort_points_range(int *coords, int n, int left, int right, int gx, int gy)
/*@ With (flat : list Z)
    Require
      0 <= n && n <= 50000 &&
      0 <= left && -1 <= right && right < n &&
      PointMemoryModel(mk_point(gx, gy), flat, n) &&
      IntArray::full(coords, 2 * n, flat)
    Ensure
      exists flat_out pts_out,
        FlatPoints(flat_out, pts_out) &&
        PointCoordsBound(cons(mk_point(gx, gy), pts_out)) &&
        PointRangeSortResult(mk_point(gx, gy), flat, pts_out, left, right) &&
        IntArray::full(coords, 2 * n, flat_out)
 */
{
  if (left < right) {
    /*@ Assert
        exists pts_l,
          coords == coords@pre && n == n@pre &&
          left == left@pre && right == right@pre &&
          gx == gx@pre && gy == gy@pre &&
          0 <= n && n <= 50000 &&
          0 <= left && left < right && right < n &&
          PointMemoryModel(mk_point(gx, gy), flat, n) &&
          Zlength(pts_l) == n &&
          FlatPoints(flat, pts_l) &&
          PointCoordsBound(cons(mk_point(gx, gy), pts_l)) &&
          IntArray::full(coords, 2 * n, flat)
      */
    /*@ Given pts_l */
    int p = partition_points(coords, n, left, right, gx, gy) /*@ where flat = flat, pts_l = pts_l */;
    if (p > left) {
      quicksort_points_range(coords, n, left, p - 1, gx, gy);
    }
    if (p < right) {
      quicksort_points_range(coords, n, p + 1, right, gx, gy);
    }
  }
}

void sort(struct Point *pts, int n)
/*@ With (flat : list Z) (pts_l : list point) gx gy
    Require
      0 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      FlatPoints(flat, pts_l) &&
      PointCoordsBound(cons(mk_point(gx, gy), pts_l)) &&
      gp.x == gx && gp.y == gy &&
      IntArray::full(pts, 2 * n, flat)
    Ensure
      exists flat_out pts_out,
        FlatPoints(flat_out, pts_out) &&
        PointCoordsBound(cons(mk_point(gx, gy), pts_out)) &&
        PointPermutation(pts_l, pts_out) &&
        PolarSorted(mk_point(gx, gy), pts_out) &&
        gp.x == gx && gp.y == gy &&
        IntArray::full(pts, 2 * n, flat_out)
 */
{
  int *coords = (int *)pts;
  int gx = gp.x;
  int gy = gp.y;
  quicksort_points_range(coords, n, 0, n - 1, gx, gy);
}
