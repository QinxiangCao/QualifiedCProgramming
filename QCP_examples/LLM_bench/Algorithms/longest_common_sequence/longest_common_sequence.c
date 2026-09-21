/*@ Extern Coq
      (LCSNLength : list Z -> list Z -> Z -> Prop)
      (LCSNTableResult : list Z -> list Z -> Z -> list Z -> Prop)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (LCSNColumnProgress : list (option Z) -> list Z -> Z -> Z -> Prop)
      (LCSNBoundaryProgress : list (option Z) -> list Z -> Z -> Z -> Prop)
      (LCSNRowsProgress : list Z -> list Z -> list (option Z) -> list Z -> Z -> Z -> Prop)
      (LCSNRowProgress : list Z -> list Z -> list (option Z) -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.longest_common_sequence.longest_common_sequence_lib */

int longest_common_sequence(int *x, int *y, int n)
/*@ With (xs ys : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(xs) == n && Zlength(ys) == n &&
      IntArray::full(x, n, xs) *
      IntArray::full(y, n, ys)
    Ensure
      LCSNLength(xs, ys, __return) &&
      IntArray::full(x, n, xs) *
      IntArray::full(y, n, ys)
 */
{
  int table[1002001];

  int stride;
  int i;
  int j;
  int above;
  int left;

  stride = n + 1;

  i = 0;
  /*@ Inv Assert
      exists mixed_table table_l,
      x == x@pre && y == y@pre && 
      n == n@pre && stride == n@pre + 1 &&
      0 <= n@pre && n@pre <= 1000 &&
      Zlength(xs) == n@pre && Zlength(ys) == n@pre &&
      0 <= i && i <= n@pre + 1 &&
      0 <= stride * i &&
      stride * i <= (n@pre + 1) * (n@pre + 1) &&
      LCSNColumnProgress(mixed_table, table_l, n@pre, i) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
      IntArray::full(x, n@pre, xs) *
      IntArray::full(y, n@pre, ys) *
      IntArray::mixed_full(
        table, (n@pre + 1) * (n@pre + 1), mixed_table) *
      has_int_permission(&j) *
      has_int_permission(&above) *
      has_int_permission(&left) *
      IntArray::undef_seg(table, (n@pre + 1) * (n@pre + 1), 1002001)
   */
  while (i <= n) {
    /*@ 0 <= stride * i &&
        stride * i < (n@pre + 1) * (n@pre + 1) by local */
    table[stride * i] = 0;
    i = i + 1;
  }

  j = 1;
  /*@ Inv Assert
      exists mixed_table table_l,
      x == x@pre && y == y@pre && 
      n == n@pre && stride == n@pre + 1 &&
      0 <= n@pre && n@pre <= 1000 &&
      Zlength(xs) == n@pre && Zlength(ys) == n@pre &&
      1 <= j && j <= n@pre + 1 &&
      LCSNBoundaryProgress(mixed_table, table_l, n@pre, j) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
      IntArray::full(x, n@pre, xs) *
      IntArray::full(y, n@pre, ys) *
      IntArray::mixed_full(
        table, (n@pre + 1) * (n@pre + 1), mixed_table) *
      has_int_permission(&i) *
      has_int_permission(&above) *
      has_int_permission(&left) *
      IntArray::undef_seg(table, (n@pre + 1) * (n@pre + 1), 1002001)
   */
  while (j <= n) {

    table[j] = 0;
    j = j + 1;
  }

  i = 1;
  /*@ Inv Assert
      exists mixed_table table_l,
      x == x@pre && y == y@pre && 
      n == n@pre && stride == n@pre + 1 &&
      0 <= n@pre && n@pre <= 1000 &&
      Zlength(xs) == n@pre && Zlength(ys) == n@pre &&
      1 <= i && i <= n@pre + 1 &&
      0 <= stride * i &&
      stride * i <= (n@pre + 1) * (n@pre + 1) &&
      LCSNRowsProgress(xs, ys, mixed_table, table_l, n@pre, i) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
      IntArray::full(x, n@pre, xs) *
      IntArray::full(y, n@pre, ys) *
      IntArray::mixed_full(
        table, (n@pre + 1) * (n@pre + 1), mixed_table) *
      has_int_permission(&j) *
      has_int_permission(&above) *
      has_int_permission(&left) *
      IntArray::undef_seg(table, (n@pre + 1) * (n@pre + 1), 1002001)
   */
  while (i <= n) {
    j = 1;
    /*@ Inv Assert
        exists mixed_table table_l,
        x == x@pre && y == y@pre && 
        n == n@pre && stride == n@pre + 1 &&
        0 <= n@pre && n@pre <= 1000 &&
        Zlength(xs) == n@pre && Zlength(ys) == n@pre &&
        1 <= i && i <= n@pre &&
        1 <= j && j <= n@pre + 1 &&
        0 <= stride * i + j &&
        stride * i + j <= (n@pre + 1) * (n@pre + 1) &&
        LCSNRowProgress(
          xs, ys, mixed_table, table_l, n@pre, i, j) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
        IntArray::full(x, n@pre, xs) *
        IntArray::full(y, n@pre, ys) *
        IntArray::mixed_full(
          table, (n@pre + 1) * (n@pre + 1), mixed_table) *
        has_int_permission(&above) *
        has_int_permission(&left) *
      IntArray::undef_seg(table, (n@pre + 1) * (n@pre + 1), 1002001)
   */
    while (j <= n) {
      /*@ Given mixed_table table_l */
      /*@ 0 <= i - 1 && i - 1 < n@pre &&
          0 <= j - 1 && j - 1 < n@pre &&
          0 <= stride * i + j &&
          stride * i + j < (n@pre + 1) * (n@pre + 1) &&
          0 <= stride * (i - 1) + (j - 1) &&
          stride * (i - 1) + (j - 1) <
            (n@pre + 1) * (n@pre + 1) &&
          0 <= stride * (i - 1) + j &&
          stride * (i - 1) + j <
            (n@pre + 1) * (n@pre + 1) &&
          0 <= stride * i + (j - 1) &&
          stride * i + (j - 1) <
            (n@pre + 1) * (n@pre + 1) by local */
      if (x[i - 1] == y[j - 1]) {
        /*@ 
            1 <= i && i <= n@pre &&
            1 <= j && j <= n@pre &&
            LCSNRowProgress(
              xs, ys, mixed_table, table_l, n@pre, i, j) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
            IntArray::mixed_full(
              table, (n@pre + 1) * (n@pre + 1), mixed_table)
            which implies
            
            1 <= i && i <= n@pre &&
            1 <= j && j <= n@pre &&
            LCSNRowProgress(
              xs, ys, mixed_table, table_l, n@pre, i, j) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
            Znth(
              (n@pre + 1) * i + j, mixed_table, None) == None &&
            Znth(
              (n@pre + 1) * (i - 1) + (j - 1), mixed_table, None) ==
              Some(Znth(
                (n@pre + 1) * (i - 1) + (j - 1), table_l, 0)) &&
            0 <= Znth(
              (n@pre + 1) * (i - 1) + (j - 1), table_l, 0) &&
            Znth(
              (n@pre + 1) * (i - 1) + (j - 1), table_l, 0) <= n@pre &&
            IntArray::mixed_seg(
              table, 0,
              (n@pre + 1) * (i - 1) + (j - 1),
              sublist(0,
                (n@pre + 1) * (i - 1) + (j - 1), mixed_table)) *
            store(
              pointer_offset(table, ((n@pre + 1) * (i - 1) + (j - 1)), sizeof(int), int),
              int,
              Znth(
                (n@pre + 1) * (i - 1) + (j - 1), table_l, 0)) *
            IntArray::mixed_seg(
              table,
              (n@pre + 1) * (i - 1) + (j - 1) + 1,
              (n@pre + 1) * i + j,
              sublist(
                (n@pre + 1) * (i - 1) + (j - 1) + 1,
                (n@pre + 1) * i + j, mixed_table)) *
            IntArray::undef_seg(
              table,
              (n@pre + 1) * i + j,
              (n@pre + 1) * i + j + 1) *
            IntArray::mixed_seg(
              table,
              (n@pre + 1) * i + j + 1,
              (n@pre + 1) * (n@pre + 1),
              sublist(
                (n@pre + 1) * i + j + 1,
                (n@pre + 1) * (n@pre + 1), mixed_table))
   */
        table[stride * i + j] =
            table[stride * (i - 1) + (j - 1)] + 1;
      } else {
        /*@ 
            1 <= i && i <= n@pre &&
            1 <= j && j <= n@pre &&
            LCSNRowProgress(
              xs, ys, mixed_table, table_l, n@pre, i, j) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
            IntArray::mixed_full(
              table, (n@pre + 1) * (n@pre + 1), mixed_table)
            which implies
            
            1 <= i && i <= n@pre &&
            1 <= j && j <= n@pre &&
            LCSNRowProgress(
              xs, ys, mixed_table, table_l, n@pre, i, j) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
            Znth(
              (n@pre + 1) * i + j, mixed_table, None) == None &&
            Znth(
              (n@pre + 1) * (i - 1) + j, mixed_table, None) ==
              Some(Znth(
                (n@pre + 1) * (i - 1) + j, table_l, 0)) &&
            Znth(
              (n@pre + 1) * i + (j - 1), mixed_table, None) ==
              Some(Znth(
                (n@pre + 1) * i + (j - 1), table_l, 0)) &&
            IntArray::mixed_seg(
              table, 0,
              (n@pre + 1) * (i - 1) + j,
              sublist(0,
                (n@pre + 1) * (i - 1) + j, mixed_table)) *
            store(
              pointer_offset(table, ((n@pre + 1) * (i - 1) + j), sizeof(int), int),
              int, Znth(
                (n@pre + 1) * (i - 1) + j, table_l, 0)) *
            IntArray::mixed_seg(
              table,
              (n@pre + 1) * (i - 1) + j + 1,
              (n@pre + 1) * i + (j - 1),
              sublist(
                (n@pre + 1) * (i - 1) + j + 1,
                (n@pre + 1) * i + (j - 1), mixed_table)) *
            store(
              pointer_offset(table, ((n@pre + 1) * i + (j - 1)), sizeof(int), int),
              int, Znth(
                (n@pre + 1) * i + (j - 1), table_l, 0)) *
            IntArray::undef_seg(
              table,
              (n@pre + 1) * i + j,
              (n@pre + 1) * i + j + 1) *
            IntArray::mixed_seg(
              table,
              (n@pre + 1) * i + j + 1,
              (n@pre + 1) * (n@pre + 1),
              sublist(
                (n@pre + 1) * i + j + 1,
                (n@pre + 1) * (n@pre + 1), mixed_table))
   */
        above = table[stride * (i - 1) + j];
        left = table[stride * i + (j - 1)];
        if (above >= left) {
          table[stride * i + j] = above;
        } else {
          table[stride * i + j] = left;
        }
      }
      /*@ Assert
          exists mixed_table table_l,
          x == x@pre && y == y@pre && 
          n == n@pre && stride == n@pre + 1 &&
          0 <= n@pre && n@pre <= 1000 &&
          Zlength(xs) == n@pre && Zlength(ys) == n@pre &&
          1 <= i && i <= n@pre &&
          1 <= j && j <= n@pre &&
          1 <= j + 1 && j + 1 <= n@pre + 1 &&
          0 <= stride * i + (j + 1) &&
          stride * i + (j + 1) <=
            (n@pre + 1) * (n@pre + 1) &&
          LCSNRowProgress(
            xs, ys, mixed_table, table_l, n@pre, i, j + 1) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
          IntArray::full(x, n@pre, xs) *
          IntArray::full(y, n@pre, ys) *
          IntArray::mixed_full(
            table, (n@pre + 1) * (n@pre + 1), mixed_table) *
          has_int_permission(&above) *
          has_int_permission(&left) *
      IntArray::undef_seg(table, (n@pre + 1) * (n@pre + 1), 1002001)
   */
      j = j + 1;
    }
    i = i + 1;
  }

  /*@ Assert
      exists mixed_table table_l,
      x == x@pre && y == y@pre && 
      n == n@pre && stride == n@pre + 1 &&
      0 <= n@pre && n@pre <= 1000 &&
      Zlength(xs) == n@pre && Zlength(ys) == n@pre &&
      LCSNRowsProgress(
        xs, ys, mixed_table, table_l, n@pre, n@pre + 1) &&
      Zlength(mixed_table) == (n@pre + 1) * (n@pre + 1) &&
      Zlength(table_l) == (n@pre + 1) * (n@pre + 1) &&
      LCSNTableResult(xs, ys, n@pre, table_l) &&
      0 <= stride * n + n &&
      stride * n + n < (n@pre + 1) * (n@pre + 1) &&
      IntArray::full(x, n@pre, xs) *
      IntArray::full(y, n@pre, ys) *
      IntArray::full(
        table, (n@pre + 1) * (n@pre + 1), table_l) *
      has_int_permission(&i) *
      has_int_permission(&j) *
      has_int_permission(&above) *
      has_int_permission(&left) *
      IntArray::undef_seg(table, (n@pre + 1) * (n@pre + 1), 1002001)
   */
  int result = table[stride * n + n];
  /*@ Assert
      x == x@pre && y == y@pre && n == n@pre &&
      LCSNLength(xs, ys, result) &&
      IntArray::full(x@pre, n@pre, xs) * IntArray::full(y@pre, n@pre, ys) *
      IntArray::undef_full(table, 1002001) *
      has_int_permission(&stride) *
      has_int_permission(&i) *
      has_int_permission(&j) *
      has_int_permission(&above) *
      has_int_permission(&left)
   */
  return result;
}
