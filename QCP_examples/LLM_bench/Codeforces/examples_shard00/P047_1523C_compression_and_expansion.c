/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib
*/

/* Codeforces 1523/C - Compression and Expansion */
// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:P047_1523C_compression_and_expansion.support */
/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> list (list Z) -> Prop)
      (concat : list (list Z) -> list Z)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib */
/*@ Extern Coq
      (CurrentItem : list (list Z) -> Z -> list Z -> Prop)
      (PopTarget : list Z -> list Z -> Z -> Prop)
      (FlatPrefix : list (list Z) -> Z -> list Z -> Prop)
      (LengthsPrefix : list (list Z) -> Z -> list Z -> Prop)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
*/
/*@ Extern Coq
      (BoundedItem : Z -> list Z -> Prop)
*/
/* QCP_INSERT_END:P047_1523C_compression_and_expansion.support */
static int solver(const int *values, int n, int *flat,
                  int *lengths) /* QCP_INSERT_BEGIN:P047_1523C_compression_and_expansion.contract */

/*@ With (last_numbers : list Z)
    Require
      1 <= Zlength(last_numbers) && Zlength(last_numbers) <= 1000 &&
      (forall i, (0 <= i && i < Zlength(last_numbers)) => (1 <= last_numbers[i] && last_numbers[i] <= Zlength(last_numbers))) &&
      Pre(last_numbers) &&
      n == Zlength(last_numbers) &&
      IntArray::full(values, n, last_numbers) *
      IntArray::undef_full(flat, n * n) * IntArray::undef_full(lengths, n)
    Ensure
      exists result lengths_data,
        Spec(last_numbers, result) &&
        (forall i, (0 <= i && i < n) => lengths_data[i] == Zlength(result[i])) &&
        __return == Zlength(concat(result)) &&
        IntArray::full(values, n, last_numbers) *
        IntArray::full(flat, Zlength(concat(result)), concat(result)) *
        IntArray::undef_seg(flat, Zlength(concat(result)), n * n) *
        IntArray::full(lengths, n, lengths_data)
*/
/* QCP_INSERT_END:P047_1523C_compression_and_expansion.contract */

{
    int stack[1005], depth = 0, total = 0;
    /*@ Inv Assert
        exists items cells active flat_data lengths_data,
          values == values@pre && n == n@pre &&
          flat == flat@pre && lengths == lengths@pre &&
          1 <= n@pre && n@pre <= 1000 &&
          n@pre == Zlength(last_numbers) &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= Znth(k, last_numbers, 0) &&
             Znth(k, last_numbers, 0) <= n@pre)) &&
          Pre(last_numbers) && Spec(last_numbers, items) &&
          Zlength(items) == n@pre &&
          0 <= line && line <= n@pre &&
          0 <= depth && depth <= line &&
          depth == Zlength(active) &&
          CurrentItem(items, line, active) &&
          BoundedItem(n@pre, active) &&
          total == Zlength(flat_data) &&
          0 <= total && total <= line * n@pre &&
          FlatPrefix(items, line, flat_data) &&
          LengthsPrefix(items, line, lengths_data) &&
          Zlength(cells) == 1005 &&
          (forall k, (0 <= k && k < depth) =>
            cells[k] == Some(active[k])) &&
          IntArray::full(values@pre, n@pre, last_numbers) *
          IntArray::mixed_full(stack, 1005, cells) *
          IntArray::seg(flat@pre, 0, total, flat_data) *
          IntArray::undef_seg(flat@pre, total, n@pre * n@pre) *
          IntArray::seg(lengths@pre, 0, line, lengths_data) *
          IntArray::undef_seg(lengths@pre, line, n@pre)
    */
    for (int line = 0; line < n; ++line)
    {
        int x = values[line];
        if (x == 1)
        {
            stack[depth] = 1;
            ++depth;
        }
        else
        {
            /*@ Inv Assert
                exists items cells active target flat_data lengths_data,
                  values == values@pre && n == n@pre &&
                  flat == flat@pre && lengths == lengths@pre &&
                  1 <= n@pre && n@pre <= 1000 &&
                  n@pre == Zlength(last_numbers) &&
                  (forall k, (0 <= k && k < n@pre) =>
                    (1 <= Znth(k, last_numbers, 0) &&
                     Znth(k, last_numbers, 0) <= n@pre)) &&
                  Pre(last_numbers) && Spec(last_numbers, items) &&
                  Zlength(items) == n@pre &&
                  0 < line && line < n@pre &&
                  x == Znth(line, last_numbers, 0) && x != 1 &&
                  target == Znth(line, items, nil) &&
                  1 <= depth && depth <= line &&
                  depth == Zlength(active) &&
                  PopTarget(active, target, x) &&
                  BoundedItem(n@pre, active) &&
                  total == Zlength(flat_data) &&
                  0 <= total && total <= line * n@pre &&
                  FlatPrefix(items, line, flat_data) &&
                  LengthsPrefix(items, line, lengths_data) &&
                  Zlength(cells) == 1005 &&
                  (forall k, (0 <= k && k < depth) =>
                    cells[k] == Some(active[k])) &&
                  cells[depth - 1] == Some(active[depth - 1]) &&
                  IntArray::full(values@pre, n@pre, last_numbers) *
                  store(pointer_offset(stack, depth - 1, int),
                    int, active[depth - 1]) *
                  IntArray::mixed_missing_i(stack, depth - 1, 0, 1005, cells) *
                  IntArray::seg(flat@pre, 0, total, flat_data) *
                  IntArray::undef_seg(flat@pre, total, n@pre * n@pre) *
                  IntArray::seg(lengths@pre, 0, line, lengths_data) *
                  IntArray::undef_seg(lengths@pre, line, n@pre)
            */
            while (depth && stack[depth - 1] + 1 != x)
                --depth;
            stack[depth - 1] = x;
        }
        /*@ Assert
            exists items cells active flat_data lengths_data,
              values == values@pre && n == n@pre &&
              flat == flat@pre && lengths == lengths@pre &&
              1 <= n@pre && n@pre <= 1000 &&
              n@pre == Zlength(last_numbers) &&
              (forall k, (0 <= k && k < n@pre) =>
                (1 <= Znth(k, last_numbers, 0) &&
                 Znth(k, last_numbers, 0) <= n@pre)) &&
              Pre(last_numbers) && Spec(last_numbers, items) &&
              Zlength(items) == n@pre &&
              0 <= line && line < n@pre &&
              active == Znth(line, items, nil) &&
              1 <= depth && depth <= line + 1 &&
              depth == Zlength(active) &&
              BoundedItem(n@pre, active) &&
              total == Zlength(flat_data) &&
              0 <= total && total <= line * n@pre &&
              FlatPrefix(items, line, flat_data) &&
              LengthsPrefix(items, line, lengths_data) &&
              Zlength(cells) == 1005 &&
              (forall k, (0 <= k && k < depth) =>
                cells[k] == Some(active[k])) &&
              has_int_permission(&x) *
              IntArray::full(values@pre, n@pre, last_numbers) *
              IntArray::mixed_full(stack, 1005, cells) *
              IntArray::seg(flat@pre, 0, total, flat_data) *
              IntArray::undef_seg(flat@pre, total, n@pre * n@pre) *
              IntArray::seg(lengths@pre, 0, line, lengths_data) *
              IntArray::undef_seg(lengths@pre, line, n@pre)
        */
        lengths[line] = depth;
        /*@ Inv Assert
            exists items cells active flat_before flat_data lengths_data,
              values == values@pre && n == n@pre &&
              flat == flat@pre && lengths == lengths@pre &&
              1 <= n@pre && n@pre <= 1000 &&
              n@pre == Zlength(last_numbers) &&
              (forall k, (0 <= k && k < n@pre) =>
                (1 <= Znth(k, last_numbers, 0) &&
                 Znth(k, last_numbers, 0) <= n@pre)) &&
              Pre(last_numbers) && Spec(last_numbers, items) &&
              Zlength(items) == n@pre &&
              0 <= line && line < n@pre &&
              active == Znth(line, items, nil) &&
              1 <= depth && depth <= line + 1 && line + 1 <= n@pre &&
              depth == Zlength(active) &&
              BoundedItem(n@pre, active) &&
              0 <= i && i <= depth &&
              FlatPrefix(items, line, flat_before) &&
              flat_data == app(flat_before, sublist(0, i, active)) &&
              total == Zlength(flat_data) &&
              0 <= total &&
              total + (depth - i) <= (line + 1) * n@pre &&
              (line + 1) * n@pre <= n@pre * n@pre &&
              LengthsPrefix(items, line + 1, lengths_data) &&
              Zlength(cells) == 1005 &&
              (forall k, (0 <= k && k < depth) =>
                cells[k] == Some(active[k])) &&
              has_int_permission(&x) *
              IntArray::full(values@pre, n@pre, last_numbers) *
              IntArray::mixed_full(stack, 1005, cells) *
              IntArray::seg(flat@pre, 0, total, flat_data) *
              IntArray::undef_seg(flat@pre, total, n@pre * n@pre) *
              IntArray::seg(lengths@pre, 0, line + 1, lengths_data) *
              IntArray::undef_seg(lengths@pre, line + 1, n@pre)
        */
        for (int i = 0; i < depth; ++i)
        {
            /*@ Assert
                exists items cells active flat_before flat_data lengths_data,
                  values == values@pre && n == n@pre &&
                  flat == flat@pre && lengths == lengths@pre &&
                  1 <= n@pre && n@pre <= 1000 &&
                  n@pre == Zlength(last_numbers) &&
                  (forall k, (0 <= k && k < n@pre) =>
                    (1 <= Znth(k, last_numbers, 0) &&
                     Znth(k, last_numbers, 0) <= n@pre)) &&
                  Pre(last_numbers) && Spec(last_numbers, items) &&
                  Zlength(items) == n@pre &&
                  0 <= line && line < n@pre &&
                  active == Znth(line, items, nil) &&
                  1 <= depth && depth <= line + 1 && line + 1 <= n@pre &&
                  depth == Zlength(active) &&
                  BoundedItem(n@pre, active) &&
                  0 <= i && i < depth &&
                  FlatPrefix(items, line, flat_before) &&
                  flat_data == app(flat_before, sublist(0, i, active)) &&
                  total == Zlength(flat_data) &&
                  0 <= total &&
                  total + (depth - i) <= (line + 1) * n@pre &&
                  (line + 1) * n@pre <= n@pre * n@pre &&
                  LengthsPrefix(items, line + 1, lengths_data) &&
                  Zlength(cells) == 1005 &&
                  (forall k, (0 <= k && k < depth) =>
                    cells[k] == Some(active[k])) &&
                  cells[i] == Some(active[i]) &&
                  has_int_permission(&x) *
                  IntArray::full(values@pre, n@pre, last_numbers) *
                  store(pointer_offset(stack, i, int),
                    int, active[i]) *
                  IntArray::mixed_missing_i(stack, i, 0, 1005, cells) *
                  IntArray::seg(flat@pre, 0, total, flat_data) *
                  IntArray::undef_seg(flat@pre, total, n@pre * n@pre) *
                  IntArray::seg(lengths@pre, 0, line + 1, lengths_data) *
                  IntArray::undef_seg(lengths@pre, line + 1, n@pre)
            */
            flat[total] = stack[i];
            ++total;
        }
    }
    /*@ Assert
        exists items flat_data lengths_data,
          values == values@pre && n == n@pre &&
          flat == flat@pre && lengths == lengths@pre &&
          1 <= n@pre && n@pre <= 1000 &&
          n@pre == Zlength(last_numbers) &&
          Spec(last_numbers, items) &&
          Zlength(items) == n@pre &&
          flat_data == concat(items) &&
          total == Zlength(flat_data) &&
          Zlength(lengths_data) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            lengths_data[k] == Zlength(items[k])) &&
          has_int_permission(&depth) *
          IntArray::full(values@pre, n@pre, last_numbers) *
          IntArray::undef_full(stack, 1005) *
          IntArray::full(flat@pre, total, flat_data) *
          IntArray::undef_seg(flat@pre, total, n@pre * n@pre) *
          IntArray::full(lengths@pre, n@pre, lengths_data)
    */
    return total;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); int *values = malloc((size_t)n * sizeof(*values));
//         int *lengths = malloc((size_t)n * sizeof(*lengths)); int *flat = malloc((size_t)n * n * sizeof(*flat));
//         for (int i = 0; i < n; ++i) scanf("%d", &values[i]); solver(values, n, flat, lengths);
//         int at = 0; for (int line = 0; line < n; ++line)
//             for (int i = 0; i < lengths[line]; ++i) printf("%d%c", flat[at++], i + 1 == lengths[line] ? '\n' : '.');
//         free(flat); free(lengths); free(values);
//     }
//     return 0;
// }
