/* Codeforces 1416/C - XOR Inverse */
// #include <stdio.h>
// #include <stdlib.h>
static int *a, *tmp;
static long long cost[30][2];
/* QCP_INSERT_BEGIN:P068_1416C_xor_inverse.support */
/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Spec : list Z -> Z * Z -> Prop)
      (SolveEffect : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Prop)
      (CostBound : list (list Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (Int64Array2::undef_full : Z -> Z -> Z -> Assertion)
      (Int64Array2::full : Z -> Z -> Z -> list (list Z) -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P068_1416C_xor_inverse_lib */
/* QCP_INSERT_END:P068_1416C_xor_inverse.support */
/*@ Extern Coq
      (SolveCountPrefix : list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StablePartitionPrefix : list Z -> list (option Z) -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PartitionCopyBack : list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (InputCopyPrefix : list Z -> list (option Z) -> Z -> Prop)
      (ZeroCostPrefix : list (list (option Z)) -> Z -> Prop)
      (XorChoicePrefix : list Z -> list (list Z) -> Z -> Z -> Z -> Prop)
      (CostArrayMixed : Z -> Z -> Z -> list (list (option Z)) -> Assertion)
*/
static void solve(int l, int r, int bit)
/*@ With (n_total a_p tmp_p capacity : Z)
             (before : list Z) (scratch : list (option Z))
             (cost_before : list (list Z))
    Require
      0 <= l && l <= r && r <= n_total && n_total <= 300000 &&
      -1 <= bit && bit < 30 && Zlength(before) == n_total &&
      Zlength(scratch) == n_total && Zlength(cost_before) == 30 &&
      0 <= capacity &&
      capacity + (bit + 1) * (r - l) * (r - l) <= 9223372036854775807 &&
      CostBound(cost_before, capacity) &&
      (forall b, (0 <= b && b < 30) =>
        (Zlength(cost_before[b]) == 2 &&
         0 <= cost_before[b][0] && 0 <= cost_before[b][1])) &&
      (forall i, (0 <= i && i < n_total) =>
        (0 <= before[i] && before[i] <= 1000000000)) &&
      store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
      IntArray::full(a_p, n_total, before) *
      IntArray::mixed_full(tmp_p, n_total, scratch) *
      Int64Array2::full(cost, 30, 2, cost_before)
    Ensure
      exists after scratch_after cost_after,
        SolveEffect(before, after, cost_before, cost_after, l@pre, r@pre, bit@pre) &&
        CostBound(cost_after,
          capacity + (bit@pre + 1) * (r@pre - l@pre) * (r@pre - l@pre)) &&
        (forall i, (0 <= i && i < n_total) =>
          (0 <= after[i] && after[i] <= 1000000000)) &&
        store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
        IntArray::full(a_p, n_total, after) *
        IntArray::mixed_full(tmp_p, n_total, scratch_after) *
        Int64Array2::full(cost, 30, 2, cost_after)
*/
{
    if (bit < 0 || r - l <= 1)
        return;
    long long zeros = 0, ones = 0;
    /*@ Inv Assert
          exists current_costs,
            l == l@pre && r == r@pre && bit == bit@pre &&
            0 <= l && l <= i && i <= r && r <= n_total &&
            n_total <= 300000 && 0 <= bit && bit < 30 &&
            0 <= capacity &&
            capacity + (bit + 1) * (r - l) * (r - l) <=
              9223372036854775807 &&
            Zlength(before) == n_total && Zlength(scratch) == n_total &&
            (forall k, (0 <= k && k < n_total) =>
              (0 <= before[k] && before[k] <= 1000000000)) &&
            0 <= zeros && 0 <= ones && zeros + ones == i - l &&
            zeros <= n_total && ones <= n_total &&
            SolveCountPrefix(before, cost_before, current_costs,
                             l, i, bit, zeros, ones) &&
            CostBound(current_costs,
                      capacity + (i - l) * (i - l)) &&
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            IntArray::full(a_p, n_total, before) *
            IntArray::mixed_full(tmp_p, n_total, scratch) *
            Int64Array2::full(cost, bit, 2,
                              sublist(0, bit, current_costs)) *
            store(pointer_offset(pointer_offset(cost, bit,
                                                sizeof(long long[2]),
                                                long long[2]),
                                 0, sizeof(long long), long long),
                  long long, current_costs[bit][0]) *
            store(pointer_offset(pointer_offset(cost, bit,
                                                sizeof(long long[2]),
                                                long long[2]),
                                 1, sizeof(long long), long long),
                  long long, current_costs[bit][1]) *
            Int64Array2::full(pointer_offset(cost, bit + 1,
                                             sizeof(long long[2]),
                                             long long[2]),
                              30 - bit - 1, 2,
                              sublist(bit + 1, 30, current_costs))
    */
    for (int i = l; i < r; i = i + 1)
    {
        if ((a[i] >> bit) & 1)
        {
            cost[bit][1] += zeros;
            ones = ones + 1;
        }
        else
        {
            cost[bit][0] += ones;
            zeros = zeros + 1;
        }
    }
    int p = l;
    /*@ Inv Assert
          exists counted_costs scratch_current,
            l == l@pre && r == r@pre && bit == bit@pre &&
            0 <= l && l <= i && i <= r && r <= n_total &&
            n_total <= 300000 && l <= p && p <= i &&
            0 <= bit && bit < 30 && 0 <= capacity &&
            capacity + (bit + 1) * (r - l) * (r - l) <=
              9223372036854775807 &&
            Zlength(before) == n_total && Zlength(scratch_current) == n_total &&
            (forall k, (0 <= k && k < n_total) =>
              (0 <= before[k] && before[k] <= 1000000000)) &&
            SolveCountPrefix(before, cost_before, counted_costs,
                             l, r, bit, zeros, ones) &&
            CostBound(counted_costs,
                      capacity + (r - l) * (r - l)) &&
            StablePartitionPrefix(before, scratch_current,
                                  l, r, bit, i, p, 0) &&
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            IntArray::full(a_p, n_total, before) *
            IntArray::mixed_full(tmp_p, n_total, scratch_current) *
            Int64Array2::full(cost, 30, 2, counted_costs)
    */
    for (int i = l; i < r; i = i + 1)
    {
        if (((a[i] >> bit) & 1) == 0)
        {
            tmp[p] = a[i];
            p = p + 1;
        }
    }
    int mid = p;
    /*@ Inv Assert
          exists counted_costs scratch_current,
            l == l@pre && r == r@pre && bit == bit@pre &&
            0 <= l && l <= i && i <= r && r <= n_total &&
            n_total <= 300000 &&
            l <= mid && mid <= p && p <= r && mid == l + zeros &&
            0 <= bit && bit < 30 &&
            0 <= capacity &&
            capacity + (bit + 1) * (r - l) * (r - l) <=
              9223372036854775807 &&
            Zlength(before) == n_total && Zlength(scratch_current) == n_total &&
            (forall k, (0 <= k && k < n_total) =>
              (0 <= before[k] && before[k] <= 1000000000)) &&
            SolveCountPrefix(before, cost_before, counted_costs,
                             l, r, bit, zeros, ones) &&
            CostBound(counted_costs,
                      capacity + (r - l) * (r - l)) &&
            StablePartitionPrefix(before, scratch_current,
                                  l, r, bit, i, p, 1) &&
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            IntArray::full(a_p, n_total, before) *
            IntArray::mixed_full(tmp_p, n_total, scratch_current) *
            Int64Array2::full(cost, 30, 2, counted_costs)
    */
    for (int i = l; i < r; i = i + 1)
    {
        if ((a[i] >> bit) & 1)
        {
            /*@ p < r by local */
            tmp[p] = a[i];
            p = p + 1;
        }
    }
    /*@ Inv Assert
          exists counted_costs scratch_current current partitioned,
            l == l@pre && r == r@pre && bit == bit@pre &&
            0 <= l && l <= i && i <= r && r <= n_total &&
            n_total <= 300000 && l <= mid && mid <= r &&
            mid == l + zeros && p == r &&
            0 <= bit && bit < 30 && 0 <= capacity &&
            capacity + (bit + 1) * (r - l) * (r - l) <=
              9223372036854775807 &&
            -1 <= bit - 1 && bit - 1 < 30 &&
            Zlength(before) == n_total && Zlength(current) == n_total &&
            Zlength(scratch_current) == n_total &&
            mid <= Zlength(current) &&
            Zlength(scratch_current) == Zlength(current) &&
            Zlength(partitioned) == r - l &&
            Zlength(counted_costs) == 30 &&
            (forall b, (0 <= b && b < 30) =>
              (Zlength(counted_costs[b]) == 2 &&
               0 <= counted_costs[b][0] && 0 <= counted_costs[b][1])) &&
            (forall k, (0 <= k && k < n_total) =>
              (0 <= current[k] && current[k] <= 1000000000)) &&
            (forall k, (0 <= k && k < Zlength(current)) =>
              (0 <= current[k] && current[k] <= 1000000000)) &&
            (forall k, (0 <= k && k < Zlength(partitioned)) =>
              (0 <= partitioned[k] && partitioned[k] <= 1000000000)) &&
            (forall k, (l <= k && k < r) =>
              scratch_current[k] == Some(partitioned[k - l])) &&
            (i < r =>
              (scratch_current[i] == Some(partitioned[i - l]) &&
               0 <= partitioned[i - l] &&
               partitioned[i - l] <= 1000000000)) &&
            SolveCountPrefix(before, cost_before, counted_costs,
                             l, r, bit, zeros, ones) &&
            CostBound(counted_costs,
                      capacity + (r - l) * (r - l)) &&
            StablePartitionPrefix(before, scratch_current,
                                  l, r, bit, r, p, 1) &&
            PartitionCopyBack(before, current, partitioned, l, r, i) &&
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            IntArray::full(a_p, Zlength(current), current) *
            IntArray::mixed_full(tmp_p, Zlength(current), scratch_current) *
            Int64Array2::full(cost, 30, 2, counted_costs)
    */
    for (int i = l; i < r; i = i + 1)
    {
        /*@ Given scratch_current current partitioned */
        /*@ Assert
              exists counted_costs scratch_current current partitioned,
                l == l@pre && r == r@pre && bit == bit@pre &&
                0 <= l && l <= i && i < r && r <= n_total &&
                n_total <= 300000 && l <= mid && mid <= r &&
                mid == l + zeros && p == r &&
                0 <= bit && bit < 30 && 0 <= capacity &&
                capacity + (bit + 1) * (r - l) * (r - l) <=
                  9223372036854775807 &&
                -1 <= bit - 1 && bit - 1 < 30 &&
                Zlength(before) == n_total && Zlength(current) == n_total &&
                Zlength(scratch_current) == n_total &&
                mid <= Zlength(current) &&
                Zlength(scratch_current) == Zlength(current) &&
                Zlength(partitioned) == r - l &&
                Zlength(counted_costs) == 30 &&
                (forall b, (0 <= b && b < 30) =>
                  (Zlength(counted_costs[b]) == 2 &&
                   0 <= counted_costs[b][0] && 0 <= counted_costs[b][1])) &&
                (forall k, (0 <= k && k < n_total) =>
                  (0 <= current[k] && current[k] <= 1000000000)) &&
                (forall k, (0 <= k && k < Zlength(current)) =>
                  (0 <= current[k] && current[k] <= 1000000000)) &&
                (forall k, (0 <= k && k < Zlength(partitioned)) =>
                  (0 <= partitioned[k] && partitioned[k] <= 1000000000)) &&
                (forall k, (l <= k && k < r) =>
                  scratch_current[k] == Some(partitioned[k - l])) &&
                scratch_current[i] == Some(partitioned[i - l]) &&
                0 <= partitioned[i - l] &&
                partitioned[i - l] <= 1000000000 &&
                SolveCountPrefix(before, cost_before, counted_costs,
                                 l, r, bit, zeros, ones) &&
                CostBound(counted_costs,
                          capacity + (r - l) * (r - l)) &&
                StablePartitionPrefix(before, scratch_current,
                                      l, r, bit, r, p, 1) &&
                PartitionCopyBack(before, current, partitioned, l, r, i) &&
                store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
                IntArray::full(a_p, Zlength(current), current) *
                store(pointer_offset(tmp_p, i, sizeof(int), int),
                      int, partitioned[i - l]) *
                IntArray::mixed_missing_i(tmp_p, i, 0,
                                          Zlength(current), scratch_current) *
                Int64Array2::full(cost, 30, 2, counted_costs)
        */
        int value = tmp[i];
        /*@ Assert
              exists counted_costs scratch_current current partitioned,
                l == l@pre && r == r@pre && bit == bit@pre &&
                0 <= l && l <= i && i < r && r <= n_total &&
                n_total <= 300000 && l <= mid && mid <= r &&
                mid == l + zeros && p == r &&
                0 <= bit && bit < 30 && 0 <= capacity &&
                capacity + (bit + 1) * (r - l) * (r - l) <=
                  9223372036854775807 &&
                -1 <= bit - 1 && bit - 1 < 30 &&
                Zlength(before) == n_total && Zlength(current) == n_total &&
                Zlength(scratch_current) == n_total &&
                mid <= Zlength(current) &&
                Zlength(scratch_current) == Zlength(current) &&
                Zlength(partitioned) == r - l &&
                Zlength(counted_costs) == 30 &&
                (forall b, (0 <= b && b < 30) =>
                  (Zlength(counted_costs[b]) == 2 &&
                   0 <= counted_costs[b][0] && 0 <= counted_costs[b][1])) &&
                (forall k, (0 <= k && k < n_total) =>
                  (0 <= current[k] && current[k] <= 1000000000)) &&
                (forall k, (0 <= k && k < Zlength(current)) =>
                  (0 <= current[k] && current[k] <= 1000000000)) &&
                (forall k, (0 <= k && k < Zlength(partitioned)) =>
                  (0 <= partitioned[k] && partitioned[k] <= 1000000000)) &&
                (forall k, (l <= k && k < r) =>
                  scratch_current[k] == Some(partitioned[k - l])) &&
                scratch_current[i] == Some(value) &&
                value == partitioned[i - l] &&
                0 <= value && value <= 1000000000 &&
                SolveCountPrefix(before, cost_before, counted_costs,
                                 l, r, bit, zeros, ones) &&
                CostBound(counted_costs,
                          capacity + (r - l) * (r - l)) &&
                StablePartitionPrefix(before, scratch_current,
                                      l, r, bit, r, p, 1) &&
                PartitionCopyBack(before, current, partitioned, l, r, i) &&
                store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
                IntArray::full(a_p, Zlength(current), current) *
                IntArray::mixed_full(tmp_p, Zlength(current), scratch_current) *
                Int64Array2::full(cost, 30, 2, counted_costs)
        */
        a[i] = value;
    }
    solve(l, mid, bit - 1)
        /*@ where capacity = capacity + (r - l) * (r - l) */;
    /*@ Assert
          exists partition_before partitioned partition_scratch counted_costs
                 first_after first_scratch first_cost,
            l == l@pre && r == r@pre && bit == bit@pre &&
            0 <= l && l <= mid && mid <= r && r <= n_total &&
            n_total <= 300000 && mid == l + zeros && p == r &&
            0 <= bit && bit < 30 && 0 <= capacity &&
            capacity + (bit + 1) * (r - l) * (r - l) <=
              9223372036854775807 &&
            -1 <= bit - 1 && bit - 1 < 30 &&
            Zlength(partition_before) == n_total &&
            Zlength(partitioned) == r - l &&
            Zlength(partition_scratch) == n_total &&
            Zlength(first_after) == n_total &&
            Zlength(first_scratch) == n_total &&
            Zlength(first_cost) == 30 &&
            (forall b, (0 <= b && b < 30) =>
              (Zlength(first_cost[b]) == 2 &&
               0 <= first_cost[b][0] && 0 <= first_cost[b][1])) &&
            (forall k, (0 <= k && k < n_total) =>
              (0 <= first_after[k] && first_after[k] <= 1000000000)) &&
            (forall k, (l <= k && k < r) =>
              partition_scratch[k] == Some(partitioned[k - l])) &&
            SolveCountPrefix(before, cost_before, counted_costs,
                             l, r, bit, zeros, ones) &&
            StablePartitionPrefix(before, partition_scratch,
                                  l, r, bit, r, p, 1) &&
            PartitionCopyBack(before, partition_before, partitioned,
                              l, r, r) &&
            SolveEffect(partition_before, first_after,
                        counted_costs, first_cost,
                        l, mid, bit - 1) &&
            CostBound(first_cost,
                      capacity + (r - l) * (r - l) +
                      bit * (mid - l) * (mid - l)) &&
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            IntArray::full(a_p, Zlength(first_after), first_after) *
            IntArray::mixed_full(tmp_p, Zlength(first_after), first_scratch) *
            Int64Array2::full(cost, 30, 2, first_cost)
    */
    solve(mid, r, bit - 1)
        /*@ where capacity = capacity + (r - l) * (r - l) +
                              bit * (mid - l) * (mid - l) */;
}
typedef unsigned long size_t;

void *malloc(size_t size)
/*@ malloc_int
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure exists cells,
      __return != 0 && Zlength(cells) == cap &&
      IntArray::mixed_full(__return, cap, cells)
*/;

void free(void *ptr)
/*@ free_int
    With (cap : Z)
    Require 0 <= cap && IntArray::undef_full(ptr, cap)
    Ensure emp
*/;

static void solver(const int *input, int n, long long *out_inv,
                   int *out_x) /* QCP_INSERT_BEGIN:P068_1416C_xor_inverse.contract */

/*@ With (input_values : list Z) (a_before tmp_before : Z)
    Require
      1 <= Zlength(input_values) && Zlength(input_values) <= 300000 &&
      (forall i, (0 <= i && i < Zlength(input_values)) =>
        (0 <= input_values[i] && input_values[i] <= 1000000000)) &&
      n == Zlength(input_values) &&
      IntArray::full(input, n, input_values) *
      Int64Array2::undef_full(cost, 30, 2) *
      store(&a, int *, a_before) * store(&tmp, int *, tmp_before) *
      undef_data_at(out_inv) * undef_data_at(out_x)
    Ensure
      exists inv x cost_post,
        Spec(input_values, pair(inv, x)) &&
        IntArray::full(input, n, input_values) *
        Int64Array2::full(cost, 30, 2, cost_post) *
        store(&a, int *, 0) * store(&tmp, int *, 0) *
        store(out_inv, long long, inv) * store(out_x, int, x)
*/
/* QCP_INSERT_END:P068_1416C_xor_inverse.contract */
{
    a = malloc((size_t)n * sizeof(*a))
        /*@ where (malloc_int) cap = n */;
    tmp = malloc((size_t)n * sizeof(*tmp))
        /*@ where (malloc_int) cap = n */;
    /*@ Inv Assert
          exists a_p tmp_p a_cells tmp_cells,
            input == input@pre && n == n@pre &&
            out_inv == out_inv@pre && out_x == out_x@pre &&
            n@pre == Zlength(input_values) &&
            1 <= n@pre && n@pre <= 300000 &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= input_values[k] && input_values[k] <= 1000000000)) &&
            0 <= i && i <= n@pre &&
            Zlength(a_cells) == n@pre && Zlength(tmp_cells) == n@pre &&
            InputCopyPrefix(input_values, a_cells, i) &&
            IntArray::full(input@pre, n@pre, input_values) *
            IntArray::mixed_full(a_p, n@pre, a_cells) *
            IntArray::mixed_full(tmp_p, n@pre, tmp_cells) *
            Int64Array2::undef_full(cost, 30, 2) *
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            undef_data_at(out_inv@pre) * undef_data_at(out_x@pre)
    */
    for (int i = 0; i < n; i = i + 1)
        a[i] = input[i];
    /*@ Inv Assert
          exists a_p tmp_p tmp_cells cost_cells zero_rows,
            input == input@pre && n == n@pre &&
            out_inv == out_inv@pre && out_x == out_x@pre &&
            n@pre == Zlength(input_values) &&
            1 <= n@pre && n@pre <= 300000 &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= input_values[k] && input_values[k] <= 1000000000)) &&
            0 <= b && b <= 30 && Zlength(tmp_cells) == n@pre &&
            Zlength(zero_rows) == b &&
            (forall row, (0 <= row && row < b) =>
              (Zlength(zero_rows[row]) == 2 &&
               zero_rows[row][0] == 0 && zero_rows[row][1] == 0)) &&
            ZeroCostPrefix(cost_cells, b) &&
            IntArray::full(input@pre, n@pre, input_values) *
            IntArray::full(a_p, n@pre, input_values) *
            IntArray::mixed_full(tmp_p, n@pre, tmp_cells) *
            Int64Array2::full(cost, b, 2, zero_rows) *
            Int64Array2::undef_full(pointer_offset(cost, b,
                                                   sizeof(long long[2]),
                                                   long long[2]),
                                    30 - b, 2) *
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            undef_data_at(out_inv@pre) * undef_data_at(out_x@pre)
    */
    for (int b = 0; b < 30; b = b + 1)
    {
        /*@ Assert
              exists a_p tmp_p tmp_cells cost_cells zero_rows,
                input == input@pre && n == n@pre &&
                out_inv == out_inv@pre && out_x == out_x@pre &&
                n@pre == Zlength(input_values) &&
                1 <= n@pre && n@pre <= 300000 &&
                (forall k, (0 <= k && k < n@pre) =>
                  (0 <= input_values[k] &&
                   input_values[k] <= 1000000000)) &&
                0 <= b && b < 30 && Zlength(tmp_cells) == n@pre &&
                Zlength(zero_rows) == b &&
                (forall row, (0 <= row && row < b) =>
                  (Zlength(zero_rows[row]) == 2 &&
                   zero_rows[row][0] == 0 && zero_rows[row][1] == 0)) &&
                ZeroCostPrefix(cost_cells, b) &&
                IntArray::full(input@pre, n@pre, input_values) *
                IntArray::full(a_p, n@pre, input_values) *
                IntArray::mixed_full(tmp_p, n@pre, tmp_cells) *
                Int64Array2::full(cost, b, 2, zero_rows) *
                undef_data_at(pointer_offset(pointer_offset(
                                cost, b, sizeof(long long[2]), long long[2]),
                                0, sizeof(long long), long long)) *
                undef_data_at(pointer_offset(pointer_offset(
                                cost, b, sizeof(long long[2]), long long[2]),
                                1, sizeof(long long), long long)) *
                Int64Array2::undef_full(pointer_offset(cost, b + 1,
                                                       sizeof(long long[2]),
                                                       long long[2]),
                                        30 - b - 1, 2) *
                store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
                undef_data_at(out_inv@pre) * undef_data_at(out_x@pre)
        */
        cost[b][1] = 0;
        cost[b][0] = 0;
    }
    /*@ Assert
          exists a_p tmp_p tmp_cells zero_costs,
            input == input@pre && n == n@pre &&
            out_inv == out_inv@pre && out_x == out_x@pre &&
            n@pre == Zlength(input_values) &&
            1 <= n@pre && n@pre <= 300000 &&
            Zlength(tmp_cells) == Zlength(input_values) &&
            Zlength(zero_costs) == 30 &&
            (forall b, (0 <= b && b < 30) =>
              (Zlength(zero_costs[b]) == 2 &&
               zero_costs[b][0] == 0 && zero_costs[b][1] == 0)) &&
            CostBound(zero_costs, 0) &&
            30 * n@pre * n@pre <= 9223372036854775807 &&
            (forall k, (0 <= k && k < Zlength(input_values)) =>
              (0 <= input_values[k] && input_values[k] <= 1000000000)) &&
            IntArray::full(input@pre, n@pre, input_values) *
            IntArray::full(a_p, Zlength(input_values), input_values) *
            IntArray::mixed_full(tmp_p, Zlength(input_values), tmp_cells) *
            Int64Array2::full(cost, 30, 2, zero_costs) *
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            undef_data_at(out_inv@pre) * undef_data_at(out_x@pre)
    */
    solve(0, n, 29) /*@ where capacity = 0 */;
    long long inv = 0;
    int x = 0;
    /*@ Inv Assert
          exists a_p tmp_p current tmp_cells costs,
            input == input@pre && n == n@pre &&
            out_inv == out_inv@pre && out_x == out_x@pre &&
            n@pre == Zlength(input_values) &&
            1 <= n@pre && n@pre <= 300000 &&
            0 <= b && b <= 30 && 0 <= inv && inv <= 90000000000 &&
            0 <= x && x < 1073741824 &&
            Zlength(current) == n@pre && Zlength(tmp_cells) == n@pre &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= input_values[k] && input_values[k] <= 1000000000)) &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= current[k] && current[k] <= 1000000000)) &&
            XorChoicePrefix(input_values, costs, b, inv, x) &&
            IntArray::full(input@pre, n@pre, input_values) *
            IntArray::full(a_p, n@pre, current) *
            IntArray::mixed_full(tmp_p, n@pre, tmp_cells) *
            Int64Array2::full(cost, 30, 2, costs) *
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            undef_data_at(out_inv@pre) * undef_data_at(out_x@pre)
    */
    for (int b = 0; b < 30; b = b + 1)
    {
        /*@ Assert
              exists a_p tmp_p current tmp_cells costs,
                input == input@pre && n == n@pre &&
                out_inv == out_inv@pre && out_x == out_x@pre &&
                n@pre == Zlength(input_values) &&
                1 <= n@pre && n@pre <= 300000 &&
                0 <= b && b < 30 && 0 <= inv && inv <= 90000000000 &&
                0 <= x && x < 1073741824 &&
                Zlength(current) == n@pre && Zlength(tmp_cells) == n@pre &&
                (forall k, (0 <= k && k < n@pre) =>
                  (0 <= input_values[k] &&
                   input_values[k] <= 1000000000)) &&
                (forall k, (0 <= k && k < n@pre) =>
                  (0 <= current[k] && current[k] <= 1000000000)) &&
                XorChoicePrefix(input_values, costs, b, inv, x) &&
                IntArray::full(input@pre, n@pre, input_values) *
                IntArray::full(a_p, n@pre, current) *
                IntArray::mixed_full(tmp_p, n@pre, tmp_cells) *
                Int64Array2::full(cost, b, 2,
                                  sublist(0, b, costs)) *
                store(pointer_offset(pointer_offset(
                        cost, b, sizeof(long long[2]), long long[2]),
                        0, sizeof(long long), long long),
                      long long, costs[b][0]) *
                store(pointer_offset(pointer_offset(
                        cost, b, sizeof(long long[2]), long long[2]),
                        1, sizeof(long long), long long),
                      long long, costs[b][1]) *
                Int64Array2::full(pointer_offset(cost, b + 1,
                                                 sizeof(long long[2]),
                                                 long long[2]),
                                  30 - b - 1, 2,
                                  sublist(b + 1, 30, costs)) *
                store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
                undef_data_at(out_inv@pre) * undef_data_at(out_x@pre)
        */
        if (cost[b][1] < cost[b][0])
        {
            inv += cost[b][1];
            x |= 1 << b;
        }
        else
            inv += cost[b][0];
    }
    *out_inv = inv;
    *out_x = x;
    /*@ Assert
          exists a_p tmp_p costs,
            input == input@pre && n == n@pre &&
            out_inv == out_inv@pre && out_x == out_x@pre &&
            0 <= n@pre && Spec(input_values, pair(inv, x)) &&
            IntArray::full(input@pre, n@pre, input_values) *
            IntArray::undef_full(a_p, n@pre) *
            IntArray::undef_full(tmp_p, n@pre) *
            Int64Array2::full(cost, 30, 2, costs) *
            store(&a, int *, a_p) * store(&tmp, int *, tmp_p) *
            store(out_inv@pre, long long, inv) *
            store(out_x@pre, int, x)
    */
    free(a) /*@ where (free_int) cap = n@pre */;
    free(tmp) /*@ where (free_int) cap = n@pre */;
    a = 0;
    tmp = 0;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     int *input = malloc((size_t)n * sizeof(*input));
//     for (int i = 0; i < n; ++i)
//         scanf("%d", &input[i]);
//     long long inv;
//     int x;
//     solver(input, n, &inv, &x);
//     printf("%lld %d\n", inv, x);
//     free(input);
//     return 0;
// }
