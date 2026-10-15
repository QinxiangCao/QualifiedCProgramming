/*
 * Codeforces 1721/D - Maximum AND  (rating 1800, BITMASKS)
 *
 * Build the answer greedily from the top bit down: a mask is achievable iff b
 * can be matched to a so that every pair XORs to a superset of the mask, i.e.
 * the multiset {a_i & mask} equals the multiset {~b_i & mask}.  Sorting both
 * lists and comparing tests that in O(n log n) per candidate bit.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P058-solver-support */
/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P058_1721D_maximum_and_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Z -> Prop)
      (MaskFeasible : list Z -> list Z -> Z -> Prop)
      (MaskedBuffersPrefix : list Z -> list Z -> Z -> list Z -> list Z -> Z -> Prop)
      (GreedyMaskPrefixOptimal : list Z -> list Z -> Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P058-solver-support */

void quicksort(const unsigned *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 200000 &&
      UIntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        UIntArray::full(arr, n, l1)
*/
;

// static int cmp_uint(const void *x, const void *y)
// {
//     unsigned a = *(const unsigned *)x, b = *(const unsigned *)y;
//     return (a > b) - (a < b);
// }

/* feasible: can b be permuted so that (a_i ^ b_i) & mask == mask for all i? */
static int feasible(const unsigned *a, const unsigned *b, int n, unsigned mask,
                    unsigned *ka, unsigned *kb)
/*@ With (left : list Z) (right : list Z)
    Require
      1 <= n && n <= 100000 &&
      n == Zlength(left) && Zlength(right) == n &&
      0 <= mask && mask < 1073741824 &&
      (forall i, (0 <= i && i < n) =>
        (0 <= left[i] && left[i] < 1073741824)) &&
      (forall i, (0 <= i && i < n) =>
        (0 <= right[i] && right[i] < 1073741824)) &&
      UIntArray::full(a, n, left) *
      UIntArray::full(b, n, right) *
      UIntArray::undef_full(ka, n) *
      UIntArray::undef_full(kb, n)
    Ensure
      0 <= __return && __return <= 1 &&
      (__return == 1 => MaskFeasible(left, right, mask@pre)) &&
      (__return == 0 => (! MaskFeasible(left, right, mask@pre))) &&
      UIntArray::full(a, n, left) *
      UIntArray::full(b, n, right) *
      UIntArray::full_shape(ka, n) *
      UIntArray::full_shape(kb, n)
*/
{
    /*@ Inv Assert
          exists ka_values kb_values,
            a == a@pre && b == b@pre && n == n@pre &&
            mask == mask@pre && ka == ka@pre && kb == kb@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            n@pre == Zlength(left) && Zlength(right) == n@pre &&
            0 <= mask@pre && mask@pre < 1073741824 &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= left[j] && left[j] < 1073741824)) &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= right[j] && right[j] < 1073741824)) &&
            0 <= i && i <= n@pre &&
            MaskedBuffersPrefix(left, right, mask@pre,
                                ka_values, kb_values, i) &&
            UIntArray::full(a, n@pre, left) *
            UIntArray::full(b, n@pre, right) *
            UIntArray::seg(ka, 0, i, ka_values) *
            UIntArray::undef_seg(ka, i, n@pre) *
            UIntArray::seg(kb, 0, i, kb_values) *
            UIntArray::undef_seg(kb, i, n@pre)
    */
    for (int i = 0; i < n; i++) {
        ka[i] = a[i] & mask;
        kb[i] = (~b[i]) & mask;
        /*@ Assert
              exists ka_next kb_next,
                a == a@pre && b == b@pre && n == n@pre &&
                mask == mask@pre && ka == ka@pre && kb == kb@pre &&
                1 <= n@pre && n@pre <= 100000 &&
                n@pre == Zlength(left) && Zlength(right) == n@pre &&
                0 <= mask@pre && mask@pre < 1073741824 &&
                (forall j, (0 <= j && j < n@pre) =>
                  (0 <= left[j] && left[j] < 1073741824)) &&
                (forall j, (0 <= j && j < n@pre) =>
                  (0 <= right[j] && right[j] < 1073741824)) &&
                0 <= i && i < n@pre &&
                MaskedBuffersPrefix(left, right, mask@pre,
                                    ka_next, kb_next, i + 1) &&
                UIntArray::full(a, n@pre, left) *
                UIntArray::full(b, n@pre, right) *
                UIntArray::seg(ka, 0, i + 1, ka_next) *
                UIntArray::undef_seg(ka, i + 1, n@pre) *
                UIntArray::seg(kb, 0, i + 1, kb_next) *
                UIntArray::undef_seg(kb, i + 1, n@pre)
        */
    }
    /*@ Assert
          exists ka_values kb_values,
            a == a@pre && b == b@pre && n == n@pre &&
            mask == mask@pre && ka == ka@pre && kb == kb@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            n@pre == Zlength(left) && Zlength(right) == n@pre &&
            0 <= mask@pre && mask@pre < 1073741824 &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= left[j] && left[j] < 1073741824)) &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= right[j] && right[j] < 1073741824)) &&
            MaskedBuffersPrefix(left, right, mask@pre,
                                ka_values, kb_values, n@pre) &&
            UIntArray::full(a, n@pre, left) *
            UIntArray::full(b, n@pre, right) *
            UIntArray::full(ka, n@pre, ka_values) *
            UIntArray::full(kb, n@pre, kb_values)
    */
    // qsort(ka, n, sizeof *ka, cmp_uint);
    // qsort(kb, n, sizeof *kb, cmp_uint);
    quicksort(ka, n);
    quicksort(kb, n);
    /*@ Assert
          exists ka_values kb_values sorted_ka sorted_kb,
            a == a@pre && b == b@pre && n == n@pre &&
            mask == mask@pre && ka == ka@pre && kb == kb@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            n@pre == Zlength(left) && Zlength(right) == n@pre &&
            0 <= mask@pre && mask@pre < 1073741824 &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= left[j] && left[j] < 1073741824)) &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= right[j] && right[j] < 1073741824)) &&
            MaskedBuffersPrefix(left, right, mask@pre,
                                ka_values, kb_values, n@pre) &&
            Permutation(ka_values, sorted_ka) &&
            Permutation(kb_values, sorted_kb) &&
            mono_nondec(sorted_ka) && mono_nondec(sorted_kb) &&
            UIntArray::full(a, n@pre, left) *
            UIntArray::full(b, n@pre, right) *
            UIntArray::full(ka, n@pre, sorted_ka) *
            UIntArray::full(kb, n@pre, sorted_kb)
    */
    /*@ Inv Assert
          exists ka_values kb_values sorted_ka sorted_kb,
            a == a@pre && b == b@pre && n == n@pre &&
            mask == mask@pre && ka == ka@pre && kb == kb@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            n@pre == Zlength(left) && Zlength(right) == n@pre &&
            0 <= mask@pre && mask@pre < 1073741824 &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= left[j] && left[j] < 1073741824)) &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= right[j] && right[j] < 1073741824)) &&
            0 <= i && i <= n@pre &&
            MaskedBuffersPrefix(left, right, mask@pre,
                                ka_values, kb_values, n@pre) &&
            Permutation(ka_values, sorted_ka) &&
            Permutation(kb_values, sorted_kb) &&
            mono_nondec(sorted_ka) && mono_nondec(sorted_kb) &&
            sublist(0, i, sorted_ka) == sublist(0, i, sorted_kb) &&
            UIntArray::full(a, n@pre, left) *
            UIntArray::full(b, n@pre, right) *
            UIntArray::full(ka, n@pre, sorted_ka) *
            UIntArray::full(kb, n@pre, sorted_kb)
    */
    for (int i = 0; i < n; i++)
        if (ka[i] != kb[i])
            return 0;
    return 1;
}

/* solver: maximum AND of the pairwise XORs over all pairings. */
static unsigned solver(const unsigned *a, const unsigned *b, int n,
                       unsigned *ka, unsigned *kb)
/* QCP_INSERT_BEGIN:shard09-P058-solver-contract */
/*@ With (left : list Z) (right : list Z)
    Require
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (0 <= left[i] && left[i] < 1073741824)) && (forall i, (0 <= i && i < n) => (0 <= right[i] && right[i] < 1073741824)) &&
      n == Zlength(left) && Zlength(right) == n && UIntArray::full(a, n, left) * UIntArray::full(b, n, right) * UIntArray::undef_full(ka, n) * UIntArray::undef_full(kb, n)
    Ensure
      Spec(left, right, __return) &&
      UIntArray::full(a, n, left) * UIntArray::full(b, n, right) * UIntArray::full_shape(ka, n) * UIntArray::full_shape(kb, n)
*/
/* QCP_INSERT_END:shard09-P058-solver-contract */
{
    unsigned ans = 0;
    /*@ Inv Assert
          a == a@pre && b == b@pre && n == n@pre &&
          ka == ka@pre && kb == kb@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          n@pre == Zlength(left) && Zlength(right) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (0 <= left[j] && left[j] < 1073741824)) &&
          (forall j, (0 <= j && j < n@pre) =>
            (0 <= right[j] && right[j] < 1073741824)) &&
          -1 <= bit && bit <= 29 &&
          0 <= ans && ans < 1073741824 &&
          GreedyMaskPrefixOptimal(left, right, bit, ans) &&
          UIntArray::full(a, n@pre, left) *
          UIntArray::full(b, n@pre, right) *
          ((0 <= bit &&
            UIntArray::undef_full(ka, n@pre) *
            UIntArray::undef_full(kb, n@pre)) ||
           (bit == -1 &&
            UIntArray::full_shape(ka, n@pre) *
            UIntArray::full_shape(kb, n@pre)))
    */
    for (int bit = 29; bit >= 0; bit--) {
        unsigned cand = ans | (1u << bit);
        /*@ 0 <= cand && cand < 1073741824 by local */
        if (feasible(a, b, n, cand, ka, kb)
              /*@ where left = left, right = right */)
            ans = cand;
    }
    return ans;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static unsigned a[100005], b[100005], ka[100005], kb[100005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%u", &a[i]);
//         for (int i = 0; i < n; i++)
//             scanf("%u", &b[i]);
//         printf("%u\n", solver(a, b, n, ka, kb));
//     }
//     return 0;
// }
