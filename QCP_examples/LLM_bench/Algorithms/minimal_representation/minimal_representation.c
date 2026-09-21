/*
 * Find the lexicographically smallest cyclic rotation of an integer sequence.
 *
 * The sequence is copied twice into b so that every cyclic rotation is
 * represented by one contiguous segment.  The two-candidate scan eliminates
 * at least one possible starting position after every mismatch, and therefore
 * runs in linear time.
 *
 * The verification case limits n to 1000.  The caller provides n initialized
 * elements in a and room for n elements in out. The doubled buffer is local.
 * The function writes the smallest rotation to out and returns its zero-based
 * starting position in a.
 */
/*@ Extern Coq
      (MRRotation : list Z -> Z -> list Z)
      (MRRotationPrefixEq : list Z -> Z -> Z -> Z -> Prop)
      (MRRotationEq : list Z -> Z -> Z -> Prop)
      (MRFirstMinimalRotationAt : list Z -> Z -> Prop)
      (MRCandidateState : list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_lib */

int minimal_representation(int *a, int n, int *out)
/*@ With (l : list Z) (best : Z)
    Require
      1 <= n && n <= 1000 &&
      Zlength(l) == n &&
      0 <= best && best < n &&
      MRFirstMinimalRotationAt(l, best) &&
      IntArray::full(a, n, l) *
      IntArray::undef_full(out, n)
    Ensure
      MRFirstMinimalRotationAt(l, __return) &&
      IntArray::full(a, n, l) *
      IntArray::full(out, n, MRRotation(l, __return))
 */
{
    int b[2000];
    int p = 0;

    /*@ Inv Assert
        a == a@pre && n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        Zlength(l) == n@pre &&
        0 <= best && best < n@pre &&
        0 <= p && p <= n@pre &&
        MRFirstMinimalRotationAt(l, best) &&
        IntArray::full(a@pre, n@pre, l) *
        IntArray::seg(b, 0, p, sublist(0, p, l)) *
        IntArray::undef_seg(b, p, n@pre) *
        IntArray::seg(b, n@pre, n@pre + p, sublist(0, p, l)) *
        IntArray::undef_seg(b, n@pre + p, 2 * n@pre) *
        IntArray::undef_seg(b, 2 * n@pre, 2000) *
        IntArray::undef_full(out@pre, n@pre)
     */
    while (p < n) {
        b[p] = a[p];
        b[n + p] = a[p];
        ++p;
    }



    int i = 0;
    int j = 1;
    int k = 0;

    /*@ Inv Assert
        a == a@pre && n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        Zlength(l) == n@pre &&
        p == n@pre &&
        0 <= best && best < n@pre &&
        0 <= i && i < 2 * n@pre &&
        0 <= j && j < 2 * n@pre &&
        i != j &&
        (i < n@pre || j < n@pre) &&
        0 <= k && k < n@pre &&
        MRFirstMinimalRotationAt(l, best) &&
        MRCandidateState(l, best, i, j) &&
        IntArray::full(a@pre, n@pre, l) *
        IntArray::full(b, 2 * n@pre, app(l, l)) *
        IntArray::undef_seg(b, 2 * n@pre, 2000) *
        IntArray::undef_full(out@pre, n@pre)
     */
    while (i < n && j < n) {
        k = 0;

        /*@ Inv Assert
            a == a@pre && n == n@pre && out == out@pre &&
            1 <= n@pre && n@pre <= 1000 &&
            Zlength(l) == n@pre &&
            p == n@pre &&
            0 <= best && best < n@pre &&
            0 <= i && i < n@pre &&
            0 <= j && j < n@pre &&
            i != j &&
            0 <= k && k <= n@pre &&
            MRFirstMinimalRotationAt(l, best) &&
            MRCandidateState(l, best, i, j) &&
            MRRotationPrefixEq(l, i, j, k) &&
            IntArray::full(a@pre, n@pre, l) *
            IntArray::full(b, 2 * n@pre, app(l, l)) *
        IntArray::undef_seg(b, 2 * n@pre, 2000) *
            IntArray::undef_full(out@pre, n@pre)
         */
        while (k < n && b[i + k] == b[j + k]) {
            ++k;
        }

        if (k == n) {
            break;
        }

        if (b[i + k] > b[j + k]) {
            i = i + k + 1;
            if (i == j) {
                ++i;
            }
        }
        else {
            j = j + k + 1;
            if (i == j) {
                ++j;
            }
        }
    }

    /*@ Assert
        a == a@pre && n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        Zlength(l) == n@pre &&
        p == n@pre &&
        0 <= best && best < n@pre &&
        0 <= i && i < 2 * n@pre &&
        0 <= j && j < 2 * n@pre &&
        i != j &&
        (i < n@pre || j < n@pre) &&
        0 <= k && k <= n@pre &&
        (i < j => i == best) &&
        (i >= j => j == best) &&
        MRFirstMinimalRotationAt(l, best) &&
        IntArray::full(a@pre, n@pre, l) *
        IntArray::full(b, 2 * n@pre, app(l, l)) *
        IntArray::undef_seg(b, 2 * n@pre, 2000) *
        IntArray::undef_full(out@pre, n@pre)
     */
    if (i < j) {
        p = i;
    }
    else {
        p = j;
    }

    k = 0;
    /*@ Inv Assert
        a == a@pre && n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        Zlength(l) == n@pre &&
        0 <= best && best < n@pre &&
        p == best &&
        0 <= p && p < n@pre &&
        0 <= i && i < 2 * n@pre &&
        0 <= j && j < 2 * n@pre &&
        i != j &&
        0 <= k && k <= n@pre &&
        MRFirstMinimalRotationAt(l, best) &&
        IntArray::full(a@pre, n@pre, l) *
        IntArray::full(b, 2 * n@pre, app(l, l)) *
        IntArray::undef_seg(b, 2 * n@pre, 2000) *
        IntArray::seg(out@pre, 0, k, sublist(0, k, MRRotation(l, p))) *
        IntArray::undef_seg(out@pre, k, n@pre)
     */
    while (k < n) {
        out[k] = b[p + k];
        ++k;
    }

    /*@ Assert
        a == a@pre && n == n@pre && out == out@pre &&
        0 <= i && 0 <= j && 0 <= k &&
        MRFirstMinimalRotationAt(l, p) &&
        IntArray::full(a, n, l) *
        IntArray::full(out, n, MRRotation(l, p)) *
        IntArray::undef_full(b, 2000)
     */
    return p;
}
