/* Codeforces 400/E - Inna and Binary Logic */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;
/* Trusted, success-only allocator models: verification assumes these calls
 * return fresh non-NULL storage. Standard C allocation may fail; these
 * contracts do not prove absence of out-of-memory failures.
 * The conservative byte bound covers every allocation made by this case. */
void *malloc(size_t size)
/*@ With (cap : Z)
    Require
      0 < cap &&
      size == cap * sizeof(int) &&
      size <= INT_MAX
    Ensure
      __return != 0 &&
      IntArray::undef_full(__return, cap)
*/;

void *calloc(size_t count, size_t size)
/*@ calloc_int
    Require
      0 < count && count * size <= INT_MAX &&
      size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, count, repeat_Z(0, count))
*/
/*@ calloc_int64
    Require
      0 < count && count * size <= INT_MAX &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, count, repeat_Z(0, count))
*/;
void free(void *ptr)
/*@ free_int
    With (cap : Z) (contents : list Z)
    Require IntArray::full(ptr, cap, contents)
    Ensure emp
*/
/*@ free_int64
    With (cap : Z) (contents : list Z)
    Require Int64Array::full(ptr, cap, contents)
    Ensure emp
*/;
#define NULL 0
#define BITS 17
static int n, *pref, *suff, *len;
static long long *cnt;
#define IX(bit, node) ((size_t)(bit) * 4 * n + (node))
/*@ Extern Coq
      (P073Summary : Z -> list Z -> Z -> Z -> Z -> Prop)
      (P073Layout : Z -> Z -> Z -> Z -> Prop)
      (P073Tree : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073ZeroTree : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073OutsideTree : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073NodePrefix : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073NodeFrame : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073BufferBounds : Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073Weighted : list Z -> Z -> Z)
      (P073History : list Z -> list (Z * Z) -> Z -> list Z -> list Z -> Prop)
      (ApplyPointUpdate : list Z -> Z * Z -> list Z)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P073_400E_inna_and_binary_logic_lib */
static void pull(int v)
/*@ With (N PP SP CP LP : Z) (pr su ct ln xs ys : list Z)
    Require
      1 <= N && N <= 100000 && 1 <= v && 2*v+1 < 4*N &&
      0 < Zlength(xs) && 0 < Zlength(ys) && Zlength(xs)+Zlength(ys) <= N &&
      Znth(v, ln, 0) == Zlength(xs)+Zlength(ys) &&
      Znth(2*v, ln, 0) == Zlength(xs) && Znth(2*v+1, ln, 0) == Zlength(ys) &&
      P073NodePrefix(N, 2*v, 17, xs, pr, su, ct) &&
      P073NodePrefix(N, 2*v+1, 17, ys, pr, su, ct) &&
      P073BufferBounds(N, pr, su, ct, ln) &&
      data_at(&n, int, N) * data_at(&pref, int *, PP) *
      data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
      IntArray::full(PP, 68*N, pr) * IntArray::full(SP, 68*N, su) *
      Int64Array::full(CP, 68*N, ct) * IntArray::full(LP, 4*N, ln)
    Ensure exists pr1 su1 ct1,
      P073NodePrefix(N, v, 17, app(xs, ys), pr1, su1, ct1) &&
      P073NodeFrame(N, v, 17, pr, su, ct, pr1, su1, ct1) &&
      P073BufferBounds(N, pr1, su1, ct1, ln) &&
      data_at(&n, int, N) * data_at(&pref, int *, PP) *
      data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
      IntArray::full(PP, 68*N, pr1) * IntArray::full(SP, 68*N, su1) *
      Int64Array::full(CP, 68*N, ct1) * IntArray::full(LP, 4*N, ln)
*/
{
    /*@ Inv Assert exists pr1 su1 ct1,
      v == v@pre && 1 <= N && N <= 100000 && 1 <= v && 2*v+1 < 4*N &&
      0 <= b && b <= 17 &&
      0 < Zlength(xs) && 0 < Zlength(ys) && Zlength(xs)+Zlength(ys) <= N &&
      Znth(v, ln, 0) == Zlength(xs)+Zlength(ys) &&
      Znth(2*v, ln, 0) == Zlength(xs) && Znth(2*v+1, ln, 0) == Zlength(ys) &&
      P073NodePrefix(N, 2*v, 17, xs, pr1, su1, ct1) &&
      P073NodePrefix(N, 2*v+1, 17, ys, pr1, su1, ct1) &&
      P073NodePrefix(N, v, b, app(xs, ys), pr1, su1, ct1) &&
      P073NodeFrame(N, v, b, pr, su, ct, pr1, su1, ct1) &&
      P073BufferBounds(N, pr1, su1, ct1, ln) &&
      data_at(&n, int, N) * data_at(&pref, int *, PP) *
      data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
      IntArray::full(PP, 68*N, pr1) * IntArray::full(SP, 68*N, su1) *
      Int64Array::full(CP, 68*N, ct1) * IntArray::full(LP, 4*N, ln)
    */
    for (int b = 0; b < BITS; ++b)
    {
        int L = v * 2, R = L + 1;
        /*@ 0 <= (b*4)*N+v && (b*4)*N+v < 68*N &&
            0 <= (b*4)*N+L && (b*4)*N+L < 68*N &&
            0 <= (b*4)*N+R && (b*4)*N+R < 68*N &&
            0 <= L && L < 4*N && 0 <= R && R < 4*N by local */
        pref[IX(b, v)] = pref[IX(b, L)] + (pref[IX(b, L)] == len[L] ? pref[IX(b, R)] : 0);
        suff[IX(b, v)] = suff[IX(b, R)] + (suff[IX(b, R)] == len[R] ? suff[IX(b, L)] : 0);
        cnt[IX(b, v)] = cnt[IX(b, L)] + cnt[IX(b, R)] + (long long)suff[IX(b, L)] * pref[IX(b, R)];
    }
}
static void build(int v, int l, int r, const int *a)
/*@ With (N PP SP CP LP : Z) (xs pr su ct ln : list Z)
    Require
      1 <= N && N <= 100000 && 1 <= v && v < 4*N &&
      0 <= l && l < r && r <= N && Zlength(xs) == N && Zlength(ln) == 4*N &&
      (forall k, (0 <= k && k < N) => (0 <= xs[k] && xs[k] <= 100000)) &&
      P073Layout(N, v, l, r) && P073ZeroTree(N, v, l, r, pr, su, ct, ln) &&
      P073BufferBounds(N, pr, su, ct, ln) &&
      data_at(&n, int, N) * data_at(&pref, int *, PP) *
      data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
      IntArray::full(a, N, xs) *
      IntArray::full(PP, 68*N, pr) * IntArray::full(SP, 68*N, su) *
      Int64Array::full(CP, 68*N, ct) * IntArray::full(LP, 4*N, ln)
    Ensure exists pr1 su1 ct1 ln1,
      P073Tree(N, v, l, r, xs, pr1, su1, ct1, ln1) &&
      P073OutsideTree(N, v, l, r, pr, su, ct, ln, pr1, su1, ct1, ln1) &&
      P073BufferBounds(N, pr1, su1, ct1, ln1) &&
      data_at(&n, int, N) * data_at(&pref, int *, PP) *
      data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
      IntArray::full(a, N, xs) *
      IntArray::full(PP, 68*N, pr1) * IntArray::full(SP, 68*N, su1) *
      Int64Array::full(CP, 68*N, ct1) * IntArray::full(LP, 4*N, ln1)
*/
{
    len[v] = r - l;
    if (r - l == 1)
    {
        /*@ Inv Assert exists pr1 su1 ct1,
          v == v@pre && l == l@pre && r == r@pre && a == a@pre &&
          1 <= N && N <= 100000 && 1 <= v && v < 4*N &&
          0 <= l && r == l+1 && r <= N && 0 <= b && b <= 17 &&
          (b < 17 => (0 <= (b*4)*N+v && (b*4)*N+v < 68*N)) &&
          Zlength(xs) == N && Zlength(ln) == 4*N &&
          (forall k, (0 <= k && k < N) => (0 <= xs[k] && xs[k] <= 100000)) &&
          P073Layout(N, v, l, r) && P073ZeroTree(N, v, l, r, pr, su, ct, ln) &&
          P073NodePrefix(N, v, b, sublist(l, r, xs), pr1, su1, ct1) &&
          P073NodeFrame(N, v, b, pr, su, ct, pr1, su1, ct1) &&
          P073BufferBounds(N, pr1, su1, ct1, replace_Znth(v, r-l, ln)) &&
          data_at(&n, int, N) * data_at(&pref, int *, PP) *
          data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
          IntArray::full(a, N, xs) *
          IntArray::full(PP, 68*N, pr1) * IntArray::full(SP, 68*N, su1) *
          Int64Array::full(CP, 68*N, ct1) * IntArray::full(LP, 4*N, replace_Znth(v, r-l, ln))
        */
        for (int b = 0; b < BITS; ++b)
            if ((a[l] >> b) & 1)
            {
                cnt[IX(b, v)] = 1;
                suff[IX(b, v)] = 1;
                pref[IX(b, v)] = 1;
            }
        return;
    }
    int m = (l + r) / 2;
    build(v * 2, l, m, a) /*@ where N = N, PP = PP, SP = SP, CP = CP, LP = LP, xs = xs */;
    build(v * 2 + 1, m, r, a) /*@ where N = N, PP = PP, SP = SP, CP = CP, LP = LP, xs = xs */;
    pull(v) /*@ where N = N, PP = PP, SP = SP, CP = CP, LP = LP,
                      xs = sublist(l, m, xs), ys = sublist(m, r, xs) */;
}
static void update(int v, int l, int r, int p, int x)
/*@ With (N PP SP CP LP : Z) (xs pr su ct ln : list Z)
    Require
      1 <= N && N <= 100000 && 1 <= v && v < 4*N &&
      0 <= l && l <= p && p < r && r <= N && 0 <= x && x <= 100000 &&
      Zlength(xs) == N &&
      (forall k, (0 <= k && k < N) => (0 <= xs[k] && xs[k] <= 100000)) &&
      P073Layout(N, v, l, r) && P073Tree(N, v, l, r, xs, pr, su, ct, ln) &&
      P073BufferBounds(N, pr, su, ct, ln) &&
      data_at(&n, int, N) * data_at(&pref, int *, PP) *
      data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
      IntArray::full(PP, 68*N, pr) * IntArray::full(SP, 68*N, su) *
      Int64Array::full(CP, 68*N, ct) * IntArray::full(LP, 4*N, ln)
    Ensure exists pr1 su1 ct1,
      P073Tree(N, v, l, r, replace_Znth(p, x, xs), pr1, su1, ct1, ln) &&
      P073OutsideTree(N, v, l, r, pr, su, ct, ln, pr1, su1, ct1, ln) &&
      P073BufferBounds(N, pr1, su1, ct1, ln) &&
      data_at(&n, int, N) * data_at(&pref, int *, PP) *
      data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
      IntArray::full(PP, 68*N, pr1) * IntArray::full(SP, 68*N, su1) *
      Int64Array::full(CP, 68*N, ct1) * IntArray::full(LP, 4*N, ln)
*/
{
    if (r - l == 1)
    {
        /*@ Inv Assert exists pr1 su1 ct1,
          v == v@pre && l == l@pre && r == r@pre && p == p@pre && x == x@pre &&
          1 <= N && N <= 100000 && 1 <= v && v < 4*N &&
          0 <= l && p == l && r == l+1 && r <= N && 0 <= x && x <= 100000 &&
          0 <= b && b <= 17 && Zlength(xs) == N &&
          (b < 17 => (0 <= (b*4)*N+v && (b*4)*N+v < 68*N)) &&
          (forall k, (0 <= k && k < N) => (0 <= xs[k] && xs[k] <= 100000)) &&
          P073Layout(N, v, l, r) && P073Tree(N, v, l, r, xs, pr, su, ct, ln) &&
          P073NodePrefix(N, v, b, sublist(l, r, replace_Znth(p, x, xs)), pr1, su1, ct1) &&
          P073NodeFrame(N, v, b, pr, su, ct, pr1, su1, ct1) &&
          P073BufferBounds(N, pr1, su1, ct1, ln) &&
          data_at(&n, int, N) * data_at(&pref, int *, PP) *
          data_at(&suff, int *, SP) * data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
          IntArray::full(PP, 68*N, pr1) * IntArray::full(SP, 68*N, su1) *
          Int64Array::full(CP, 68*N, ct1) * IntArray::full(LP, 4*N, ln)
        */
        for (int b = 0; b < BITS; ++b)
        {
            int on = (x >> b) & 1;
            suff[IX(b, v)] = on;
            pref[IX(b, v)] = on;
            cnt[IX(b, v)] = on;
        }
        return;
    }
    int m = (l + r) / 2;
    if (p < m)
        update(v * 2, l, m, p, x) /*@ where N = N, PP = PP, SP = SP, CP = CP, LP = LP, xs = xs */;
    else
        update(v * 2 + 1, m, r, p, x) /*@ where N = N, PP = PP, SP = SP, CP = CP, LP = LP, xs = xs */;
    pull(v) /*@ where N = N, PP = PP, SP = SP, CP = CP, LP = LP,
                      xs = sublist(l, m, replace_Znth(p, x, xs)),
                      ys = sublist(m, r, replace_Znth(p, x, xs)) */;
}
/* QCP_INSERT_BEGIN:P073_400E_inna_and_binary_logic.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : list Z -> list (Z * Z) -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P073_400E_inna_and_binary_logic_lib */
/* QCP_INSERT_END:P073_400E_inna_and_binary_logic.support */
static void solver(int size, const int *input, int m, const int *positions, const int *values,
                   long long *out) /* QCP_INSERT_BEGIN:P073_400E_inna_and_binary_logic.contract */

/*@ With (initial_a : list Z)
             (updates : list (Z * Z))
             (positions_data values_data : list Z)
    Require
      1 <= Zlength(initial_a) && Zlength(initial_a) <= 100000 &&
      1 <= Zlength(updates) && Zlength(updates) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(initial_a)) => (0 <= initial_a[i] && initial_a[i] <= 100000)) &&
      (forall i, (0 <= i && i < Zlength(updates)) => ((0 <= fst(updates[i]) && fst(updates[i]) < Zlength(initial_a)) && (0 <= snd(updates[i]) && snd(updates[i]) <= 100000))) &&
      size == Zlength(initial_a) && m == Zlength(updates) &&
      Zlength(positions_data) == m && Zlength(values_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (fst(updates[i]) == positions_data[i] &&
         snd(updates[i]) == values_data[i])) &&
      IntArray::full(input, size, initial_a) *
      IntArray::full(positions, m, positions_data) *
      IntArray::full(values, m, values_data) *
      Int64Array::undef_full(out, m) *
      undef_data_at(&n, int) *
      undef_data_at(&pref, int *) *
      undef_data_at(&suff, int *) *
      undef_data_at(&cnt, long long *) *
      undef_data_at(&len, int *)
    Ensure
      exists result,
        Spec(initial_a, updates, result) &&
        IntArray::full(input, size, initial_a) *
        IntArray::full(positions, m, positions_data) *
        IntArray::full(values, m, values_data) *
        Int64Array::full(out, m, result) *
        data_at(&n, int, size) *
        data_at(&pref, int *, 0) *
        data_at(&suff, int *, 0) *
        data_at(&cnt, long long *, 0) *
        data_at(&len, int *, 0)
*/
/* QCP_INSERT_END:P073_400E_inna_and_binary_logic.contract */
{
    n = size;
    /*@ Assert exists original,
        original == initial_a &&
        size == size@pre && input == input@pre && m == m@pre &&
        positions == positions@pre && values == values@pre && out == out@pre &&
        1 <= size && size <= 100000 && 1 <= m && m <= 100000 &&
        Zlength(original) == size && Zlength(updates) == m &&
        Zlength(positions_data) == m && Zlength(values_data) == m &&
        (forall k, (0 <= k && k < size) => (0 <= original[k] && original[k] <= 100000)) &&
        (forall k, (0 <= k && k < m) =>
          (0 <= fst(updates[k]) && fst(updates[k]) < size &&
           0 <= snd(updates[k]) && snd(updates[k]) <= 100000 &&
           fst(updates[k]) == positions_data[k] && snd(updates[k]) == values_data[k])) &&
        IntArray::full(input, size, original) *
        IntArray::full(positions, m, positions_data) *
        IntArray::full(values, m, values_data) *
        Int64Array::undef_full(out, m) *
        data_at(&n, int, size) *
        undef_data_at(&pref, int *) * undef_data_at(&suff, int *) *
        undef_data_at(&cnt, long long *) * undef_data_at(&len, int *)
    */
    //@ Given original
    int *a = malloc((size_t)n * sizeof(*a)) /*@ where cap = size */;
    /*@ Inv Assert
        original == initial_a &&
        size == size@pre && input == input@pre && m == m@pre &&
        positions == positions@pre && values == values@pre && out == out@pre &&
        1 <= size && size <= 100000 && 1 <= m && m <= 100000 &&
        0 <= i && i <= size &&
        Zlength(original) == size && Zlength(updates) == m &&
        Zlength(positions_data) == m && Zlength(values_data) == m &&
        (forall k, (0 <= k && k < size) => (0 <= original[k] && original[k] <= 100000)) &&
        (forall k, (0 <= k && k < m) =>
          (0 <= fst(updates[k]) && fst(updates[k]) < size &&
           0 <= snd(updates[k]) && snd(updates[k]) <= 100000 &&
           fst(updates[k]) == positions_data[k] && snd(updates[k]) == values_data[k])) &&
        IntArray::full(input, size, original) *
        IntArray::full(positions, m, positions_data) *
        IntArray::full(values, m, values_data) *
        Int64Array::undef_full(out, m) *
        IntArray::seg(a, 0, i, sublist(0, i, original)) *
        IntArray::undef_seg(a, i, size) *
        data_at(&n, int, size) *
        undef_data_at(&pref, int *) * undef_data_at(&suff, int *) *
        undef_data_at(&cnt, long long *) * undef_data_at(&len, int *)
    */
    for (int i = 0; i < n; ++i)
        a[i] = input[i];
    /*@ Assert
        original == initial_a &&
        size == size@pre && input == input@pre && m == m@pre &&
        positions == positions@pre && values == values@pre && out == out@pre &&
        1 <= size && size <= 100000 && 1 <= m && m <= 100000 &&
        Zlength(original) == size && Zlength(updates) == m &&
        Zlength(positions_data) == m && Zlength(values_data) == m &&
        (forall k, (0 <= k && k < size) => (0 <= original[k] && original[k] <= 100000)) &&
        (forall k, (0 <= k && k < m) =>
          (0 <= fst(updates[k]) && fst(updates[k]) < size &&
           0 <= snd(updates[k]) && snd(updates[k]) <= 100000 &&
           fst(updates[k]) == positions_data[k] && snd(updates[k]) == values_data[k])) &&
        IntArray::full(input, size, original) * IntArray::full(a, size, original) *
        IntArray::full(positions, m, positions_data) * IntArray::full(values, m, values_data) *
        Int64Array::undef_full(out, m) * data_at(&n, int, size) *
        undef_data_at(&pref, int *) * undef_data_at(&suff, int *) *
        undef_data_at(&cnt, long long *) * undef_data_at(&len, int *)
    */
    size_t all = (size_t)BITS * 4 * n;
    pref = calloc(all, sizeof(*pref)) /*@ where (calloc_int) */;
    suff = calloc(all, sizeof(*suff)) /*@ where (calloc_int) */;
    cnt = calloc(all, sizeof(*cnt)) /*@ where (calloc_int64) */;
    len = calloc((size_t)4 * n, sizeof(*len)) /*@ where (calloc_int) */;
    /*@ Assert exists PP SP CP LP,
        original == initial_a &&
        size == size@pre && input == input@pre && m == m@pre &&
        positions == positions@pre && values == values@pre && out == out@pre &&
        1 <= size && size <= 100000 && 1 <= m && m <= 100000 && all == 68*size &&
        Zlength(original) == size && Zlength(updates) == m &&
        Zlength(positions_data) == m && Zlength(values_data) == m &&
        (forall k, (0 <= k && k < size) => (0 <= original[k] && original[k] <= 100000)) &&
        (forall k, (0 <= k && k < m) =>
          (0 <= fst(updates[k]) && fst(updates[k]) < size &&
           0 <= snd(updates[k]) && snd(updates[k]) <= 100000 &&
           fst(updates[k]) == positions_data[k] && snd(updates[k]) == values_data[k])) &&
        P073Layout(size, 1, 0, size) &&
        P073ZeroTree(size, 1, 0, size, repeat_Z(0,68*size), repeat_Z(0,68*size),
                      repeat_Z(0,68*size), repeat_Z(0,4*size)) &&
        P073BufferBounds(size, repeat_Z(0,68*size), repeat_Z(0,68*size),
                           repeat_Z(0,68*size), repeat_Z(0,4*size)) &&
        IntArray::full(input, size, original) * IntArray::full(a, size, original) *
        IntArray::full(positions, m, positions_data) * IntArray::full(values, m, values_data) *
        Int64Array::undef_full(out, m) *
        data_at(&n, int, size) * data_at(&pref, int *, PP) * data_at(&suff, int *, SP) *
        data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
        IntArray::full(PP, 68*size, repeat_Z(0,68*size)) *
        IntArray::full(SP, 68*size, repeat_Z(0,68*size)) *
        Int64Array::full(CP, 68*size, repeat_Z(0,68*size)) *
        IntArray::full(LP, 4*size, repeat_Z(0,4*size))
    */
    build(1, 0, n, a) /*@ where N = size, xs = original,
        pr = repeat_Z(0, 68*size), su = repeat_Z(0, 68*size),
        ct = repeat_Z(0, 68*size), ln = repeat_Z(0, 4*size) */;
    /*@ Inv Assert exists cur pr su ct ln PP SP CP LP result,
        original == initial_a &&
        size == size@pre && input == input@pre && m == m@pre &&
        positions == positions@pre && values == values@pre && out == out@pre &&
        1 <= size && size <= 100000 && 1 <= m && m <= 100000 &&
        0 <= i && i <= m && all == 68*size &&
        Zlength(original) == size && Zlength(cur) == size && Zlength(updates) == m &&
        Zlength(positions_data) == m && Zlength(values_data) == m &&
        (forall k, (0 <= k && k < size) => (0 <= cur[k] && cur[k] <= 100000)) &&
        (forall k, (0 <= k && k < m) =>
          (0 <= fst(updates[k]) && fst(updates[k]) < size &&
           0 <= snd(updates[k]) && snd(updates[k]) <= 100000 &&
           fst(updates[k]) == positions_data[k] && snd(updates[k]) == values_data[k])) &&
        P073Layout(size, 1, 0, size) &&
        P073Tree(size, 1, 0, size, cur, pr, su, ct, ln) &&
        P073BufferBounds(size, pr, su, ct, ln) &&
        P073History(original, updates, i, cur, result) &&
        IntArray::full(input, size, original) * IntArray::full(a, size, cur) *
        IntArray::full(positions, m, positions_data) * IntArray::full(values, m, values_data) *
        Int64Array::seg(out, 0, i, result) * Int64Array::undef_seg(out, i, m) *
        data_at(&n, int, size) * data_at(&pref, int *, PP) * data_at(&suff, int *, SP) *
        data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
        IntArray::full(PP, 68*size, pr) * IntArray::full(SP, 68*size, su) *
        Int64Array::full(CP, 68*size, ct) * IntArray::full(LP, 4*size, ln)
    */
    for (int i = 0; i < m; ++i)
    {
        //@ Given current from cur
        //@ Given completed from result
        int p = positions[i], v = values[i];
        a[p] = v;
        update(1, 0, n, p, v) /*@ where N = size, xs = current */;
        long long ans = 0;
        /*@ Inv Assert exists pr su ct ln PP SP CP LP,
          original == initial_a &&
          size == size@pre && input == input@pre && m == m@pre &&
          positions == positions@pre && values == values@pre && out == out@pre &&
          1 <= size && size <= 100000 && 1 <= m && m <= 100000 &&
          0 <= i && i < m && all == 68*size && 0 <= b && b <= 17 &&
          0 <= p && p < size && 0 <= v && v <= 100000 &&
          p == positions_data[i] && v == values_data[i] &&
          Zlength(original) == size && Zlength(current) == size && Zlength(updates) == m &&
          Zlength(positions_data) == m && Zlength(values_data) == m &&
          (forall k, (0 <= k && k < size) => (0 <= current[k] && current[k] <= 100000)) &&
          (forall k, (0 <= k && k < m) =>
            (0 <= fst(updates[k]) && fst(updates[k]) < size &&
             0 <= snd(updates[k]) && snd(updates[k]) <= 100000 &&
             fst(updates[k]) == positions_data[k] && snd(updates[k]) == values_data[k])) &&
          P073Layout(size, 1, 0, size) &&
          P073Tree(size, 1, 0, size, replace_Znth(p, v, current), pr, su, ct, ln) &&
          P073BufferBounds(size, pr, su, ct, ln) &&
          P073History(original, updates, i, current, completed) &&
          ans == P073Weighted(replace_Znth(p, v, current), b) &&
          0 <= ans && ans <= 655361553550000 &&
          (b < 17 => (0 <= (b*4)*size+1 && (b*4)*size+1 < 68*size)) &&
          IntArray::full(input, size, original) *
          IntArray::full(a, size, replace_Znth(p, v, current)) *
          IntArray::full(positions, m, positions_data) * IntArray::full(values, m, values_data) *
          Int64Array::seg(out, 0, i, completed) * Int64Array::undef_seg(out, i, m) *
          data_at(&n, int, size) * data_at(&pref, int *, PP) * data_at(&suff, int *, SP) *
          data_at(&cnt, long long *, CP) * data_at(&len, int *, LP) *
          IntArray::full(PP, 68*size, pr) * IntArray::full(SP, 68*size, su) *
          Int64Array::full(CP, 68*size, ct) * IntArray::full(LP, 4*size, ln)
        */
        for (int b = 0; b < BITS; ++b)
            ans += cnt[IX(b, 1)] * (1 << b);
        out[i] = ans;
    }
    //@ Given final_values from cur
    //@ Given final_prefix from pr
    //@ Given final_suffix from su
    //@ Given final_counts from ct
    //@ Given final_lengths from ln
    free(a) /*@ where (free_int) cap = size, contents = final_values */;
    free(pref) /*@ where (free_int) cap = 68*size, contents = final_prefix */;
    free(suff) /*@ where (free_int) cap = 68*size, contents = final_suffix */;
    free(cnt) /*@ where (free_int64) cap = 68*size, contents = final_counts */;
    free(len) /*@ where (free_int) cap = 4*size, contents = final_lengths */;
    len = NULL;
    suff = NULL;
    pref = NULL;
    cnt = NULL;
}
// int main(void)
// {
//     int size, m;
//     if (scanf("%d %d", &size, &m) != 2)
//         return 0;
//     int *a = malloc((size_t)size * sizeof(*a)), *positions = malloc((size_t)m * sizeof(*positions)),
//         *values = malloc((size_t)m * sizeof(*values));
//     long long *out = malloc((size_t)m * sizeof(*out));
//     for (int i = 0; i < size; ++i)
//         scanf("%d", &a[i]);
//     for (int i = 0; i < m; ++i)
//     {
//         scanf("%d %d", &positions[i], &values[i]);
//         --positions[i];
//     }
//     solver(size, a, m, positions, values, out);
//     for (int i = 0; i < m; ++i)
//         printf("%lld\n", out[i]);
//     free(a);
//     free(positions);
//     free(values);
//     free(out);
//     return 0;
// }
