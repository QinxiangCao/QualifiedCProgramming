/* Codeforces 1194/C - From S To T */
// #include <stdio.h>
#include "string.h"

/* QCP_INSERT_BEGIN:P031_1194C_from_s_to_t.support */
/*@ Extern Coq
      (Spec : list Z -> list Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P031_1194C_from_s_to_t_lib */
/* QCP_INSERT_END:P031_1194C_from_s_to_t.support */
/*@ Extern Coq
      (CanInsertFromPool : list Z -> list Z -> list Z -> Prop)
      (GreedyPrefixMatch : list Z -> list Z -> Z -> Z -> Prop)
      (IsSubsequence : list Z -> list Z -> Prop)
      (NoSubsequence : list Z -> list Z -> Prop)
      (CountState : list Z -> list Z -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (NonnegativeCounts : list Z -> Prop)
      (SupplyShortage : list Z -> list Z -> list Z -> Prop)
*/
static int solver(const char *s, const char *t, const char *p)/* QCP_INSERT_BEGIN:P031_1194C_from_s_to_t.contract */

/*@ With (source target pool : list Z)
    Require
      1 <= Zlength(source) && Zlength(source) <= 100 &&
      1 <= Zlength(target) && Zlength(target) <= 100 &&
      1 <= Zlength(pool) && Zlength(pool) <= 100 &&
      (forall idx, (0 <= idx && idx < Zlength(source)) =>
        (97 <= source[idx] && source[idx] <= 122)) &&
      (forall idx, (0 <= idx && idx < Zlength(target)) =>
        (97 <= target[idx] && target[idx] <= 122)) &&
      (forall idx, (0 <= idx && idx < Zlength(pool)) =>
        (97 <= pool[idx] && pool[idx] <= 122)) &&
      CharArray::full(s, Zlength(source) + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, Zlength(source) + 1, 105) *
      CharArray::full(t, Zlength(target) + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, Zlength(target) + 1, 105) *
      CharArray::full(p, Zlength(pool) + 1, app(pool, cons(0, nil))) *
      CharArray::undef_seg(p, Zlength(pool) + 1, 105)
    Ensure
      Spec(source, target, pool, __return) &&
      CharArray::full(s, Zlength(source) + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, Zlength(source) + 1, 105) *
      CharArray::full(t, Zlength(target) + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, Zlength(target) + 1, 105) *
      CharArray::full(p, Zlength(pool) + 1, app(pool, cons(0, nil))) *
      CharArray::undef_seg(p, Zlength(pool) + 1, 105)
*/
/* QCP_INSERT_END:P031_1194C_from_s_to_t.contract */

{
    int i = 0, cnt[26] = {0};
    /*@ Inv Assert
          exists counts,
          s == s@pre && t == t@pre && p == p@pre &&
          1 <= Zlength(source) && Zlength(source) <= 100 &&
          1 <= Zlength(target) && Zlength(target) <= 100 &&
          1 <= Zlength(pool) && Zlength(pool) <= 100 &&
          (forall k, (0 <= k && k < Zlength(source)) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(target)) =>
            (97 <= target[k] && target[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(pool)) =>
            (97 <= pool[k] && pool[k] <= 122)) &&
          0 <= j && j <= Zlength(target) &&
          0 <= i && i <= Zlength(source) &&
          ((j == Zlength(target) && app(target, cons(0, nil))[j] == 0) ||
           (j < Zlength(target) &&
            app(target, cons(0, nil))[j] == target[j] &&
            97 <= target[j] && target[j] <= 122)) &&
          ((i == Zlength(source) && app(source, cons(0, nil))[i] == 0) ||
           (i < Zlength(source) &&
            app(source, cons(0, nil))[i] == source[i] &&
            97 <= source[i] && source[i] <= 122)) &&
          GreedyPrefixMatch(source, target, j, i) &&
          CountState(source, pool, target, 0, 0, 0, counts) &&
          NonnegativeCounts(counts) &&
          CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
          CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
          CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
          CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
          CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
          CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
          IntArray::full(cnt, 26, counts)
    */
    for (int j = 0; t[j]; ++j) if (s[i]) {
        /*@ 0 <= i && i < Zlength(source) */
        if (s[i] == t[j]) ++i;
    }
    if (s[i])
        /*@ Assert
              exists counts,
              s == s@pre && t == t@pre && p == p@pre &&
              0 <= i && i < Zlength(source) &&
              NoSubsequence(source, target) &&
              CountState(source, pool, target, 0, 0, 0, counts) &&
              NonnegativeCounts(counts) &&
              CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
              CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
              CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
              CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
              CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
              CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
              IntArray::full(cnt, 26, counts)
        */
        return 0;
    /*@ Assert
          exists counts,
          s == s@pre && t == t@pre && p == p@pre &&
          1 <= Zlength(source) && Zlength(source) <= 100 &&
          1 <= Zlength(target) && Zlength(target) <= 100 &&
          1 <= Zlength(pool) && Zlength(pool) <= 100 &&
          (forall k, (0 <= k && k < Zlength(source)) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(target)) =>
            (97 <= target[k] && target[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(pool)) =>
            (97 <= pool[k] && pool[k] <= 122)) &&
          i == Zlength(source) &&
          IsSubsequence(source, target) &&
          CountState(source, pool, target, 0, 0, 0, counts) &&
          NonnegativeCounts(counts) &&
          CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
          CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
          CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
          CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
          CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
          CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
          IntArray::full(cnt, 26, counts)
    */
    /*@ Inv Assert
          exists counts,
          s == s@pre && t == t@pre && p == p@pre &&
          1 <= Zlength(source) && Zlength(source) <= 100 &&
          1 <= Zlength(target) && Zlength(target) <= 100 &&
          1 <= Zlength(pool) && Zlength(pool) <= 100 &&
          (forall k, (0 <= k && k < Zlength(source)) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(target)) =>
            (97 <= target[k] && target[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(pool)) =>
            (97 <= pool[k] && pool[k] <= 122)) &&
          IsSubsequence(source, target) &&
          0 <= i && i <= Zlength(source) &&
          ((i == Zlength(source) && app(source, cons(0, nil))[i] == 0) ||
           (i < Zlength(source) &&
            app(source, cons(0, nil))[i] == source[i] &&
            97 <= source[i] && source[i] <= 122)) &&
          CountState(source, pool, target, i, 0, 0, counts) &&
          NonnegativeCounts(counts) &&
          CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
          CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
          CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
          CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
          CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
          CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
          IntArray::full(cnt, 26, counts)
    */
    for (i = 0; s[i]; ++i)
        /*@ 97 <= source[i] && source[i] <= 122 &&
            app(source, cons(0, nil))[i] == source[i] */
        ++cnt[s[i] - 'a'];
    /*@ Inv Assert
          exists counts,
          s == s@pre && t == t@pre && p == p@pre &&
          1 <= Zlength(source) && Zlength(source) <= 100 &&
          1 <= Zlength(target) && Zlength(target) <= 100 &&
          1 <= Zlength(pool) && Zlength(pool) <= 100 &&
          (forall k, (0 <= k && k < Zlength(source)) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(target)) =>
            (97 <= target[k] && target[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(pool)) =>
            (97 <= pool[k] && pool[k] <= 122)) &&
          IsSubsequence(source, target) &&
          0 <= i && i <= Zlength(pool) &&
          ((i == Zlength(pool) && app(pool, cons(0, nil))[i] == 0) ||
           (i < Zlength(pool) &&
            app(pool, cons(0, nil))[i] == pool[i] &&
            97 <= pool[i] && pool[i] <= 122)) &&
          CountState(source, pool, target, Zlength(source), i, 0, counts) &&
          NonnegativeCounts(counts) &&
          CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
          CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
          CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
          CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
          CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
          CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
          IntArray::full(cnt, 26, counts)
    */
    for (i = 0; p[i]; ++i)
        /*@ 97 <= pool[i] && pool[i] <= 122 &&
            app(pool, cons(0, nil))[i] == pool[i] */
        ++cnt[p[i] - 'a'];
    /*@ Inv Assert
          exists counts,
          s == s@pre && t == t@pre && p == p@pre &&
          1 <= Zlength(source) && Zlength(source) <= 100 &&
          1 <= Zlength(target) && Zlength(target) <= 100 &&
          1 <= Zlength(pool) && Zlength(pool) <= 100 &&
          (forall k, (0 <= k && k < Zlength(source)) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(target)) =>
            (97 <= target[k] && target[k] <= 122)) &&
          (forall k, (0 <= k && k < Zlength(pool)) =>
            (97 <= pool[k] && pool[k] <= 122)) &&
          IsSubsequence(source, target) &&
          0 <= i && i <= Zlength(target) &&
          ((i == Zlength(target) && app(target, cons(0, nil))[i] == 0) ||
           (i < Zlength(target) &&
            app(target, cons(0, nil))[i] == target[i] &&
            97 <= target[i] && target[i] <= 122)) &&
          CountState(source, pool, target,
            Zlength(source), Zlength(pool), i, counts) &&
          NonnegativeCounts(counts) &&
          CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
          CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
          CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
          CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
          CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
          CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
          IntArray::full(cnt, 26, counts)
    */
    for (i = 0; t[i]; ++i) {
        /*@ 97 <= target[i] && target[i] <= 122 &&
            app(target, cons(0, nil))[i] == target[i] */
        cnt[t[i] - 'a'] = cnt[t[i] - 'a'] - 1;
        if (cnt[t[i] - 'a'] < 0)
        /*@ Assert
              exists counts,
              s == s@pre && t == t@pre && p == p@pre &&
              IsSubsequence(source, target) &&
              0 <= i && i < Zlength(target) &&
              CountState(source, pool, target,
                Zlength(source), Zlength(pool), i + 1, counts) &&
              SupplyShortage(source, pool, target) &&
              CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
              CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
              CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
              CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
              CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
              CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
              IntArray::full(cnt, 26, counts)
        */
        return 0;
    }
    /*@ Assert
          exists counts,
          s == s@pre && t == t@pre && p == p@pre &&
          i == Zlength(target) &&
          IsSubsequence(source, target) &&
          CountState(source, pool, target,
            Zlength(source), Zlength(pool), Zlength(target), counts) &&
          NonnegativeCounts(counts) &&
          CanInsertFromPool(source, pool, target) &&
          CharArray::full(s@pre, Zlength(source) + 1, app(source, cons(0, nil))) *
          CharArray::undef_seg(s@pre, Zlength(source) + 1, 105) *
          CharArray::full(t@pre, Zlength(target) + 1, app(target, cons(0, nil))) *
          CharArray::undef_seg(t@pre, Zlength(target) + 1, 105) *
          CharArray::full(p@pre, Zlength(pool) + 1, app(pool, cons(0, nil))) *
          CharArray::undef_seg(p@pre, Zlength(pool) + 1, 105) *
          IntArray::full(cnt, 26, counts)
    */
    return 1;
}

// int main(void)
// {
//     int q; scanf("%d", &q);
//     while (q--) {
//         char s[105], t[105], p[105]; scanf("%104s %104s %104s", s, t, p);
//         puts(solver(s, t, p) ? "YES" : "NO");
//     }
//     return 0;
// }
