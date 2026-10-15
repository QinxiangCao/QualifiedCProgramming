/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib
*/

/*
 * Codeforces 1243/B2 - Character Swap (Hard Version)  (rating 1600, STRINGS)
 *
 * Solvable iff every letter occurs an even number of times overall.  Fix
 * positions left to right: to repair position i, find another copy of s[i]
 * further right — in s[j], which takes one swap (s_j <-> t_i), or in t[j],
 * which first needs s_j <-> t_j to move it into s.  That is at most 2 swaps
 * per position, so at most 2n in total.
 */

// #include <stdio.h>
// #include <string.h>
/* QCP_INSERT_BEGIN:shard09-P046-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> option(list(Z*Z)) -> Prop)
*/
/*@ Extern Coq
      (CountedPrefix : list Z -> list Z -> Z -> list Z -> Prop)
      (CountsEvenBefore : list Z -> Z -> Prop)
      (CombinedEven : list Z -> list Z -> Prop)
      (CombinedOddAt : list Z -> list Z -> Z -> Prop)
      (RepairState : list Z -> list Z -> list Z -> list Z -> Z -> list(Z*Z) -> Prop)
      (NoValueInRange : list Z -> Z -> Z -> Z -> Prop)
      (OperationLists : list(Z*Z) -> list Z -> list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P046-solver-support */


/* solver: pure.  Fills oi/oj with the swap pairs (1-based) and returns the
 * number of swaps, or -1 if the strings cannot be made equal.  s and t are
 * modified into their final (equal) state. */
static int solver(char *s, char *t, int n, int *oi, int *oj)
/* QCP_INSERT_BEGIN:shard09-P046-solver-contract */
/*@ With (source : list Z) (target : list Z)
    Require
      Pre(source, target) &&
      2 <= n && n <= 50 && (forall i, (0 <= i && i < n) => (97 <= source[i] && source[i] <= 122)) && (forall i, (0 <= i && i < n) => (97 <= target[i] && target[i] <= 122)) &&
      n == Zlength(source) && Zlength(target) == n && CharArray::full(s, n, source) * CharArray::full(t, n, target) * IntArray::undef_full(oi, 2 * n) * IntArray::undef_full(oj, 2 * n)
    Ensure
      exists (out : option(list(Z*Z))),
        Spec(source, target, out) &&
        ((out == None && __return == -1 && exists (oi_cells : list(option Z)) (oj_cells : list(option Z)), CharArray::full_shape(s, n) * CharArray::full_shape(t, n) * IntArray::mixed_full(oi, 2 * n, oi_cells) * IntArray::mixed_full(oj, 2 * n, oj_cells)) || (exists (ops : list(Z*Z)), out == Some(ops) && __return == Zlength(ops) && 1 <= Zlength(ops) && Zlength(ops) <= 2 * n && exists (is : list Z) (js : list Z), Zlength(is) == Zlength(ops) && Zlength(js) == Zlength(ops) && (forall q, (0 <= q && q < Zlength(ops)) => is[q] == fst(ops[q]) + 1 && js[q] == snd(ops[q]) + 1) && CharArray::full_shape(s, n) * CharArray::full_shape(t, n) * IntArray::full(oi, Zlength(ops), is) * IntArray::undef_seg(oi, Zlength(ops), 2 * n) * IntArray::full(oj, Zlength(ops), js) * IntArray::undef_seg(oj, Zlength(ops), 2 * n)))
*/
/* QCP_INSERT_END:shard09-P046-solver-contract */
{
    int cnt[26] = {0};
    /*@ Inv Assert
          exists (counts : list Z),
          s == s@pre && t == t@pre && n == n@pre && oi == oi@pre && oj == oj@pre &&
          Pre(source, target) &&
          2 <= n@pre && n@pre <= 50 &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= target[k] && target[k] <= 122)) &&
          n@pre == Zlength(source) && Zlength(target) == n@pre &&
          0 <= i && i <= n@pre &&
          CountedPrefix(source, target, i, counts) &&
          CharArray::full(s@pre, n@pre, source) *
          CharArray::full(t@pre, n@pre, target) *
          IntArray::undef_full(oi@pre, 2 * n@pre) *
          IntArray::undef_full(oj@pre, 2 * n@pre) *
          IntArray::full(cnt, 26, counts)
    */
    for (int i = 0; i < n; i++) {
        cnt[s[i] - 'a']++;
        cnt[t[i] - 'a']++;
    }
    /*@ Inv Assert
          exists (counts : list Z),
          s == s@pre && t == t@pre && n == n@pre && oi == oi@pre && oj == oj@pre &&
          Pre(source, target) &&
          2 <= n@pre && n@pre <= 50 &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= target[k] && target[k] <= 122)) &&
          n@pre == Zlength(source) && Zlength(target) == n@pre &&
          0 <= c && c <= 26 &&
          CountedPrefix(source, target, n@pre, counts) &&
          CountsEvenBefore(counts, c) &&
          CharArray::full(s@pre, n@pre, source) *
          CharArray::full(t@pre, n@pre, target) *
          IntArray::undef_full(oi@pre, 2 * n@pre) *
          IntArray::undef_full(oj@pre, 2 * n@pre) *
          IntArray::full(cnt, 26, counts)
    */
    for (int c = 0; c < 26; c++)
        if (cnt[c] % 2) {
            /*@ Assert
                  exists (counts : list Z),
                  s == s@pre && t == t@pre && n == n@pre && oi == oi@pre && oj == oj@pre &&
                  Pre(source, target) &&
                  2 <= n@pre && n@pre <= 50 &&
                  n@pre == Zlength(source) && Zlength(target) == n@pre &&
                  0 <= c && c < 26 &&
                  CountedPrefix(source, target, n@pre, counts) &&
                  CombinedOddAt(source, target, c) &&
                  CharArray::full(s@pre, n@pre, source) *
                  CharArray::full(t@pre, n@pre, target) *
                  IntArray::undef_full(oi@pre, 2 * n@pre) *
                  IntArray::undef_full(oj@pre, 2 * n@pre) *
                  IntArray::full(cnt, 26, counts)
            */
            return -1;
        }

    /*@ Assert
          exists (counts : list Z),
          s == s@pre && t == t@pre && n == n@pre && oi == oi@pre && oj == oj@pre &&
          Pre(source, target) &&
          2 <= n@pre && n@pre <= 50 &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= source[k] && source[k] <= 122)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= target[k] && target[k] <= 122)) &&
          n@pre == Zlength(source) && Zlength(target) == n@pre &&
          CountedPrefix(source, target, n@pre, counts) &&
          CombinedEven(source, target) &&
          CharArray::full(s@pre, n@pre, source) *
          CharArray::full(t@pre, n@pre, target) *
          IntArray::undef_full(oi@pre, 2 * n@pre) *
          IntArray::undef_full(oj@pre, 2 * n@pre) *
          IntArray::full(cnt, 26, counts)
    */

    int m = 0;
    /*@ Inv Assert
          exists (ss : list Z) (tt : list Z) (ops : list(Z*Z))
                 (is : list Z) (js : list Z) (counts : list Z),
          s == s@pre && t == t@pre && n == n@pre && oi == oi@pre && oj == oj@pre &&
          Pre(source, target) &&
          2 <= n@pre && n@pre <= 50 &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= ss[k] && ss[k] <= 122)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (97 <= tt[k] && tt[k] <= 122)) &&
          n@pre == Zlength(source) && Zlength(target) == n@pre &&
          0 <= i && i <= n@pre &&
          0 <= m && m <= 2 * i &&
          m == Zlength(ops) && OperationLists(ops, is, js) &&
          RepairState(source, target, ss, tt, i, ops) &&
          CharArray::full(s@pre, n@pre, ss) *
          CharArray::full(t@pre, n@pre, tt) *
          IntArray::full(oi@pre, m, is) * IntArray::undef_seg(oi@pre, m, 2 * n@pre) *
          IntArray::full(oj@pre, m, js) * IntArray::undef_seg(oj@pre, m, 2 * n@pre) *
          IntArray::full(cnt, 26, counts)
    */
    for (int i = 0; i < n; i++) {
        if (s[i] == t[i])
            continue;
        int j;
        /*@ Inv Assert
              exists (ss : list Z) (tt : list Z) (ops : list(Z*Z))
                     (is : list Z) (js : list Z) (counts : list Z),
              s == s@pre && t == t@pre && n == n@pre && oi == oi@pre && oj == oj@pre &&
              Pre(source, target) &&
              2 <= n@pre && n@pre <= 50 &&
              (forall k, (0 <= k && k < n@pre) =>
                (97 <= ss[k] && ss[k] <= 122)) &&
              (forall k, (0 <= k && k < n@pre) =>
                (97 <= tt[k] && tt[k] <= 122)) &&
              n@pre == Zlength(source) && Zlength(target) == n@pre &&
              0 <= i && i < n@pre && i + 1 <= j && j <= n@pre &&
              ss[i] != tt[i] &&
              NoValueInRange(ss, ss[i], i + 1, j) &&
              0 <= m && m <= 2 * i &&
              m == Zlength(ops) && OperationLists(ops, is, js) &&
              RepairState(source, target, ss, tt, i, ops) &&
              CharArray::full(s@pre, n@pre, ss) *
              CharArray::full(t@pre, n@pre, tt) *
              IntArray::full(oi@pre, m, is) * IntArray::undef_seg(oi@pre, m, 2 * n@pre) *
              IntArray::full(oj@pre, m, js) * IntArray::undef_seg(oj@pre, m, 2 * n@pre) *
              IntArray::full(cnt, 26, counts)
        */
        for (j = i + 1; j < n; j++)
            if (s[j] == s[i])
                break;
        if (j < n) {                       /* one swap: s_j <-> t_i */
            char tmp = s[j];
            s[j] = t[i];
            t[i] = tmp;
            oi[m] = j + 1;
            oj[m] = i + 1;
            m++;
            continue;
        }
        /*@ Inv Assert
              exists (ss : list Z) (tt : list Z) (ops : list(Z*Z))
                     (is : list Z) (js : list Z) (counts : list Z),
              s == s@pre && t == t@pre && n == n@pre && oi == oi@pre && oj == oj@pre &&
              Pre(source, target) &&
              2 <= n@pre && n@pre <= 50 &&
              (forall k, (0 <= k && k < n@pre) =>
                (97 <= ss[k] && ss[k] <= 122)) &&
              (forall k, (0 <= k && k < n@pre) =>
                (97 <= tt[k] && tt[k] <= 122)) &&
              n@pre == Zlength(source) && Zlength(target) == n@pre &&
              0 <= i && i < n@pre && i + 1 <= j && j <= n@pre &&
              ss[i] != tt[i] &&
              NoValueInRange(ss, ss[i], i + 1, n@pre) &&
              NoValueInRange(tt, ss[i], i + 1, j) &&
              0 <= m && m <= 2 * i &&
              m == Zlength(ops) && OperationLists(ops, is, js) &&
              RepairState(source, target, ss, tt, i, ops) &&
              CharArray::full(s@pre, n@pre, ss) *
              CharArray::full(t@pre, n@pre, tt) *
              IntArray::full(oi@pre, m, is) * IntArray::undef_seg(oi@pre, m, 2 * n@pre) *
              IntArray::full(oj@pre, m, js) * IntArray::undef_seg(oj@pre, m, 2 * n@pre) *
              IntArray::full(cnt, 26, counts)
        */
        for (j = i + 1; j < n; j++)
            if (t[j] == s[i])
                break;
        if (j >= n)
            return -1;                     /* cannot happen: counts are even */
        char tmp = s[j];                   /* move it into s: s_j <-> t_j */
        s[j] = t[j];
        t[j] = tmp;
        oi[m] = j + 1;
        oj[m] = j + 1;
        m++;
        tmp = s[j];                        /* then s_j <-> t_i */
        s[j] = t[i];
        t[i] = tmp;
        oi[m] = j + 1;
        oj[m] = i + 1;
        m++;
    }
    return m;
}

// int main(void)
// {
//     int k;
//     if (scanf("%d", &k) != 1)
//         return 0;
//     static char s[55], t[55];
//     static int oi[205], oj[205];
//     while (k--) {
//         int n;
//         scanf("%d %54s %54s", &n, s, t);
//         int m = solver(s, t, n, oi, oj);
//         if (m < 0) {
//             puts("No");
//             continue;
//         }
//         puts("Yes");
//         printf("%d\n", m);
//         for (int i = 0; i < m; i++)
//             printf("%d %d\n", oi[i], oj[i]);
//     }
//     return 0;
// }
