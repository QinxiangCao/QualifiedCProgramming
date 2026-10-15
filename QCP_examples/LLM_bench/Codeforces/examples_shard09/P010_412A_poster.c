/*
 * Codeforces 412/A - Poster  (rating 900, GREEDY)
 *
 * Every square must be painted, so the ladder has to visit all n positions;
 * the cheapest route walks to the nearer end first and then sweeps across.
 * Cost = (n-1) sweep steps + min(k-1, n-k) steps to reach that end + n prints.
 */

// #include <stdio.h>
#include "array2_ext_def.h"

/*@ Extern Coq
      (Spec : Z -> list Z -> list (Z*Z) -> Prop)
      (SolverOutputBridge : Z -> list (Z*Z) -> Z -> list(list Z) -> list(list Z) -> Prop)
*/
/*@ Extern Coq
      (LeftAction : Z * Z)
      (RightAction : Z * Z)
      (PrintAction : Z -> Z * Z)
      (ActionSlotBridge : Z * Z -> list Z -> list Z -> Prop)
      (LeftWalkPlan : Z -> Z -> list (Z * Z))
      (RightWalkPlan : Z -> Z -> list (Z * Z))
      (ForwardSweepPlan : list Z -> Z -> list (Z * Z))
      (BackwardSweepPlan : list Z -> Z -> list (Z * Z))
      (LeftFirstPlan : Z -> list Z -> list (Z * Z))
      (RightFirstPlan : Z -> list Z -> list (Z * Z))
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P010_412A_poster_lib */


static void write_left(char dst[8])
/*@ With (before : list Z)
    Require Zlength(before) == 8 && CharArray::full(dst, 8, before)
    Ensure exists (after : list Z),
      Zlength(after) == 8 &&
      ActionSlotBridge(LeftAction, before, after) &&
      CharArray::full(dst, 8, after)
*/
{
    dst[0] = 'L';
    dst[1] = 'E';
    dst[2] = 'F';
    dst[3] = 'T';
    dst[4] = '\0';
}

static void write_right(char dst[8])
/*@ With (before : list Z)
    Require Zlength(before) == 8 && CharArray::full(dst, 8, before)
    Ensure exists (after : list Z),
      Zlength(after) == 8 &&
      ActionSlotBridge(RightAction, before, after) &&
      CharArray::full(dst, 8, after)
*/
{
    dst[0] = 'R';
    dst[1] = 'I';
    dst[2] = 'G';
    dst[3] = 'H';
    dst[4] = 'T';
    dst[5] = '\0';
}

static void write_print(char dst[8], char ch)
/*@ With (before : list Z)
    Require Zlength(before) == 8 && CharArray::full(dst, 8, before)
    Ensure exists (after : list Z),
      Zlength(after) == 8 &&
      ActionSlotBridge(PrintAction(ch), before, after) &&
      CharArray::full(dst, 8, after)
*/
{
    dst[0] = 'P';
    dst[1] = 'R';
    dst[2] = 'I';
    dst[3] = 'N';
    dst[4] = 'T';
    dst[5] = ' ';
    dst[6] = ch;
    dst[7] = '\0';
}

/* solver: pure.  Writes the optimal plan into out[] as one action per row
 * ("LEFT", "RIGHT" or "PRINT x") and returns the number of actions. */
static int solver(const char *s, int n, int k, char out[][8])
/* QCP_INSERT_BEGIN:shard09-P010-solver-contract */
/*@ With (cursor : Z) (text : list Z) (out_before : list(list Z))
    Require
      1 <= k && k <= n && 1 <= n && n <= 100 &&
      (forall i, (0 <= i && i < n) =>
        ((65 <= text[i] && text[i] <= 90) ||
         (48 <= text[i] && text[i] <= 57) ||
         text[i] == 46 || text[i] == 33 || text[i] == 44 || text[i] == 63)) &&
      n == Zlength(text) && k == cursor && Zlength(out_before) == 3 * n && 
      (forall i, (0 <= i && i < 3 * n) => Zlength(out_before[i]) == 8) && CharArray::full(s, n, text) * CharArray2::full(out, 3 * n, 8, out_before)
    Ensure
      exists (out_spec : list (Z*Z)) (out_after : list(list Z)),
        Spec(cursor, text, out_spec) &&
        SolverOutputBridge(3 * n, out_spec, __return, out_before, out_after) && CharArray::full(s, n, text) * CharArray2::full(out, 3 * n, 8, out_after)
*/
/* QCP_INSERT_END:shard09-P010-solver-contract */
{
    int t = 0;
    if (k - 1 <= n - k) {                     /* walk left, then sweep right */
        /*@ Inv Assert
              exists (rows : list(list Z)),
                n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                1 <= k@pre && k@pre <= n@pre &&
                1 <= n@pre && n@pre <= 100 &&
                (forall j, (0 <= j && j < n@pre) =>
                  ((65 <= text[j] && text[j] <= 90) ||
                   (48 <= text[j] && text[j] <= 57) ||
                   text[j] == 46 || text[j] == 33 ||
                   text[j] == 44 || text[j] == 63)) &&
                n@pre == Zlength(text) && k@pre == cursor &&
                k@pre - 1 <= n@pre - k@pre &&
                Spec(k@pre, text, LeftFirstPlan(k@pre, text)) &&
                1 <= p && p <= k@pre && 0 <= t && t < 3 * n@pre &&
                t + (p - 1) + (2 * n@pre - 1) < 3 * n@pre &&
                t == Zlength(LeftWalkPlan(k@pre, p)) &&
                SolverOutputBridge(3 * n@pre, LeftWalkPlan(k@pre, p), t, out_before, rows) &&
                (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                CharArray::full(s@pre, n@pre, text) *
                CharArray2::full(out@pre, 3 * n@pre, 8, rows)
        */
        for (int p = k; p > 1; p--)
            {
                /*@ Assert
                      exists (rows : list(list Z)),
                        n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                        1 <= k@pre && k@pre <= n@pre &&
                        1 <= n@pre && n@pre <= 100 &&
                        (forall j, (0 <= j && j < n@pre) =>
                          ((65 <= text[j] && text[j] <= 90) ||
                           (48 <= text[j] && text[j] <= 57) ||
                           text[j] == 46 || text[j] == 33 ||
                           text[j] == 44 || text[j] == 63)) &&
                        n@pre == Zlength(text) && k@pre == cursor &&
                        k@pre - 1 <= n@pre - k@pre &&
                        Spec(k@pre, text, LeftFirstPlan(k@pre, text)) &&
                        1 < p && p <= k@pre && 0 <= t && t < 3 * n@pre &&
                        0 <= t + 1 && t + 1 < 3 * n@pre &&
                        t + (p - 1) + (2 * n@pre - 1) < 3 * n@pre &&
                        t == Zlength(LeftWalkPlan(k@pre, p)) &&
                        SolverOutputBridge(3 * n@pre, LeftWalkPlan(k@pre, p), t, out_before, rows) &&
                        (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                        Zlength(rows[t]) == 8 &&
                        CharArray::full(s@pre, n@pre, text) *
                        CharArray2::missing_i(out@pre, t, 0, 3 * n@pre, 8, rows) *
                        CharArray::full(
                          pointer_offset(pointer_offset(out@pre, t, sizeof(char[8]), char[8]),
                            0, sizeof(char), signed char),
                          8, rows[t])
                */
                write_left(out[t]);
                t++;
            }
        /*@ Inv Assert
              exists (rows : list(list Z)),
                n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                1 <= k@pre && k@pre <= n@pre &&
                1 <= n@pre && n@pre <= 100 &&
                (forall j, (0 <= j && j < n@pre) =>
                  ((65 <= text[j] && text[j] <= 90) ||
                   (48 <= text[j] && text[j] <= 57) ||
                   text[j] == 46 || text[j] == 33 ||
                   text[j] == 44 || text[j] == 63)) &&
                n@pre == Zlength(text) && k@pre == cursor &&
                k@pre - 1 <= n@pre - k@pre &&
                1 <= p && p <= n@pre + 1 && 0 <= t && t < 3 * n@pre &&
                (p <= n@pre => t + (2 * (n@pre - p) + 1) < 3 * n@pre) &&
                t == Zlength(app(LeftWalkPlan(k@pre, 1), ForwardSweepPlan(text, p))) &&
                Spec(k@pre, text, LeftFirstPlan(k@pre, text)) &&
                SolverOutputBridge(3 * n@pre, app(LeftWalkPlan(k@pre, 1), ForwardSweepPlan(text, p)), t, out_before, rows) &&
                (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                CharArray::full(s@pre, n@pre, text) *
                CharArray2::full(out@pre, 3 * n@pre, 8, rows)
        */
        for (int p = 1; p <= n; p++) {
            /*@ Assert
                  exists (rows : list(list Z)),
                    n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                    1 <= k@pre && k@pre <= n@pre &&
                    1 <= n@pre && n@pre <= 100 &&
                    (forall j, (0 <= j && j < n@pre) =>
                      ((65 <= text[j] && text[j] <= 90) ||
                       (48 <= text[j] && text[j] <= 57) ||
                       text[j] == 46 || text[j] == 33 ||
                       text[j] == 44 || text[j] == 63)) &&
                    n@pre == Zlength(text) && k@pre == cursor &&
                    k@pre - 1 <= n@pre - k@pre &&
                    1 <= p && p <= n@pre && 0 <= t && t < 3 * n@pre &&
                    0 <= t + 1 && t + 1 < 3 * n@pre &&
                    (p < n@pre => 0 <= t + 2 && t + 2 < 3 * n@pre) &&
                    t + (2 * (n@pre - p) + 1) < 3 * n@pre &&
                    t == Zlength(app(LeftWalkPlan(k@pre, 1), ForwardSweepPlan(text, p))) &&
                    Spec(k@pre, text, LeftFirstPlan(k@pre, text)) &&
                    SolverOutputBridge(3 * n@pre, app(LeftWalkPlan(k@pre, 1), ForwardSweepPlan(text, p)), t, out_before, rows) &&
                    (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                    Zlength(rows[t]) == 8 &&
                    CharArray::full(s@pre, n@pre, text) *
                    CharArray2::missing_i(out@pre, t, 0, 3 * n@pre, 8, rows) *
                    CharArray::full(
                      pointer_offset(pointer_offset(out@pre, t, sizeof(char[8]), char[8]),
                        0, sizeof(char), signed char),
                      8, rows[t])
            */
            write_print(out[t], s[p - 1]);
            t++;
            if (p < n)
                {
                    /*@ Assert
                          exists (rows : list(list Z)),
                            n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                            1 <= k@pre && k@pre <= n@pre &&
                            1 <= n@pre && n@pre <= 100 &&
                            (forall j, (0 <= j && j < n@pre) =>
                              ((65 <= text[j] && text[j] <= 90) ||
                               (48 <= text[j] && text[j] <= 57) ||
                               text[j] == 46 || text[j] == 33 ||
                               text[j] == 44 || text[j] == 63)) &&
                            n@pre == Zlength(text) && k@pre == cursor &&
                            k@pre - 1 <= n@pre - k@pre &&
                            1 <= p && p < n@pre && 0 <= t && t < 3 * n@pre &&
                            0 <= t + 1 && t + 1 < 3 * n@pre &&
                            t + 2 * (n@pre - p) < 3 * n@pre &&
                            t == Zlength(app(app(LeftWalkPlan(k@pre, 1), ForwardSweepPlan(text, p)), cons(PrintAction(text[p - 1]), nil))) &&
                            Spec(k@pre, text, LeftFirstPlan(k@pre, text)) &&
                            SolverOutputBridge(3 * n@pre, app(app(LeftWalkPlan(k@pre, 1), ForwardSweepPlan(text, p)), cons(PrintAction(text[p - 1]), nil)), t, out_before, rows) &&
                            (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                            Zlength(rows[t]) == 8 &&
                            CharArray::full(s@pre, n@pre, text) *
                            CharArray2::missing_i(out@pre, t, 0, 3 * n@pre, 8, rows) *
                            CharArray::full(
                              pointer_offset(pointer_offset(out@pre, t, sizeof(char[8]), char[8]),
                                0, sizeof(char), signed char),
                              8, rows[t])
                    */
                    write_right(out[t]);
                    t++;
                }
        }
    } else {                                  /* walk right, then sweep left */
        /*@ Inv Assert
              exists (rows : list(list Z)),
                n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                1 <= k@pre && k@pre <= n@pre &&
                1 <= n@pre && n@pre <= 100 &&
                (forall j, (0 <= j && j < n@pre) =>
                  ((65 <= text[j] && text[j] <= 90) ||
                   (48 <= text[j] && text[j] <= 57) ||
                   text[j] == 46 || text[j] == 33 ||
                   text[j] == 44 || text[j] == 63)) &&
                n@pre == Zlength(text) && k@pre == cursor &&
                k@pre - 1 > n@pre - k@pre &&
                Spec(k@pre, text, RightFirstPlan(k@pre, text)) &&
                k@pre <= p && p <= n@pre && 0 <= t && t < 3 * n@pre &&
                t + (n@pre - p) + (2 * n@pre - 1) < 3 * n@pre &&
                t == Zlength(RightWalkPlan(k@pre, p)) &&
                SolverOutputBridge(3 * n@pre, RightWalkPlan(k@pre, p), t, out_before, rows) &&
                (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                CharArray::full(s@pre, n@pre, text) *
                CharArray2::full(out@pre, 3 * n@pre, 8, rows)
        */
        for (int p = k; p < n; p++)
            {
                /*@ Assert
                      exists (rows : list(list Z)),
                        n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                        1 <= k@pre && k@pre <= n@pre &&
                        1 <= n@pre && n@pre <= 100 &&
                        (forall j, (0 <= j && j < n@pre) =>
                          ((65 <= text[j] && text[j] <= 90) ||
                           (48 <= text[j] && text[j] <= 57) ||
                           text[j] == 46 || text[j] == 33 ||
                           text[j] == 44 || text[j] == 63)) &&
                        n@pre == Zlength(text) && k@pre == cursor &&
                        k@pre - 1 > n@pre - k@pre &&
                        Spec(k@pre, text, RightFirstPlan(k@pre, text)) &&
                        k@pre <= p && p < n@pre && 0 <= t && t < 3 * n@pre &&
                        0 <= t + 1 && t + 1 < 3 * n@pre &&
                        t + (n@pre - p) + (2 * n@pre - 1) < 3 * n@pre &&
                        t == Zlength(RightWalkPlan(k@pre, p)) &&
                        SolverOutputBridge(3 * n@pre, RightWalkPlan(k@pre, p), t, out_before, rows) &&
                        (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                        Zlength(rows[t]) == 8 &&
                        CharArray::full(s@pre, n@pre, text) *
                        CharArray2::missing_i(out@pre, t, 0, 3 * n@pre, 8, rows) *
                        CharArray::full(
                          pointer_offset(pointer_offset(out@pre, t, sizeof(char[8]), char[8]),
                            0, sizeof(char), signed char),
                          8, rows[t])
                */
                write_right(out[t]);
                t++;
            }
        /*@ Inv Assert
              exists (rows : list(list Z)),
                n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                1 <= k@pre && k@pre <= n@pre &&
                1 <= n@pre && n@pre <= 100 &&
                (forall j, (0 <= j && j < n@pre) =>
                  ((65 <= text[j] && text[j] <= 90) ||
                   (48 <= text[j] && text[j] <= 57) ||
                   text[j] == 46 || text[j] == 33 ||
                   text[j] == 44 || text[j] == 63)) &&
                n@pre == Zlength(text) && k@pre == cursor &&
                k@pre - 1 > n@pre - k@pre &&
                0 <= p && p <= n@pre && 0 <= t && t < 3 * n@pre &&
                (p > 0 => t + (2 * p - 1) < 3 * n@pre) &&
                t == Zlength(app(RightWalkPlan(k@pre, n@pre), BackwardSweepPlan(text, p))) &&
                Spec(k@pre, text, RightFirstPlan(k@pre, text)) &&
                SolverOutputBridge(3 * n@pre, app(RightWalkPlan(k@pre, n@pre), BackwardSweepPlan(text, p)), t, out_before, rows) &&
                (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                CharArray::full(s@pre, n@pre, text) *
                CharArray2::full(out@pre, 3 * n@pre, 8, rows)
        */
        for (int p = n; p >= 1; p--) {
            /*@ Assert
                  exists (rows : list(list Z)),
                    n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                    1 <= k@pre && k@pre <= n@pre &&
                    1 <= n@pre && n@pre <= 100 &&
                    (forall j, (0 <= j && j < n@pre) =>
                      ((65 <= text[j] && text[j] <= 90) ||
                       (48 <= text[j] && text[j] <= 57) ||
                       text[j] == 46 || text[j] == 33 ||
                       text[j] == 44 || text[j] == 63)) &&
                    n@pre == Zlength(text) && k@pre == cursor &&
                    k@pre - 1 > n@pre - k@pre &&
                    1 <= p && p <= n@pre && 0 <= t && t < 3 * n@pre &&
                    0 <= t + 1 && t + 1 < 3 * n@pre &&
                    (p > 1 => 0 <= t + 2 && t + 2 < 3 * n@pre) &&
                    t + (2 * p - 1) < 3 * n@pre &&
                    t == Zlength(app(RightWalkPlan(k@pre, n@pre), BackwardSweepPlan(text, p))) &&
                    Spec(k@pre, text, RightFirstPlan(k@pre, text)) &&
                    SolverOutputBridge(3 * n@pre, app(RightWalkPlan(k@pre, n@pre), BackwardSweepPlan(text, p)), t, out_before, rows) &&
                    (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                    Zlength(rows[t]) == 8 &&
                    CharArray::full(s@pre, n@pre, text) *
                    CharArray2::missing_i(out@pre, t, 0, 3 * n@pre, 8, rows) *
                    CharArray::full(
                      pointer_offset(pointer_offset(out@pre, t, sizeof(char[8]), char[8]),
                        0, sizeof(char), signed char),
                      8, rows[t])
            */
            write_print(out[t], s[p - 1]);
            t++;
            if (p > 1)
                {
                    /*@ Assert
                          exists (rows : list(list Z)),
                            n == n@pre && k == k@pre && s == s@pre && out == out@pre &&
                            1 <= k@pre && k@pre <= n@pre &&
                            1 <= n@pre && n@pre <= 100 &&
                            (forall j, (0 <= j && j < n@pre) =>
                              ((65 <= text[j] && text[j] <= 90) ||
                               (48 <= text[j] && text[j] <= 57) ||
                               text[j] == 46 || text[j] == 33 ||
                               text[j] == 44 || text[j] == 63)) &&
                            n@pre == Zlength(text) && k@pre == cursor &&
                            k@pre - 1 > n@pre - k@pre &&
                            1 < p && p <= n@pre && 0 <= t && t < 3 * n@pre &&
                            0 <= t + 1 && t + 1 < 3 * n@pre &&
                            t + 2 * (p - 1) < 3 * n@pre &&
                            t == Zlength(app(app(RightWalkPlan(k@pre, n@pre), BackwardSweepPlan(text, p)), cons(PrintAction(text[p - 1]), nil))) &&
                            Spec(k@pre, text, RightFirstPlan(k@pre, text)) &&
                            SolverOutputBridge(3 * n@pre, app(app(RightWalkPlan(k@pre, n@pre), BackwardSweepPlan(text, p)), cons(PrintAction(text[p - 1]), nil)), t, out_before, rows) &&
                            (forall i, (0 <= i && i < 3 * n@pre) => Zlength(rows[i]) == 8) &&
                            Zlength(rows[t]) == 8 &&
                            CharArray::full(s@pre, n@pre, text) *
                            CharArray2::missing_i(out@pre, t, 0, 3 * n@pre, 8, rows) *
                            CharArray::full(
                              pointer_offset(pointer_offset(out@pre, t, sizeof(char[8]), char[8]),
                                0, sizeof(char), signed char),
                              8, rows[t])
                    */
                    write_left(out[t]);
                    t++;
                }
        }
    }
    return t;
}

// int main(void)
// {
//     int n, k;
//     if (scanf("%d %d", &n, &k) != 2)
//         return 0;
//     static char s[105];
//     scanf("%104s", s);
//     static char out[305][8];
//     int t = solver(s, n, k, out);
//     for (int i = 0; i < t; i++)
//         puts(out[i]);
//     return 0;
// }
