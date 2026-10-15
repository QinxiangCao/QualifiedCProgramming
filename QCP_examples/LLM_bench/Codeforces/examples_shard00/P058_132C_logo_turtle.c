/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib
*/

/* Codeforces 132/C - Logo Turtle */
// #include <stdio.h>
#include "string.h"
// #include <stdlib.h>

typedef unsigned long size_t;

#define AT(a, c, d, p) (a)[((c) * 2 + (d)) * W + (p)]

/* QCP_INSERT_BEGIN:P058_132C_logo_turtle.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (TurtleLayerMeaning : list Z -> Z -> Z -> list Z -> Prop)
      (TurtleNextPrefix : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (TurtleAnswerPrefix : list Z -> Z -> Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (UCharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib */
/* QCP_INSERT_END:P058_132C_logo_turtle.support */

void *calloc(unsigned long nmemb, unsigned long size)
    /*@ calloc_uchar
    With (cells : Z)
    Require
      0 <= cells && cells <= INT_MAX &&
      nmemb == cells && size == 1
    Ensure
      __return != 0 &&
      UCharArray::full(__return, cells, repeat_Z(0, cells))
*/
    ;

char *memset(char *s, int c, int n)
    /*@ memset_uchar_zero
    With (old : list Z)
    Require
      0 <= n && n <= INT_MAX &&
      c == 0 && Zlength(old) == n &&
      UCharArray::full(s, n, old)
    Ensure
      __return == s &&
      UCharArray::full(s, n, repeat_Z(0, n))
*/
    ;

int strlen(char *s)
    /*@ strlen_logo_commands
    With (text : list Z)
    Require
      0 <= Zlength(text) && Zlength(text) < INT_MAX &&
      (forall i, (0 <= i && i < Zlength(text)) =>
        ((text[i] == 70) || (text[i] == 84))) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    Ensure
      __return == Zlength(text) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
*/
    ;

int abs(int value)
    /*@ abs_logo_position
    Require
      INT_MIN < value && value <= INT_MAX
    Ensure
      ((0 <= value && __return == value) ||
       (value < 0 && __return == -value))
*/
    ;

void free(void *ptr)
    /*@ free_uchar
    Require
      exists cells values,
        UCharArray::full(ptr, cells, values)
    Ensure emp
*/
    ;

static int solver(const char *s, int changes) /* QCP_INSERT_BEGIN:P058_132C_logo_turtle.contract */

/*@ With (n : Z)
             (commands : list Z)
    Require
      1 <= Zlength(commands) && Zlength(commands) <= 100 &&
      1 <= n && n <= 50 &&
      (forall i, (0 <= i && i < Zlength(commands)) =>
        ((commands[i] == 70) || (commands[i] == 84))) &&
      changes == n &&
      CharArray::full(s, Zlength(commands) + 1, app(commands, cons(0, nil)))
    Ensure
      Spec(n, commands, __return) &&
      CharArray::full(s, Zlength(commands) + 1, app(commands, cons(0, nil)))
*/
/* QCP_INSERT_END:P058_132C_logo_turtle.contract */
{
    int len = (int)strlen(s)
        /*@ where (strlen_logo_commands) text = commands */;
    int W = 2 * len + 1;
    int O = len;
    unsigned char *dp = calloc((size_t)(changes + 1) * 2 * W, 1)
        /*@ where (calloc_uchar) cells = (changes + 1) * 2 * W */;
    unsigned char *ndp = calloc((size_t)(changes + 1) * 2 * W, 1)
        /*@ where (calloc_uchar) cells = (changes + 1) * 2 * W */;

    AT(dp, 0, 0, O) = 1;
    /*@ Inv Assert
        exists current_table spare_table,
          s == s@pre && changes == changes@pre && changes@pre == n &&
          len == Zlength(commands) && W == 2 * len + 1 && O == len &&
          1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
          (forall k, (0 <= k && k < len) =>
             (commands[k] == 70 || commands[k] == 84)) &&
          0 <= i && i <= len &&
          0 <= (changes + 1) * 2 * W &&
          (changes + 1) * 2 * W <= INT_MAX &&
          dp != 0 && ndp != 0 &&
          Zlength(current_table) == (changes + 1) * 2 * W &&
          Zlength(spare_table) == (changes + 1) * 2 * W &&
          TurtleLayerMeaning(commands, i, changes, current_table) &&
          CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
          UCharArray::full(dp, (changes + 1) * 2 * W, current_table) *
          UCharArray::full(ndp, (changes + 1) * 2 * W, spare_table)
    */
    for (int i = 0; i < len; ++i) {
        memset((char *)ndp, 0, (int)((size_t)(changes + 1) * 2 * W))
            /*@ where (memset_uchar_zero) */;
        /*@ Inv Assert
            exists current_table next_table,
              s == s@pre && changes == changes@pre && changes@pre == n &&
              len == Zlength(commands) && W == 2 * len + 1 && O == len &&
              1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
              (forall k, (0 <= k && k < len) =>
                 (commands[k] == 70 || commands[k] == 84)) &&
              0 <= i && i < len && 0 <= c && c <= changes + 1 &&
              0 <= (changes + 1) * 2 * W &&
              (changes + 1) * 2 * W <= INT_MAX &&
              dp != 0 && ndp != 0 &&
              Zlength(current_table) == (changes + 1) * 2 * W &&
              Zlength(next_table) == (changes + 1) * 2 * W &&
              TurtleLayerMeaning(commands, i, changes, current_table) &&
              TurtleNextPrefix(commands, i, changes, 4 * c * W, next_table) &&
              CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
              UCharArray::full(dp, (changes + 1) * 2 * W, current_table) *
              UCharArray::full(ndp, (changes + 1) * 2 * W, next_table)
        */
        for (int c = 0; c <= changes; ++c) {
            /*@ Inv Assert
                exists current_table next_table,
                  s == s@pre && changes == changes@pre && changes@pre == n &&
                  len == Zlength(commands) && W == 2 * len + 1 && O == len &&
                  1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
                  (forall k, (0 <= k && k < len) =>
                     (commands[k] == 70 || commands[k] == 84)) &&
                  0 <= i && i < len && 0 <= c && c <= changes &&
                  0 <= dir && dir <= 2 &&
                  (changes + 1) * 2 * W <= INT_MAX &&
                  dp != 0 && ndp != 0 &&
                  Zlength(current_table) == (changes + 1) * 2 * W &&
                  Zlength(next_table) == (changes + 1) * 2 * W &&
                  TurtleLayerMeaning(commands, i, changes, current_table) &&
                  TurtleNextPrefix(commands, i, changes,
                    2 * ((c * 2 + dir) * W), next_table) &&
                  CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
                  UCharArray::full(dp, (changes + 1) * 2 * W, current_table) *
                  UCharArray::full(ndp, (changes + 1) * 2 * W, next_table)
            */
            for (int dir = 0; dir < 2; ++dir) {
                /*@ Inv Assert
                    exists current_table next_table,
                      s == s@pre && changes == changes@pre && changes@pre == n &&
                      len == Zlength(commands) && W == 2 * len + 1 && O == len &&
                      1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
                      (forall k, (0 <= k && k < len) =>
                         (commands[k] == 70 || commands[k] == 84)) &&
                      0 <= i && i < len && 0 <= c && c <= changes &&
                      0 <= dir && dir < 2 && 0 <= pos && pos <= W &&
                      (changes + 1) * 2 * W <= INT_MAX &&
                      0 <= (c * 2 + dir) * W + pos &&
                      (c * 2 + dir) * W + pos <= (changes + 1) * 2 * W &&
                      dp != 0 && ndp != 0 &&
                      Zlength(current_table) == (changes + 1) * 2 * W &&
                      Zlength(next_table) == (changes + 1) * 2 * W &&
                      TurtleLayerMeaning(commands, i, changes, current_table) &&
                      TurtleNextPrefix(commands, i, changes,
                        2 * ((c * 2 + dir) * W + pos), next_table) &&
                      CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
                      UCharArray::full(dp, (changes + 1) * 2 * W, current_table) *
                      UCharArray::full(ndp, (changes + 1) * 2 * W, next_table)
                */
                for (int pos = 0; pos < W; ++pos) {
                    /*@ 0 <= (c * 2 + dir) * W + pos &&
                        (c * 2 + dir) * W + pos <
                          (changes + 1) * 2 * W by local */
                    if (AT(dp, c, dir, pos)) {
                        /*@ Inv Assert
                            exists current_table next_table,
                              s == s@pre && changes == changes@pre && changes@pre == n &&
                              len == Zlength(commands) && W == 2 * len + 1 && O == len &&
                              1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
                              (forall k, (0 <= k && k < len) =>
                                 (commands[k] == 70 || commands[k] == 84)) &&
                              0 <= i && i < len && 0 <= c && c <= changes &&
                              0 <= dir && dir < 2 && 0 <= pos && pos < W &&
                              0 <= flip && flip <= 2 &&
                              current_table[(c * 2 + dir) * W + pos] != 0 &&
                              (changes + 1) * 2 * W <= INT_MAX &&
                              dp != 0 && ndp != 0 &&
                              Zlength(current_table) == (changes + 1) * 2 * W &&
                              Zlength(next_table) == (changes + 1) * 2 * W &&
                              TurtleLayerMeaning(commands, i, changes, current_table) &&
                              TurtleNextPrefix(commands, i, changes,
                                2 * ((c * 2 + dir) * W + pos) + flip,
                                next_table) &&
                              CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
                              UCharArray::full(dp, (changes + 1) * 2 * W, current_table) *
                              UCharArray::full(ndp, (changes + 1) * 2 * W, next_table)
                        */
                        for (int flip = 0; flip <= 1; ++flip) {
                            if (c + flip > changes) {
                                continue;
                            }
                            char cmd = s[i];
                            if (flip) {
                                cmd = cmd == 'T' ? 'F' : 'T';
                            }
                            int nd = dir;
                            int np = pos;
                            if (cmd == 'T') {
                                nd ^= 1;
                            } else {
                                np += dir ? -1 : 1;
                            }
                            /*@ 0 <= nd && nd < 2 by local */
                            if (np >= 0 && np < W) {
                                /*@ 0 <= ((c + flip) * 2 + nd) * W + np &&
                                    ((c + flip) * 2 + nd) * W + np <
                                      (changes + 1) * 2 * W by local */
                                AT(ndp, c + flip, nd, np) = 1;
                            }
                        }
                    }
                }
            }
        }
        /*@ Assert
            exists current_table next_table,
              s == s@pre && changes == changes@pre && changes@pre == n &&
              len == Zlength(commands) && W == 2 * len + 1 && O == len &&
              1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
              (forall k, (0 <= k && k < len) =>
                 (commands[k] == 70 || commands[k] == 84)) &&
              0 <= i && i < len &&
              dp != 0 && ndp != 0 &&
              Zlength(current_table) == (changes + 1) * 2 * W &&
              Zlength(next_table) == (changes + 1) * 2 * W &&
              TurtleLayerMeaning(commands, i, changes, current_table) &&
              TurtleNextPrefix(commands, i, changes,
                (changes + 1) * 2 * W * 2, next_table) &&
              CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
              UCharArray::full(dp, (changes + 1) * 2 * W, current_table) *
              UCharArray::full(ndp, (changes + 1) * 2 * W, next_table)
        */
        unsigned char *tmp = dp;
        dp = ndp;
        ndp = tmp;
    }

    /*@ Assert
        exists final_table spare_table,
          s == s@pre && changes == changes@pre && changes@pre == n &&
          len == Zlength(commands) && W == 2 * len + 1 && O == len &&
          1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
          (forall k, (0 <= k && k < len) =>
             (commands[k] == 70 || commands[k] == 84)) &&
          dp != 0 && ndp != 0 &&
          Zlength(final_table) == (changes + 1) * 2 * W &&
          Zlength(spare_table) == (changes + 1) * 2 * W &&
          TurtleLayerMeaning(commands, len, changes, final_table) &&
          CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
          UCharArray::full(dp, (changes + 1) * 2 * W, final_table) *
          UCharArray::full(ndp, (changes + 1) * 2 * W, spare_table)
    */
    int ans = 0;
    /*@ Inv Assert
        exists final_table spare_table,
          s == s@pre && changes == changes@pre && changes@pre == n &&
          len == Zlength(commands) && W == 2 * len + 1 && O == len &&
          1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
          (forall k, (0 <= k && k < len) =>
             (commands[k] == 70 || commands[k] == 84)) &&
          0 <= c && c <= changes + 1 && 0 <= ans && ans <= len &&
          dp != 0 && ndp != 0 &&
          Zlength(final_table) == (changes + 1) * 2 * W &&
          Zlength(spare_table) == (changes + 1) * 2 * W &&
          TurtleLayerMeaning(commands, len, changes, final_table) &&
          TurtleAnswerPrefix(commands, changes, c * 2 * W, ans) &&
          CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
          UCharArray::full(dp, (changes + 1) * 2 * W, final_table) *
          UCharArray::full(ndp, (changes + 1) * 2 * W, spare_table)
    */
    for (int c = 0; c <= changes; ++c) {
        if (((changes - c) & 1) == 0) {
            /*@ Inv Assert
                exists final_table spare_table,
                  s == s@pre && changes == changes@pre && changes@pre == n &&
                  len == Zlength(commands) && W == 2 * len + 1 && O == len &&
                  1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
                  (forall k, (0 <= k && k < len) =>
                     (commands[k] == 70 || commands[k] == 84)) &&
                  0 <= c && c <= changes && 0 <= d && d <= 2 &&
                  ((changes - c) & 1) == 0 &&
                  0 <= ans && ans <= len && dp != 0 && ndp != 0 &&
                  Zlength(final_table) == (changes + 1) * 2 * W &&
                  Zlength(spare_table) == (changes + 1) * 2 * W &&
                  TurtleLayerMeaning(commands, len, changes, final_table) &&
                  TurtleAnswerPrefix(commands, changes, (c * 2 + d) * W, ans) &&
                  CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
                  UCharArray::full(dp, (changes + 1) * 2 * W, final_table) *
                  UCharArray::full(ndp, (changes + 1) * 2 * W, spare_table)
            */
            for (int d = 0; d < 2; ++d) {
                /*@ Inv Assert
                    exists final_table spare_table,
                      s == s@pre && changes == changes@pre && changes@pre == n &&
                      len == Zlength(commands) && W == 2 * len + 1 && O == len &&
                      1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
                      (forall k, (0 <= k && k < len) =>
                         (commands[k] == 70 || commands[k] == 84)) &&
                      0 <= c && c <= changes && 0 <= d && d < 2 &&
                      0 <= p && p <= W && ((changes - c) & 1) == 0 &&
                      0 <= ans && ans <= len &&
                      0 <= (c * 2 + d) * W + p &&
                      (c * 2 + d) * W + p <= (changes + 1) * 2 * W &&
                      dp != 0 && ndp != 0 &&
                      Zlength(final_table) == (changes + 1) * 2 * W &&
                      Zlength(spare_table) == (changes + 1) * 2 * W &&
                      TurtleLayerMeaning(commands, len, changes, final_table) &&
                      TurtleAnswerPrefix(commands, changes,
                        (c * 2 + d) * W + p, ans) &&
                      CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
                      UCharArray::full(dp, (changes + 1) * 2 * W, final_table) *
                      UCharArray::full(ndp, (changes + 1) * 2 * W, spare_table)
                */
                for (int p = 0; p < W; ++p) {
                    /*@ 0 <= (c * 2 + d) * W + p &&
                        (c * 2 + d) * W + p <
                          (changes + 1) * 2 * W by local */
                    if (AT(dp, c, d, p)) {
                        int x = abs(p - O)
                            /*@ where (abs_logo_position) */;
                        if (x > ans) {
                            ans = x;
                        }
                    }
                }
            }
        }
    }

    /*@ Assert
        exists final_table spare_table,
          s == s@pre && changes == changes@pre && changes@pre == n &&
          len == Zlength(commands) && W == 2 * len + 1 && O == len &&
          1 <= len && len <= 100 && 1 <= changes && changes <= 50 &&
          (forall k, (0 <= k && k < len) =>
             (commands[k] == 70 || commands[k] == 84)) &&
          0 <= ans && ans <= len && dp != 0 && ndp != 0 &&
          Zlength(final_table) == (changes + 1) * 2 * W &&
          Zlength(spare_table) == (changes + 1) * 2 * W &&
          Spec(changes, commands, ans) &&
          CharArray::full(s, len + 1, app(commands, cons(0, nil))) *
          UCharArray::full(dp, (changes + 1) * 2 * W, final_table) *
          UCharArray::full(ndp, (changes + 1) * 2 * W, spare_table)
    */
    free(dp) /*@ where (free_uchar) */;
    free(ndp) /*@ where (free_uchar) */;
    return ans;
}

// int main(void)
// {
//     char s[105];
//     int changes;
//     if (scanf("%104s %d", s, &changes) != 2) {
//         return 0;
//     }
//     printf("%d\n", solver(s, changes));
//     return 0;
// }
