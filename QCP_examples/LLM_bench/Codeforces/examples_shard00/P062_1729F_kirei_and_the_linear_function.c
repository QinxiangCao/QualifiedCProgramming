/* Codeforces 1729/F - Kirei and the Linear Function */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"
#include "array2_ext_def.h"

typedef unsigned long size_t;

void *calloc(size_t nmemb, size_t size)
/*@ Require
      0 <= nmemb && size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, nmemb, repeat_Z(0, nmemb))
*/;

void free(void *ptr)
/*@ Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/;

/* QCP_INSERT_BEGIN:P062_1729F_kirei_and_the_linear_function.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> list (Z * Z * Z) -> list (Z * Z) -> Prop)
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P062_1729F_kirei_and_the_linear_function_lib */
/* QCP_INSERT_END:P062_1729F_kirei_and_the_linear_function.support */
/*@ Extern Coq
      (DigitPrefixSums : list Z -> list Z -> Z -> Prop)
      (pos_init_stage : Z -> list (list (option Z)))
      (PositionsPrefix : list Z -> Z -> Z -> list (list Z) -> Prop)
      (QueryBestPrefix : list Z -> Z -> (Z * Z * Z) -> Z -> Z -> Z -> Prop)
      (QueryOutputPrefix : Z -> list Z -> list (Z * Z * Z) -> Z -> list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (FlatPositionsPrefix : list Z -> Z -> Z -> list Z -> Prop)
*/
static void
solver(const char *s, int w, int m, const int *ql, const int *qr, const int *qk, int *out1,
       int *out2) /* QCP_INSERT_BEGIN:P062_1729F_kirei_and_the_linear_function.contract */

/*@ With (text : list Z)
             (qs : list (Z * Z * Z))
             (ql_data qr_data qk_data : list Z)
    Require
      2 <= Zlength(text) && Zlength(text) <= 200000 &&
      1 <= w && w < Zlength(text) &&
      (forall i, (0 <= i && i < Zlength(text)) =>
        (48 <= text[i] && text[i] <= 57)) &&
      m == Zlength(qs) && Zlength(ql_data) == m &&
      Zlength(qr_data) == m && Zlength(qk_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (ql_data[i] == ztriple_1(qs[i]) && qr_data[i] == ztriple_2(qs[i]) &&
         qk_data[i] == ztriple_3(qs[i]) &&
         1 <= ql_data[i] && ql_data[i] <= qr_data[i] &&
         qr_data[i] <= Zlength(text) &&
         0 <= qk_data[i] && qk_data[i] < 9)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
      IntArray::full(ql, m, ql_data) * IntArray::full(qr, m, qr_data) *
      IntArray::full(qk, m, qk_data) *
      IntArray::undef_full(out1, m) * IntArray::undef_full(out2, m)
    Ensure
      exists out out1_data out2_data,
        Spec(w, text, qs, out) &&
        Zlength(out) == m && Zlength(out1_data) == m && Zlength(out2_data) == m &&
        (forall i, (0 <= i && i < m) =>
          (out1_data[i] == fst(out[i]) && out2_data[i] == snd(out[i]))) &&
        CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
        IntArray::full(ql, m, ql_data) * IntArray::full(qr, m, qr_data) *
        IntArray::full(qk, m, qk_data) *
        IntArray::full(out1, m, out1_data) * IntArray::full(out2, m, out2_data)
*/
/* QCP_INSERT_END:P062_1729F_kirei_and_the_linear_function.contract */
{
    /*@ 2 <= Zlength(text) && Zlength(text) <= 200000 &&
        (forall j, (0 <= j && j < Zlength(text)) =>
          (48 <= text[j] && text[j] <= 57)) &&
        CharArray::full(s@pre, Zlength(text) + 1, app(text, cons(0, nil)))
        which implies
        valid_string(text) &&
        string_length(text) == Zlength(text) &&
        c_string(text) == app(text, cons(0, nil)) &&
        CharArray::full(s@pre, string_length(text) + 1, c_string(text))
    */
    int n = (int)strlen(s),
        *pre = calloc((size_t)n + 1, sizeof(*pre));
    /*@ Inv Assert
          exists prefix_values,
            s == s@pre && w == w@pre && m == m@pre &&
            ql == ql@pre && qr == qr@pre && qk == qk@pre &&
            out1 == out1@pre && out2 == out2@pre &&
            n == Zlength(text) && string_length(text) == Zlength(text) &&
            c_string(text) == app(text, cons(0, nil)) && pre != 0 &&
            2 <= Zlength(text) && Zlength(text) <= 200000 &&
            1 <= w@pre && w@pre < Zlength(text) &&
            (forall j, (0 <= j && j < Zlength(text)) =>
              (48 <= text[j] && text[j] <= 57)) &&
            m@pre == Zlength(qs) && Zlength(ql_data) == m@pre &&
            Zlength(qr_data) == m@pre && Zlength(qk_data) == m@pre &&
            (forall j, (0 <= j && j < m@pre) =>
              (ql_data[j] == ztriple_1(qs[j]) &&
               qr_data[j] == ztriple_2(qs[j]) &&
               qk_data[j] == ztriple_3(qs[j]) &&
               1 <= ql_data[j] && ql_data[j] <= qr_data[j] &&
               qr_data[j] <= Zlength(text) &&
               0 <= qk_data[j] && qk_data[j] < 9)) &&
            0 <= i && i <= n &&
            Zlength(prefix_values) == n + 1 &&
            DigitPrefixSums(text, prefix_values, i) &&
            (forall j, (0 <= j && j <= i) =>
              (0 <= prefix_values[j] && prefix_values[j] <= 9 * j)) &&
            store_string(s@pre, text) *
            IntArray::full(ql@pre, m@pre, ql_data) *
            IntArray::full(qr@pre, m@pre, qr_data) *
            IntArray::full(qk@pre, m@pre, qk_data) *
            IntArray::undef_full(out1@pre, m@pre) *
            IntArray::undef_full(out2@pre, m@pre) *
            IntArray::full(pre, n + 1, prefix_values)
    */
    for (int i = 0; i < n; ++i)
        pre[i + 1] = pre[i] + s[i] - '0';
    int pos[18];
    /*@ Inv Assert
          exists prefix_values,
            s == s@pre && w == w@pre && m == m@pre &&
            ql == ql@pre && qr == qr@pre && qk == qk@pre &&
            out1 == out1@pre && out2 == out2@pre &&
            n == Zlength(text) && string_length(text) == Zlength(text) &&
            c_string(text) == app(text, cons(0, nil)) && pre != 0 &&
            2 <= Zlength(text) && Zlength(text) <= 200000 &&
            1 <= w@pre && w@pre < Zlength(text) &&
            (forall j, (0 <= j && j < Zlength(text)) =>
              (48 <= text[j] && text[j] <= 57)) &&
            m@pre == Zlength(qs) && Zlength(ql_data) == m@pre &&
            Zlength(qr_data) == m@pre && Zlength(qk_data) == m@pre &&
            (forall j, (0 <= j && j < m@pre) =>
              (ql_data[j] == ztriple_1(qs[j]) &&
               qr_data[j] == ztriple_2(qs[j]) &&
               qk_data[j] == ztriple_3(qs[j]) &&
               1 <= ql_data[j] && ql_data[j] <= qr_data[j] &&
               qr_data[j] <= Zlength(text) &&
               0 <= qk_data[j] && qk_data[j] < 9)) &&
            0 <= r && r <= 9 &&
            Zlength(prefix_values) == n + 1 &&
            DigitPrefixSums(text, prefix_values, n) &&
            (forall lo hi,
              (0 <= lo && lo <= hi && hi <= n) =>
              (0 <= prefix_values[hi] - prefix_values[lo] &&
               prefix_values[hi] - prefix_values[lo] <= 9 * (hi - lo))) &&
            store_string(s@pre, text) *
            IntArray::full(ql@pre, m@pre, ql_data) *
            IntArray::full(qr@pre, m@pre, qr_data) *
            IntArray::full(qk@pre, m@pre, qk_data) *
            IntArray::undef_full(out1@pre, m@pre) *
            IntArray::undef_full(out2@pre, m@pre) *
            IntArray::full(pre, n + 1, prefix_values) *
            IntArray::seg(pos, 0, 2 * r, repeat_Z(-1, 2 * r)) *
            IntArray::undef_seg(pos, 2 * r, 18)
    */
    for (int r = 0; r < 9; ++r)
    {
        pos[2 * r] = -1;
        pos[2 * r + 1] = -1;
    }
    /*@ Inv Assert
          exists prefix_values position_values,
            s == s@pre && w == w@pre && m == m@pre &&
            ql == ql@pre && qr == qr@pre && qk == qk@pre &&
            out1 == out1@pre && out2 == out2@pre &&
            n == Zlength(text) && string_length(text) == Zlength(text) &&
            c_string(text) == app(text, cons(0, nil)) && pre != 0 &&
            2 <= Zlength(text) && Zlength(text) <= 200000 &&
            1 <= w@pre && w@pre < Zlength(text) &&
            (forall j, (0 <= j && j < Zlength(text)) =>
              (48 <= text[j] && text[j] <= 57)) &&
            m@pre == Zlength(qs) && Zlength(ql_data) == m@pre &&
            Zlength(qr_data) == m@pre && Zlength(qk_data) == m@pre &&
            (forall j, (0 <= j && j < m@pre) =>
              (ql_data[j] == ztriple_1(qs[j]) &&
               qr_data[j] == ztriple_2(qs[j]) &&
               qk_data[j] == ztriple_3(qs[j]) &&
               1 <= ql_data[j] && ql_data[j] <= qr_data[j] &&
               qr_data[j] <= Zlength(text) &&
               0 <= qk_data[j] && qk_data[j] < 9)) &&
            0 <= i && i <= n - w@pre + 1 &&
            Zlength(prefix_values) == n + 1 &&
            Zlength(position_values) == 18 &&
            DigitPrefixSums(text, prefix_values, n) &&
            (forall lo hi,
              (0 <= lo && lo <= hi && hi <= n) =>
              (0 <= prefix_values[hi] - prefix_values[lo] &&
               prefix_values[hi] - prefix_values[lo] <= 9 * (hi - lo))) &&
            FlatPositionsPrefix(text, w@pre, i, position_values) &&
            store_string(s@pre, text) *
            IntArray::full(ql@pre, m@pre, ql_data) *
            IntArray::full(qr@pre, m@pre, qr_data) *
            IntArray::full(qk@pre, m@pre, qk_data) *
            IntArray::undef_full(out1@pre, m@pre) *
            IntArray::undef_full(out2@pre, m@pre) *
            IntArray::full(pre, n + 1, prefix_values) *
            IntArray::full(pos, 18, position_values)
    */
    for (int i = 0; i + w <= n; ++i)
    {
        int r = (pre[i + w] - pre[i]) % 9;
        /*@ 0 <= r && r < 9 by local */
        if (pos[2 * r] < 0)
            pos[2 * r] = i + 1;
        else if (pos[2 * r + 1] < 0)
            pos[2 * r + 1] = i + 1;
    }
    /*@ Inv Assert
          exists prefix_values position_values out1_prefix out2_prefix,
            s == s@pre && w == w@pre && m == m@pre &&
            ql == ql@pre && qr == qr@pre && qk == qk@pre &&
            out1 == out1@pre && out2 == out2@pre &&
            n == Zlength(text) && string_length(text) == Zlength(text) &&
            c_string(text) == app(text, cons(0, nil)) && pre != 0 &&
            2 <= Zlength(text) && Zlength(text) <= 200000 &&
            1 <= w@pre && w@pre < Zlength(text) &&
            (forall j, (0 <= j && j < Zlength(text)) =>
              (48 <= text[j] && text[j] <= 57)) &&
            m@pre == Zlength(qs) && Zlength(ql_data) == m@pre &&
            Zlength(qr_data) == m@pre && Zlength(qk_data) == m@pre &&
            (forall j, (0 <= j && j < m@pre) =>
              (ql_data[j] == ztriple_1(qs[j]) &&
               qr_data[j] == ztriple_2(qs[j]) &&
               qk_data[j] == ztriple_3(qs[j]) &&
               1 <= ql_data[j] && ql_data[j] <= qr_data[j] &&
               qr_data[j] <= Zlength(text) &&
               0 <= qk_data[j] && qk_data[j] < 9)) &&
            0 <= z && z <= m@pre &&
            Zlength(prefix_values) == n + 1 &&
            Zlength(position_values) == 18 &&
            DigitPrefixSums(text, prefix_values, n) &&
            (forall lo hi,
              (0 <= lo && lo <= hi && hi <= n) =>
              (0 <= prefix_values[hi] - prefix_values[lo] &&
               prefix_values[hi] - prefix_values[lo] <= 9 * (hi - lo))) &&
            FlatPositionsPrefix(text, w@pre, n - w@pre + 1, position_values) &&
            QueryOutputPrefix(w@pre, text, qs, z, out1_prefix, out2_prefix) &&
            store_string(s@pre, text) *
            IntArray::full(ql@pre, m@pre, ql_data) *
            IntArray::full(qr@pre, m@pre, qr_data) *
            IntArray::full(qk@pre, m@pre, qk_data) *
            IntArray::seg(out1@pre, 0, z, out1_prefix) *
            IntArray::undef_seg(out1@pre, z, m@pre) *
            IntArray::seg(out2@pre, 0, z, out2_prefix) *
            IntArray::undef_seg(out2@pre, z, m@pre) *
            IntArray::full(pre, n + 1, prefix_values) *
            IntArray::full(pos, 18, position_values)
    */
    for (int z = 0; z < m; ++z)
    {
        int l = ql[z], r = qr[z], k = qk[z], v = (pre[r] - pre[l - 1]) % 9, best1 = 1 << 30,
            best2 = 1 << 30;
        /*@ 0 <= v && v < 9 by local */
        /*@ Inv Assert
              exists prefix_values position_values out1_prefix out2_prefix,
                s == s@pre && w == w@pre && m == m@pre &&
                ql == ql@pre && qr == qr@pre && qk == qk@pre &&
                out1 == out1@pre && out2 == out2@pre &&
                n == Zlength(text) && string_length(text) == Zlength(text) &&
                c_string(text) == app(text, cons(0, nil)) && pre != 0 &&
                2 <= Zlength(text) && Zlength(text) <= 200000 &&
                1 <= w@pre && w@pre < Zlength(text) &&
                (forall j, (0 <= j && j < Zlength(text)) =>
                  (48 <= text[j] && text[j] <= 57)) &&
                m@pre == Zlength(qs) && Zlength(ql_data) == m@pre &&
                Zlength(qr_data) == m@pre && Zlength(qk_data) == m@pre &&
                (forall j, (0 <= j && j < m@pre) =>
                  (ql_data[j] == ztriple_1(qs[j]) &&
                   qr_data[j] == ztriple_2(qs[j]) &&
                   qk_data[j] == ztriple_3(qs[j]) &&
                   1 <= ql_data[j] && ql_data[j] <= qr_data[j] &&
                   qr_data[j] <= Zlength(text) &&
                   0 <= qk_data[j] && qk_data[j] < 9)) &&
                0 <= z && z < m@pre && 0 <= a && a <= 9 &&
                l == ql_data[z] && r == qr_data[z] && k == qk_data[z] &&
                l == ztriple_1(qs[z]) && r == ztriple_2(qs[z]) &&
                k == ztriple_3(qs[z]) &&
                1 <= l && l <= r && r <= n && 0 <= k && k < 9 &&
                v == (prefix_values[r] - prefix_values[l - 1]) % 9 &&
                0 <= v && v < 9 &&
                Zlength(prefix_values) == n + 1 &&
                Zlength(position_values) == 18 &&
                DigitPrefixSums(text, prefix_values, n) &&
                (forall lo hi,
                  (0 <= lo && lo <= hi && hi <= n) =>
                  (0 <= prefix_values[hi] - prefix_values[lo] &&
                   prefix_values[hi] - prefix_values[lo] <= 9 * (hi - lo))) &&
                FlatPositionsPrefix(text, w@pre, n - w@pre + 1, position_values) &&
                QueryOutputPrefix(w@pre, text, qs, z, out1_prefix, out2_prefix) &&
                QueryBestPrefix(text, w@pre, qs[z], a, best1, best2) &&
                store_string(s@pre, text) *
                IntArray::full(ql@pre, m@pre, ql_data) *
                IntArray::full(qr@pre, m@pre, qr_data) *
                IntArray::full(qk@pre, m@pre, qk_data) *
                IntArray::seg(out1@pre, 0, z, out1_prefix) *
                IntArray::undef_seg(out1@pre, z, m@pre) *
                IntArray::seg(out2@pre, 0, z, out2_prefix) *
                IntArray::undef_seg(out2@pre, z, m@pre) *
                IntArray::full(pre, n + 1, prefix_values) *
                IntArray::full(pos, 18, position_values)
        */
        for (int a = 0; a < 9; ++a)
        {
            int b = (k - a * v) % 9;
            if (b < 0)
                b += 9;
            /*@ 0 <= b && b < 9 by local */
            if (pos[2 * a] < 0)
                continue;
            int p1 = pos[2 * a], p2 = (a == b) ? pos[2 * b + 1] : pos[2 * b];
            if (p2 < 0)
                continue;
            if (p1 < best1 || (p1 == best1 && p2 < best2))
            {
                best1 = p1;
                best2 = p2;
            }
        }
        /*@ Assert
              exists prefix_values position_values out1_prefix out2_prefix,
                s == s@pre && w == w@pre && m == m@pre &&
                ql == ql@pre && qr == qr@pre && qk == qk@pre &&
                out1 == out1@pre && out2 == out2@pre &&
                n == Zlength(text) && string_length(text) == Zlength(text) &&
                c_string(text) == app(text, cons(0, nil)) && pre != 0 &&
                2 <= Zlength(text) && Zlength(text) <= 200000 &&
                1 <= w@pre && w@pre < Zlength(text) &&
                (forall j, (0 <= j && j < Zlength(text)) =>
                  (48 <= text[j] && text[j] <= 57)) &&
                m@pre == Zlength(qs) && Zlength(ql_data) == m@pre &&
                Zlength(qr_data) == m@pre && Zlength(qk_data) == m@pre &&
                (forall j, (0 <= j && j < m@pre) =>
                  (ql_data[j] == ztriple_1(qs[j]) &&
                   qr_data[j] == ztriple_2(qs[j]) &&
                   qk_data[j] == ztriple_3(qs[j]) &&
                   1 <= ql_data[j] && ql_data[j] <= qr_data[j] &&
                   qr_data[j] <= Zlength(text) &&
                   0 <= qk_data[j] && qk_data[j] < 9)) &&
                0 <= z && z < m@pre &&
                l == ql_data[z] && r == qr_data[z] && k == qk_data[z] &&
                l == ztriple_1(qs[z]) && r == ztriple_2(qs[z]) &&
                k == ztriple_3(qs[z]) &&
                1 <= l && l <= r && r <= n && 0 <= k && k < 9 &&
                v == (prefix_values[r] - prefix_values[l - 1]) % 9 &&
                0 <= v && v < 9 &&
                Zlength(prefix_values) == n + 1 &&
                Zlength(position_values) == 18 &&
                DigitPrefixSums(text, prefix_values, n) &&
                (forall lo hi,
                  (0 <= lo && lo <= hi && hi <= n) =>
                  (0 <= prefix_values[hi] - prefix_values[lo] &&
                   prefix_values[hi] - prefix_values[lo] <= 9 * (hi - lo))) &&
                FlatPositionsPrefix(text, w@pre, n - w@pre + 1, position_values) &&
                QueryOutputPrefix(w@pre, text, qs, z, out1_prefix, out2_prefix) &&
                QueryBestPrefix(text, w@pre, qs[z], 9, best1, best2) &&
                store_string(s@pre, text) *
                IntArray::full(ql@pre, m@pre, ql_data) *
                IntArray::full(qr@pre, m@pre, qr_data) *
                IntArray::full(qk@pre, m@pre, qk_data) *
                IntArray::seg(out1@pre, 0, z, out1_prefix) *
                IntArray::undef_seg(out1@pre, z, m@pre) *
                IntArray::seg(out2@pre, 0, z, out2_prefix) *
                IntArray::undef_seg(out2@pre, z, m@pre) *
                IntArray::full(pre, n + 1, prefix_values) *
                IntArray::full(pos, 18, position_values)
        */
        out1[z] = best1 == (1 << 30) ? -1 : best1;
        out2[z] = best1 == (1 << 30) ? -1 : best2;
    }
    /*@ Assert
          exists prefix_values position_values out1_data_now out2_data_now,
            s == s@pre && w == w@pre && m == m@pre &&
            ql == ql@pre && qr == qr@pre && qk == qk@pre &&
            out1 == out1@pre && out2 == out2@pre &&
            n == Zlength(text) && string_length(text) == Zlength(text) &&
            c_string(text) == app(text, cons(0, nil)) && pre != 0 &&
            2 <= Zlength(text) && Zlength(text) <= 200000 &&
            1 <= w@pre && w@pre < Zlength(text) &&
            (forall j, (0 <= j && j < Zlength(text)) =>
              (48 <= text[j] && text[j] <= 57)) &&
            m@pre == Zlength(qs) && Zlength(ql_data) == m@pre &&
            Zlength(qr_data) == m@pre && Zlength(qk_data) == m@pre &&
            (forall j, (0 <= j && j < m@pre) =>
              (ql_data[j] == ztriple_1(qs[j]) &&
               qr_data[j] == ztriple_2(qs[j]) &&
               qk_data[j] == ztriple_3(qs[j]) &&
               1 <= ql_data[j] && ql_data[j] <= qr_data[j] &&
               qr_data[j] <= Zlength(text) &&
               0 <= qk_data[j] && qk_data[j] < 9)) &&
            Zlength(prefix_values) == n + 1 &&
            Zlength(position_values) == 18 &&
            DigitPrefixSums(text, prefix_values, n) &&
            (forall lo hi,
              (0 <= lo && lo <= hi && hi <= n) =>
              (0 <= prefix_values[hi] - prefix_values[lo] &&
               prefix_values[hi] - prefix_values[lo] <= 9 * (hi - lo))) &&
            FlatPositionsPrefix(text, w@pre, n - w@pre + 1, position_values) &&
            QueryOutputPrefix(w@pre, text, qs, m@pre, out1_data_now, out2_data_now) &&
            store_string(s@pre, text) *
            IntArray::full(ql@pre, m@pre, ql_data) *
            IntArray::full(qr@pre, m@pre, qr_data) *
            IntArray::full(qk@pre, m@pre, qk_data) *
            IntArray::full(out1@pre, m@pre, out1_data_now) *
            IntArray::full(out2@pre, m@pre, out2_data_now) *
            IntArray::full(pre, n + 1, prefix_values) *
            IntArray::full(pos, 18, position_values)
    */
    free(pre);
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         char *s = malloc(200005);
//         scanf("%s", s);
//         int w, m;
//         scanf("%d %d", &w, &m);
//         int *l = malloc((size_t)m * sizeof(*l)), *r = malloc((size_t)m * sizeof(*r)),
//             *k = malloc((size_t)m * sizeof(*k)), *o1 = malloc((size_t)m * sizeof(*o1)),
//             *o2 = malloc((size_t)m * sizeof(*o2));
//         for (int i = 0; i < m; ++i)
//             scanf("%d %d %d", &l[i], &r[i], &k[i]);
//         solver(s, w, m, l, r, k, o1, o2);
//         for (int i = 0; i < m; ++i)
//             printf("%d %d\n", o1[i], o2[i]);
//         free(l);
//         free(r);
//         free(k);
//         free(o1);
//         free(o2);
//         free(s);
//     }
//     return 0;
// }
