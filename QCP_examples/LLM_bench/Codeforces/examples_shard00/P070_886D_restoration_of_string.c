/* Codeforces 886/D - Restoration of string */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"
/* QCP_INSERT_BEGIN:P070_886D_restoration_of_string.support */
/*@ Extern Coq
      (Pre : list (list Z) -> Prop)
      (Spec : list (list Z) -> option (list Z) -> Prop)
      (InitState : list Z -> list Z -> list Z -> Prop)
      (GraphBuildState : list (list Z) -> Z -> list Z -> list Z -> list Z -> Prop)
      (WordScanState : list (list Z) -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (TraversalState : list Z -> list Z -> list Z -> Z -> list Z -> list Z -> Prop)
      (PathScanState : list Z -> list Z -> list Z -> Z -> Z -> list Z -> list Z -> Prop)
      (CoverageScanState : list Z -> list Z -> Z -> Prop)
      (SuccessfulTraversal : list (list Z) -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (CharPtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
      (CharPtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P070_886D_restoration_of_string_lib */
/*@ include strategies "ptr_array2.strategies" */
/* QCP_INSERT_END:P070_886D_restoration_of_string.support */
static int solver(int n, char *const *words,
                  char *out) /* QCP_INSERT_BEGIN:P070_886D_restoration_of_string.contract */

/*@ With (g rows : list (list Z))
    Require
      Pre(g) &&
      1 <= Zlength(g) && Zlength(g) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(g)) =>
        0 < Zlength(Znth(i, g, nil)) &&
        Zlength(Znth(i, g, nil)) <= 100000) &&
      (forall i j,
        (0 <= i && i < Zlength(g) &&
         0 <= j && j < Zlength(Znth(i, g, nil))) =>
          (97 <= Znth(j, Znth(i, g, nil), 0) &&
           Znth(j, Znth(i, g, nil), 0) <= 122)) &&
      n == Zlength(g) &&
      Zlength(rows) == n &&
      (forall i, (0 <= i && i < n) =>
        (Znth(i, rows, nil) == c_string(Znth(i, g, nil)) &&
         valid_string(Znth(i, g, nil)) &&
         string_length(Znth(i, g, nil)) < INT_MAX)) &&
      CharPtrArray2::full(words, n, rows) * CharArray::undef_full(out, 64)
    Ensure
      CharPtrArray2::full(words, n, rows) *
      (((__return == 0 && Spec(g, None)) &&
        exists written partial,
          0 <= written && written <= 26 && Zlength(partial) == written &&
          CharArray::full(out, written, partial) *
          CharArray::undef_seg(out, written, 64)) ||
       (exists result,
          __return == 1 && Spec(g, Some(result)) && Zlength(result) < 64 &&
          CharArray::full(out, Zlength(result) + 1, app(result, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(result) + 1, 64)))
*/
/* QCP_INSERT_END:P070_886D_restoration_of_string.contract */
{
    int next[26], prev[26], used[26] = {0};
    /*@ Inv Assert
        exists next_prefix prev_prefix used_l,
          words == words@pre && out == out@pre && n == n@pre &&
          Pre(g) &&
          n@pre == Zlength(g) &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(rows) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 < Zlength(Znth(k, g, nil)) &&
             Zlength(Znth(k, g, nil)) <= 100000 &&
             Znth(k, rows, nil) == c_string(Znth(k, g, nil)) &&
             valid_string(Znth(k, g, nil)) &&
             string_length(Znth(k, g, nil)) < INT_MAX)) &&
          (forall k q,
            (0 <= k && k < n@pre &&
             0 <= q && q < Zlength(Znth(k, g, nil))) =>
              (97 <= Znth(q, Znth(k, g, nil), 0) &&
               Znth(q, Znth(k, g, nil), 0) <= 122)) &&
          0 <= i && i <= 26 &&
          Zlength(next_prefix) == i && Zlength(prev_prefix) == i &&
          InitState(next_prefix, prev_prefix, used_l) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          CharArray::undef_full(out@pre, 64) *
          IntArray::seg(next, 0, i, next_prefix) *
          IntArray::undef_seg(next, i, 26) *
          IntArray::seg(prev, 0, i, prev_prefix) *
          IntArray::undef_seg(prev, i, 26) *
          IntArray::full(used, 26, used_l)
    */
    for (int i = 0; i < 26; ++i)
    {
        prev[i] = -1;
        next[i] = -1;
    }
    /*@ Inv Assert
        exists next_l prev_l used_l,
          words == words@pre && out == out@pre && n == n@pre &&
          n@pre == Zlength(g) &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(rows) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 < Zlength(Znth(k, g, nil)) &&
             Zlength(Znth(k, g, nil)) <= 100000 &&
             Znth(k, rows, nil) == c_string(Znth(k, g, nil)) &&
             valid_string(Znth(k, g, nil)) &&
             string_length(Znth(k, g, nil)) < INT_MAX)) &&
          (forall k q,
            (0 <= k && k < n@pre &&
             0 <= q && q < Zlength(Znth(k, g, nil))) =>
              (97 <= Znth(q, Znth(k, g, nil), 0) &&
               Znth(q, Znth(k, g, nil), 0) <= 122)) &&
          0 <= z && z <= n@pre &&
          Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
          Zlength(used_l) == 26 &&
          (forall k, (0 <= k && k < 26) =>
            (-1 <= Znth(k, next_l, -1) && Znth(k, next_l, -1) < 26)) &&
          (forall k, (0 <= k && k < 26) =>
            (-1 <= Znth(k, prev_l, -1) && Znth(k, prev_l, -1) < 26)) &&
          GraphBuildState(g, z, next_l, prev_l, used_l) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          CharArray::undef_full(out@pre, 64) *
          IntArray::full(next, 26, next_l) *
          IntArray::full(prev, 26, prev_l) *
          IntArray::full(used, 26, used_l)
    */
    for (int z = 0; z < n; ++z)
    {
        /*@ Assert
            exists next_l prev_l used_l row_ptr,
              words == words@pre && out == out@pre && n == n@pre &&
              n@pre == Zlength(g) &&
              1 <= n@pre && n@pre <= 100000 &&
              Zlength(rows) == n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (0 < Zlength(Znth(k, g, nil)) &&
                 Zlength(Znth(k, g, nil)) <= 100000 &&
                 Znth(k, rows, nil) == c_string(Znth(k, g, nil)) &&
                 valid_string(Znth(k, g, nil)) &&
                 string_length(Znth(k, g, nil)) < INT_MAX)) &&
              (forall k q,
                (0 <= k && k < n@pre &&
                 0 <= q && q < Zlength(Znth(k, g, nil))) =>
                  (97 <= Znth(q, Znth(k, g, nil), 0) &&
                   Znth(q, Znth(k, g, nil), 0) <= 122)) &&
              0 <= z && z < n@pre &&
              Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
              Zlength(used_l) == 26 &&
              (forall k, (0 <= k && k < 26) =>
                (-1 <= Znth(k, next_l, -1) && Znth(k, next_l, -1) < 26)) &&
              (forall k, (0 <= k && k < 26) =>
                (-1 <= Znth(k, prev_l, -1) && Znth(k, prev_l, -1) < 26)) &&
              GraphBuildState(g, z, next_l, prev_l, used_l) &&
              CharPtrArray2::missing_i(words@pre, n@pre, z, row_ptr, rows) *
              data_at(words@pre + z * sizeof(char *), char *, row_ptr) *
              CharArray::full(row_ptr,
                              Zlength(Znth(z, g, nil)) + 1,
                              c_string(Znth(z, g, nil))) *
              CharArray::undef_full(out@pre, 64) *
              IntArray::full(next, 26, next_l) *
              IntArray::full(prev, 26, prev_l) *
              IntArray::full(used, 26, used_l)
        */
        int seen[26] = {0}, last = -1;
        const char *s = words[z];
        /*@ Inv Assert
            exists next_l prev_l used_l seen_l saved_s,
              words == words@pre && out == out@pre && n == n@pre &&
              n@pre == Zlength(g) &&
              1 <= n@pre && n@pre <= 100000 &&
              Zlength(rows) == n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (0 < Zlength(Znth(k, g, nil)) &&
                 Zlength(Znth(k, g, nil)) <= 100000 &&
                 Znth(k, rows, nil) == c_string(Znth(k, g, nil)) &&
                 valid_string(Znth(k, g, nil)) &&
              string_length(Znth(k, g, nil)) < INT_MAX)) &&
              0 <= z && z < n@pre &&
              s == saved_s &&
              0 <= i && i <= Zlength(Znth(z, g, nil)) &&
              -1 <= last && last < 26 &&
              (forall k q,
                (0 <= k && k < n@pre &&
                 0 <= q && q < Zlength(Znth(k, g, nil))) =>
                  (97 <= Znth(q, Znth(k, g, nil), 0) &&
                   Znth(q, Znth(k, g, nil), 0) <= 122)) &&
              Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
              Zlength(used_l) == 26 && Zlength(seen_l) == 26 &&
              (forall k, (0 <= k && k < 26) =>
                (-1 <= Znth(k, next_l, -1) && Znth(k, next_l, -1) < 26)) &&
              (forall k, (0 <= k && k < 26) =>
                (-1 <= Znth(k, prev_l, -1) && Znth(k, prev_l, -1) < 26)) &&
              WordScanState(g, z, i, next_l, prev_l, used_l, seen_l, last) &&
              CharPtrArray2::missing_i(words@pre, n@pre, z, saved_s, rows) *
              data_at(words@pre + z * sizeof(char *), char *, saved_s) *
              CharArray::full(saved_s,
                              Zlength(Znth(z, g, nil)) + 1,
                              c_string(Znth(z, g, nil))) *
              CharArray::undef_full(out@pre, 64) *
              IntArray::full(next, 26, next_l) *
              IntArray::full(prev, 26, prev_l) *
              IntArray::full(used, 26, used_l) *
              IntArray::full(seen, 26, seen_l)
        */
        for (int i = 0; s[i]; ++i)
        {
            int c = s[i] - 'a';
            /*@ 0 <= c && c < 26 by local */
            used[c] = 1;
            if (seen[c])
                return 0;
            seen[c] = 1;
            if (last >= 0)
            {
                if ((next[last] >= 0 && next[last] != c) || (prev[c] >= 0 && prev[c] != last))
                    return 0;
                next[last] = c;
                prev[c] = last;
            }
            last = c;
        }
        /*@ Assert
            exists next_l prev_l used_l seen_l saved_s,
              words == words@pre && out == out@pre && n == n@pre &&
              n@pre == Zlength(g) &&
              1 <= n@pre && n@pre <= 100000 &&
              Zlength(rows) == n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (0 < Zlength(Znth(k, g, nil)) &&
                 Zlength(Znth(k, g, nil)) <= 100000 &&
                 Znth(k, rows, nil) == c_string(Znth(k, g, nil)) &&
                 valid_string(Znth(k, g, nil)) &&
              string_length(Znth(k, g, nil)) < INT_MAX)) &&
              (forall k q,
                (0 <= k && k < n@pre &&
                 0 <= q && q < Zlength(Znth(k, g, nil))) =>
                  (97 <= Znth(q, Znth(k, g, nil), 0) &&
                   Znth(q, Znth(k, g, nil), 0) <= 122)) &&
              0 <= z && z < n@pre &&
              s == saved_s && -1 <= last && last < 26 &&
              Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
              Zlength(used_l) == 26 && Zlength(seen_l) == 26 &&
              (forall k, (0 <= k && k < 26) =>
                (-1 <= Znth(k, next_l, -1) && Znth(k, next_l, -1) < 26)) &&
              (forall k, (0 <= k && k < 26) =>
                (-1 <= Znth(k, prev_l, -1) && Znth(k, prev_l, -1) < 26)) &&
              GraphBuildState(g, z + 1, next_l, prev_l, used_l) &&
              CharPtrArray2::full(words@pre, n@pre, rows) *
              CharArray::undef_full(out@pre, 64) *
              IntArray::full(next, 26, next_l) *
              IntArray::full(prev, 26, prev_l) *
              IntArray::full(used, 26, used_l) *
              IntArray::full(seen, 26, seen_l)
        */
    }
    int visited[26] = {0}, len = 0;
    /*@ Inv Assert
        exists next_l prev_l used_l visited_l output_l,
          words == words@pre && out == out@pre && n == n@pre &&
          n@pre == Zlength(g) &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(rows) == n@pre &&
          0 <= start && start <= 26 &&
          0 <= len && len <= 26 && Zlength(output_l) == len &&
          Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
          Zlength(used_l) == 26 && Zlength(visited_l) == 26 &&
          (forall k, (0 <= k && k < 26) =>
            (-1 <= Znth(k, next_l, -1) && Znth(k, next_l, -1) < 26)) &&
          (forall k, (0 <= k && k < 26) =>
            (-1 <= Znth(k, prev_l, -1) && Znth(k, prev_l, -1) < 26)) &&
          GraphBuildState(g, n@pre, next_l, prev_l, used_l) &&
          TraversalState(next_l, prev_l, used_l, start, visited_l, output_l) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          IntArray::full(next, 26, next_l) *
          IntArray::full(prev, 26, prev_l) *
          IntArray::full(used, 26, used_l) *
          IntArray::full(visited, 26, visited_l) *
          CharArray::seg(out@pre, 0, len, output_l) *
          CharArray::undef_seg(out@pre, len, 64)
    */
    for (int start = 0; start < 26; ++start)
        if (used[start] && prev[start] < 0)
        {
            int c = start;
            /*@ Inv Assert
                exists next_l prev_l used_l visited_l output_l,
                  words == words@pre && out == out@pre && n == n@pre &&
                  n@pre == Zlength(g) &&
                  1 <= n@pre && n@pre <= 100000 &&
                  Zlength(rows) == n@pre &&
                  0 <= start && start < 26 &&
                  -1 <= c && c < 26 &&
                  0 <= len && len <= 26 && Zlength(output_l) == len &&
                  Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
                  Zlength(used_l) == 26 && Zlength(visited_l) == 26 &&
                  (forall k, (0 <= k && k < 26) =>
                    (-1 <= Znth(k, next_l, -1) && Znth(k, next_l, -1) < 26)) &&
                  (forall k, (0 <= k && k < 26) =>
                    (-1 <= Znth(k, prev_l, -1) && Znth(k, prev_l, -1) < 26)) &&
                  GraphBuildState(g, n@pre, next_l, prev_l, used_l) &&
                  PathScanState(next_l, prev_l, used_l, start, c,
                                visited_l, output_l) &&
                  CharPtrArray2::full(words@pre, n@pre, rows) *
                  IntArray::full(next, 26, next_l) *
                  IntArray::full(prev, 26, prev_l) *
                  IntArray::full(used, 26, used_l) *
                  IntArray::full(visited, 26, visited_l) *
                  CharArray::seg(out@pre, 0, len, output_l) *
                  CharArray::undef_seg(out@pre, len, 64)
            */
            while (c >= 0 && !visited[c])
            {
                visited[c] = 1;
                out[len] = (char)('a' + c);
                ++len;
                c = next[c];
            }
            /*@ Assert
                exists next_l prev_l used_l visited_l output_l,
                  words == words@pre && out == out@pre && n == n@pre &&
                  n@pre == Zlength(g) &&
                  1 <= n@pre && n@pre <= 100000 &&
                  Zlength(rows) == n@pre &&
                  0 <= start && start < 26 &&
                  -1 <= c && c < 26 &&
                  0 <= len && len <= 26 && Zlength(output_l) == len &&
                  Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
                  Zlength(used_l) == 26 && Zlength(visited_l) == 26 &&
                  GraphBuildState(g, n@pre, next_l, prev_l, used_l) &&
                  TraversalState(next_l, prev_l, used_l, start + 1,
                                 visited_l, output_l) &&
                  CharPtrArray2::full(words@pre, n@pre, rows) *
                  IntArray::full(next, 26, next_l) *
                  IntArray::full(prev, 26, prev_l) *
                  IntArray::full(used, 26, used_l) *
                  IntArray::full(visited, 26, visited_l) *
                  CharArray::seg(out@pre, 0, len, output_l) *
                  CharArray::undef_seg(out@pre, len, 64)
            */
        }
    /*@ Inv Assert
        exists next_l prev_l used_l visited_l output_l,
          words == words@pre && out == out@pre && n == n@pre &&
          n@pre == Zlength(g) &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(rows) == n@pre &&
          0 <= c && c <= 26 &&
          0 <= len && len <= 26 && Zlength(output_l) == len &&
          Zlength(next_l) == 26 && Zlength(prev_l) == 26 &&
          Zlength(used_l) == 26 && Zlength(visited_l) == 26 &&
          (forall k, (0 <= k && k < 26) =>
            (-1 <= Znth(k, next_l, -1) && Znth(k, next_l, -1) < 26)) &&
          (forall k, (0 <= k && k < 26) =>
            (-1 <= Znth(k, prev_l, -1) && Znth(k, prev_l, -1) < 26)) &&
          GraphBuildState(g, n@pre, next_l, prev_l, used_l) &&
          TraversalState(next_l, prev_l, used_l, 26, visited_l, output_l) &&
          CoverageScanState(used_l, visited_l, c) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          IntArray::full(next, 26, next_l) *
          IntArray::full(prev, 26, prev_l) *
          IntArray::full(used, 26, used_l) *
          IntArray::full(visited, 26, visited_l) *
          CharArray::seg(out@pre, 0, len, output_l) *
          CharArray::undef_seg(out@pre, len, 64)
    */
    for (int c = 0; c < 26; ++c)
        if (used[c] && !visited[c])
            return 0;
    /*@ Assert
        exists next_l prev_l used_l visited_l output_l,
          words == words@pre && out == out@pre && n == n@pre &&
          n@pre == Zlength(g) &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(rows) == n@pre &&
          0 <= len && len <= 26 && Zlength(output_l) == len &&
          SuccessfulTraversal(g, next_l, prev_l, used_l, visited_l, output_l) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          IntArray::full(next, 26, next_l) *
          IntArray::full(prev, 26, prev_l) *
          IntArray::full(used, 26, used_l) *
          IntArray::full(visited, 26, visited_l) *
          CharArray::seg(out@pre, 0, len, output_l) *
          CharArray::undef_seg(out@pre, len, 64)
    */
    out[len] = '\0';
    return 1;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     char **words = malloc((size_t)n * sizeof(*words));
//     for (int i = 0; i < n; ++i)
//     {
//         words[i] = malloc(100005);
//         scanf("%100004s", words[i]);
//     }
//     char out[64];
//     if (solver(n, words, out))
//         puts(out);
//     else
//         puts("NO");
//     for (int i = 0; i < n; ++i)
//         free(words[i]);
//     free(words);
//     return 0;
// }
