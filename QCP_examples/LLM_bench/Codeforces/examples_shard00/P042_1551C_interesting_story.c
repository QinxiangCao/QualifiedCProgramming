/* Codeforces 1551/C - Interesting Story */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"

static int cmp_desc(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (b > a) - (b < a);
}

/* QCP_INSERT_BEGIN:P042_1551C_interesting_story.support */
/*@ Extern Coq
      (Spec : list (list Z) -> Z -> Prop)
      (CharPtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P042_1551C_interesting_story_lib */
/*@ Extern Coq
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (CharPtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (decreasing : list Z -> Prop)
*/
/*@ Extern Coq
      (ScoreBuildState : list (list Z) -> Z -> list (option Z) -> Prop)
      (TotalLength : list (list Z) -> Z)
      (ScoreRowState : list (list Z) -> Z -> Z -> list (option Z) -> Prop)
      (CountPrefixState : list Z -> Z -> list Z -> Prop)
      (ScoreTable : list (list Z) -> list Z -> Prop)
      (PreparedScoreTable : list (list Z) -> Z -> list Z -> Prop)
      (PositivePrefixState : list Z -> Z -> Z -> Prop)
      (LetterBest : list (list Z) -> Z -> Z -> Prop)
      (AnswerState : list (list Z) -> Z -> Z -> Prop)
*/
/*@ include strategies "ptr_array2.strategies" */
/* QCP_INSERT_END:P042_1551C_interesting_story.support */

void *malloc(unsigned long size)
    /*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      size == cap * sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::undef_full(__return, cap)
*/
    ;

void qsort(int *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
    /*@ With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      size == sizeof(int) &&
      IntArray::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        decreasing(sorted) &&
        Zlength(sorted) == nmemb &&
        IntArray::full(base, nmemb, sorted)
*/
    ;

void free(void *ptr)
    /*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/
    ;

static int solver(char *const *words,
                  int n) /* QCP_INSERT_BEGIN:P042_1551C_interesting_story.contract */

/*@ With (words_data rows : list (list Z))
    Require
      1 <= Zlength(words_data) && Zlength(words_data) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(words_data)) =>
        0 < Zlength(words_data[i])) &&
      (forall i j,
        (0 <= i && i < Zlength(words_data) &&
         0 <= j && j < Zlength(words_data[i])) =>
          (97 <= Znth(j, Znth(i, words_data, nil), 0) &&
           Znth(j, Znth(i, words_data, nil), 0) <= 101)) &&
      TotalLength(words_data) <= 200000 &&
      n == Zlength(words_data) &&
      Zlength(rows) == n &&
      (forall i, (0 <= i && i < n) =>
        (Znth(i, rows, nil) == c_string(Znth(i, words_data, nil)) &&
         valid_string(Znth(i, words_data, nil)) &&
         string_length(Znth(i, words_data, nil)) < INT_MAX)) &&
      CharPtrArray2::full(words, n, rows)
    Ensure
      Spec(words_data, __return) &&
      CharPtrArray2::full(words, n, rows)
*/
/* QCP_INSERT_END:P042_1551C_interesting_story.contract */

{
    int *score = malloc(5 * n * sizeof(*score))
        /*@ where (malloc_int) cap = 5 * n */;
    /*@ Inv Assert
        exists score_mem,
          words == words@pre && n == n@pre &&
          n@pre == Zlength(words_data) &&
          1 <= n@pre && n@pre <= 200000 &&
          TotalLength(words_data) <= 200000 &&
          (forall k q, (0 <= k && k < n@pre &&
                        0 <= q && q < Zlength(Znth(k, words_data, nil))) =>
            (97 <= Znth(q, Znth(k, words_data, nil), 0) &&
             Znth(q, Znth(k, words_data, nil), 0) <= 101)) &&
          Zlength(rows) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (Znth(k, rows, nil) == c_string(Znth(k, words_data, nil)) &&
             valid_string(Znth(k, words_data, nil)) &&
             string_length(Znth(k, words_data, nil)) < INT_MAX)) &&
          0 <= i && i <= n@pre &&
          Zlength(score_mem) == 5 * n@pre &&
          ScoreBuildState(words_data, i, score_mem) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          IntArray::mixed_full(score, 5 * n@pre, score_mem)
    */
    for (int i = 0; i < n; ++i)
    {
        /*@ Assert
            exists score_mem row_ptr,
              words == words@pre && n == n@pre &&
              n@pre == Zlength(words_data) &&
              1 <= n@pre && n@pre <= 200000 &&
              TotalLength(words_data) <= 200000 &&
              (forall k q, (0 <= k && k < n@pre &&
                            0 <= q && q < Zlength(Znth(k, words_data, nil))) =>
                (97 <= Znth(q, Znth(k, words_data, nil), 0) &&
                 Znth(q, Znth(k, words_data, nil), 0) <= 101)) &&
              Zlength(rows) == n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (Znth(k, rows, nil) == c_string(Znth(k, words_data, nil)) &&
                 valid_string(Znth(k, words_data, nil)) &&
                 string_length(Znth(k, words_data, nil)) < INT_MAX)) &&
              0 <= i && i < n@pre &&
              Zlength(score_mem) == 5 * n@pre &&
              ScoreBuildState(words_data, i, score_mem) &&
              CharPtrArray2::missing_i(words@pre, n@pre, i, row_ptr, rows) *
              data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
              CharArray::full(row_ptr,
                              string_length(Znth(i, words_data, nil)) + 1,
                              c_string(Znth(i, words_data, nil))) *
              IntArray::mixed_full(score, 5 * n@pre, score_mem)
        */
        int len = (int)strlen(words[i])
            /*@ where str = Znth(i, words_data, nil) */,
            cnt[5] = {0};
        /*@ Inv Assert
            exists score_mem cnt_data row_ptr,
              words == words@pre && n == n@pre &&
              n@pre == Zlength(words_data) &&
              1 <= n@pre && n@pre <= 200000 &&
              TotalLength(words_data) <= 200000 &&
              (forall k q, (0 <= k && k < n@pre &&
                            0 <= q && q < Zlength(Znth(k, words_data, nil))) =>
                (97 <= Znth(q, Znth(k, words_data, nil), 0) &&
                 Znth(q, Znth(k, words_data, nil), 0) <= 101)) &&
              Zlength(rows) == n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (Znth(k, rows, nil) == c_string(Znth(k, words_data, nil)) &&
                 valid_string(Znth(k, words_data, nil)) &&
                 string_length(Znth(k, words_data, nil)) < INT_MAX)) &&
              0 <= i && i < n@pre &&
              len == Zlength(Znth(i, words_data, nil)) &&
              (forall q, (0 <= q && q < len) =>
                (97 <= Znth(q, c_string(Znth(i, words_data, nil)), 0) &&
                 Znth(q, c_string(Znth(i, words_data, nil)), 0) <= 101)) &&
              0 <= j && j <= len &&
              Zlength(score_mem) == 5 * n@pre &&
              Zlength(cnt_data) == 5 &&
              ScoreBuildState(words_data, i, score_mem) &&
              CountPrefixState(Znth(i, words_data, nil), j, cnt_data) &&
              CharPtrArray2::missing_i(words@pre, n@pre, i, row_ptr, rows) *
              data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
              CharArray::full(row_ptr, len + 1,
                              c_string(Znth(i, words_data, nil))) *
              IntArray::mixed_full(score, 5 * n@pre, score_mem) *
              IntArray::full(cnt, 5, cnt_data)
        */
        for (int j = 0; j < len; ++j)
        {
            /*@ 0 <= Znth(j, c_string(Znth(i, words_data, nil)), 0) - 97 &&
                Znth(j, c_string(Znth(i, words_data, nil)), 0) - 97 < 5
                by local */
            ++cnt[words[i][j] - 'a'];
        }
        /*@ Inv Assert
            exists score_mem cnt_data row_ptr,
              words == words@pre && n == n@pre &&
              n@pre == Zlength(words_data) &&
              1 <= n@pre && n@pre <= 200000 &&
              TotalLength(words_data) <= 200000 &&
              (forall k q, (0 <= k && k < n@pre &&
                            0 <= q && q < Zlength(Znth(k, words_data, nil))) =>
                (97 <= Znth(q, Znth(k, words_data, nil), 0) &&
                 Znth(q, Znth(k, words_data, nil), 0) <= 101)) &&
              Zlength(rows) == n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (Znth(k, rows, nil) == c_string(Znth(k, words_data, nil)) &&
                 valid_string(Znth(k, words_data, nil)) &&
                 string_length(Znth(k, words_data, nil)) < INT_MAX)) &&
              0 <= i && i < n@pre &&
              len == Zlength(Znth(i, words_data, nil)) &&
              0 <= c && c <= 5 &&
              Zlength(score_mem) == 5 * n@pre &&
              Zlength(cnt_data) == 5 &&
              ScoreRowState(words_data, i, c, score_mem) &&
              CountPrefixState(Znth(i, words_data, nil), len, cnt_data) &&
              CharPtrArray2::missing_i(words@pre, n@pre, i, row_ptr, rows) *
              data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
              CharArray::full(row_ptr, len + 1,
                              c_string(Znth(i, words_data, nil))) *
              IntArray::mixed_full(score, 5 * n@pre, score_mem) *
              IntArray::full(cnt, 5, cnt_data)
        */
        for (int c = 0; c < 5; ++c)
        {
            /*@ 0 <= c * n + i && c * n + i < 5 * n by local */
            score[c * n + i] = 2 * cnt[c] - len;
        }
    }
    /*@ Assert
        exists scores,
          words == words@pre && n == n@pre &&
          n@pre == Zlength(words_data) &&
          1 <= n@pre && n@pre <= 200000 &&
          TotalLength(words_data) <= 200000 &&
          Zlength(rows) == n@pre &&
          Zlength(scores) == 5 * n@pre &&
          ScoreTable(words_data, scores) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          IntArray::full(score, 5 * n@pre, scores)
    */
    int answer = 0;
    /*@ Inv Assert
        exists scores,
          words == words@pre && n == n@pre &&
          n@pre == Zlength(words_data) &&
          1 <= n@pre && n@pre <= 200000 &&
          TotalLength(words_data) <= 200000 &&
          Zlength(rows) == n@pre &&
          0 <= c && c <= 5 &&
          0 <= answer && answer <= n@pre &&
          Zlength(scores) == 5 * n@pre &&
          PreparedScoreTable(words_data, c, scores) &&
          AnswerState(words_data, c, answer) &&
          (forall p, (0 <= p && p < 5 * n@pre) =>
            (-200000 <= Znth(p, scores, 0) &&
             Znth(p, scores, 0) <= 200000)) &&
          CharPtrArray2::full(words@pre, n@pre, rows) *
          IntArray::full(score, 5 * n@pre, scores)
    */
    for (int c = 0; c < 5; ++c)
    {
        /*@ Assert
            exists before block after,
              words == words@pre && n == n@pre &&
              n@pre == Zlength(words_data) &&
              1 <= n@pre && n@pre <= 200000 &&
              TotalLength(words_data) <= 200000 &&
              Zlength(rows) == n@pre &&
              0 <= c && c < 5 &&
              0 <= answer && answer <= n@pre &&
              PreparedScoreTable(words_data, c, app(before, app(block, after))) &&
              AnswerState(words_data, c, answer) &&
              Zlength(before) == c * n@pre &&
              Zlength(block) == n@pre &&
              Zlength(after) == (5 - c - 1) * n@pre &&
              (forall p, (0 <= p && p < Zlength(block)) =>
                (-200000 <= Znth(p, block, 0) &&
                 Znth(p, block, 0) <= 200000)) &&
              CharPtrArray2::full(words@pre, n@pre, rows) *
              IntArray::seg(score, 0, c * n@pre, before) *
              IntArray::full(score + c * n@pre, n@pre, block) *
              IntArray::seg(score, (c + 1) * n@pre, 5 * n@pre, after)
        */
        qsort(score + c * n, n, sizeof(*score), cmp_desc);
        /*@ Assert
            exists scores,
              words == words@pre && n == n@pre &&
              n@pre == Zlength(words_data) &&
              1 <= n@pre && n@pre <= 200000 &&
              TotalLength(words_data) <= 200000 &&
              Zlength(rows) == n@pre &&
              0 <= c && c < 5 &&
              0 <= answer && answer <= n@pre &&
              Zlength(scores) == 5 * n@pre &&
              PreparedScoreTable(words_data, c + 1, scores) &&
              AnswerState(words_data, c, answer) &&
              decreasing(sublist(c * n@pre, (c + 1) * n@pre, scores)) &&
              (forall p, (0 <= p && p < 5 * n@pre) =>
                (-200000 <= Znth(p, scores, 0) &&
                 Znth(p, scores, 0) <= 200000)) &&
              CharPtrArray2::full(words@pre, n@pre, rows) *
              IntArray::full(score, 5 * n@pre, scores)
        */
        int sum = 0, take = 0;
        /*@ Inv Assert
            exists scores,
              words == words@pre && n == n@pre &&
              n@pre == Zlength(words_data) &&
              1 <= n@pre && n@pre <= 200000 &&
              TotalLength(words_data) <= 200000 &&
              Zlength(rows) == n@pre &&
              0 <= c && c < 5 &&
              0 <= answer && answer <= n@pre &&
              Zlength(scores) == 5 * n@pre &&
              PreparedScoreTable(words_data, c + 1, scores) &&
              AnswerState(words_data, c, answer) &&
              decreasing(sublist(c * n@pre, (c + 1) * n@pre, scores)) &&
              (forall p, (0 <= p && p < 5 * n@pre) =>
                (-200000 <= Znth(p, scores, 0) &&
                 Znth(p, scores, 0) <= 200000)) &&
              0 <= take && take <= n@pre &&
              0 <= c * n@pre + take &&
              (take < n@pre => c * n@pre + take < 5 * n@pre) &&
              0 <= sum && sum <= 200000 &&
              PositivePrefixState(
                sublist(c * n@pre, (c + 1) * n@pre, scores), take, sum) &&
              CharPtrArray2::full(words@pre, n@pre, rows) *
              IntArray::full(score, 5 * n@pre, scores)
        */
        while (take < n && sum + score[c * n + take] > 0)
        {
            sum += score[c * n + take];
            ++take;
        }
        /*@ Assert
            exists scores,
              words == words@pre && n == n@pre &&
              n@pre == Zlength(words_data) &&
              1 <= n@pre && n@pre <= 200000 &&
              TotalLength(words_data) <= 200000 &&
              Zlength(rows) == n@pre &&
              0 <= c && c < 5 &&
              0 <= answer && answer <= n@pre &&
              0 <= take && take <= n@pre &&
              0 <= sum && sum <= 200000 &&
              Zlength(scores) == 5 * n@pre &&
              PreparedScoreTable(words_data, c + 1, scores) &&
              AnswerState(words_data, c, answer) &&
              PositivePrefixState(
                sublist(c * n@pre, (c + 1) * n@pre, scores), take, sum) &&
              LetterBest(words_data, 97 + c, take) &&
              CharPtrArray2::full(words@pre, n@pre, rows) *
              IntArray::full(score, 5 * n@pre, scores)
        */
        if (take > answer)
            answer = take;
    }
    free(score) /*@ where (free_int) */;
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); char **words = malloc((size_t)n * sizeof(*words));
//         for (int i = 0; i < n; ++i) { words[i] = malloc(200005); scanf("%200004s", words[i]); }
//         printf("%d\n", solver(words, n));
//         for (int i = 0; i < n; ++i) free(words[i]); free(words);
//     }
//     return 0;
// }
