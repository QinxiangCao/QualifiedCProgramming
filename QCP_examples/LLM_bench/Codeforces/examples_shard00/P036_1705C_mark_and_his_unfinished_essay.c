/* Codeforces 1705/C - Mark and His Unfinished Essay */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"

/* QCP_INSERT_BEGIN:P036_1705C_mark_and_his_unfinished_essay.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : list Z -> list (Z * Z) -> list Z -> Prop)
      (Spec : list Z -> list (Z * Z) -> list Z -> list Z -> Prop)
      (store_string : Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P036_1705C_mark_and_his_unfinished_essay_lib */
/* QCP_INSERT_END:P036_1705C_mark_and_his_unfinished_essay.support */
/*@ Extern Coq
      (Z::pow : Z -> Z -> Z)
      (CopyPasteStates : list Z -> list (Z * Z) -> list (list Z) -> Prop)
      (StateLengthsPrefix : list (list Z) -> Z -> list Z -> Prop)
      (BacktrackedPosition : list (list Z) -> Z -> Z -> Z -> Prop)
      (AnswerPrefix : list Z -> list (Z * Z) -> list Z -> Z -> list Z -> Prop)
      (FinalCharacter : list Z -> list (Z * Z) -> Z -> Z -> Prop)
*/
static void
solver(const char *s, int c, const long long *l, const long long *r, int q,
       const long long *queries,
       char *answers) /* QCP_INSERT_BEGIN:P036_1705C_mark_and_his_unfinished_essay.contract */

/*@ With (text : list Z)
             (ops : list (Z * Z))
             (queries_data : list Z)
             (lefts rights : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 200000 &&
      1 <= Zlength(ops) && Zlength(ops) <= 40 &&
      1 <= Zlength(queries_data) && Zlength(queries_data) <= 10000 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      Pre(text, ops, queries_data) &&
      c == Zlength(ops) && q == Zlength(queries_data) &&
      Zlength(lefts) == c && Zlength(rights) == c &&
      (forall i, (0 <= i && i < c) =>
        (fst(ops[i]) == lefts[i] &&
         snd(ops[i]) == rights[i])) &&
      store_string(s, text) *
      Int64Array::full(l, c, lefts) *
      Int64Array::full(r, c, rights) *
      Int64Array::full(queries, q, queries_data) *
      CharArray::undef_full(answers, q)
    Ensure
      exists out,
        Spec(text, ops, queries_data, out) &&
        store_string(s, text) *
        Int64Array::full(l, c, lefts) *
        Int64Array::full(r, c, rights) *
        Int64Array::full(queries, q, queries_data) *
        CharArray::full(answers, q, out)
*/
/* QCP_INSERT_END:P036_1705C_mark_and_his_unfinished_essay.contract */

{
    long long before[40], length = (long long)strlen(s) /*@ where str = text */;
    /*@ Inv Assert
          exists (states : list (list Z)) (before_data : list Z),
          s == s@pre && c == c@pre && l == l@pre && r == r@pre &&
          q == q@pre && queries == queries@pre && answers == answers@pre &&
          1 <= Zlength(text) && Zlength(text) <= 200000 &&
          1 <= Zlength(ops) && Zlength(ops) <= 40 &&
          1 <= Zlength(queries_data) && Zlength(queries_data) <= 10000 &&
          (forall j, (0 <= j && j < Zlength(text)) =>
             (97 <= text[j] && text[j] <= 122)) &&
          Pre(text, ops, queries_data) && CopyPasteStates(text, ops, states) &&
          c@pre == Zlength(ops) && q@pre == Zlength(queries_data) &&
          Zlength(lefts) == c@pre && Zlength(rights) == c@pre &&
          (forall j, (0 <= j && j < c@pre) =>
             (fst(ops[j]) == lefts[j] && snd(ops[j]) == rights[j])) &&
          0 <= i && i <= c@pre &&
          length == Zlength(states[i]) &&
          1 <= length && length <= 200000 * Z::pow(2, 40) &&
          StateLengthsPrefix(states, i, before_data) &&
          store_string(s@pre, text) *
          Int64Array::full(l@pre, c@pre, lefts) *
          Int64Array::full(r@pre, c@pre, rights) *
          Int64Array::full(queries@pre, q@pre, queries_data) *
          CharArray::undef_full(answers@pre, q@pre) *
          Int64Array::seg(before, 0, i, before_data) *
          Int64Array::undef_seg(before, i, 40)
    */
    for (int i = 0; i < c; ++i)
    {
        before[i] = length;
        length += r[i] - l[i] + 1;
    }
    /*@ Inv Assert
          exists (states : list (list Z)) (before_data : list Z)
                 (out : list Z),
          s == s@pre && c == c@pre && l == l@pre && r == r@pre &&
          q == q@pre && queries == queries@pre && answers == answers@pre &&
          1 <= Zlength(text) && Zlength(text) <= 200000 &&
          1 <= Zlength(ops) && Zlength(ops) <= 40 &&
          1 <= Zlength(queries_data) && Zlength(queries_data) <= 10000 &&
          (forall j, (0 <= j && j < Zlength(text)) =>
             (97 <= text[j] && text[j] <= 122)) &&
          Pre(text, ops, queries_data) && CopyPasteStates(text, ops, states) &&
          c@pre == Zlength(ops) && q@pre == Zlength(queries_data) &&
          Zlength(lefts) == c@pre && Zlength(rights) == c@pre &&
          (forall j, (0 <= j && j < c@pre) =>
             (fst(ops[j]) == lefts[j] && snd(ops[j]) == rights[j])) &&
          StateLengthsPrefix(states, c@pre, before_data) &&
          length == Zlength(states[c@pre]) &&
          0 <= z && z <= q@pre && AnswerPrefix(text, ops, queries_data, z, out) &&
          store_string(s@pre, text) *
          Int64Array::full(l@pre, c@pre, lefts) *
          Int64Array::full(r@pre, c@pre, rights) *
          Int64Array::full(queries@pre, q@pre, queries_data) *
          CharArray::seg(answers@pre, 0, z, out) *
          CharArray::undef_seg(answers@pre, z, q@pre) *
          Int64Array::seg(before, 0, c@pre, before_data) *
          Int64Array::undef_seg(before, c@pre, 40)
    */
    for (int z = 0; z < q; ++z)
    {
        long long k = queries[z];
        /*@ Inv Assert
              exists (states : list (list Z)) (before_data : list Z)
                     (out : list Z),
              s == s@pre && c == c@pre && l == l@pre && r == r@pre &&
              q == q@pre && queries == queries@pre && answers == answers@pre &&
              1 <= Zlength(text) && Zlength(text) <= 200000 &&
              1 <= Zlength(ops) && Zlength(ops) <= 40 &&
              1 <= Zlength(queries_data) && Zlength(queries_data) <= 10000 &&
              (forall j, (0 <= j && j < Zlength(text)) =>
                 (97 <= text[j] && text[j] <= 122)) &&
              Pre(text, ops, queries_data) && CopyPasteStates(text, ops, states) &&
              c@pre == Zlength(ops) && q@pre == Zlength(queries_data) &&
              Zlength(lefts) == c@pre && Zlength(rights) == c@pre &&
              (forall j, (0 <= j && j < c@pre) =>
                 (fst(ops[j]) == lefts[j] && snd(ops[j]) == rights[j])) &&
              StateLengthsPrefix(states, c@pre, before_data) &&
              length == Zlength(states[c@pre]) &&
              0 <= z && z < q@pre && AnswerPrefix(text, ops, queries_data, z, out) &&
              -1 <= i && i < c@pre &&
              BacktrackedPosition(states, queries_data[z], i, k) &&
              1 <= k && k <= 200000 * Z::pow(2, 40) &&
              store_string(s@pre, text) *
              Int64Array::full(l@pre, c@pre, lefts) *
              Int64Array::full(r@pre, c@pre, rights) *
              Int64Array::full(queries@pre, q@pre, queries_data) *
              CharArray::seg(answers@pre, 0, z, out) *
              CharArray::undef_seg(answers@pre, z, q@pre) *
              Int64Array::seg(before, 0, c@pre, before_data) *
              Int64Array::undef_seg(before, c@pre, 40)
        */
        for (int i = c - 1; i >= 0; --i)
            if (k > before[i])
                k = l[i] + k - before[i] - 1;
        /*@ Assert
              exists (states : list (list Z)) (before_data : list Z)
                     (out : list Z),
              s == s@pre && c == c@pre && l == l@pre && r == r@pre &&
              q == q@pre && queries == queries@pre && answers == answers@pre &&
              1 <= Zlength(text) && Zlength(text) <= 200000 &&
              1 <= Zlength(ops) && Zlength(ops) <= 40 &&
              1 <= Zlength(queries_data) && Zlength(queries_data) <= 10000 &&
              (forall j, (0 <= j && j < Zlength(text)) =>
                 (97 <= text[j] && text[j] <= 122)) &&
              Pre(text, ops, queries_data) && CopyPasteStates(text, ops, states) &&
              c@pre == Zlength(ops) && q@pre == Zlength(queries_data) &&
              Zlength(lefts) == c@pre && Zlength(rights) == c@pre &&
              (forall j, (0 <= j && j < c@pre) =>
                 (fst(ops[j]) == lefts[j] && snd(ops[j]) == rights[j])) &&
              StateLengthsPrefix(states, c@pre, before_data) &&
              length == Zlength(states[c@pre]) &&
              0 <= z && z < q@pre && AnswerPrefix(text, ops, queries_data, z, out) &&
              1 <= k && k <= Zlength(text) &&
              FinalCharacter(text, ops, queries_data[z], text[k - 1]) &&
              store_string(s@pre, text) *
              Int64Array::full(l@pre, c@pre, lefts) *
              Int64Array::full(r@pre, c@pre, rights) *
              Int64Array::full(queries@pre, q@pre, queries_data) *
              CharArray::seg(answers@pre, 0, z, out) *
              CharArray::undef_seg(answers@pre, z, q@pre) *
              Int64Array::seg(before, 0, c@pre, before_data) *
              Int64Array::undef_seg(before, c@pre, 40)
        */
        answers[z] = s[k - 1];
    }
    /*@ Assert
          exists (states : list (list Z)) (out : list Z),
          s == s@pre && c == c@pre && l == l@pre && r == r@pre &&
          q == q@pre && queries == queries@pre && answers == answers@pre &&
          CopyPasteStates(text, ops, states) &&
          length == Zlength(states[c@pre]) &&
          Spec(text, ops, queries_data, out) &&
          store_string(s@pre, text) *
          Int64Array::full(l@pre, c@pre, lefts) *
          Int64Array::full(r@pre, c@pre, rights) *
          Int64Array::full(queries@pre, q@pre, queries_data) *
          CharArray::full(answers@pre, q@pre, out) *
          Int64Array::undef_full(before, 40)
    */
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, c, q; scanf("%d %d %d", &n, &c, &q);
//         char *s = malloc((size_t)n + 1); scanf("%s", s);
//         long long l[40], r[40];
//         for (int i = 0; i < c; ++i) {
//             scanf("%lld %lld", &l[i], &r[i]);
//         }
//         long long *queries = malloc((size_t)q * sizeof(*queries)); char *answers = malloc((size_t)q);
//         for (int i = 0; i < q; ++i) scanf("%lld", &queries[i]);
//         solver(s, c, l, r, q, queries, answers);
//         for (int i = 0; i < q; ++i) printf("%c\n", answers[i]);
//         free(answers); free(queries);
//         free(s);
//     }
//     return 0;
// }
