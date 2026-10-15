/* Codeforces 1082/C - Multi-Subject Competition */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;
typedef struct
{
    int subject, skill;
} Candidate;

static int cmp_candidate(const void *x, const void *y)
{
    const Candidate *a = x, *b = y;
    if (a->subject != b->subject)
        return (a->subject > b->subject) - (a->subject < b->subject);
    return (b->skill > a->skill) - (b->skill < a->skill);
}

/* QCP_INSERT_BEGIN:P046_1082C_multi_subject_competition.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> list (Z*Z) -> Z -> Prop)
      (Permutation : list (Z * Z) -> list (Z * Z) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P046_1082C_multi_subject_competition_lib */
/* QCP_INSERT_END:P046_1082C_multi_subject_competition.support */
/*@ Extern Coq
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (CandidatesSorted : list (Z*Z) -> Prop)
      (CompetitionOuterState : list (Z*Z) -> Z -> list Z -> Prop)
      (CompetitionInnerState : list (Z*Z) -> Z -> Z -> Z -> list Z -> Prop)
      (CompetitionAnswerPrefix : list Z -> Z -> Z -> Z -> Prop)
*/

void *calloc(unsigned long nmemb, unsigned long size)
    /*@ calloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, cap, repeat_Z(0, cap))
*/
    ;

void qsort(Candidate *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *))
    /*@ qsort_candidates
    With (contents : list (Z*Z)) (raw_contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      Zlength(raw_contents) == 2 * nmemb &&
      (forall i, (0 <= i && i < nmemb) =>
        (raw_contents[2 * i] == fst(contents[i]) &&
         raw_contents[2 * i + 1] == snd(contents[i]))) &&
      IntArray::full(base, 2 * nmemb, raw_contents)
    Ensure
      exists sorted raw_sorted,
        Permutation(contents, sorted) &&
        CandidatesSorted(sorted) &&
        Zlength(sorted) == nmemb &&
        Zlength(raw_sorted) == 2 * nmemb &&
        (forall i, (0 <= i && i < nmemb) =>
          (raw_sorted[2 * i] == fst(sorted[i]) &&
           raw_sorted[2 * i + 1] == snd(sorted[i]))) &&
        IntArray::full(base, 2 * nmemb, raw_sorted)
*/
    ;

void free(void *ptr)
    /*@ free_int64
    Require exists values cap,
      Int64Array::full(ptr, cap, values)
    Ensure emp
*/
    ;

static long long solver(Candidate *a, int n,
                        int m) /* QCP_INSERT_BEGIN:P046_1082C_multi_subject_competition.contract */

/*@ With (students : list (Z*Z))
             (raw : list Z)
    Require
      1 <= Zlength(students) && Zlength(students) <= 100000 &&
      1 <= m && m <= 100000 &&
      (forall i, (0 <= i && i < Zlength(students)) => ((1 <= fst(students[i]) && fst(students[i]) <= m) && (-10000 <= snd(students[i]) && snd(students[i]) <= 10000))) &&
      n == Zlength(students) && Zlength(raw) == 2 * n &&
      (forall i, (0 <= i && i < n) =>
        (raw[2 * i] == fst(students[i]) &&
         raw[2 * i + 1] == snd(students[i]))) &&
      IntArray::full(a, 2 * n, raw)
    Ensure
      exists students_after raw_after,
        Spec(m, students, __return) &&
        Permutation(students, students_after) &&
        Zlength(raw_after) == 2 * n &&
        (forall i, (0 <= i && i < n) =>
          (raw_after[2 * i] == fst(students_after[i]) &&
           raw_after[2 * i + 1] == snd(students_after[i]))) &&
        IntArray::full(a, 2 * n, raw_after)
*/
/* QCP_INSERT_END:P046_1082C_multi_subject_competition.contract */

{
    (void)m;
    long long *total = calloc((size_t)n + 1, sizeof(*total))
        /*@ where (calloc_int64) cap = n + 1 */;
    qsort(a, (size_t)n, sizeof(*a), cmp_candidate)
        /*@ where (qsort_candidates) contents = students, raw_contents = raw */;
    /*@ Inv Assert
        exists sorted raw_sorted totals,
          a == a@pre && n == n@pre && m == m@pre && total != 0 &&
          n@pre == Zlength(students) && Zlength(raw) == 2 * n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          (forall k, (0 <= k && k < n@pre) =>
            ((1 <= fst(students[k]) && fst(students[k]) <= m@pre) &&
             (-10000 <= snd(students[k]) && snd(students[k]) <= 10000))) &&
          Permutation(students, sorted) && CandidatesSorted(sorted) &&
          Zlength(sorted) == n@pre && Zlength(raw_sorted) == 2 * n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (raw_sorted[2 * k] == fst(sorted[k]) &&
             raw_sorted[2 * k + 1] == snd(sorted[k]))) &&
          (forall k, (0 <= k && k < n@pre) =>
            ((1 <= fst(sorted[k]) && fst(sorted[k]) <= m@pre) &&
             (-10000 <= snd(sorted[k]) && snd(sorted[k]) <= 10000))) &&
          0 <= i && i <= n@pre &&
          CompetitionOuterState(sorted, i, totals) &&
          (forall k, (0 <= k && k <= n@pre) =>
            (0 <= totals[k] && totals[k] <= i * 10000)) &&
          IntArray::full(a@pre, 2 * n@pre, raw_sorted) *
          Int64Array::full(total, n@pre + 1, totals)
    */
    for (int i = 0; i < n;)
    {
        int j = i;
        long long prefix = 0;
        /*@ Inv Assert
            exists sorted raw_sorted totals,
              a == a@pre && n == n@pre && m == m@pre && total != 0 &&
              n@pre == Zlength(students) && Zlength(raw) == 2 * n@pre &&
              1 <= n@pre && n@pre <= 100000 &&
              1 <= m@pre && m@pre <= 100000 &&
              (forall k, (0 <= k && k < n@pre) =>
                ((1 <= fst(students[k]) && fst(students[k]) <= m@pre) &&
                 (-10000 <= snd(students[k]) && snd(students[k]) <= 10000))) &&
              Permutation(students, sorted) && CandidatesSorted(sorted) &&
              Zlength(sorted) == n@pre && Zlength(raw_sorted) == 2 * n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (raw_sorted[2 * k] == fst(sorted[k]) &&
                 raw_sorted[2 * k + 1] == snd(sorted[k]))) &&
              (forall k, (0 <= k && k < n@pre) =>
                ((1 <= fst(sorted[k]) && fst(sorted[k]) <= m@pre) &&
                 (-10000 <= snd(sorted[k]) && snd(sorted[k]) <= 10000))) &&
              0 <= i && i < n@pre && i <= j && j <= n@pre &&
              -10000 * (j - i) <= prefix && prefix <= 10000 * (j - i) &&
              CompetitionInnerState(sorted, i, j, prefix, totals) &&
              (forall k, (0 <= k && k <= n@pre) =>
                (0 <= totals[k] && totals[k] <= j * 10000)) &&
              (forall k, (j - i < k && k <= n@pre) =>
                totals[k] <= i * 10000) &&
              IntArray::full(a@pre, 2 * n@pre, raw_sorted) *
              Int64Array::full(total, n@pre + 1, totals)
        */
        while (j < n && ((int *)a)[2 * j] == ((int *)a)[2 * i])
        {
            prefix += ((int *)a)[2 * j + 1];
            ++j;
            if (prefix > 0)
                total[j - i] += prefix;
        }
        i = j;
    }
    long long answer = 0;
    /*@ Inv Assert
        exists sorted raw_sorted totals,
          a == a@pre && n == n@pre && m == m@pre && total != 0 &&
          n@pre == Zlength(students) && Zlength(raw) == 2 * n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          (forall p, (0 <= p && p < n@pre) =>
            ((1 <= fst(students[p]) && fst(students[p]) <= m@pre) &&
             (-10000 <= snd(students[p]) && snd(students[p]) <= 10000))) &&
          Permutation(students, sorted) && CandidatesSorted(sorted) &&
          Zlength(sorted) == n@pre && Zlength(raw_sorted) == 2 * n@pre &&
          (forall p, (0 <= p && p < n@pre) =>
            (raw_sorted[2 * p] == fst(sorted[p]) &&
             raw_sorted[2 * p + 1] == snd(sorted[p]))) &&
          (forall p, (0 <= p && p < n@pre) =>
            ((1 <= fst(sorted[p]) && fst(sorted[p]) <= m@pre) &&
             (-10000 <= snd(sorted[p]) && snd(sorted[p]) <= 10000))) &&
          1 <= k && k <= n@pre + 1 &&
          0 <= answer && answer <= n@pre * 10000 &&
          CompetitionOuterState(sorted, n@pre, totals) &&
          CompetitionAnswerPrefix(totals, n@pre, k - 1, answer) &&
          (forall p, (0 <= p && p <= n@pre) =>
            (0 <= totals[p] && totals[p] <= n@pre * 10000)) &&
          IntArray::full(a@pre, 2 * n@pre, raw_sorted) *
          Int64Array::full(total, n@pre + 1, totals)
    */
    for (int k = 1; k <= n; ++k)
        if (total[k] > answer)
            answer = total[k];
    free(total) /*@ where (free_int64) */;
    return answer;
}

// int main(void)
// {
//     int n, m; if (scanf("%d %d", &n, &m) != 2) return 0;
//     Candidate *a = malloc((size_t)n * sizeof(*a));
//     for (int i = 0; i < n; ++i) scanf("%d %d", &a[i].subject, &a[i].skill);
//     printf("%lld\n", solver(a, n, m)); free(a);
//     return 0;
// }
