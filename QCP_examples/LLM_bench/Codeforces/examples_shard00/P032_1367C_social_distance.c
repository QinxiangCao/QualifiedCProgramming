/* Codeforces 1367/C - Social Distance */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/* QCP_INSERT_BEGIN:P032_1367C_social_distance.support */
/*@ Extern Coq
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P032_1367C_social_distance_lib */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (RightNearest : list Z -> Z -> Z -> Z -> Prop)
      (RightNearestSuffix : list Z -> Z -> Z -> list Z -> Prop)
      (PrefixPlacementState : list Z -> Z -> Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P032_1367C_social_distance.support */

void *malloc(size_t size)
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

void free(void *ptr)
    /*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/
    ;

static int solver(char *s, int n, int k) /* QCP_INSERT_BEGIN:P032_1367C_social_distance.contract */

/*@ With (seats : list Z)
    Require
      n == Zlength(seats) &&
      1 <= k && k <= Zlength(seats) && Zlength(seats) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(seats)) =>
        (seats[i] == 48 || seats[i] == 49)) &&
      Pre(k, seats) &&
      CharArray::full(s, n + 1, app(seats, cons(0, nil)))
    Ensure
      Spec(k, seats, __return) &&
      CharArray::full(s, n + 1, app(seats, cons(0, nil)))
*/
/* QCP_INSERT_END:P032_1367C_social_distance.contract */

{
    int answer = 0, last = -k - 1;
    int *next = malloc((size_t)n * sizeof(*next))
        /*@ where (malloc_int) cap = n */;
    int nearest = n + k;
    /*@ Inv Assert
          exists suffix,
            s == s@pre && n == n@pre && k == k@pre &&
            n@pre == Zlength(seats) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
            (forall j, (0 <= j && j < n@pre) =>
              (seats[j] == 48 || seats[j] == 49)) &&
            Pre(k@pre, seats) &&
            answer == 0 && last == -k@pre - 1 &&
            -1 <= i && i < n@pre &&
            i + 1 <= nearest && nearest <= n@pre + k@pre &&
            RightNearest(seats, k@pre, i + 1, nearest) &&
            RightNearestSuffix(seats, k@pre, i + 1, suffix) &&
            CharArray::full(s, n@pre + 1, app(seats, cons(0, nil))) *
            IntArray::undef_seg(next, 0, i + 1) *
            IntArray::seg(next, i + 1, n@pre, suffix)
    */
    for (int i = n - 1; i >= 0; --i)
    {
        if (s[i] == '1')
            nearest = i;
        next[i] = nearest;
    }
    /*@ Assert
          exists next_values,
            s == s@pre && n == n@pre && k == k@pre &&
            n@pre == Zlength(seats) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
            (forall j, (0 <= j && j < n@pre) =>
              (seats[j] == 48 || seats[j] == 49)) &&
            Pre(k@pre, seats) &&
            answer == 0 && last == -k@pre - 1 &&
            0 <= nearest && nearest <= n@pre + k@pre &&
            RightNearest(seats, k@pre, 0, nearest) &&
            RightNearestSuffix(seats, k@pre, 0, next_values) &&
            CharArray::full(s, n@pre + 1, app(seats, cons(0, nil))) *
            IntArray::full(next, n@pre, next_values)
    */
    /*@ Inv Assert
          exists next_values,
            s == s@pre && n == n@pre && k == k@pre &&
            n@pre == Zlength(seats) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
            (forall j, (0 <= j && j < n@pre) =>
              (seats[j] == 48 || seats[j] == 49)) &&
            Pre(k@pre, seats) &&
            0 <= i && i <= n@pre &&
            0 <= answer && answer <= i &&
            -k@pre - 1 <= last && last < i &&
            0 <= nearest && nearest <= n@pre + k@pre &&
            RightNearest(seats, k@pre, 0, nearest) &&
            PrefixPlacementState(seats, k@pre, i, last, answer) &&
            RightNearestSuffix(seats, k@pre, 0, next_values) &&
            CharArray::full(s, n@pre + 1, app(seats, cons(0, nil))) *
            IntArray::full(next, n@pre, next_values)
    */
    for (int i = 0; i < n; ++i)
    {
        if (s[i] == '1')
        {
            last = i;
            continue;
        }
        if (i - last > k && next[i] - i > k)
        {
            ++answer;
            last = i;
        }
    }
    /*@ Assert
          exists next_values,
            s == s@pre && n == n@pre && k == k@pre &&
            -k@pre - 1 <= last && last < n@pre &&
            0 <= nearest && nearest <= n@pre + k@pre &&
            RightNearest(seats, k@pre, 0, nearest) &&
            PrefixPlacementState(seats, k@pre, n@pre, last, answer) &&
            Spec(k@pre, seats, answer) &&
            CharArray::full(s, n@pre + 1, app(seats, cons(0, nil))) *
            IntArray::full(next, n@pre, next_values)
    */
    free(next);
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, k; char *s; scanf("%d %d", &n, &k);
//         s = malloc((size_t)n + 1); scanf("%s", s);
//         printf("%d\n", solver(s, n, k)); free(s);
//     }
//     return 0;
// }
