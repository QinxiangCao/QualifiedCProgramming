/*
 * Codeforces 1492/D - Genius's Gambit  (rating 1900, CONSTRUCTIVE)
 *
 * Start from x = 1^b 0^a and build y by moving a single one from position i
 * into a zero at position j > i.  Then x - y = 2^(n-1-i) - 2^(n-1-j), whose
 * binary form is exactly j-i ones.  Avoiding a leading zero forces i >= 1, so
 * k can reach a+b-2 but no further, and a zero and at least two ones are
 * needed for any k >= 1.
 */

// #include <stdio.h>
// #include <string.h>
#include "string.h"

/* solver: pure.  Writes x and y (length a+b, NUL-terminated) and returns 1,
 * or returns 0 when no pair exists. */
/* QCP_INSERT_BEGIN:shard09-P062-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P062_1492D_geniuss_gambit_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> option(list Z * list Z) -> Prop)
      (pair : {A B} -> A -> B -> A * B)
*/
/*@ Extern Coq
      (GambitX : Z -> Z -> list Z)
      (GambitY : Z -> Z -> Z -> list Z)
      (EncodeDigits : list Z -> list Z)
      (CanonicalGambit : Z -> Z -> Z -> Prop)
      (GambitImpossible : Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P062-solver-support */
static int solver(int a, int b, int k, char *x, char *y)
/* QCP_INSERT_BEGIN:shard09-P062-solver-contract */
/*@ Require
      0 <= a && 1 <= b && 0 <= k && k <= a + b && a + b <= 200000 &&
      CharArray::undef_full(x, a + b + 1) * CharArray::undef_full(y, a + b + 1)
    Ensure
      exists (out : option(list Z * list Z)),
        Spec(a@pre, b@pre, k@pre, out) &&
        ((out == None && __return == 0 &&
        CharArray::full_shape(x, a + b + 1) * CharArray::full_shape(y, a + b + 1)) || 
        (exists (xs : list Z) (ys : list Z), 
        out == Some(pair(xs, ys)) && __return == 1 && Zlength(xs) == a + b && Zlength(ys) == a + b && 
        exists (xbytes : list Z) (ybytes : list Z), Zlength(xbytes) == a + b && Zlength(ybytes) == a + b && 
        (forall i, (0 <= i && i < a + b) => xbytes[i] == xs[i] + 48 && ybytes[i] == ys[i] + 48) && 
        CharArray::full(x, a + b + 1, app(xbytes, cons(0, nil))) * CharArray::full(y, a + b + 1, app(ybytes, cons(0, nil)))))
*/
/* QCP_INSERT_END:shard09-P062-solver-contract */
{
    int n = a + b;
    /*@ Inv Assert
        a == a@pre && b == b@pre && k == k@pre &&
        x == x@pre && y == y@pre &&
        n == a@pre + b@pre &&
        0 <= a@pre && 1 <= b@pre &&
        0 <= k@pre && k@pre <= n && n <= 200000 &&
        0 <= i && i <= b@pre &&
        CharArray::full(x@pre, i, repeat_Z(49, i)) *
        CharArray::undef_seg(x@pre, i, n + 1) *
        CharArray::undef_full(y@pre, n + 1)
    */
    for (int i = 0; i < b; i++)
        x[i] = '1';
    /*@ Inv Assert
        a == a@pre && b == b@pre && k == k@pre &&
        x == x@pre && y == y@pre &&
        n == a@pre + b@pre &&
        0 <= a@pre && 1 <= b@pre &&
        0 <= k@pre && k@pre <= n && n <= 200000 &&
        b@pre <= i && i <= n &&
        CharArray::full(
          x@pre, i,
          app(repeat_Z(49, b@pre), repeat_Z(48, i - b@pre))) *
        CharArray::undef_seg(x@pre, i, n + 1) *
        CharArray::undef_full(y@pre, n + 1)
    */
    for (int i = b; i < n; i++)
        x[i] = '0';
    x[n] = '\0';
    /*@ Assert
        a == a@pre && b == b@pre && k == k@pre &&
        x == x@pre && y == y@pre &&
        n == a@pre + b@pre &&
        0 <= a@pre && 1 <= b@pre &&
        0 <= k@pre && k@pre <= n && n <= 200000 &&
        0 <= n && n + 1 < INT_MAX &&
        all_ascii(app(repeat_Z(49, b@pre),
                      app(repeat_Z(48, a@pre), cons(0, nil)))) &&
        Zlength(app(repeat_Z(49, b@pre),
                    app(repeat_Z(48, a@pre), cons(0, nil)))) == n + 1 &&
        CharArray::full(
          x@pre, n + 1,
          app(repeat_Z(49, b@pre),
              app(repeat_Z(48, a@pre), cons(0, nil)))) *
        CharArray::undef_full(y@pre, n + 1)
    */
    memcpy(y, x, n + 1)
      /*@ where bytes = app(repeat_Z(49, b@pre),
                            app(repeat_Z(48, a@pre), cons(0, nil))) */;
    if (k == 0)
        /*@ Assert
            a == a@pre && b == b@pre && k == k@pre &&
            x == x@pre && y == y@pre &&
            n == a@pre + b@pre && k@pre == 0 &&
            0 <= a@pre && 1 <= b@pre &&
            0 <= k@pre && k@pre <= n && n <= 200000 &&
            CanonicalGambit(a@pre, b@pre, k@pre) &&
            CharArray::full(
              x@pre, n + 1,
              app(repeat_Z(49, b@pre),
                  app(repeat_Z(48, a@pre), cons(0, nil)))) *
            CharArray::full(
              y@pre, n + 1,
              app(repeat_Z(49, b@pre),
                  app(repeat_Z(48, a@pre), cons(0, nil))))
        */
        return 1;
    if (a == 0 || b < 2 || k > n - 2)
        /*@ Assert
            a == a@pre && b == b@pre && k == k@pre &&
            x == x@pre && y == y@pre &&
            n == a@pre + b@pre && 0 < k@pre &&
            0 <= a@pre && 1 <= b@pre &&
            0 <= k@pre && k@pre <= n && n <= 200000 &&
            (a@pre == 0 || b@pre < 2 || k@pre > n - 2) &&
            GambitImpossible(a@pre, b@pre, k@pre) &&
            CharArray::full(
              x@pre, n + 1,
              app(repeat_Z(49, b@pre),
                  app(repeat_Z(48, a@pre), cons(0, nil)))) *
            CharArray::full(
              y@pre, n + 1,
              app(repeat_Z(49, b@pre),
                  app(repeat_Z(48, a@pre), cons(0, nil))))
        */
        return 0;
    int i, j;
    if (k <= a) {
        i = b - 1;                        /* last one, into the zero field */
        j = i + k;
    } else {
        j = n - 1;                        /* last zero, from an earlier one */
        i = j - k;
    }
    /*@ 1 <= i && i < j && j < n by local */
    y[i] = '0';
    y[j] = '1';
    /*@ Assert
        a == a@pre && b == b@pre && k == k@pre &&
        x == x@pre && y == y@pre &&
        n == a@pre + b@pre &&
        0 <= a@pre && 1 <= b@pre &&
        0 <= k@pre && k@pre <= n && n <= 200000 &&
        0 < k@pre && 0 < a@pre && 2 <= b@pre && k@pre <= n - 2 &&
        1 <= i && i < j && j < n && j - i == k@pre &&
        ((k@pre <= a@pre && i == b@pre - 1 && j == i + k@pre) ||
         (k@pre > a@pre && j == n - 1 && i == j - k@pre)) &&
        CanonicalGambit(a@pre, b@pre, k@pre) &&
        CharArray::full(
          x@pre, n + 1,
          app(repeat_Z(49, b@pre),
              app(repeat_Z(48, a@pre), cons(0, nil)))) *
        CharArray::full(
          y@pre, n + 1,
          replace_Znth(
            j, 49,
            replace_Znth(
              i, 48,
              app(repeat_Z(49, b@pre),
                  app(repeat_Z(48, a@pre), cons(0, nil))))))
    */
    return 1;
}

// int main(void)
// {
//     int a, b, k;
//     if (scanf("%d %d %d", &a, &b, &k) != 3)
//         return 0;
//     static char x[200005], y[200005];
//     if (solver(a, b, k, x, y)) {
//         puts("Yes");
//         puts(x);
//         puts(y);
//     } else {
//         puts("No");
//     }
//     return 0;
// }
