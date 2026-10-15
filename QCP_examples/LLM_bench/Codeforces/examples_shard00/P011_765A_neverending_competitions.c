/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib
*/

/* Codeforces 765/A - Neverending competitions */
// #include <stdio.h>
#include "array2_ext_def.h"

/* QCP_INSERT_BEGIN:P011_765A_neverending_competitions.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : list Z -> list (list Z * list Z) -> Prop)
      (Spec : list Z -> list (list Z * list Z) -> list Z -> Prop)
      (store_string : Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib */
/* QCP_INSERT_END:P011_765A_neverending_competitions.support */
static int solver(const char home[4], const char flights[][16],
                  int n) /* QCP_INSERT_BEGIN:P011_765A_neverending_competitions.contract */

/*@ With (home_data : list Z)
             (flights_data : list (list Z * list Z))
             (flight_rows : list (list (option Z)))
    Require
      Zlength(home_data) == 3 &&
      (forall j, (0 <= j && j < 3) =>
        (65 <= home_data[j] && home_data[j] <= 90)) &&
      1 <= Zlength(flights_data) && Zlength(flights_data) <= 100 &&
      Pre(home_data, flights_data) &&
      n == Zlength(flights_data) &&
      Zlength(flight_rows) == n &&
      (forall i, (0 <= i && i < n) =>
        (Zlength(fst(flights_data[i])) == 3 &&
         Zlength(snd(flights_data[i])) == 3 &&
         Zlength(Znth(i, flight_rows, nil)) == 16 &&
         (forall j, (0 <= j && j < 3) =>
           (65 <= Znth(j, fst(flights_data[i]), 0) &&
            Znth(j, fst(flights_data[i]), 0) <= 90 &&
            65 <= Znth(j, snd(flights_data[i]), 0) &&
            Znth(j, snd(flights_data[i]), 0) <= 90 &&
            Znth(j, Znth(i, flight_rows, nil), None) ==
              Some(Znth(j, fst(flights_data[i]), 0)) &&
            Znth(5 + j, Znth(i, flight_rows, nil), None) ==
              Some(Znth(j, snd(flights_data[i]), 0)))) &&
         Znth(3, Znth(i, flight_rows, nil), None) == Some(45) &&
         Znth(4, Znth(i, flight_rows, nil), None) == Some(62) &&
         Znth(8, Znth(i, flight_rows, nil), None) == Some(0))) &&
      store_string(home, home_data) *
      CharArray2::mixed_full(flights, n, 16, flight_rows)
    Ensure
      exists result,
        Spec(home_data, flights_data, result) &&
        ((__return == 1 && result == cons(104, cons(111, cons(109, cons(101, nil))))) ||
         (__return == 0 && result == cons(99, cons(111, cons(110, cons(116,
          cons(101, cons(115, cons(116, nil))))))))) &&
        store_string(home, home_data) *
        CharArray2::mixed_full(flights, n, 16, flight_rows)
*/
/* QCP_INSERT_END:P011_765A_neverending_competitions.contract */

{
    (void)home;
    (void)flights;
    return (n & 1) == 0;
}

// int main(void)
// {
//     int n; char home[4], flights[100][16];
//     if (scanf("%d %3s", &n, home) != 2) return 0;
//     for (int i = 0; i < n; ++i) scanf("%15s", flights[i]);
//     puts(solver(home, flights, n) ? "home" : "contest");
//     return 0;
// }
