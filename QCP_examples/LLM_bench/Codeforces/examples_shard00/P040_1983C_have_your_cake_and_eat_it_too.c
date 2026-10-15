/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib
*/

/* Codeforces 1983/C - Have Your Cake and Eat It Too */
// #include <stdio.h>
// #include <stdlib.h>
#include "array2_ext_def.h"

/*@ Extern Coq
      (Pre : list Z -> list Z -> list Z -> Prop)
      (TryOrderSpec : list Z -> list Z -> list Z -> list Z -> option (list Z) -> Prop)
      (CakeOrder : list Z -> Prop)
      (SearchState : list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
      (SearchPrefixState : list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
      (SuffixSumState : list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (GreedyPrefixState : list (list Z) -> list Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (GreedyRawState : list (list Z) -> list Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (OutputBounds : list Z -> list Z -> list Z)
      (OrderAt : Z -> list Z -> Prop)
      (OrderTable : list Z -> Prop)
      (OrderFor : Z -> list Z)
      (FailedOrders : list Z -> list Z -> list Z -> Z -> Prop)
      (sum : list Z -> Z)
      (Int64PtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
      (Int64PtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib */

static int try_order(long long **v, int n, long long need, const int order[3], int out[6])
/*@ With (a : list Z)
             (b : list Z)
             (c : list Z)
             (ord : list Z)
    Require
      3 <= Zlength(a) && Zlength(a) <= 200000 &&
      Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
      (forall row col,
        (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
          (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
           Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
      Pre(a, b, c) && n == Zlength(a) &&
      need == (sum(a) + 2) / 3 && CakeOrder(ord) && Zlength(ord) == 3 &&
      Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) *
      IntArray::full(order, 3, ord) * IntArray::undef_full(out, 6)
    Ensure
      ((__return == 0 && TryOrderSpec(a, b, c, ord, None) &&
        Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) *
        IntArray::full(order, 3, ord) * IntArray::undef_full(out, 6)) ||
       (__return == 1 && exists result raw_result,
          TryOrderSpec(a, b, c, ord, Some(result)) &&
          (forall i, (0 <= i && i < 6) => raw_result[i] == result[i] + 1) &&
          Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::full(order, 3, ord) * IntArray::full(out, 6, raw_result)))
*/
{
    int left[3] = {0, 0, 0}, right[3] = {0, 0, 0}, pos = 0;
    /*@ Inv Assert
        exists lefts rights,
          v == v@pre && n == n@pre && need == need@pre &&
          order == order@pre && out == out@pre &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          need@pre == (sum(a) + 2) / 3 &&
          1 <= need@pre && need@pre <= 200000000000 &&
          CakeOrder(ord) && Zlength(ord) == 3 &&
          0 <= part && part <= 2 &&
          GreedyRawState(cons(a, cons(b, cons(c, nil))), ord,
                         need@pre, part, pos, lefts, rights) &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::full(order@pre, 3, ord) *
          IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
          IntArray::undef_full(out@pre, 6)
    */
    for (int part = 0; part < 2; ++part)
    {
        int who = order[part], start = pos;
        long long acc = 0;
        /*@ Assert
            exists lefts rights row_ptr,
              v == v@pre && n == n@pre && need == need@pre &&
              order == order@pre && out == out@pre &&
              3 <= Zlength(a) && Zlength(a) <= 200000 &&
              Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
              (forall row col,
                (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
                  (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
                   Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
              Pre(a, b, c) && n@pre == Zlength(a) &&
              need@pre == (sum(a) + 2) / 3 &&
              1 <= need@pre && need@pre <= 200000000000 &&
              CakeOrder(ord) && Zlength(ord) == 3 &&
              0 <= part && part < 2 && who == Znth(part, ord, 0) &&
              0 <= who && who < 3 && start == pos && acc == 0 &&
              GreedyRawState(cons(a, cons(b, cons(c, nil))), ord,
                             need@pre, part, pos, lefts, rights) &&
              Int64PtrArray2::missing_i(v@pre, 3, who, row_ptr,
                                        cons(a, cons(b, cons(c, nil)))) *
              data_at(v@pre + who * sizeof(long long *), long long *, row_ptr) *
              Int64Array::full(row_ptr, n@pre,
                               Znth(who, cons(a, cons(b, cons(c, nil))), nil)) *
              IntArray::full(order@pre, 3, ord) *
              IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
              IntArray::undef_full(out@pre, 6)
        */
        /*@ Inv Assert
            exists lefts rights row_ptr,
              v == v@pre && n == n@pre && need == need@pre &&
              order == order@pre && out == out@pre &&
              3 <= Zlength(a) && Zlength(a) <= 200000 &&
              Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
              (forall row col,
                (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
                  (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
                   Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
              Pre(a, b, c) && n@pre == Zlength(a) &&
              need@pre == (sum(a) + 2) / 3 &&
              1 <= need@pre && need@pre <= 200000000000 &&
              CakeOrder(ord) && Zlength(ord) == 3 &&
              0 <= part && part < 2 && who == Znth(part, ord, 0) &&
              0 <= who && who < 3 && start >= 0 && start <= n@pre &&
              0 <= pos && pos <= n@pre && 0 <= acc && acc <= 200000000000 &&
              GreedyRawState(cons(a, cons(b, cons(c, nil))), ord,
                             need@pre, part, start, lefts, rights) &&
              SearchPrefixState(cons(a, cons(b, cons(c, nil))), who,
                                start, pos, need@pre, acc) &&
              Int64PtrArray2::missing_i(v@pre, 3, who, row_ptr,
                                        cons(a, cons(b, cons(c, nil)))) *
              data_at(v@pre + who * sizeof(long long *), long long *, row_ptr) *
              Int64Array::full(row_ptr, n@pre,
                               Znth(who, cons(a, cons(b, cons(c, nil))), nil)) *
              IntArray::full(order@pre, 3, ord) *
              IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
              IntArray::undef_full(out@pre, 6)
        */
        while (pos < n && acc < need)
        {
            acc += v[who][pos];
            ++pos;
        }
        /*@ Assert
            exists lefts rights,
              v == v@pre && n == n@pre && need == need@pre &&
              order == order@pre && out == out@pre &&
              3 <= Zlength(a) && Zlength(a) <= 200000 &&
              Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
              (forall row col,
                (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
                  (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
                   Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
              Pre(a, b, c) && n@pre == Zlength(a) &&
              need@pre == (sum(a) + 2) / 3 && CakeOrder(ord) && Zlength(ord) == 3 &&
              0 <= part && part < 2 && who == Znth(part, ord, 0) &&
              0 <= who && who < 3 && 0 <= start && start <= pos && pos <= n@pre &&
              (acc < need@pre => pos >= n@pre) &&
              GreedyRawState(cons(a, cons(b, cons(c, nil))), ord,
                             need@pre, part, start, lefts, rights) &&
              SearchPrefixState(cons(a, cons(b, cons(c, nil))), who,
                                start, pos, need@pre, acc) &&
              Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
              IntArray::full(order@pre, 3, ord) *
              IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
              IntArray::undef_full(out@pre, 6)
        */
        if (acc < need)
        {
            /*@ Assert
                exists lefts rights,
                v == v@pre && n == n@pre && need == need@pre &&
                order == order@pre && out == out@pre &&
                0 <= part && part < 2 && 0 <= who && who < 3 &&
                0 <= start && start <= pos && pos == n@pre &&
                0 <= acc && acc < need@pre &&
                TryOrderSpec(a, b, c, ord, None) &&
                Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
                IntArray::full(order@pre, 3, ord) *
                IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
                IntArray::undef_full(out@pre, 6)
            */
            return 0;
        }
        left[who] = start + 1;
        right[who] = pos;
    }
    int who = order[2];
    long long acc = 0;
    /*@ Assert
        exists lefts rights row_ptr,
          v == v@pre && n == n@pre && need == need@pre &&
          order == order@pre && out == out@pre &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          need@pre == (sum(a) + 2) / 3 &&
          1 <= need@pre && need@pre <= 200000000000 &&
          CakeOrder(ord) && Zlength(ord) == 3 &&
          who == Znth(2, ord, 0) && 0 <= who && who < 3 &&
          0 <= pos && pos <= n@pre && acc == 0 &&
          GreedyRawState(cons(a, cons(b, cons(c, nil))), ord,
                         need@pre, 2, pos, lefts, rights) &&
          Int64PtrArray2::missing_i(v@pre, 3, who, row_ptr,
                                    cons(a, cons(b, cons(c, nil)))) *
          data_at(v@pre + who * sizeof(long long *), long long *, row_ptr) *
          Int64Array::full(row_ptr, n@pre,
                           Znth(who, cons(a, cons(b, cons(c, nil))), nil)) *
          IntArray::full(order@pre, 3, ord) *
          IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
          IntArray::undef_full(out@pre, 6)
    */
    /*@ Inv Assert
        exists lefts rights row_ptr,
          v == v@pre && n == n@pre && need == need@pre &&
          order == order@pre && out == out@pre &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          need@pre == (sum(a) + 2) / 3 &&
          1 <= need@pre && need@pre <= 200000000000 &&
          CakeOrder(ord) && Zlength(ord) == 3 &&
          who == Znth(2, ord, 0) && 0 <= who && who < 3 &&
          0 <= pos && pos <= i && i <= n@pre &&
          0 <= acc && acc <= 200000000000 &&
          GreedyRawState(cons(a, cons(b, cons(c, nil))), ord,
                         need@pre, 2, pos, lefts, rights) &&
          SuffixSumState(cons(a, cons(b, cons(c, nil))), who,
                         pos, i, acc) &&
          Int64PtrArray2::missing_i(v@pre, 3, who, row_ptr,
                                    cons(a, cons(b, cons(c, nil)))) *
          data_at(v@pre + who * sizeof(long long *), long long *, row_ptr) *
          Int64Array::full(row_ptr, n@pre,
                           Znth(who, cons(a, cons(b, cons(c, nil))), nil)) *
          IntArray::full(order@pre, 3, ord) *
          IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
          IntArray::undef_full(out@pre, 6)
    */
    for (int i = pos; i < n; ++i)
        acc += v[who][i];
    /*@ Assert
        exists lefts rights,
          v == v@pre && n == n@pre && need == need@pre &&
          order == order@pre && out == out@pre &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          need@pre == (sum(a) + 2) / 3 &&
          1 <= need@pre && need@pre <= 200000000000 &&
          CakeOrder(ord) && Zlength(ord) == 3 &&
          0 <= pos && pos <= n@pre && who == Znth(2, ord, 0) &&
          0 <= who && who < 3 && 0 <= acc && acc <= 200000000000 &&
          GreedyRawState(cons(a, cons(b, cons(c, nil))), ord,
                         need@pre, 2, pos, lefts, rights) &&
          SuffixSumState(cons(a, cons(b, cons(c, nil))), who,
                         pos, n@pre, acc) &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::full(order@pre, 3, ord) *
          IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
          IntArray::undef_full(out@pre, 6)
    */
    if (acc < need)
    {
        /*@ Assert
            exists lefts rights,
              v == v@pre && n == n@pre && need == need@pre &&
              order == order@pre && out == out@pre &&
              0 <= pos && pos <= n@pre && 0 <= who && who < 3 &&
              0 <= acc && acc < need@pre &&
              TryOrderSpec(a, b, c, ord, None) &&
              Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
              IntArray::full(order@pre, 3, ord) *
              IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
              IntArray::undef_full(out@pre, 6)
        */
        return 0;
    }
    left[who] = pos + 1;
    right[who] = n;
    /*@ Assert
        exists lefts rights,
          v == v@pre && n == n@pre && need == need@pre &&
          order == order@pre && out == out@pre &&
          0 <= pos && pos <= n@pre && 0 <= who && who < 3 &&
          need@pre <= acc && acc <= 200000000000 &&
          TryOrderSpec(a, b, c, ord, Some(OutputBounds(lefts, rights))) &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::full(order@pre, 3, ord) *
          IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
          IntArray::undef_full(out@pre, 6)
    */
    /*@ Inv Assert
        exists lefts rights raw_prefix,
          v == v@pre && n == n@pre && need == need@pre &&
          order == order@pre && out == out@pre &&
          0 <= pos && pos <= n@pre && 0 <= who && who < 3 &&
          need@pre <= acc && acc <= 200000000000 &&
          0 <= i && i <= 3 && Zlength(raw_prefix) == 2 * i &&
          TryOrderSpec(a, b, c, ord, Some(OutputBounds(lefts, rights))) &&
          (forall j, (0 <= j && j < 2 * i) =>
            raw_prefix[j] == OutputBounds(lefts, rights)[j] + 1) &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::full(order@pre, 3, ord) *
          IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
          IntArray::seg(out@pre, 0, 2 * i, raw_prefix) *
          IntArray::undef_seg(out@pre, 2 * i, 6)
    */
    for (int i = 0; i < 3; ++i)
    {
        out[2 * i] = left[i];
        out[2 * i + 1] = right[i];
    }
    /*@ Assert
        exists lefts rights raw_result,
          v == v@pre && n == n@pre && need == need@pre &&
          order == order@pre && out == out@pre &&
          0 <= pos && pos <= n@pre && 0 <= who && who < 3 &&
          need@pre <= acc && acc <= 200000000000 &&
          TryOrderSpec(a, b, c, ord, Some(OutputBounds(lefts, rights))) &&
          Zlength(raw_result) == 6 &&
          (forall j, (0 <= j && j < 6) =>
            raw_result[j] == OutputBounds(lefts, rights)[j] + 1) &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::full(order@pre, 3, ord) *
          IntArray::full(left, 3, lefts) * IntArray::full(right, 3, rights) *
          IntArray::full(out@pre, 6, raw_result)
    */
    return 1;
}

/* QCP_INSERT_BEGIN:P040_1983C_have_your_cake_and_eat_it_too.support */
/*@ Extern Coq
      (Pre : list Z -> list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> option (list Z) -> Prop)
      (Int64PtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib */
/* QCP_INSERT_END:P040_1983C_have_your_cake_and_eat_it_too.support */
/*@ Extern Coq
      (Int64PtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (sum : list Z -> Z)
*/
static int
solver(long long **v, int n,
       int out[6]) /* QCP_INSERT_BEGIN:P040_1983C_have_your_cake_and_eat_it_too.contract */

/*@ With (a : list Z)
             (b : list Z)
             (c : list Z)
    Require
      3 <= Zlength(a) && Zlength(a) <= 200000 &&
      Zlength(b) == Zlength(a) &&
      Zlength(c) == Zlength(a) &&
      (forall row col,
        (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
          (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
           Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
      Pre(a, b, c) &&
      n == Zlength(a) &&
      Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) *
      IntArray::undef_full(out, 6)
    Ensure
      ((__return == 0 && Spec(a, b, c, None) &&
      Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) * IntArray::undef_full(out, 6)) ||
       (__return == 1 && exists result raw_result,
          Spec(a, b, c, Some(result)) &&
          (forall i, (0 <= i && i < 6) => raw_result[i] == result[i] + 1) &&
        Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) * IntArray::full(out, 6, raw_result)))
*/
/* QCP_INSERT_END:P040_1983C_have_your_cake_and_eat_it_too.contract */

{
    const int orders[18] = {0, 1, 2, 0, 2, 1, 1, 0, 2, 1, 2, 0, 2, 0, 1, 2, 1, 0};
    long long total = 0;
    /*@ Assert
        exists row0,
          v == v@pre && n == n@pre && out == out@pre &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          total == 0 &&
          Int64PtrArray2::missing_i(v@pre, 3, 0, row0,
                                    cons(a, cons(b, cons(c, nil)))) *
          data_at(v@pre + 0 * sizeof(long long *), long long *, row0) *
          Int64Array::full(row0, n@pre, a) *
          IntArray::undef_full(out@pre, 6) *
          IntArray::full(orders, 18,
            cons(0, cons(1, cons(2, cons(0, cons(2, cons(1,
            cons(1, cons(0, cons(2, cons(1, cons(2, cons(0,
            cons(2, cons(0, cons(1, cons(2, cons(1, cons(0, nil)))))))))))))))))))
    */
    long long *row0 = v[0];
    /*@ Inv Assert
        exists row0_addr,
          v == v@pre && n == n@pre && out == out@pre &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          0 <= i && i <= n@pre &&
          total == sum(sublist(0, i, a)) &&
          0 <= total && total <= 200000000000 &&
          row0 == row0_addr &&
          Int64PtrArray2::missing_i(v@pre, 3, 0, row0_addr,
                                    cons(a, cons(b, cons(c, nil)))) *
          data_at(v@pre + 0 * sizeof(long long *), long long *, row0_addr) *
          Int64Array::full(row0_addr, n@pre, a) *
          IntArray::undef_full(out@pre, 6) *
          IntArray::full(orders, 18,
            cons(0, cons(1, cons(2, cons(0, cons(2, cons(1,
            cons(1, cons(0, cons(2, cons(1, cons(2, cons(0,
            cons(2, cons(0, cons(1, cons(2, cons(1, cons(0, nil)))))))))))))))))))
    */
    for (int i = 0; i < n; ++i)
        total += row0[i];
    /*@ Assert
        exists row0_addr,
          v == v@pre && n == n@pre && out == out@pre &&
          row0 == row0_addr &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          total == sum(a) && 0 <= total && total <= 200000000000 &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::undef_full(out@pre, 6) *
          IntArray::full(orders, 18,
            cons(0, cons(1, cons(2, cons(0, cons(2, cons(1,
            cons(1, cons(0, cons(2, cons(1, cons(2, cons(0,
            cons(2, cons(0, cons(1, cons(2, cons(1, cons(0, nil)))))))))))))))))))
    */
    long long need = (total + 2) / 3;
    /*@ Inv Assert
        exists table row0_addr,
          v == v@pre && n == n@pre && out == out@pre && row0 == row0_addr &&
          3 <= Zlength(a) && Zlength(a) <= 200000 &&
          Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
          (forall row col,
            (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
              (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
               Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
          Pre(a, b, c) && n@pre == Zlength(a) &&
          total == sum(a) && need == (sum(a) + 2) / 3 &&
          1 <= need && need <= 200000000000 &&
          0 <= z && z <= 6 && OrderTable(table) && FailedOrders(a, b, c, z) &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::undef_full(out@pre, 6) * IntArray::full(orders, 18, table)
    */
    for (int z = 0; z < 6; ++z)
    {
        const int *ordp = orders + 3 * z;
        /*@ Assert
            exists table before after row0_addr,
              v == v@pre && n == n@pre && out == out@pre && row0 == row0_addr &&
              3 <= Zlength(a) && Zlength(a) <= 200000 &&
              Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
              (forall row col,
                (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
                  (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
                   Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
              Pre(a, b, c) && n@pre == Zlength(a) &&
              total == sum(a) && need == (sum(a) + 2) / 3 &&
              1 <= need && need <= 200000000000 &&
              0 <= z && z < 6 && FailedOrders(a, b, c, z) &&
              ordp == orders + 3 * z * sizeof(int) &&
              OrderTable(table) && table == app(before, app(OrderFor(z), after)) &&
              Zlength(before) == 3 * z && Zlength(OrderFor(z)) == 3 &&
              Zlength(after) == 18 - 3 * (z + 1) &&
              OrderAt(z, OrderFor(z)) && CakeOrder(OrderFor(z)) &&
              Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
              IntArray::undef_full(out@pre, 6) *
              IntArray::seg(orders, 0, 3 * z, before) *
              IntArray::full(ordp, 3, OrderFor(z)) *
              IntArray::seg(orders, 3 * (z + 1), 18, after)
        */
        int ok = try_order(v, n, need, ordp, out)
            /*@ where a = a, b = b, c = c, ord = OrderFor(z) */;
        if (ok)
        {
            /*@ Assert
                exists table before after result raw_result row0_addr,
                  v == v@pre && n == n@pre && out == out@pre && row0 == row0_addr &&
                  total == sum(a) && need == (sum(a) + 2) / 3 &&
                  0 <= z && z < 6 && ok == 1 &&
                  ordp == orders + 3 * z * sizeof(int) &&
                  Spec(a, b, c, Some(result)) &&
                  (forall j, (0 <= j && j < 6) => raw_result[j] == result[j] + 1) &&
                  OrderTable(table) && table == app(before, app(OrderFor(z), after)) &&
                  Zlength(before) == 3 * z && Zlength(OrderFor(z)) == 3 &&
                  Zlength(after) == 18 - 3 * (z + 1) &&
                  Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
                  IntArray::full(out@pre, 6, raw_result) * IntArray::full(orders, 18, table)
            */
            return 1;
        }
        /*@ Assert
            exists table row0_addr,
              v == v@pre && n == n@pre && out == out@pre && row0 == row0_addr &&
              3 <= Zlength(a) && Zlength(a) <= 200000 &&
              Zlength(b) == Zlength(a) && Zlength(c) == Zlength(a) &&
              Pre(a, b, c) && n@pre == Zlength(a) &&
              total == sum(a) && need == (sum(a) + 2) / 3 &&
              1 <= need && need <= 200000000000 &&
              0 <= z && z < 6 && ok == 0 && OrderTable(table) &&
              ordp == orders + 3 * z * sizeof(int) &&
              FailedOrders(a, b, c, z + 1) &&
              Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
              IntArray::undef_full(out@pre, 6) * IntArray::full(orders, 18, table)
        */
    }
    /*@ Assert
        exists table row0_addr,
          v == v@pre && n == n@pre && out == out@pre && row0 == row0_addr &&
          total == sum(a) && need == (sum(a) + 2) / 3 &&
          FailedOrders(a, b, c, 6) && Spec(a, b, c, None) && OrderTable(table) &&
          Int64PtrArray2::full(v@pre, 3, cons(a, cons(b, cons(c, nil)))) *
          IntArray::undef_full(out@pre, 6) * IntArray::full(orders, 18, table)
    */
    return 0;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n);
//         long long *v[3]; int out[6];
//         for (int p = 0; p < 3; ++p) {
//             v[p] = malloc((size_t)n * sizeof(**v));
//             for (int i = 0; i < n; ++i) scanf("%lld", &v[p][i]);
//         }
//         int ok = solver(v, n, out);
//         if (!ok) puts("-1");
//         else printf("%d %d %d %d %d %d\n", out[0], out[1], out[2], out[3], out[4], out[5]);
//         for (int p = 0; p < 3; ++p) free(v[p]);
//     }
//     return 0;
// }
