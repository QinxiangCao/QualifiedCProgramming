
#include "int_array_def.h"
#include "array2_def.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (StockRowLength : list Z -> Z)
      (IntArray2::undef_full : Z -> Z -> Z -> Assertion)
      (StockMaximumProfit : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (StockFillRows : list (list Z) -> Z -> Z -> Z -> Prop)
      (StockFillCells : list Z -> Z -> Z -> Z -> Prop)
      (StockDaysDone : list Z -> list Z -> list Z -> list Z -> list (list Z) -> Z -> Z -> Z -> Prop)
      (StockCopyProgress : list Z -> list Z -> list Z -> list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (StockEarlyBuyProgress : list Z -> list Z -> list Z -> list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (StockSellQueue : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockSellQueueExpiring : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockSellQueuePopping : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockSellQueuePending : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockBuyQueue : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockBuyQueueExpiring : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockBuyQueuePopping : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockBuyQueuePending : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockSellProgress : list Z -> list Z -> list Z -> list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockBuyProgress : list Z -> list Z -> list Z -> list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StockAnswerProgress : list Z -> list Z -> list Z -> list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib */

/* Initialize owned local storage before the dynamic programming invariants. */
void stock_init_storage(int *storage, int length)
/*@ Require 0 <= length && length <= 982081 && IntArray::undef_full(storage, length)
    Ensure exists cells, Zlength(cells) == length && IntArray::full(storage, length, cells)
 */
{
    /*@ Inv Assert
        exists cells,
        storage == storage@pre && length == length@pre &&
        0 <= length && length <= 982081 && 0 <= index && index <= length &&
        Zlength(cells) == index &&
        IntArray::seg(storage, 0, index, cells) *
        IntArray::undef_seg(storage, index, length)
     */
    for (int index = 0; index < length; ++index) {
        storage[index] = 0;
    }

}

int maximum_profit(int days, int max_stock, int wait_days,
                         int *ap, int *bp, int *buy_limit, int *sell_limit)
/*@ With (ap_l bp_l buy_l sell_l : list Z)
    Require
        1 <= days && days <= 990 &&
        1 <= max_stock && max_stock <= 990 &&
        0 <= wait_days && wait_days < days &&
        Zlength(ap_l) == days &&
        Zlength(bp_l) == days &&
        Zlength(buy_l) == days &&
        Zlength(sell_l) == days &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock), sell_l) &&
        IntArray::full(ap, days, ap_l) *
        IntArray::full(bp, days, bp_l) *
        IntArray::full(buy_limit, days, buy_l) *
        IntArray::full(sell_limit, days, sell_l)
    Ensure
        StockMaximumProfit(ap_l, bp_l, buy_l, sell_l,
                           days, max_stock, wait_days, __return) &&
        IntArray::full(ap, days, ap_l) *
        IntArray::full(bp, days, bp_l) *
        IntArray::full(buy_limit, days, buy_l) *
        IntArray::full(sell_limit, days, sell_l)
 */
{
    int queue_index[991];
    int dp[982081];
    /*@ Assert
        days == days@pre && max_stock == max_stock@pre && wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre && buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        1 <= days && days <= 990 &&
        1 <= max_stock && max_stock <= 990 &&
        0 <= wait_days && wait_days < days &&
        Zlength(ap_l) == days &&
        Zlength(bp_l) == days &&
        Zlength(buy_l) == days &&
        Zlength(sell_l) == days &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock), sell_l) &&
        IntArray::full(ap, days, ap_l) *
        IntArray::full(bp, days, bp_l) *
        IntArray::full(buy_limit, days, buy_l) *
        IntArray::full(sell_limit, days, sell_l) *
        IntArray::undef_full(pointer_offset(queue_index, 0, sizeof(int), int), max_stock + 1) *
        IntArray::undef_seg(queue_index, max_stock + 1, 991) *
        IntArray::undef_full(pointer_offset(dp, 0, sizeof(int), int), (days + 1) * (max_stock + 1)) *
        IntArray::undef_seg(dp, (days + 1) * (max_stock + 1), 982081)
     */
    stock_init_storage(queue_index, max_stock + 1);
    stock_init_storage(dp, (days + 1) * (max_stock + 1));
    /*@ Assert
        exists queue0 dp_init,
        days == days@pre && max_stock == max_stock@pre && wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre && buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        1 <= days && days <= 990 &&
        1 <= max_stock && max_stock <= 990 &&
        0 <= wait_days && wait_days < days &&
        Zlength(ap_l) == days &&
        Zlength(bp_l) == days &&
        Zlength(buy_l) == days &&
        Zlength(sell_l) == days &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock), sell_l) &&
        IntArray::full(ap, days, ap_l) *
        IntArray::full(bp, days, bp_l) *
        IntArray::full(buy_limit, days, buy_l) *
        IntArray::full(sell_limit, days, sell_l) *
        IntArray::full(queue_index, max_stock + 1, queue0) *
        IntArray::undef_seg(queue_index, max_stock + 1, 991) *
        IntArray2::full(dp, days + 1, max_stock + 1, dp_init) *
        IntArray::undef_seg(dp, (days + 1) * (max_stock + 1), 982081) &&
        Zlength(queue0) == max_stock + 1 &&
        Zlength(dp_init) == days + 1 &&
        Forall(eq(max_stock + 1), map(StockRowLength, dp_init))
     */
    /*@ Given dp_init */

    int neg_inf = -1000000000;
    int width = max_stock + 1;
    /*@ Inv Assert
        exists queue_l,
        neg_inf == -1000000000 &&
        0 <= q_init && q_init <= width &&
        days == days@pre && max_stock == max_stock@pre &&
        wait_days == wait_days@pre &&
      ap == ap@pre && bp == bp@pre &&
      buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
      width == max_stock@pre + 1 &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        Zlength(ap_l) == days &&
        Zlength(bp_l) == days &&
        Zlength(buy_l) == days &&
        Zlength(sell_l) == days &&
        days <= 990 &&
        max_stock <= 990 &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock), sell_l) &&
        (Zlength(queue_l) == max_stock@pre + 1) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        (Zlength(dp_init) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_init))) &&
        IntArray2::full(dp, days@pre + 1, width, dp_init)
     */
    for (int q_init = 0; q_init < width; ++q_init) {
        queue_index[q_init] = 0;
    }
    /*@ Inv Assert
        exists queue_l dp_l,
        neg_inf == -1000000000 &&
        days == days@pre && max_stock == max_stock@pre &&
        wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre &&
        buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        width == max_stock@pre + 1 &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        0 <= i && i <= days@pre + 1 &&
        Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
        StockFillRows(dp_l, days@pre, max_stock@pre, i) &&
        (Zlength(queue_l) == max_stock@pre + 1) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
     */
    for (int i = 0; i < days + 1; ++i) {
        /*@ Inv Assert
            exists queue_l dp_l,
            neg_inf == -1000000000 &&
            days == days@pre && max_stock == max_stock@pre &&
            wait_days == wait_days@pre &&
            ap == ap@pre && bp == bp@pre &&
            buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
            width == max_stock@pre + 1 &&
            1 <= days@pre && days@pre <= 990 &&
            1 <= max_stock@pre && max_stock@pre <= 990 &&
            0 <= wait_days@pre && wait_days@pre < days@pre &&
            0 <= i && i < days@pre + 1 &&
            0 <= j && j <= width &&
            Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
            StockFillRows(dp_l, days@pre, max_stock@pre, i) &&
            StockFillCells(dp_l[i], max_stock@pre, i, j) &&
            (Zlength(queue_l) == max_stock@pre + 1 &&
        i <= days@pre + 1 &&
        j <= max_stock@pre + 1 &&
        Zlength(dp_l[i]) == max_stock@pre + 1) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
         */
        for (int j = 0; j < width; ++j) {
            if (i == 0 && j == 0) {
                *(dp + i * width + j) = 0;
            } else {
                *(dp + i * width + j) = neg_inf;
            }
        }
    }
    
    /*@ Inv Assert
        exists queue_l dp_l,
        neg_inf == -1000000000 &&
        days == days@pre && max_stock == max_stock@pre &&
        wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre &&
        buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        width == max_stock@pre + 1 &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        1 <= i && i <= days@pre + 1 &&
        Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
        StockDaysDone(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i) &&
        (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        0 <= i) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
     */
    for (int i = 1; i <= days; ++i) {
        /*@ Inv Assert
            exists queue_l dp_l,
            neg_inf == -1000000000 &&
            width == max_stock@pre + 1 &&
            days == days@pre && max_stock == max_stock@pre &&
            wait_days == wait_days@pre &&
            ap == ap@pre && bp == bp@pre &&
            buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
            1 <= days@pre && days@pre <= 990 &&
            1 <= max_stock@pre && max_stock@pre <= 990 &&
            0 <= wait_days@pre && wait_days@pre < days@pre &&
            1 <= i && i <= days@pre &&
            0 <= j && j <= max_stock@pre + 1 &&
            Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
            StockCopyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, j) &&
            (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
        */
        for (int j = 0; j <= max_stock; ++j) {
            int previous_value = *(dp + (i - 1) * width + j);
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                neg_inf == -1000000000 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                0 <= j && j <= max_stock@pre &&
                previous_value == dp_l[i - 1][j] &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockCopyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, j) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        j <= max_stock@pre + 1) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            *(dp + i * width + j) = previous_value;
        }
        if (i - 1 <= wait_days) {
            int buy_cap = buy_limit[i - 1];
            int ask_price = ap[i - 1];
            /*@ Inv Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                i - 1 <= wait_days@pre &&
                buy_cap == buy_l[i - 1] && ask_price == ap_l[i - 1] &&
                1 <= buy_cap && buy_cap <= max_stock@pre &&
                1 <= ask_price && ask_price <= 1000 &&
                1 <= j && j <= buy_cap + 1 &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockEarlyBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, j) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        j <= Znth(i - 1, buy_l, 0) + 1) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            for (int j = 1; j <= buy_cap; ++j) {
                int candidate = -j * ask_price;
                if (candidate > *(dp + i * width + j)) {
                    *(dp + i * width + j) = candidate;
                }
            }

            continue;
        }
        int source_day = i - wait_days - 1;
        int bid_price = bp[i - 1];
        int sell_cap = sell_limit[i - 1];
        int head = 0;
        int tail = 0;
        /*@ Inv Assert
            exists queue_l dp_l,
            neg_inf == -1000000000 &&
            width == max_stock@pre + 1 &&
            days == days@pre && max_stock == max_stock@pre &&
            wait_days == wait_days@pre &&
            ap == ap@pre && bp == bp@pre &&
            buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
            0 <= wait_days@pre && wait_days@pre < days@pre &&
            1 <= days@pre && days@pre <= 990 &&
            1 <= max_stock@pre && max_stock@pre <= 990 &&
            1 <= i && i <= days@pre &&
            wait_days@pre < i - 1 &&
            source_day == i - wait_days@pre - 1 &&
            0 < source_day && source_day < i &&
            bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
            1 <= bid_price && bid_price <= 1000 &&
            1 <= sell_cap && sell_cap <= max_stock@pre &&
            -1 <= j && j <= max_stock@pre - 1 &&
            0 <= head && head <= tail &&
            tail <= max_stock@pre - j - 1 &&
            Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
            StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
            StockSellQueue(dp_l, queue_l, source_day, bid_price,
                           j + 2, j + sell_cap + 1, head, tail) &&
            (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        j < max_stock@pre &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
        */
        for (int j = max_stock - 1; j >= 0; --j) {
            /*@ Inv Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                1 <= i && i <= days@pre &&
                wait_days@pre < i - 1 &&
                source_day == i - wait_days@pre - 1 &&
                0 < source_day && source_day < i &&
                0 <= j && j < max_stock@pre &&
                1 <= sell_cap && sell_cap <= max_stock@pre &&
                0 <= head && head <= tail &&
                tail <= max_stock@pre - j - 1 &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                1 <= bid_price && bid_price <= 1000 &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueueExpiring(dp_l, queue_l, source_day, bid_price,
                                       j + 2, j + sell_cap, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        -1 <= j &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            while (head < tail && queue_index[head] - sell_cap > j) {
                ++head;
            }
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                width == max_stock@pre + 1 &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                wait_days@pre < i - 1 &&
                0 < source_day && source_day < i &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                1 <= bid_price && bid_price <= 1000 &&
                0 <= j && j < max_stock@pre &&
                source_day < days@pre + 1 && j + 1 < width &&
                0 <= head && head <= tail &&
                tail <= max_stock@pre - j - 1 &&
                (head < tail => j <= queue_l[head]) &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 2, j + sell_cap, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        -1 <= j &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (*(dp + source_day * width + (j + 1)) != neg_inf) {
            int last_index = j + 1;
            if (head < tail) {
                last_index = queue_index[tail - 1];
            }
            int incoming_score = *(dp + source_day * width + (j + 1)) + (j + 1) * bid_price;
            /*@ Inv Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                width == max_stock@pre + 1 &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                0 <= j && j < max_stock@pre &&
                0 <= source_day && source_day < i &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                0 <= bid_price && bid_price <= 1000 &&
                0 <= head && head <= tail &&
                tail <= max_stock@pre - j - 1 &&
                0 <= last_index && last_index <= max_stock@pre &&
                incoming_score == dp_l[source_day][j + 1] + (j + 1) * bid_price &&
                (head < tail => last_index == queue_l[tail - 1]) &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueuePopping(dp_l, queue_l, source_day, bid_price,
                                      j + 1, j + sell_cap, head, tail) &&
                Forall(Z::le(0), sublist(head, tail, queue_l)) &&
                Forall(Z::ge(max_stock@pre), sublist(head, tail, queue_l)) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        -1 <= j &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            while (head < tail &&
                   *(dp + source_day * width + last_index) +
                       last_index * bid_price <= incoming_score) {
                --tail;
                if (head < tail) {
                    last_index = queue_index[tail - 1];
                }
            }

            queue_index[tail] = j + 1;
            ++tail;
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre && width == max_stock@pre + 1 &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                0 <= source_day && source_day < i &&
                0 <= j && j < max_stock@pre &&
                0 <= head && head <= tail &&
                tail <= max_stock@pre - j &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                store(&last_index, last_index) *
                store(&incoming_score, incoming_score) *
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        -1 <= j &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            }
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 && width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                wait_days@pre < i - 1 &&
                1 <= i && i <= days@pre && 0 <= source_day && source_day < i &&
                0 <= j && j < max_stock@pre &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                0 <= head && head <= tail &&
                tail <= max_stock@pre - j &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        -1 <= j &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (head < tail) {
            int best_index = queue_index[head];
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                width == max_stock@pre + 1 &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                wait_days@pre < i - 1 &&
                1 <= i && i <= days@pre &&
                0 <= source_day && source_day < i &&
                0 <= bid_price && bid_price <= 1000 &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                0 <= j && j < max_stock@pre &&
                0 <= best_index && best_index <= max_stock@pre &&
                best_index == queue_l[head] &&
                0 <= head && head < tail && tail <= max_stock@pre - j &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        -1 <= j &&
        head <= tail &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            int sell_candidate = *(dp + source_day * width + best_index) + best_index * bid_price - j * bid_price;
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                width == max_stock@pre + 1 &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                wait_days@pre < i - 1 &&
                1 <= i && i <= days@pre &&
                0 <= j && j < max_stock@pre &&
                0 <= source_day && source_day < i &&
                0 <= best_index && best_index <= max_stock@pre &&
                best_index == queue_l[head] &&
                0 <= head && head < tail && tail <= max_stock@pre - j &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                sell_candidate == dp_l[source_day][best_index] + best_index * bid_price - j * bid_price &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        -1 <= j &&
        head <= tail &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (sell_candidate > *(dp + i * width + j)) {
                *(dp + i * width + j) = sell_candidate;
            }
            }
        }
        int ask_price = ap[i - 1];
        int buy_cap = buy_limit[i - 1];
        head = 0;
        tail = 0;
        /*@ Inv Assert
            exists queue_l dp_l,
            neg_inf == -1000000000 &&
            width == max_stock@pre + 1 &&
            days == days@pre && max_stock == max_stock@pre &&
            wait_days == wait_days@pre &&
            ap == ap@pre && bp == bp@pre &&
            buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
            0 <= wait_days@pre && wait_days@pre < days@pre &&
            1 <= i && i <= days@pre &&
            wait_days@pre < i - 1 &&
            source_day == i - wait_days@pre - 1 &&
            0 < source_day && source_day < i &&
            bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
            ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
            1 <= ask_price && ask_price <= 1000 &&
            1 <= buy_cap && buy_cap <= max_stock@pre &&
            1 <= j && j <= max_stock@pre + 1 &&
            0 <= head && head <= tail && tail <= j - 1 &&
            Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        1 <= days@pre &&
        days@pre <= 990 &&
        1 <= max_stock@pre &&
        max_stock@pre <= 990 &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
            StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
            StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                          j - buy_cap - 1, j - 2, head, tail) &&
            (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
        */
        for (int j = 1; j <= max_stock; ++j) {
            /*@ Inv Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                width == max_stock@pre + 1 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                wait_days@pre < i - 1 &&
                source_day == i - wait_days@pre - 1 &&
                0 < source_day && source_day < i &&
                1 <= j && j <= max_stock@pre &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                1 <= buy_cap && buy_cap <= max_stock@pre &&
                1 <= ask_price && ask_price <= 1000 &&
                0 <= head && head <= tail && tail <= j - 1 &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueueExpiring(dp_l, queue_l, source_day, ask_price,
                                      j - buy_cap, j - 2, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        j <= max_stock@pre + 1 &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            while (head < tail && queue_index[head] + buy_cap < j) {
                ++head;
            }
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                width == max_stock@pre + 1 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                0 <= source_day && source_day < i &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                0 <= ask_price && ask_price <= 1000 &&
                1 <= j && j <= max_stock@pre &&
                source_day < days@pre + 1 && j - 1 < width &&
                0 <= head && head <= tail && tail <= j - 1 &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 2, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        j <= max_stock@pre + 1 &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (*(dp + source_day * width + (j - 1)) != neg_inf) {
            int last_index = j - 1;
            if (head < tail) {
                last_index = queue_index[tail - 1];
            }
            int incoming_score = *(dp + source_day * width + (j - 1)) + (j - 1) * ask_price;
            /*@ Inv Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                width == max_stock@pre + 1 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                1 <= j && j <= max_stock@pre &&
                0 <= source_day && source_day < i &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                0 <= ask_price && ask_price <= 1000 &&
                0 <= head && head <= tail && tail <= j - 1 &&
                0 <= last_index && last_index <= max_stock@pre &&
                incoming_score ==  dp_l[source_day][j - 1] + (j - 1) * ask_price &&
                (head < tail => last_index == queue_l[tail - 1]) &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueuePopping(dp_l, queue_l, source_day, ask_price,
                                     j - buy_cap, j - 1, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        j <= max_stock@pre + 1 &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            while (head < tail &&
                   *(dp + source_day * width + last_index) +
                       last_index * ask_price <= incoming_score) {
                --tail;
                if (head < tail) {
                    last_index = queue_index[tail - 1];
                }
            }

            queue_index[tail] = j - 1;
            ++tail;
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre && width == max_stock@pre + 1 &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                0 <= source_day && source_day < i &&
                1 <= j && j <= max_stock@pre &&
                0 <= head && head <= tail && tail <= j &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                store(&last_index, last_index) *
                store(&incoming_score, incoming_score) *
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        j <= max_stock@pre + 1 &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            }
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 && width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre && 0 <= source_day && source_day < i &&
                1 <= j && j <= max_stock@pre &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                0 <= head && head <= tail && tail <= j &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        j <= max_stock@pre + 1 &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (head < tail) {
            int best_index = queue_index[head];
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                width == max_stock@pre + 1 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                0 <= source_day && source_day < i &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                0 <= ask_price && ask_price <= 1000 &&
                1 <= j && j <= max_stock@pre &&
                0 <= best_index && best_index <= max_stock@pre &&
                best_index == queue_l[head] &&
                0 <= head && head < tail && tail <= j &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        j <= max_stock@pre + 1 &&
        head <= tail &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            int buy_candidate =
                *(dp + source_day * width + best_index) +
                best_index * ask_price - j * ask_price;
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                width == max_stock@pre + 1 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                1 <= j && j <= max_stock@pre &&
                0 <= source_day && source_day < i &&
                0 <= best_index && best_index <= max_stock@pre &&
                best_index == queue_l[head] &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                0 <= head && head < tail && tail <= j &&
                Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                buy_candidate == dp_l[source_day][best_index] + best_index * ask_price - j * ask_price &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        i <= Zlength(ap_l) &&
        source_day == i - wait_days@pre - 1 &&
        0 < source_day &&
        j <= max_stock@pre + 1 &&
        head <= tail &&
        tail <= Zlength(queue_l)) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (buy_candidate > *(dp + i * width + j)) {
                *(dp + i * width + j) = buy_candidate;
            }
            }
        }

    }
    int answer = 0;
    /*@ Inv Assert
        exists queue_l dp_l,
        neg_inf == -1000000000 &&
        width == max_stock@pre + 1 &&
        days == days@pre && max_stock == max_stock@pre &&
        wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre &&
        buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        0 <= j && j <= max_stock@pre + 1 &&
        0 <= answer && answer <= 1000000000 &&
        Zlength(ap_l) == days@pre &&
        Zlength(bp_l) == days@pre &&
        Zlength(buy_l) == days@pre &&
        Zlength(sell_l) == days@pre &&
        Forall(Z::le(1), bp_l) &&
        Forall(Z::ge(1000), ap_l) &&
        Forall2(Z::le, bp_l, ap_l) &&
        Forall(Z::le(1), buy_l) &&
        Forall(Z::ge(max_stock@pre), buy_l) &&
        Forall(Z::le(1), sell_l) &&
        Forall(Z::ge(max_stock@pre), sell_l) &&
        StockAnswerProgress(ap_l, bp_l, buy_l, sell_l, dp_l, days@pre, max_stock@pre, wait_days@pre, j, answer) &&
        (Zlength(queue_l) == max_stock@pre + 1 &&
        Forall(Forall(Z::le(-1000000000)), dp_l) &&
        Forall(Forall(Z::ge(1000000000)), dp_l) &&
        0 <= days@pre + 1) &&
        IntArray::undef_seg(queue_index, max_stock@pre + 1, 991) *
        IntArray::undef_seg(dp, (days@pre + 1) * (max_stock@pre + 1), 982081) *
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        (Zlength(dp_l) == days@pre + 1 &&
        Forall(eq(max_stock@pre + 1), map(StockRowLength, dp_l))) && IntArray2::full(dp, days@pre + 1, width, dp_l)
     */
    for (int j = 0; j <= max_stock; ++j) {
        if (*(dp + days * width + j) > answer) {
            answer = *(dp + days * width + j);
        }
    }
    
    /*@ Assert
        neg_inf == -1000000000 && width == max_stock + 1 &&
        days == days@pre && max_stock == max_stock@pre && wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre && buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        StockMaximumProfit(ap_l, bp_l, buy_l, sell_l,
                           days, max_stock, wait_days, answer) &&
        IntArray::full(ap, days, ap_l) *
        IntArray::full(bp, days, bp_l) *
        IntArray::full(buy_limit, days, buy_l) *
        IntArray::full(sell_limit, days, sell_l) *
        IntArray::undef_full(queue_index, 991) *
        IntArray::undef_full(dp, 982081)
     */
    return answer;
}
