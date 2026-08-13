#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "array2_def.h"

/*@ Extern Coq
      (IntArray2::undef_full : Z -> Z -> Z -> Assertion)
      (StockTableShape : list (list Z) -> Z -> Z -> Prop)
      (StockInputsBounded : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
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

int maximum_profit(int days, int max_stock, int wait_days,
                         int *ap, int *bp, int *buy_limit, int *sell_limit,
                         int *queue_index, int *dp)
/*@ With (ap_l bp_l buy_l sell_l queue0 : list Z)
         (dp_init : list (list Z))
    Require
        1 <= days && days <= 990 &&
        1 <= max_stock && max_stock <= 990 &&
        0 <= wait_days && wait_days < days &&
        StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days, max_stock) &&
        IntArray::full(ap, days, ap_l) *
        IntArray::full(bp, days, bp_l) *
        IntArray::full(buy_limit, days, buy_l) *
        IntArray::full(sell_limit, days, sell_l) *
        IntArray::full(queue_index, max_stock + 1, queue0) *
        StockTableShape(dp_init, days, max_stock) &&
        IntArray2::full(dp, days + 1, max_stock + 1, dp_init)
    Ensure
        StockMaximumProfit(ap_l, bp_l, buy_l, sell_l,
                           days, max_stock, wait_days, __return) &&
        0 <= __return && __return <= 1000000000 &&
        IntArray::full(ap, days, ap_l) *
        IntArray::full(bp, days, bp_l) *
        IntArray::full(buy_limit, days, buy_l) *
        IntArray::full(sell_limit, days, sell_l) *
        IntArray::undef_full(queue_index, max_stock + 1) *
        IntArray2::undef_full(dp, days + 1, max_stock + 1)
 */
{
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
      queue_index == queue_index@pre && dp == dp@pre &&
      width == max_stock@pre + 1 &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days, max_stock) &&
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        StockTableShape(dp_init, days@pre, max_stock@pre) &&
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
        queue_index == queue_index@pre && dp == dp@pre &&
        width == max_stock@pre + 1 &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        0 <= i && i <= days@pre + 1 &&
        StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
        StockFillRows(dp_l, days@pre, max_stock@pre, i) &&
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
     */
    for (int i = 0; i < days + 1; ++i) {
        /*@ Inv Assert
            exists queue_l dp_l,
            neg_inf == -1000000000 &&
            days == days@pre && max_stock == max_stock@pre &&
            wait_days == wait_days@pre &&
            ap == ap@pre && bp == bp@pre &&
            buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
            queue_index == queue_index@pre && dp == dp@pre &&
            width == max_stock@pre + 1 &&
            1 <= days@pre && days@pre <= 990 &&
            1 <= max_stock@pre && max_stock@pre <= 990 &&
            0 <= wait_days@pre && wait_days@pre < days@pre &&
            0 <= i && i < days@pre + 1 &&
            0 <= j && j <= width &&
            StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
            StockFillRows(dp_l, days@pre, max_stock@pre, i) &&
            StockFillCells(dp_l[i], max_stock@pre, i, j) &&
            IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
         */
        for (int j = 0; j < width; ++j) {
            if (i == 0 && j == 0) {
                *(dp + i * width + j) = 0;
            } else {
                *(dp + i * width + j) = neg_inf;
            }
        }
    }
    /*@ Assert
        exists queue_l dp_l,
        neg_inf == -1000000000 &&
        days == days@pre && max_stock == max_stock@pre &&
        wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre &&
        buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        queue_index == queue_index@pre && dp == dp@pre &&
        width == max_stock@pre + 1 &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
        StockDaysDone(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, 1) &&
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
     */
    /*@ Inv Assert
        exists queue_l dp_l,
        neg_inf == -1000000000 &&
        days == days@pre && max_stock == max_stock@pre &&
        wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre &&
        buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        queue_index == queue_index@pre && dp == dp@pre &&
        width == max_stock@pre + 1 &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        1 <= i && i <= days@pre + 1 &&
        StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
        StockDaysDone(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i) &&
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
            queue_index == queue_index@pre && dp == dp@pre &&
            1 <= days@pre && days@pre <= 990 &&
            1 <= max_stock@pre && max_stock@pre <= 990 &&
            0 <= wait_days@pre && wait_days@pre < days@pre &&
            1 <= i && i <= days@pre &&
            0 <= j && j <= max_stock@pre + 1 &&
            StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
            StockCopyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, j) &&
            IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
                neg_inf == -1000000000 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                0 <= j && j <= max_stock@pre &&
                previous_value == dp_l[i - 1][j] &&
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockCopyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, j) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre &&
                i - 1 <= wait_days@pre &&
                buy_cap == buy_l[i - 1] && ask_price == ap_l[i - 1] &&
                1 <= buy_cap && buy_cap <= max_stock@pre &&
                1 <= ask_price && ask_price <= 1000 &&
                1 <= j && j <= buy_cap + 1 &&
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockEarlyBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, j) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            for (int j = 1; j <= buy_cap; ++j) {
                int candidate = -j * ask_price;
                if (candidate > *(dp + i * width + j)) {
                    *(dp + i * width + j) = candidate;
                }
            }
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 &&
                width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                queue_index == queue_index@pre && dp == dp@pre &&
                buy_cap == buy_l[i - 1] && ask_price == ap_l[i - 1] &&
                1 <= i && i <= days@pre &&
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockDaysDone(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i + 1) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
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
            queue_index == queue_index@pre && dp == dp@pre &&
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
            StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
            StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
            StockSellQueue(dp_l, queue_l, source_day, bid_price,
                           j + 2, j + sell_cap + 1, head, tail) &&
            IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueueExpiring(dp_l, queue_l, source_day, bid_price,
                                       j + 2, j + sell_cap, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            while (head < tail && queue_index[head] - sell_cap > j) {
                ++head;
            }
            /*@ Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 2, j + sell_cap, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (*(dp + source_day * width + (j + 1)) != neg_inf) {
            int last_index = j + 1;
            if (head < tail) {
                last_index = queue_index[tail - 1];
            }
            int incoming_score = *(dp + source_day * width + (j + 1)) + (j + 1) * bid_price;
            /*@ Inv Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueuePopping(dp_l, queue_l, source_day, bid_price,
                                      j + 1, j + sell_cap, head, tail) &&
                (forall (pos : Z), (head <= pos && pos < tail) =>
                    (0 <= queue_l[pos] && queue_l[pos] <= max_stock@pre)) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            while (head < tail &&
                   *(dp + source_day * width + last_index) +
                       last_index * bid_price <= incoming_score) {
                --tail;
                if (head < tail) {
                    last_index = queue_index[tail - 1];
                }
            }
            /*@ Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
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
                0 <= source_day && source_day < i &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                0 <= bid_price && bid_price <= 1000 &&
                0 <= j && j < max_stock@pre &&
                0 <= head && head <= tail &&
                tail <= max_stock@pre - j - 1 &&
                Zlength(queue_l) == width &&
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueuePending(dp_l, queue_l, source_day, bid_price,
                                      j + 1, j + sell_cap, head, tail) &&
                store(&last_index, last_index) *
                store(&incoming_score, incoming_score) *
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            queue_index[tail] = j + 1;
            ++tail;
            /*@ Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                store(&last_index, last_index) *
                store(&incoming_score, incoming_score) *
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            }
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 && width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                queue_index == queue_index@pre && dp == dp@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                wait_days@pre < i - 1 &&
                1 <= i && i <= days@pre && 0 <= source_day && source_day < i &&
                0 <= j && j < max_stock@pre &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                0 <= head && head <= tail &&
                tail <= max_stock@pre - j &&
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockSellProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                sell_candidate == dp_l[source_day][best_index] + best_index * bid_price - j * bid_price &&
                StockSellQueue(dp_l, queue_l, source_day, bid_price,
                               j + 1, j + sell_cap, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
            queue_index == queue_index@pre && dp == dp@pre &&
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
            StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
            StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
            StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                          j - buy_cap - 1, j - 2, head, tail) &&
            IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
        */
        for (int j = 1; j <= max_stock; ++j) {
            /*@ Inv Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueueExpiring(dp_l, queue_l, source_day, ask_price,
                                      j - buy_cap, j - 2, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 2, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (*(dp + source_day * width + (j - 1)) != neg_inf) {
            int last_index = j - 1;
            if (head < tail) {
                last_index = queue_index[tail - 1];
            }
            int incoming_score = *(dp + source_day * width + (j - 1)) + (j - 1) * ask_price;
            /*@ Inv Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueuePopping(dp_l, queue_l, source_day, ask_price,
                                     j - buy_cap, j - 1, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            while (head < tail &&
                   *(dp + source_day * width + last_index) +
                       last_index * ask_price <= incoming_score) {
                --tail;
                if (head < tail) {
                    last_index = queue_index[tail - 1];
                }
            }
            /*@ Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
                neg_inf == -1000000000 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                width == max_stock@pre + 1 &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= j && j <= max_stock@pre &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                0 <= head && head <= tail && tail <= j - 1 &&
                Zlength(queue_l) == width &&
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueuePending(dp_l, queue_l, source_day, ask_price,
                                     j - buy_cap, j - 1, head, tail) &&
                store(&last_index, last_index) *
                store(&incoming_score, incoming_score) *
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            queue_index[tail] = j - 1;
            ++tail;
            /*@ Assert
                exists queue_l dp_l,
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                store(&last_index, last_index) *
                store(&incoming_score, incoming_score) *
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            }
            /*@ Assert
                exists queue_l dp_l,
                neg_inf == -1000000000 && width == max_stock@pre + 1 &&
                days == days@pre && max_stock == max_stock@pre &&
                wait_days == wait_days@pre &&
                ap == ap@pre && bp == bp@pre &&
                buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
                queue_index == queue_index@pre && dp == dp@pre &&
                1 <= days@pre && days@pre <= 990 &&
                1 <= max_stock@pre && max_stock@pre <= 990 &&
                0 <= wait_days@pre && wait_days@pre < days@pre &&
                1 <= i && i <= days@pre && 0 <= source_day && source_day < i &&
                1 <= j && j <= max_stock@pre &&
                bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
                ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
                0 <= head && head <= tail && tail <= j &&
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
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
                queue_index == queue_index@pre && dp == dp@pre &&
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
                StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
                StockBuyProgress(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i, source_day, j) &&
                buy_candidate == dp_l[source_day][best_index] + best_index * ask_price - j * ask_price &&
                StockBuyQueue(dp_l, queue_l, source_day, ask_price,
                              j - buy_cap, j - 1, head, tail) &&
                IntArray::full(ap, days@pre, ap_l) *
                IntArray::full(bp, days@pre, bp_l) *
                IntArray::full(buy_limit, days@pre, buy_l) *
                IntArray::full(sell_limit, days@pre, sell_l) *
                IntArray::full(queue_index, width, queue_l) *
                StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
             */
            if (buy_candidate > *(dp + i * width + j)) {
                *(dp + i * width + j) = buy_candidate;
            }
            }
        }
        /*@ Assert
            exists queue_l dp_l,
            neg_inf == -1000000000 &&
            width == max_stock@pre + 1 &&
            days == days@pre && max_stock == max_stock@pre &&
            wait_days == wait_days@pre &&
            ap == ap@pre && bp == bp@pre &&
            buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
            queue_index == queue_index@pre && dp == dp@pre &&
            1 <= i && i <= days@pre &&
            0 <= wait_days@pre && wait_days@pre < days@pre &&
            source_day == i - wait_days@pre - 1 &&
            bid_price == bp_l[i - 1] && sell_cap == sell_l[i - 1] &&
            0 <= bid_price && bid_price <= 1000 &&
            0 <= sell_cap && sell_cap <= max_stock@pre &&
            ask_price == ap_l[i - 1] && buy_cap == buy_l[i - 1] &&
            0 <= head && head <= tail && tail <= max_stock@pre &&
            StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
            StockDaysDone(ap_l, bp_l, buy_l, sell_l, dp_l, max_stock@pre, wait_days@pre, i + 1) &&
            IntArray::full(ap, days@pre, ap_l) *
            IntArray::full(bp, days@pre, bp_l) *
            IntArray::full(buy_limit, days@pre, buy_l) *
            IntArray::full(sell_limit, days@pre, sell_l) *
            IntArray::full(queue_index, width, queue_l) *
            StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
         */
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
        queue_index == queue_index@pre && dp == dp@pre &&
        1 <= days@pre && days@pre <= 990 &&
        1 <= max_stock@pre && max_stock@pre <= 990 &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        0 <= j && j <= max_stock@pre + 1 &&
        0 <= answer && answer <= 1000000000 &&
        StockInputsBounded(ap_l, bp_l, buy_l, sell_l, days@pre, max_stock@pre) &&
        StockAnswerProgress(ap_l, bp_l, buy_l, sell_l, dp_l, days@pre, max_stock@pre, wait_days@pre, j, answer) &&
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        StockTableShape(dp_l, days@pre, max_stock@pre) && IntArray2::full(dp, days@pre + 1, width, dp_l)
     */
    for (int j = 0; j <= max_stock; ++j) {
        if (*(dp + days * width + j) > answer) {
            answer = *(dp + days * width + j);
        }
    }
    /*@ Assert
        exists queue_l dp_l,
        neg_inf == -1000000000 &&
        days == days@pre && max_stock == max_stock@pre &&
        wait_days == wait_days@pre &&
        ap == ap@pre && bp == bp@pre &&
        buy_limit == buy_limit@pre && sell_limit == sell_limit@pre &&
        queue_index == queue_index@pre && dp == dp@pre &&
        0 <= wait_days@pre && wait_days@pre < days@pre &&
        width == max_stock@pre + 1 &&
        StockMaximumProfit(ap_l, bp_l, buy_l, sell_l,
                           days@pre, max_stock@pre, wait_days@pre, answer) &&
        0 <= answer && answer <= 1000000000 &&
        IntArray::full(ap, days@pre, ap_l) *
        IntArray::full(bp, days@pre, bp_l) *
        IntArray::full(buy_limit, days@pre, buy_l) *
        IntArray::full(sell_limit, days@pre, sell_l) *
        IntArray::full(queue_index, width, queue_l) *
        StockTableShape(dp_l, days@pre, max_stock@pre) &&
        IntArray2::full(dp, days@pre + 1, width, dp_l)
     */
    return answer;
}
