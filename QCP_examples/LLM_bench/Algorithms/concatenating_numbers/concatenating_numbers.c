#include "array2_def.h"

/*@ Extern Coq
      (concat : {A} -> list (list A) -> list A)
      (DecimalRowValues : list (list Z) -> list Z -> list Z)
      (sum : list Z -> Z)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (eq : {A} -> A -> A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (hd : {A} -> A -> list A -> A)
      (concatenate_rows : list (list Z) -> list Z -> list Z)
      (FlatRows : list Z -> list (list Z) -> Z -> Z -> Prop)
      (PairedPermutation : list (list Z) -> list (list Z) -> list Z -> list Z -> Prop)
      (SameOutsidePairedRange : list (list Z) -> list (list Z) -> list Z -> list Z -> Z -> Z -> Prop)
      (ConcatComparePrefix : list (list Z) -> list Z -> Z -> Z -> Z -> Prop)
      (ConcatCompareOutcome : list (list Z) -> list Z -> Z -> Z -> Z -> Prop)
      (ConcatLeftDigit : list (list Z) -> list Z -> Z -> Z -> Z -> Z)
      (ConcatRightDigit : list (list Z) -> list Z -> Z -> Z -> Z -> Z)
      (SwapRowsPrefix : list (list Z) -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (PartitionScanState : list (list Z) -> list (list Z) -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (GreedyPartitionedAt : list (list Z) -> list Z -> Z -> Z -> Z -> Prop)
      (GreedySortedRange : list (list Z) -> list Z -> Z -> Z -> Prop)
      (GreedySorted : list (list Z) -> list Z -> Prop)
      (ConcatenatedPrefix : list (list Z) -> list Z -> Z -> list Z)
      (ConcatenatedOutputPrefix : list (list Z) -> list Z -> Z -> Z -> list Z)
      (LargestConcatenation : list (list Z) -> list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib */

/*
 * Sort a contiguous row-major matrix of decimal digits in descending greedy
 * order.  Row i starts at numbers + i * number_width, and lengths[i] records
 * the number of valid digits in that row.
 */
void quicksort_numbers(int *numbers, int *lengths, int count,
                       int number_width, int low, int high)
/*@ With (rows : list (list Z)) (lens : list Z) (flat : list Z)
    Require
      1 <= count && count <= 20 &&
      1 <= number_width && number_width <= 10 &&
      0 <= low && low <= count && -1 <= high && high < count &&
      1 <= sum(lens) && sum(lens) <= 200 &&
      Zlength(rows) == count &&
      Zlength(lens) == count &&
      Forall(eq(number_width), map(Zlength, rows)) &&
      Forall(Z::le(1), lens) &&
      Forall(Z::ge(number_width), lens) &&
      Forall(Z::le(1), map(hd(0), rows)) &&
      Forall(Z::ge(9), map(hd(0), rows)) &&
      Forall(Z::le(0), concatenate_rows(rows, lens)) &&
      Forall(Z::ge(9), concatenate_rows(rows, lens)) &&
      FlatRows(flat, rows, count, number_width) &&
      IntArray::full(numbers, count * number_width, flat) *
      IntArray::full(lengths, count, lens)
    Ensure
      exists rows1 lens1 flat1,
        FlatRows(flat1, rows1, count, number_width) &&
        PairedPermutation(rows, rows1, lens, lens1) &&
        SameOutsidePairedRange(rows, rows1, lens, lens1, low, high) &&
        GreedySortedRange(rows1, lens1, low, high) &&
        IntArray::full(numbers, count * number_width, flat1) *
        IntArray::full(lengths, count, lens1)
 */
{
    if (0 <= low && low < high && high < count) {
        int pivot_length = lengths[high];
        int boundary = low - 1;
        int scan;
        int pivot;

        /*@ Inv Assert
            exists rows1 lens1 flat1,
              numbers == numbers@pre && lengths == lengths@pre &&
              count == count@pre && number_width == number_width@pre &&
              low == low@pre && high == high@pre &&
              0 <= high@pre * number_width@pre &&
              high@pre * number_width@pre + number_width@pre <=
                count@pre * number_width@pre &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
              low@pre - 1 <= boundary && boundary < scan &&
              low@pre <= scan && scan <= high@pre &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              pivot_length == Znth(high@pre, lens1, 0) &&
              1 <= pivot_length && pivot_length <= number_width@pre &&
              Zlength(rows1) == count@pre &&
              Zlength(lens1) == count@pre &&
              Forall(eq(number_width@pre), map(Zlength, rows1)) &&
              Forall(Z::le(1), lens1) &&
              Forall(Z::ge(number_width@pre), lens1) &&
              Forall(Z::le(1), map(hd(0), rows1)) &&
              Forall(Z::ge(9), map(hd(0), rows1)) &&
              Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
              Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
              PartitionScanState(rows, rows1, lens, lens1,
                                 low@pre, high@pre, boundary, scan) &&
              sum(lens1) == sum(lens) &&
              FlatRows(flat1, rows1, count@pre, number_width@pre) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
              IntArray::full(lengths@pre, count@pre, lens1) *
              has_int_permission(&pivot)
         */
        for (scan = low; scan < high; ++scan) {
            int current_length = lengths[scan];
            int total_length = current_length + pivot_length;
            int comparison = 0;
            int position;

            /* Compare current+pivot with pivot+current without constructing
             * either temporary concatenation. */
            /*@ Inv Assert
                exists rows1 lens1 flat1,
                  numbers == numbers@pre && lengths == lengths@pre &&
                  count == count@pre && number_width == number_width@pre &&
                  low == low@pre && high == high@pre &&
                  0 <= scan * number_width@pre &&
                  scan * number_width@pre + number_width@pre <=
                    count@pre * number_width@pre &&
                  0 <= high@pre * number_width@pre &&
                  high@pre * number_width@pre + number_width@pre <=
                    count@pre * number_width@pre &&
                  1 <= count@pre && count@pre <= 20 &&
                  1 <= number_width@pre && number_width@pre <= 10 &&
                  0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
                  low@pre - 1 <= boundary && boundary < scan &&
                  low@pre <= scan && scan < high@pre &&
                  1 <= sum(lens) && sum(lens) <= 200 &&
                  pivot_length == Znth(high@pre, lens1, 0) &&
                  current_length == Znth(scan, lens1, 0) &&
                  1 <= current_length && current_length <= number_width@pre &&
                  1 <= pivot_length && pivot_length <= number_width@pre &&
                  total_length == current_length + pivot_length &&
                  comparison == 0 &&
                  0 <= position && position <= total_length &&
                  Zlength(rows1) == count@pre &&
                  Zlength(lens1) == count@pre &&
                  Forall(eq(number_width@pre), map(Zlength, rows1)) &&
                  Forall(Z::le(1), lens1) &&
                  Forall(Z::ge(number_width@pre), lens1) &&
                  Forall(Z::le(1), map(hd(0), rows1)) &&
                  Forall(Z::ge(9), map(hd(0), rows1)) &&
                  Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
                  Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
                  PartitionScanState(rows, rows1, lens, lens1,
                                     low@pre, high@pre, boundary, scan) &&
                  ConcatComparePrefix(rows1, lens1, scan, high@pre, position) &&
                  sum(lens1) == sum(lens) &&
                  FlatRows(flat1, rows1, count@pre, number_width@pre) &&
                  IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
                  IntArray::full(lengths@pre, count@pre, lens1) *
                  has_int_permission(&pivot)
             */
            for (position = 0; position < total_length; ++position) {
                int left_digit;
                int right_digit;

                if (position < current_length) {
                    left_digit = numbers[scan * number_width + position];
                } else {
                    left_digit = numbers[high * number_width +
                                         (position - current_length)];
                }

                /*@ Assert
                    exists rows1 lens1 flat1,
                      numbers == numbers@pre && lengths == lengths@pre &&
                      count == count@pre && number_width == number_width@pre &&
                      low == low@pre && high == high@pre &&
                      0 <= scan * number_width@pre &&
                      scan * number_width@pre + number_width@pre <=
                        count@pre * number_width@pre &&
                      0 <= high@pre * number_width@pre &&
                      high@pre * number_width@pre + number_width@pre <=
                        count@pre * number_width@pre &&
                      1 <= count@pre && count@pre <= 20 &&
                      1 <= number_width@pre && number_width@pre <= 10 &&
                      0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
                      low@pre - 1 <= boundary && boundary < scan &&
                      low@pre <= scan && scan < high@pre &&
                      1 <= sum(lens) && sum(lens) <= 200 &&
                      pivot_length == Znth(high@pre, lens1, 0) &&
                      current_length == Znth(scan, lens1, 0) &&
                      1 <= current_length && current_length <= number_width@pre &&
                      1 <= pivot_length && pivot_length <= number_width@pre &&
                      total_length == current_length + pivot_length &&
                      comparison == 0 &&
                      0 <= position && position < total_length &&
                      left_digit == ConcatLeftDigit(rows1, lens1, scan,
                                                   high@pre, position) &&
                      Zlength(rows1) == count@pre &&
                      Zlength(lens1) == count@pre &&
                      Forall(eq(number_width@pre), map(Zlength, rows1)) &&
                      Forall(Z::le(1), lens1) &&
                      Forall(Z::ge(number_width@pre), lens1) &&
                      Forall(Z::le(1), map(hd(0), rows1)) &&
                      Forall(Z::ge(9), map(hd(0), rows1)) &&
                      Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
                      Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
                      PartitionScanState(rows, rows1, lens, lens1,
                                         low@pre, high@pre, boundary, scan) &&
                      ConcatComparePrefix(rows1, lens1, scan, high@pre, position) &&
                      sum(lens1) == sum(lens) &&
                      FlatRows(flat1, rows1, count@pre, number_width@pre) &&
                      IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
                      IntArray::full(lengths@pre, count@pre, lens1) *
                      has_int_permission(&right_digit) *
                      has_int_permission(&pivot)
                 */

                if (position < pivot_length) {
                    right_digit = numbers[high * number_width + position];
                } else {
                    right_digit = numbers[scan * number_width +
                                          (position - pivot_length)];
                }

                /*@ Assert
                    exists rows1 lens1 flat1,
                      numbers == numbers@pre && lengths == lengths@pre &&
                      count == count@pre && number_width == number_width@pre &&
                      low == low@pre && high == high@pre &&
                      0 <= scan * number_width@pre &&
                      scan * number_width@pre + number_width@pre <=
                        count@pre * number_width@pre &&
                      0 <= high@pre * number_width@pre &&
                      high@pre * number_width@pre + number_width@pre <=
                        count@pre * number_width@pre &&
                      1 <= count@pre && count@pre <= 20 &&
                      1 <= number_width@pre && number_width@pre <= 10 &&
                      0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
                      low@pre - 1 <= boundary && boundary < scan &&
                      low@pre <= scan && scan < high@pre &&
                      1 <= sum(lens) && sum(lens) <= 200 &&
                      pivot_length == Znth(high@pre, lens1, 0) &&
                      current_length == Znth(scan, lens1, 0) &&
                      1 <= current_length && current_length <= number_width@pre &&
                      1 <= pivot_length && pivot_length <= number_width@pre &&
                      total_length == current_length + pivot_length &&
                      comparison == 0 &&
                      0 <= position && position < total_length &&
                      left_digit == ConcatLeftDigit(rows1, lens1, scan,
                                                   high@pre, position) &&
                      right_digit == ConcatRightDigit(rows1, lens1, scan,
                                                     high@pre, position) &&
                      Zlength(rows1) == count@pre &&
                      Zlength(lens1) == count@pre &&
                      Forall(eq(number_width@pre), map(Zlength, rows1)) &&
                      Forall(Z::le(1), lens1) &&
                      Forall(Z::ge(number_width@pre), lens1) &&
                      Forall(Z::le(1), map(hd(0), rows1)) &&
                      Forall(Z::ge(9), map(hd(0), rows1)) &&
                      Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
                      Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
                      PartitionScanState(rows, rows1, lens, lens1,
                                         low@pre, high@pre, boundary, scan) &&
                      ConcatComparePrefix(rows1, lens1, scan, high@pre, position) &&
                      sum(lens1) == sum(lens) &&
                      FlatRows(flat1, rows1, count@pre, number_width@pre) &&
                      IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
                      IntArray::full(lengths@pre, count@pre, lens1) *
                      has_int_permission(&pivot)
                 */

                if (left_digit != right_digit) {
                    comparison = left_digit - right_digit;
                    break;
                }
            }

            /*@ Assert
                exists rows1 lens1 flat1,
                  numbers == numbers@pre && lengths == lengths@pre &&
                  count == count@pre && number_width == number_width@pre &&
                  low == low@pre && high == high@pre &&
                  0 <= scan * number_width@pre &&
                  scan * number_width@pre + number_width@pre <=
                    count@pre * number_width@pre &&
                  0 <= high@pre * number_width@pre &&
                  high@pre * number_width@pre + number_width@pre <=
                    count@pre * number_width@pre &&
                  1 <= count@pre && count@pre <= 20 &&
                  1 <= number_width@pre && number_width@pre <= 10 &&
                  0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
                  low@pre - 1 <= boundary && boundary < scan &&
                  low@pre <= scan && scan < high@pre &&
                  1 <= sum(lens) && sum(lens) <= 200 &&
                  pivot_length == Znth(high@pre, lens1, 0) &&
                  current_length == Znth(scan, lens1, 0) &&
                  1 <= current_length && current_length <= number_width@pre &&
                  1 <= pivot_length && pivot_length <= number_width@pre &&
                  total_length == current_length + pivot_length &&
                  Zlength(rows1) == count@pre &&
                  Zlength(lens1) == count@pre &&
                  Forall(eq(number_width@pre), map(Zlength, rows1)) &&
                  Forall(Z::le(1), lens1) &&
                  Forall(Z::ge(number_width@pre), lens1) &&
                  Forall(Z::le(1), map(hd(0), rows1)) &&
                  Forall(Z::ge(9), map(hd(0), rows1)) &&
                  Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
                  Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
                  PartitionScanState(rows, rows1, lens, lens1,
                                     low@pre, high@pre, boundary, scan) &&
                  ConcatCompareOutcome(rows1, lens1, scan, high@pre, comparison) &&
                  sum(lens1) == sum(lens) &&
                  FlatRows(flat1, rows1, count@pre, number_width@pre) &&
                  IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
                  IntArray::full(lengths@pre, count@pre, lens1) *
                  has_int_permission(&position) *
                  has_int_permission(&pivot)
             */

            if (comparison > 0) {
                int column;
                int temporary_length;

                ++boundary;
                /*@ Inv Assert
                    exists rows_before rows_now lens1 flat_now,
                      numbers == numbers@pre && lengths == lengths@pre &&
                      count == count@pre && number_width == number_width@pre &&
                      low == low@pre && high == high@pre &&
                      0 <= boundary * number_width@pre &&
                      boundary * number_width@pre + number_width@pre <=
                        count@pre * number_width@pre &&
                      0 <= scan * number_width@pre &&
                      scan * number_width@pre + number_width@pre <=
                        count@pre * number_width@pre &&
                      0 <= high@pre * number_width@pre &&
                      high@pre * number_width@pre + number_width@pre <=
                        count@pre * number_width@pre &&
                      1 <= count@pre && count@pre <= 20 &&
                      1 <= number_width@pre && number_width@pre <= 10 &&
                      0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
                      low@pre <= boundary && boundary <= scan && scan < high@pre &&
                      0 <= column && column <= number_width@pre &&
                      1 <= sum(lens) && sum(lens) <= 200 &&
                      pivot_length == Znth(high@pre, lens1, 0) &&
                      1 <= pivot_length && pivot_length <= number_width@pre &&
                      Zlength(rows_before) == count@pre &&
                      Zlength(lens1) == count@pre &&
                      Forall(eq(number_width@pre), map(Zlength, rows_before)) &&
                      Forall(Z::le(1), lens1) &&
                      Forall(Z::ge(number_width@pre), lens1) &&
                      Forall(Z::le(1), map(hd(0), rows_before)) &&
                      Forall(Z::ge(9), map(hd(0), rows_before)) &&
                      Forall(Z::le(0), concatenate_rows(rows_before, lens1)) &&
                      Forall(Z::ge(9), concatenate_rows(rows_before, lens1)) &&
                      PartitionScanState(rows, rows_before, lens, lens1,
                                         low@pre, high@pre, boundary - 1, scan) &&
                      ConcatCompareOutcome(rows_before, lens1, scan, high@pre, comparison) &&
                      comparison > 0 &&
                      SwapRowsPrefix(rows_before, rows_now, boundary, scan,
                                     column, number_width@pre) &&
                      sum(lens1) == sum(lens) &&
                      FlatRows(flat_now, rows_now, count@pre, number_width@pre) &&
                      IntArray::full(numbers@pre, count@pre * number_width@pre, flat_now) *
                      IntArray::full(lengths@pre, count@pre, lens1) *
                      has_int_permission(&current_length) *
                      has_int_permission(&total_length) *
                      has_int_permission(&position) *
                      has_int_permission(&temporary_length) *
                      has_int_permission(&pivot)
                 */
                for (column = 0; column < number_width; ++column) {
                    int temporary_digit =
                        numbers[boundary * number_width + column];
                    numbers[boundary * number_width + column] =
                        numbers[scan * number_width + column];
                    numbers[scan * number_width + column] = temporary_digit;
                }

                temporary_length = lengths[boundary];
                lengths[boundary] = lengths[scan];
                lengths[scan] = temporary_length;
            }

            /*@ Assert
                exists rows1 lens1 flat1,
                  numbers == numbers@pre && lengths == lengths@pre &&
                  count == count@pre && number_width == number_width@pre &&
                  low == low@pre && high == high@pre &&
                  0 <= high@pre * number_width@pre &&
                  high@pre * number_width@pre + number_width@pre <=
                    count@pre * number_width@pre &&
                  1 <= count@pre && count@pre <= 20 &&
                  1 <= number_width@pre && number_width@pre <= 10 &&
                  0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
                  low@pre - 1 <= boundary && boundary <= scan && scan < high@pre &&
                  1 <= sum(lens) && sum(lens) <= 200 &&
                  pivot_length == Znth(high@pre, lens1, 0) &&
                  1 <= pivot_length && pivot_length <= number_width@pre &&
                  Zlength(rows1) == count@pre &&
                  Zlength(lens1) == count@pre &&
                  Forall(eq(number_width@pre), map(Zlength, rows1)) &&
                  Forall(Z::le(1), lens1) &&
                  Forall(Z::ge(number_width@pre), lens1) &&
                  Forall(Z::le(1), map(hd(0), rows1)) &&
                  Forall(Z::ge(9), map(hd(0), rows1)) &&
                  Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
                  Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
                  PartitionScanState(rows, rows1, lens, lens1,
                                     low@pre, high@pre, boundary, scan + 1) &&
                  sum(lens1) == sum(lens) &&
                  FlatRows(flat1, rows1, count@pre, number_width@pre) &&
                  IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
                  IntArray::full(lengths@pre, count@pre, lens1) *
                  has_int_permission(&current_length) *
                  has_int_permission(&total_length) *
                  has_int_permission(&comparison) *
                  has_int_permission(&position) *
                  has_int_permission(&pivot)
             */
        }

        pivot = boundary + 1;
        /*@ Inv Assert
            exists rows_before rows_now lens1 flat_now,
              numbers == numbers@pre && lengths == lengths@pre &&
              count == count@pre && number_width == number_width@pre &&
              low == low@pre && high == high@pre &&
              0 <= pivot * number_width@pre &&
              pivot * number_width@pre + number_width@pre <=
                count@pre * number_width@pre &&
              0 <= high@pre * number_width@pre &&
              high@pre * number_width@pre + number_width@pre <=
                count@pre * number_width@pre &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
              low@pre <= pivot && pivot <= high@pre &&
              0 <= column && column <= number_width@pre &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              pivot_length == Znth(high@pre, lens1, 0) &&
              1 <= pivot_length && pivot_length <= number_width@pre &&
              Zlength(rows_before) == count@pre &&
              Zlength(lens1) == count@pre &&
              Forall(eq(number_width@pre), map(Zlength, rows_before)) &&
              Forall(Z::le(1), lens1) &&
              Forall(Z::ge(number_width@pre), lens1) &&
              Forall(Z::le(1), map(hd(0), rows_before)) &&
              Forall(Z::ge(9), map(hd(0), rows_before)) &&
              Forall(Z::le(0), concatenate_rows(rows_before, lens1)) &&
              Forall(Z::ge(9), concatenate_rows(rows_before, lens1)) &&
              PartitionScanState(rows, rows_before, lens, lens1,
                                 low@pre, high@pre, pivot - 1, high@pre) &&
              SwapRowsPrefix(rows_before, rows_now, pivot, high@pre,
                             column, number_width@pre) &&
              sum(lens1) == sum(lens) &&
              FlatRows(flat_now, rows_now, count@pre, number_width@pre) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat_now) *
              IntArray::full(lengths@pre, count@pre, lens1) *
              has_int_permission(&scan) *
              has_int_permission(&boundary)
         */
        for (int column = 0; column < number_width; ++column) {
            int temporary_digit =
                numbers[pivot * number_width + column];
            numbers[pivot * number_width + column] =
                numbers[high * number_width + column];
            numbers[high * number_width + column] = temporary_digit;
        }

        lengths[high] = lengths[pivot];
        lengths[pivot] = pivot_length;

        /*@ Assert
            exists rows1 lens1 flat1,
              numbers == numbers@pre && lengths == lengths@pre &&
              count == count@pre && number_width == number_width@pre &&
              low == low@pre && high == high@pre &&
              0 <= pivot * number_width@pre &&
              pivot * number_width@pre + number_width@pre <=
                count@pre * number_width@pre &&
              0 <= high@pre * number_width@pre &&
              high@pre * number_width@pre + number_width@pre <=
                count@pre * number_width@pre &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              0 <= low@pre && low@pre < high@pre && high@pre < count@pre &&
              low@pre <= pivot && pivot <= high@pre &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              Zlength(rows1) == count@pre &&
              Zlength(lens1) == count@pre &&
              Forall(eq(number_width@pre), map(Zlength, rows1)) &&
              Forall(Z::le(1), lens1) &&
              Forall(Z::ge(number_width@pre), lens1) &&
              Forall(Z::le(1), map(hd(0), rows1)) &&
              Forall(Z::ge(9), map(hd(0), rows1)) &&
              Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
              Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
              PairedPermutation(rows, rows1, lens, lens1) &&
              SameOutsidePairedRange(rows, rows1, lens, lens1, low@pre, high@pre) &&
              GreedyPartitionedAt(rows1, lens1, low@pre, high@pre, pivot) &&
              sum(lens1) == sum(lens) &&
              FlatRows(flat1, rows1, count@pre, number_width@pre) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
              IntArray::full(lengths@pre, count@pre, lens1) *
              has_int_permission(&scan) *
              has_int_permission(&boundary) *
              has_int_permission(&pivot_length)
         */
        /*@ Given rows1 lens1 flat1 */
        if (pivot > low) {
            quicksort_numbers(numbers, lengths, count, number_width,
                              low, pivot - 1) /*@ where rows = rows1, lens = lens1, flat = flat1 @mark left_sort */;
            /*@ Given rows2 from rows1 of left_sort
                      lens2 from lens1 of left_sort
                      flat2 from flat1 of left_sort */
            if (pivot < high) {
                quicksort_numbers(numbers, lengths, count, number_width,
                                  pivot + 1, high) /*@ where rows = rows2, lens = lens2, flat = flat2 */;
            }
        } else if (pivot < high) {
            quicksort_numbers(numbers, lengths, count, number_width,
                              pivot + 1, high) /*@ where rows = rows1, lens = lens1, flat = flat1 */;
        }
    }
}

/*
 * numbers contains count rows of number_width integer cells.  Each row holds
 * one positive integer as decimal digits in 0..9.  result receives the largest
 * possible concatenation and the return value is result itself.
 */
int* concatenating_numbers(int *numbers, int count, int number_width,
                          int *lengths, int *result)
/*@ With (rows : list (list Z)) (lens : list Z) (flat : list Z)
    Require
      1 <= count && count <= 20 &&
      1 <= number_width && number_width <= 10 &&
      1 <= sum(lens) && sum(lens) <= 200 &&
      Zlength(rows) == count &&
      Zlength(lens) == count &&
      Forall(eq(number_width), map(Zlength, rows)) &&
      Forall(Z::le(1), lens) &&
      Forall(Z::ge(number_width), lens) &&
      Forall(Z::le(1), map(hd(0), rows)) &&
      Forall(Z::ge(9), map(hd(0), rows)) &&
      Forall(Z::le(0), concatenate_rows(rows, lens)) &&
      Forall(Z::ge(9), concatenate_rows(rows, lens)) &&
      flat == concat(rows) &&
      Forall(Z::ge(1000000000), DecimalRowValues(rows, lens)) &&
      IntArray2::full(numbers, count, number_width, rows) *
      IntArray::full(lengths, count, lens) *
      IntArray::undef_full(result, sum(lens))
    Ensure
      exists lens1 rows1 output,
        __return == result &&
        LargestConcatenation(rows, lens, output) &&
        IntArray2::full(numbers, count, number_width, rows1) *
        IntArray::full(lengths, count, lens1) *
        IntArray::full(result, sum(lens), output)
 */
{
    /* The public matrix resource is viewed linearly by the established helpers. */
    /*@ Assert
      numbers == numbers@pre && lengths == lengths@pre &&
      result == result@pre && count == count@pre && number_width == number_width@pre &&
      1 <= count && count <= 20 &&
      1 <= number_width && number_width <= 10 &&
      1 <= sum(lens) && sum(lens) <= 200 &&
      Zlength(rows) == count &&
      Zlength(lens) == count &&
      Forall(eq(number_width), map(Zlength, rows)) &&
      Forall(Z::le(1), lens) &&
      Forall(Z::ge(number_width), lens) &&
      Forall(Z::le(1), map(hd(0), rows)) &&
      Forall(Z::ge(9), map(hd(0), rows)) &&
      Forall(Z::le(0), concatenate_rows(rows, lens)) &&
      Forall(Z::ge(9), concatenate_rows(rows, lens)) &&
      FlatRows(flat, rows, count, number_width) &&
      IntArray::full(numbers, count * number_width, flat) *
      IntArray::full(lengths, count, lens) *
      IntArray::undef_full(result, sum(lens))
    */

    int result_length = 0;
    int i;

    if (count > 1) {
        quicksort_numbers(numbers, lengths, count, number_width,
                          0, count - 1) /*@ where rows = rows, lens = lens, flat = flat */;
    }

    /*@ Inv Assert
        exists rows1 lens1 flat1 output,
          numbers == numbers@pre && lengths == lengths@pre &&
          result == result@pre && count == count@pre &&
          number_width == number_width@pre &&
          1 <= count@pre && count@pre <= 20 &&
          1 <= number_width@pre && number_width@pre <= 10 &&
          1 <= sum(lens) && sum(lens) <= 200 &&
          0 <= i && i <= count@pre &&
          Zlength(rows1) == count@pre &&
          Zlength(lens1) == count@pre &&
          Forall(eq(number_width@pre), map(Zlength, rows1)) &&
          Forall(Z::le(1), lens1) &&
          Forall(Z::ge(number_width@pre), lens1) &&
          Forall(Z::le(1), map(hd(0), rows1)) &&
          Forall(Z::ge(9), map(hd(0), rows1)) &&
          Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
          Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
          PairedPermutation(rows, rows1, lens, lens1) &&
          GreedySorted(rows1, lens1) &&
          sum(lens1) == sum(lens) &&
          output == ConcatenatedPrefix(rows1, lens1, i) &&
          result_length == Zlength(output) &&
          0 <= result_length && result_length <= sum(lens) &&
          FlatRows(flat1, rows1, count@pre, number_width@pre) &&
          IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
          IntArray::full(lengths@pre, count@pre, lens1) *
          IntArray::seg(result@pre, 0, result_length, output) *
          IntArray::undef_seg(result@pre, result_length, sum(lens))
     */
    for (i = 0; i < count; ++i) {
        int j;

        /*@ Inv Assert
            exists rows1 lens1 flat1 output,
              numbers == numbers@pre && lengths == lengths@pre &&
              result == result@pre && count == count@pre &&
              number_width == number_width@pre &&
              0 <= i * number_width@pre &&
              i * number_width@pre + number_width@pre <=
                count@pre * number_width@pre &&
              (j < Znth(i, lens1, 0) => result_length < sum(lens)) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              0 <= i && i < count@pre &&
              0 <= j && j <= Znth(i, lens1, 0) &&
              1 <= Znth(i, lens1, 0) &&
              Znth(i, lens1, 0) <= number_width@pre &&
              Zlength(rows1) == count@pre &&
              Zlength(lens1) == count@pre &&
              Forall(eq(number_width@pre), map(Zlength, rows1)) &&
              Forall(Z::le(1), lens1) &&
              Forall(Z::ge(number_width@pre), lens1) &&
              Forall(Z::le(1), map(hd(0), rows1)) &&
              Forall(Z::ge(9), map(hd(0), rows1)) &&
              Forall(Z::le(0), concatenate_rows(rows1, lens1)) &&
              Forall(Z::ge(9), concatenate_rows(rows1, lens1)) &&
              PairedPermutation(rows, rows1, lens, lens1) &&
              GreedySorted(rows1, lens1) &&
              sum(lens1) == sum(lens) &&
              output == ConcatenatedOutputPrefix(rows1, lens1, i, j) &&
              result_length == Zlength(output) &&
              0 <= result_length && result_length <= sum(lens) &&
              FlatRows(flat1, rows1, count@pre, number_width@pre) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat1) *
              IntArray::full(lengths@pre, count@pre, lens1) *
              IntArray::seg(result@pre, 0, result_length, output) *
              IntArray::undef_seg(result@pre, result_length, sum(lens))
         */
        for (j = 0; j < lengths[i]; ++j) {
            result[result_length] = numbers[i * number_width + j];
            ++result_length;
        }
    }

    return result;
}
