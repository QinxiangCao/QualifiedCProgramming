



/*@ Extern Coq
      (sum : list Z -> Z)
      (Z::shiftl : Z -> Z -> Z)
      (RowsWellFormed : list (list Z) -> list Z -> Z -> Z -> Prop)
      (FlatRows : list Z -> list (list Z) -> Z -> Z -> Prop)
      (ConcatLeftDigit : list (list Z) -> list Z -> Z -> Z -> Z -> Z)
      (ConcatRightDigit : list (list Z) -> list Z -> Z -> Z -> Z -> Z)
      (ConcatComparePrefix : list (list Z) -> list Z -> Z -> Z -> Z -> Prop)
      (ConcatCompareLoopState : list (list Z) -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (ConcatCompareSignOutcome : list (list Z) -> list Z -> Z -> Z -> Z -> Prop)
      (BestIndexForMask : list (list Z) -> list Z -> Z -> Z -> Z -> Prop)
      (DPTablePrefix : list (list Z) -> list Z -> Z -> Z -> list Z -> Prop)
      (BitScanState : Z -> Z -> Z -> Z -> Prop)
      (SelectedBitState : Z -> Z -> Z -> Z -> Z -> Prop)
      (LargestConcatenation : list (list Z) -> list Z -> list Z -> Prop)
      (GreedyOutputPrefix : list (list Z) -> list Z -> Z -> Z -> list Z -> Prop)
      (AppendRowPrefix : list (list Z) -> list Z -> list Z -> Z -> Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_lib */

/*
 * Compare the two possible orders left+right and right+left without building
 * either temporary concatenation.  A positive result means that left should
 * be placed before right in a largest concatenation.
 */
int compare_concatenated_order(const int *numbers, const int *lengths,
                                      int number_width, int left, int right)
/*@ With (rows : list (list Z)) (lens : list Z) (flat : list Z) (count : Z)
    Require
      1 <= count && count <= 20 &&
      1 <= number_width && number_width <= 10 &&
      0 <= left && left < count &&
      0 <= right && right < count &&
      RowsWellFormed(rows, lens, count, number_width) &&
      FlatRows(flat, rows, count, number_width) &&
      IntArray::full(numbers, count * number_width, flat) *
      IntArray::full(lengths, count, lens)
    Ensure
      ConcatCompareSignOutcome(rows, lens, left, right, __return) &&
      IntArray::full(numbers, count * number_width, flat) *
      IntArray::full(lengths, count, lens)
 */
{
    int left_length = lengths[left];
    int right_length = lengths[right];
    int total_length = left_length + right_length;

    /*@ Inv Assert
        numbers == numbers@pre && lengths == lengths@pre &&
        number_width == number_width@pre &&
        left == left@pre && right == right@pre &&
        1 <= count && count <= 20 &&
        1 <= number_width@pre && number_width@pre <= 10 &&
        0 <= left@pre && left@pre < count &&
        0 <= right@pre && right@pre < count &&
        1 <= left_length && left_length <= number_width@pre &&
        1 <= right_length && right_length <= number_width@pre &&
        total_length == left_length + right_length &&
        2 <= total_length && total_length <= 2 * number_width@pre &&
        0 <= position && position <= total_length &&
        RowsWellFormed(rows, lens, count, number_width@pre) &&
        FlatRows(flat, rows, count, number_width@pre) &&
        ConcatCompareLoopState(rows, lens, left@pre, right@pre,
                               left_length, right_length, position) &&
        IntArray::full(numbers@pre, count * number_width@pre, flat) *
        IntArray::full(lengths@pre, count, lens)
     */
    for (int position = 0; position < total_length; ++position) {
        int left_then_right;
        int right_then_left;

        if (position < left_length) {
            /*@ 0 <= position && position < number_width by local */
            /*@ 0 <= left * number_width + position &&
                left * number_width + position < count * number_width by local */
            left_then_right = numbers[left * number_width + position];
        } else {
            /*@ 0 <= position - left_length &&
                position - left_length < number_width by local */
            /*@ 0 <= right * number_width + position - left_length &&
                right * number_width + position - left_length <
                  count * number_width by local */
            left_then_right =
                numbers[right * number_width + position - left_length];
        }

        /*@ Assert
            numbers == numbers@pre && lengths == lengths@pre &&
            number_width == number_width@pre &&
            left == left@pre && right == right@pre &&
            1 <= count && count <= 20 &&
            1 <= number_width@pre && number_width@pre <= 10 &&
            0 <= left@pre && left@pre < count &&
            0 <= right@pre && right@pre < count &&
            1 <= left_length && left_length <= number_width@pre &&
            1 <= right_length && right_length <= number_width@pre &&
            total_length == left_length + right_length &&
            0 <= position && position < total_length &&
            left_then_right ==
              ConcatLeftDigit(rows, lens, left@pre, right@pre, position) &&
            RowsWellFormed(rows, lens, count, number_width@pre) &&
            FlatRows(flat, rows, count, number_width@pre) &&
            ConcatCompareLoopState(rows, lens, left@pre, right@pre,
                                   left_length, right_length, position) &&
            IntArray::full(numbers@pre, count * number_width@pre, flat) *
            IntArray::full(lengths@pre, count, lens) *
            has_int_permission(&right_then_left)
         */

        if (position < right_length) {
            /*@ 0 <= position && position < number_width by local */
            /*@ 0 <= right * number_width + position &&
                right * number_width + position < count * number_width by local */
            right_then_left = numbers[right * number_width + position];
        } else {
            /*@ 0 <= position - right_length &&
                position - right_length < number_width by local */
            /*@ 0 <= left * number_width + position - right_length &&
                left * number_width + position - right_length <
                  count * number_width by local */
            right_then_left =
                numbers[left * number_width + position - right_length];
        }

        /*@ Assert
            numbers == numbers@pre && lengths == lengths@pre &&
            number_width == number_width@pre &&
            left == left@pre && right == right@pre &&
            1 <= count && count <= 20 &&
            1 <= number_width@pre && number_width@pre <= 10 &&
            0 <= left@pre && left@pre < count &&
            0 <= right@pre && right@pre < count &&
            1 <= left_length && left_length <= number_width@pre &&
            1 <= right_length && right_length <= number_width@pre &&
            total_length == left_length + right_length &&
            0 <= position && position < total_length &&
            left_then_right ==
              ConcatLeftDigit(rows, lens, left@pre, right@pre, position) &&
            right_then_left ==
              ConcatRightDigit(rows, lens, left@pre, right@pre, position) &&
            RowsWellFormed(rows, lens, count, number_width@pre) &&
            FlatRows(flat, rows, count, number_width@pre) &&
            ConcatCompareLoopState(rows, lens, left@pre, right@pre,
                                   left_length, right_length, position) &&
            IntArray::full(numbers@pre, count * number_width@pre, flat) *
            IntArray::full(lengths@pre, count, lens)
         */

        if (left_then_right > right_then_left) {
            return 1;
        }
        if (left_then_right < right_then_left) {
            return -1;
        }
    }

    return 0;
}

/*
 * Build the largest concatenation with subset dynamic programming.
 *
 * numbers contains count rows of number_width integer cells.  Row i stores
 * the decimal digits of one positive integer, and lengths[i] is the number of
 * valid cells in that row.  Digits are stored from most to least significant.
 *
 * best_first must contain at least 2^count integer cells.  For each nonempty
 * mask, best_first[mask] records an index that can be placed first in an
 * optimal concatenation of exactly the rows selected by mask.  Removing that
 * index produces the next subset state.  result must contain at least
 * sum(lengths[0..count)) cells and receives the answer as decimal digits.
 *
 * The exchange rule x+y >= y+x determines which of two rows may occur first
 * in an optimal answer.  Consequently, if bit is one selected index and rest
 * is the mask without bit, the transition is
 *
 *   best_first[mask] = better(bit, best_first[rest]).
 *
 * There are 2^count states.  Finding the selected bit takes at most count
 * steps, and each transition compares at most 2 * number_width digits, so the
 * running time is O(2^count * (count + number_width)).  The DP uses
 * O(2^count) integer cells.
 */
int *concatenating_numbers_dp(const int *numbers, int count, int number_width,
                              const int *lengths, int *best_first,
                              int *result)
/*@ With (rows : list (list Z)) (lens : list Z) (flat : list Z)
    Require
      1 <= count && count <= 20 &&
      1 <= number_width && number_width <= 10 &&
      2 <= Z::shiftl(1, count) && Z::shiftl(1, count) <= 1048576 &&
      1 <= sum(lens) && sum(lens) <= 200 &&
      RowsWellFormed(rows, lens, count, number_width) &&
      FlatRows(flat, rows, count, number_width) &&
      IntArray::full(numbers, count * number_width, flat) *
      IntArray::full(lengths, count, lens) *
      IntArray::undef_full(best_first, Z::shiftl(1, count)) *
      IntArray::undef_full(result, sum(lens))
    Ensure
      exists choices output,
        __return == result &&
        DPTablePrefix(rows, lens, count, Z::shiftl(1, count), choices) &&
        LargestConcatenation(rows, lens, output) &&
        Zlength(output) == sum(lens) &&
        IntArray::full(numbers, count * number_width, flat) *
        IntArray::full(lengths, count, lens) *
        IntArray::full(best_first, Z::shiftl(1, count), choices) *
        IntArray::full(result, sum(lens), output)
 */
{
    int state_count = 1 << count;

    best_first[0] = -1;

    /*@ Inv Assert
        exists choices,
          numbers == numbers@pre && lengths == lengths@pre &&
          best_first == best_first@pre && result == result@pre &&
          count == count@pre && number_width == number_width@pre &&
          state_count == Z::shiftl(1, count@pre) &&
          1 <= count@pre && count@pre <= 20 &&
          1 <= number_width@pre && number_width@pre <= 10 &&
          1 <= sum(lens) && sum(lens) <= 200 &&
          1 <= mask && mask <= state_count &&
          RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
          FlatRows(flat, rows, count@pre, number_width@pre) &&
          Zlength(choices) == mask &&
          DPTablePrefix(rows, lens, count@pre, mask, choices) &&
          IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
          IntArray::full(lengths@pre, count@pre, lens) *
          IntArray::seg(best_first@pre, 0, mask, choices) *
          IntArray::undef_seg(best_first@pre, mask, state_count) *
          IntArray::undef_full(result@pre, sum(lens))
     */
    for (int mask = 1; mask < state_count; ++mask) {
        int bit = 0;
        int bit_value = 1;
        /*@ Inv Assert
            exists choices,
              numbers == numbers@pre && lengths == lengths@pre &&
              best_first == best_first@pre && result == result@pre &&
              count == count@pre && number_width == number_width@pre &&
              state_count == Z::shiftl(1, count@pre) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              1 <= mask && mask < state_count &&
              0 <= bit && bit <= count@pre &&
              1 <= bit_value && bit_value <= state_count &&
              RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
              FlatRows(flat, rows, count@pre, number_width@pre) &&
              Zlength(choices) == mask &&
              DPTablePrefix(rows, lens, count@pre, mask, choices) &&
              BitScanState(mask, count@pre, bit, bit_value) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
              IntArray::full(lengths@pre, count@pre, lens) *
              IntArray::seg(best_first@pre, 0, mask, choices) *
              IntArray::undef_seg(best_first@pre, mask, state_count) *
              IntArray::undef_full(result@pre, sum(lens))
         */
        while ((mask & bit_value) == 0) {
            ++bit;
            bit_value = bit_value << 1;
        }

        int rest = mask ^ bit_value;
        /*@ Assert
            exists choices,
              numbers == numbers@pre && lengths == lengths@pre &&
              best_first == best_first@pre && result == result@pre &&
              count == count@pre && number_width == number_width@pre &&
              state_count == Z::shiftl(1, count@pre) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              1 <= mask && mask < state_count &&
              0 <= bit && bit < count@pre &&
              1 <= bit_value && bit_value < state_count &&
              0 <= rest && rest < mask &&
              RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
              FlatRows(flat, rows, count@pre, number_width@pre) &&
              Zlength(choices) == mask &&
              DPTablePrefix(rows, lens, count@pre, mask, choices) &&
              SelectedBitState(mask, count@pre, bit, bit_value, rest) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
              IntArray::full(lengths@pre, count@pre, lens) *
              IntArray::seg(best_first@pre, 0, mask, choices) *
              IntArray::undef_seg(best_first@pre, mask, state_count) *
              IntArray::undef_full(result@pre, sum(lens))
         */
        int previous_best = best_first[rest];

        /*@ Assert
            (exists choices,
              numbers == numbers@pre && lengths == lengths@pre &&
              best_first == best_first@pre && result == result@pre &&
              count == count@pre && number_width == number_width@pre &&
              state_count == Z::shiftl(1, count@pre) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              1 <= mask && mask < state_count &&
              0 <= bit && bit < count@pre &&
              0 <= rest && rest < mask &&
              Zlength(choices) == mask &&
              previous_best == Znth(rest, choices, 0) &&
              rest == 0 && previous_best == -1 &&
              RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
              FlatRows(flat, rows, count@pre, number_width@pre) &&
              DPTablePrefix(rows, lens, count@pre, mask, choices) &&
              SelectedBitState(mask, count@pre, bit, bit_value, rest) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
              IntArray::full(lengths@pre, count@pre, lens) *
              IntArray::seg(best_first@pre, 0, mask, choices) *
              IntArray::undef_seg(best_first@pre, mask, state_count) *
              IntArray::undef_full(result@pre, sum(lens))) ||
            (exists choices,
              numbers == numbers@pre && lengths == lengths@pre &&
              best_first == best_first@pre && result == result@pre &&
              count == count@pre && number_width == number_width@pre &&
              state_count == Z::shiftl(1, count@pre) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              1 <= mask && mask < state_count &&
              0 <= bit && bit < count@pre &&
              0 <= rest && rest < mask &&
              Zlength(choices) == mask &&
              previous_best == Znth(rest, choices, 0) &&
              1 <= rest &&
              0 <= previous_best && previous_best < count@pre &&
              BestIndexForMask(rows, lens, count@pre, rest, previous_best) &&
              RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
              FlatRows(flat, rows, count@pre, number_width@pre) &&
              DPTablePrefix(rows, lens, count@pre, mask, choices) &&
              SelectedBitState(mask, count@pre, bit, bit_value, rest) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
              IntArray::full(lengths@pre, count@pre, lens) *
              IntArray::seg(best_first@pre, 0, mask, choices) *
              IntArray::undef_seg(best_first@pre, mask, state_count) *
              IntArray::undef_full(result@pre, sum(lens)))
         */

        if (previous_best < 0 ||
            compare_concatenated_order(numbers, lengths, number_width,
                                       bit, previous_best) /*@ where rows = rows, lens = lens, flat = flat, count = count */ > 0) {
            best_first[mask] = bit;
        } else {
            best_first[mask] = previous_best;
        }

        /*@ Assert
            exists choices,
              numbers == numbers@pre && lengths == lengths@pre &&
              best_first == best_first@pre && result == result@pre &&
              count == count@pre && number_width == number_width@pre &&
              state_count == Z::shiftl(1, count@pre) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              1 <= mask && mask < state_count &&
              RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
              FlatRows(flat, rows, count@pre, number_width@pre) &&
              Zlength(choices) == mask + 1 &&
              DPTablePrefix(rows, lens, count@pre, mask + 1, choices) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
              IntArray::full(lengths@pre, count@pre, lens) *
              IntArray::seg(best_first@pre, 0, mask + 1, choices) *
              IntArray::undef_seg(best_first@pre, mask + 1, state_count) *
              IntArray::undef_full(result@pre, sum(lens)) *
              has_int_permission(&bit) *
              has_int_permission(&bit_value) *
              has_int_permission(&rest) *
              has_int_permission(&previous_best)
         */
    }

    int mask = state_count - 1;
    int result_length = 0;
    /*@ Inv Assert
        exists choices output,
          numbers == numbers@pre && lengths == lengths@pre &&
          best_first == best_first@pre && result == result@pre &&
          count == count@pre && number_width == number_width@pre &&
          state_count == Z::shiftl(1, count@pre) &&
          1 <= count@pre && count@pre <= 20 &&
          1 <= number_width@pre && number_width@pre <= 10 &&
          1 <= sum(lens) && sum(lens) <= 200 &&
          0 <= mask && mask < state_count &&
          result_length == Zlength(output) &&
          0 <= result_length && result_length <= sum(lens) &&
          RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
          FlatRows(flat, rows, count@pre, number_width@pre) &&
          Zlength(choices) == state_count &&
          DPTablePrefix(rows, lens, count@pre, state_count, choices) &&
          GreedyOutputPrefix(rows, lens, count@pre, mask, output) &&
          IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
          IntArray::full(lengths@pre, count@pre, lens) *
          IntArray::full(best_first@pre, state_count, choices) *
          IntArray::seg(result@pre, 0, result_length, output) *
          IntArray::undef_seg(result@pre, result_length, sum(lens))
     */
    while (mask != 0) {
        int first = best_first[mask];
        /*@ Assert
            exists choices output,
              numbers == numbers@pre && lengths == lengths@pre &&
              best_first == best_first@pre && result == result@pre &&
              count == count@pre && number_width == number_width@pre &&
              state_count == Z::shiftl(1, count@pre) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              1 <= mask && mask < state_count &&
              Zlength(choices) == state_count &&
              first == Znth(mask, choices, 0) &&
              0 <= first && first < count@pre &&
              1 <= Znth(first, lens, 0) &&
              Znth(first, lens, 0) <= number_width@pre &&
              result_length == Zlength(output) &&
              0 <= result_length &&
              result_length + Znth(first, lens, 0) <= sum(lens) &&
              RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
              FlatRows(flat, rows, count@pre, number_width@pre) &&
              DPTablePrefix(rows, lens, count@pre, state_count, choices) &&
              BestIndexForMask(rows, lens, count@pre, mask, first) &&
              GreedyOutputPrefix(rows, lens, count@pre, mask, output) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
              IntArray::full(lengths@pre, count@pre, lens) *
              IntArray::full(best_first@pre, state_count, choices) *
              IntArray::seg(result@pre, 0, result_length, output) *
              IntArray::undef_seg(result@pre, result_length, sum(lens))
         */
        /*@ Inv Assert
            exists choices prior output,
              numbers == numbers@pre && lengths == lengths@pre &&
              best_first == best_first@pre && result == result@pre &&
              count == count@pre && number_width == number_width@pre &&
              state_count == Z::shiftl(1, count@pre) &&
              1 <= count@pre && count@pre <= 20 &&
              1 <= number_width@pre && number_width@pre <= 10 &&
              1 <= sum(lens) && sum(lens) <= 200 &&
              1 <= mask && mask < state_count &&
              Zlength(choices) == state_count &&
              first == Znth(mask, choices, 0) &&
              0 <= first && first < count@pre &&
              0 <= position && position <= Znth(first, lens, 0) &&
              1 <= Znth(first, lens, 0) &&
              Znth(first, lens, 0) <= number_width@pre &&
              result_length == Zlength(output) &&
              0 <= result_length &&
              result_length + (Znth(first, lens, 0) - position) <= sum(lens) &&
              RowsWellFormed(rows, lens, count@pre, number_width@pre) &&
              FlatRows(flat, rows, count@pre, number_width@pre) &&
              DPTablePrefix(rows, lens, count@pre, state_count, choices) &&
              BestIndexForMask(rows, lens, count@pre, mask, first) &&
              GreedyOutputPrefix(rows, lens, count@pre, mask, prior) &&
              AppendRowPrefix(rows, lens, prior, first, position, output) &&
              IntArray::full(numbers@pre, count@pre * number_width@pre, flat) *
              IntArray::full(lengths@pre, count@pre, lens) *
              IntArray::full(best_first@pre, state_count, choices) *
              IntArray::seg(result@pre, 0, result_length, output) *
              IntArray::undef_seg(result@pre, result_length, sum(lens))
         */
        for (int position = 0; position < lengths[first]; ++position) {
            /*@ 0 <= first * number_width + position &&
                first * number_width + position < count * number_width by local */
            /*@ 0 <= result_length && result_length < sum(lens) by local */
            result[result_length] =
                numbers[first * number_width + position];
            ++result_length;
        }

        mask = mask ^ (1 << first);
    }

    return result;
}
