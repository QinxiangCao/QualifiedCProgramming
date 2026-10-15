import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib

run_cmd do
  let proved := #[
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_input_phi,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_input_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_result_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_result_divides_phi,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_factor_completed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_advance,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.walk_global_coprime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.walk_exponent_phi,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.factor_at_prime_is_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.factor_at_prime_exit_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.valid_factor_table_lengths,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.prefix_choice_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.prefix_choice_selected,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.prefix_selected_extend,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.prime_power_transition_values,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.walk_exp_suffix_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.walk_exp_suffix_exhausted,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.walk_pending_terminal,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.cycle_answer_to_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_prime_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_is_prime_iff_std,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_std_prime_factor_exists,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_prime_factor_exists,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_prime_divisor_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_prime_divisor_of_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_no_prime_below_not_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_smallest_remaining_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_residual_remainder_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_mod_base_nat,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_mod_base,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_add_mod_left_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_multiple_mod_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_divmod_remainder,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_search_minimal,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_search_terminal_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_ord_search_exact,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_minimal_success_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_success_of_period_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_input_power_law,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_no_prime_below_two,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_no_prime_below_divisor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_no_prime_below_advance,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_excess_divides_ord,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_reduce,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_irreducible_from_ord,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_irreducible_from_pow_failure,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_init_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_skip_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_enter_factor_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_factor_step_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_factor_completed_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_step_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_exit_nodiv_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_exit_pow_failure_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_unit_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_support_empty_is_unit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_exit_exhausted_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_enter_final_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_step_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_support_only_irreducible_is_unit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_exit_nodiv_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_exit_pow_failure_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_factor_step_div_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_step_div_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_exit_mod_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_exit_power_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.prime_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.no_prime_below_two,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.no_prime_below_divisor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.no_prime_below_advance,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_core_order_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_core_excess_divides_ord,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_core_reduce,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_core_excess_irreducible_from_ord,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_core_excess_irreducible_from_pow_failure,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_trial_init,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_trial_skip,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_trial_enter_factor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_factor_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_factor_completed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_strip_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_strip_exit_nodiv,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_strip_exit_pow_failure,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_core_unit_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.support_empty_is_unit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_trial_exit_exhausted,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_trial_enter_final,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_final_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.support_only_irreducible_is_unit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_final_exit_nodiv,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess.order_final_exit_pow_failure,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.order_power_law_0_2_counterexample,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.order_power_law_falsified,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.is_prime_iff_std,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.std_prime_factor_exists,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.prime_factor_exists_law,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.prime_divisor_product_law,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.prime_divisor_of_prime_law,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.no_prime_below_not_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.smallest_remaining_divisor_prime_law,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderFoundations.P090_OrderFoundations.residual_remainder_prime_law,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_mod_base_nat,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_mod_base,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_add_mod_left_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_multiple_mod_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_divmod_remainder,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_search_minimal,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_search_terminal_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.ord_search_exact,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.minimal_success_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.success_of_period_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_input_implies_order_power_law,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_base,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_forgets_order,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_has_order,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_prime_prefix_lt,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_prime_prefix_distinct_indices,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_prime_prefix_snoc,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.factor_product_snoc,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_length_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_snoc_capacity,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.factor_prefix_smaller_prime_survives_division,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_append_completed_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_residual_ge_candidate,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_finalize_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.strict_factor_prefix_finalize_prime_residual,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.duplicated_prefix_is_rejected,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorTable.duplicated_complete_prefix_is_rejected,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.factor_entries_of_strict_prefix,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.factor_product_lower_bound,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.strict_factor_prefix_product_lower_bound,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.strict_factor_prefix_power_bounded_by_m,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.strict_factor_prefix_length_lt_47,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.strict_factor_prefix_has_free_slot,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.standard_prime_is_case_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.standard_prime_divisor_exists,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.case_prime_divisor_exists,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.no_small_prime_divisor_implies_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.strict_factor_prefix_residual_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorFoundations.strict_factor_prefix_finalize_after_square_exit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.coprime_count_filter,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.euler_phi_bridge,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.coprime_count_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.euler_phi_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.euler_phi_positive_bounded,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.euler_phi_zero_counterexample,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.is_prime_to_coq_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.euler_phi_prime_power,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.euler_phi_coprime_multiplicative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.euler_phi_coprime_prime_power,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.gcd_prime_power_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.pow_mod_coprime_product_one_iff,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.lcm_as_gcd_quotient_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.exact_order_coprime_product_lcm,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.order_lcm_runtime_formula,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.order_search_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ord_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ord_non_coprime_counterexample,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.cycle_term_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.sum_nat_range_nonnegative_local,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.walk_suffix_lists_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.walk_suffix_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.walk_suffix_lists_cons,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.walk_suffix_zero_index,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.walk_suffix_mismatched_left,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.walk_suffix_mismatched_right,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.gcd_stratum_preserved,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.catches_all_contains_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.catches_all_hits_same_gcd_stratum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.sum_nat_range_ext,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.sum_nat_range_mono,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.sum_nat_range_app,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.euler_phi_prime_power_sum_nat,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.euler_phi_prime_power_sum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.cycle_term_le_euler_phi,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.walk_prime_power_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.unit_orbit_return_iff,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.unit_orbit_period,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.unit_orbit_no_early_return,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitOptimality.catches_all_hits_unit_orbit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.sum_nat_range_head,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.sum_nat_range_app,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.sum_nat_range_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.sum_nat_range_nonnegative_pointwise,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.walk_exp_suffix_head_tail,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.walk_exp_suffix_exact_exhaustion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.walk_exp_suffix_past_exhaustion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.walk_exp_suffix_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.prefix_selected_at_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.prefix_selected_successor_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.prefix_selected_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.prefix_selected_index_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.prefix_selected_positive_from_valid_table,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.prefix_selected_step_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.prime_power_transition_build,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.walk_completed_from_exhausted_loop,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.orbit_cover_bounds_imply_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkBridge.walk_completed_and_orbit_bounds_imply_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.valid_factor_table_ordered_aux,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.valid_factor_table_ordered,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.sum_nat_range_mul_l,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.sum_nat_range_mul_r,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.euler_phi_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.euler_phi_coprime_prime_power_all,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.euler_phi_coprime_prime_power_sum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.smaller_distinct_primes_coprime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.coprime_to_table_extend,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.ordered_prime_table_all_primes,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.enumerated_phi_sum_factor_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.coprime_one_table,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.valid_factor_table_enumerated_phi_exact,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.walk_suffix_lists_le_enumerated_phi,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.nonunit_cycle_term_exact_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.ordered_table_walk_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.walk_suffix_recursive_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.valid_factor_table_walk_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.valid_factor_table_initial_walk_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.walk_budget_from_cumulative_bound,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_TableBudget.walk_suffix_cumulative_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.exponent_trace_lengths,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.exponent_trace_product_functional,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.enumerated_products_trace,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.valid_factor_table_exponents_nonnegative,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.valid_factor_table_exact_trace_enumeration,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.sum_nat_range_as_seq,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.fold_right_add_acc,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.fold_right_concat_map,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.walk_suffix_lists_exact_terms,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.enumerated_walk_terms_as_products,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.walk_suffix_exact_divisor_cycle_sum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.cycle_term_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.fold_filter_cycle_term_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.walk_suffix_zero_is_nonunit_cycle_sum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.walk_budget_nonunit_cycle_interface,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.prefix_selected_trace_forget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.prefix_selected_has_trace,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.prefix_selected_trace_length,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorEnumeration.prefix_selected_exact_trace_interface,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.smaller_prime_not_divide_factor_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.valid_factor_table_canonical,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.extract_prime_power_from_divisor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.canonical_factor_product_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.canonical_divisor_complete,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.valid_factor_table_divisor_complete,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.prime_power_residual_unique,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.exponent_trace_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.exponent_trace_divides_factor_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.exponent_trace_cons_inv,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.canonical_exponent_trace_unique,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.valid_factor_table_exponent_vector_unique,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.map_injective_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.tagged_vectors_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.enumerated_exponent_vectors_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.enumerated_products_as_vector_map,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.enumerated_vector_has_trace,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.valid_factor_table_enumerated_products_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCompleteness.valid_factor_table_exact_positive_divisor_bijection,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ord_search_exact_from_terminal,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.reduced_base_coprime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.reduced_base_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.euler_power_for_case_phi,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.coprime_implies_order_input,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ord_reduced_base,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.coprime_implies_reduced_order_input,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.coprime_implies_exact_order_criterion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.coprime_implies_reduced_exact_order_criterion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.exact_order_criterion_unique,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.exact_order_criterion_is_ord,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.coprime_implies_order_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_trial_init,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_trial_skip,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_trial_enter_factor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_factor_at_prime_forgets_order,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_factor_divide_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_factor_positive_exponent_at_exit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_factor_finish_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_trial_finalize_after_square_exit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorConsumer.strict_trial_finalize_from_failed_guard,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.strict_trial_numeric_components,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.strict_trial_candidate_bound_under_guard,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.strict_trial_guard_square_range,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.strict_factor_exponent_cap,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.strict_factor_exponent_nonnegative_bounded,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_trial_init,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_trial_skip,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_enter_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_divide_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_active_exponent_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_finish_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_candidate_square_signed64,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_candidate_increment_signed64,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_square_guard_no_wrap,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FactorMachineBounds.factor_machine_finalize_from_failed_square_guard,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_trial_init_from_coprime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_power_law_from_trial,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_power_law_from_factor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_power_law_from_strip,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_power_law_from_final,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_trial_enter_factor_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_factor_step_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_strip_step_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_strip_exit_pow_failure_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_trial_exit_exhausted_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_trial_enter_final_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_final_step_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_final_exit_nodiv_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderConsumer.order_final_exit_pow_failure_closed,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.valid_table_exponent_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.valid_table_initial_prefix_choice,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.prefix_choice_zero_extend,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.walk_suffix_at_terminal,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.prefix_choice_leaf_cycle_term,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.prefix_choice_terminal_walk_value,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.skipn_nth_cons_nat,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.skipn_Znth_cons,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.walk_suffix_as_exp_suffix_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.walk_suffix_head_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.walk_pending_after_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.walk_pending_consume_head,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.walk_pending_finish,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkConsumer.walk_recursive_return_continuation,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.walk_budget_split_head_tail,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.incoming_walk_suffix_zero_head_tail_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.incoming_walk_suffix_zero_call_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.incoming_walk_suffix_zero_return_continuation,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.incoming_walk_suffix_zero_call_and_continuation,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.walk_pending_head_tail_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.walk_pending_recursive_call_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.walk_pending_post_return_tail_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkCallBudget.walk_pending_recursive_call_and_return,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.valid_factor_table_entry,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.table_power_at_divides_factor_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.valid_table_power_at_divides_m,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.prefix_selected_coprime_later_prime,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.coprime_divisors_product_divides,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.prefix_selected_divides_m,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.gcd_with_divisor_of_coprime_modulus,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.gcd_coprime_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.prime_power_consumer_basic,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.prime_power_consumer_order_input,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.prime_power_consumer_euler,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.prime_power_consumer_order_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_PrimePowerConsumer.prime_power_consumer_transition,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_init_from_table,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_pk_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_phi_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.positive_prime_power_divisor_bound,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_step_from_table,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_step_first_from_table,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_step_later_from_table,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_ready_for_transition,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_state_consumer_transition,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_exit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkExponentConsumer.walk_exponent_pending_exit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.orbit_hit_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.catches_all_gives_orbit_hit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_catches_all,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.separated_witnesses_length,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_lower_bound,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_zlength_lower_bound,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_implies_orbit_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_implies_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.order_input_exact_order_criterion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.stratum_representatives_lower_bound,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.zero_singleton_stratum_system,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_length,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_zlength,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.nodup_map_on,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.find_extensional_bool,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.canonical_key_in_and_related,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.canonical_key_equal_on_class,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.canonical_key_idempotent,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_key_in,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_forall_universe,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_covers,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_separated,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.orbit_advance,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_forall_range,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_forall_unit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_member_is_hit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_hit_in_list,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_exact,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.orbit_hit_transitive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_hit_symmetric,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_relatedb_true_iff,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_equivalence_on_units,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_residueb_true_iff,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_residues_member_iff,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_residues_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_residues_zlength,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_orbit_equivb_true_iff,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_orbit_equiv_laws,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_forall_unit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_cover,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_separated,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_stratum_system,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.nodup_concat_map_disjoint,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_orbit_blocks_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_orbit_blocks_member_iff,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_orbit_blocks_permutation,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.concat_map_constant_length,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_product_count,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_order_divides_phi,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_quotient_count,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.unit_representatives_exact_package,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.reduced_unit_representatives_exact,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.divisor_quotient_factorization,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.positive_divisor_quotient_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.coprime_mod_positive_divisor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.stratum_lift_range_and_gcd,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.stratum_extract_unit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.stratum_project_lift,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.stratum_lift_injective,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.stratum_lift_mul_mod,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.stratum_lift_orbit_hit,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.stratum_lift_orbit_hit_inverse,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.coprime_stratum_orbit_compatibility,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.lifted_representatives_length,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.lifted_representatives_zlength,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.transport_unit_stratum_system,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.divisor_one_lift_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.divisor_one_zero_stratum_transport,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.positive_divisor_list_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.positive_divisor_list_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.valid_factor_table_m_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.valid_factor_table_divisor_permutation,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.permutation_fold_right_add,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.permutation_filter_bool,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.divisor_permutation_nonunit_cycle_sum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.walk_suffix_is_concrete_nonunit_divisor_cycle_sum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.concrete_nonunit_divisor_cycle_budget,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.room_zero_final_decomposition,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.walk_suffix_is_concrete_full_divisor_cycle_sum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorCycleBridge.room_zero_full_divisor_decomposition,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.exact_nonunit_systems_aligned,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.exact_nonunit_blocks_length,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.aligned_system_member_has_key,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.aligned_systems_concat_forall_range,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.aligned_systems_concat_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.orbit_hit_preserves_gcd_key,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.aligned_systems_concat_separated,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.aligned_system_for_key,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.global_cover_from_strata,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.aligned_strata_form_global_representative_system,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.divisor_classification_gives_key_membership,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.exact_divisor_strata_global_system,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.exact_divisor_strata_imply_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.exact_divisor_strata_global_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GlobalOrbitBridge.concrete_divisor_strata_imply_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_nonunit_divisor_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_nonunit_divisors_nodup,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.positive_divisor_exact_product,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.positive_divisor_quotient_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.positive_divisor_quotient_injective,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_nonunit_key_positive,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_nonunit_key_nonzero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_nonunit_keys_pairwise_distinct,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_nonunit_key_distinct_from_zero_key,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_distinct_global_stratum_keys,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.gcd_positive_with_positive_modulus,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.gcd_quotient_is_positive_divisor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.gcd_equal_modulus_room_zero,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.gcd_quotient_nonunit_when_not_zero_stratum,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_divisor_strata_classify,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_nonunit_stratum_divisor_unique,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_DivisorStrataKeys.concrete_divisor_strata_key_premises,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.coprime_with_positive_divisor,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.concrete_zero_block_exact,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.concrete_nonunit_block_exact,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.concrete_nonunit_subsystems,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.concrete_exact_nonunit_divisor_systems,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.concrete_room_zero_cycle_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.valid_factor_table_walk_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.valid_factor_table_walk_spec_solver_order,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_FinalOrbitInstantiation.walk_global_bounds_factor_table_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_exit_bounded_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_step_div_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_exit_mod_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_exit_power_guard_ex,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.pow_mod_base__powmod_loop,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.land_one_mod_two__powmod_loop,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.pow_loop_odd_step__powmod_loop,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.pow_loop_even_step__powmod_loop,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.rem_one_implies_mod_one__order_entry_and_factorization,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "unproved dependency in {decl}"

example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerModularPowerProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerModularPowerProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPhi = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhi := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPhiFactorCompletion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiFactorCompletion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPhiFactorCompletion_divide = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiFactorCompletion_divide := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPhiProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPhiRemovalProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiRemovalProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPhiRemovalProgress_complete = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiRemovalProgress_complete := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPhiResidual = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiResidual := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerPrime = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPrime := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerTheoremInverse = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerTheoremInverse := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.EulerTotientValue = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerTotientValue := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.ModularPower = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.ModularPower := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.NoPrimeDivisorBelow = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.NoPrimeDivisorBelow := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.bounded_residue_product_int__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.bounded_residue_product_int__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_active_frontier_bound__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_active_frontier_bound__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_completed_progress__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_completed_progress__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_coprime_residue_member__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_coprime_residue_member__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_crt_residue_pair_injective__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_residue_pair_injective__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_crt_solution_mod_left__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_solution_mod_left__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_crt_solution_mod_right__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_solution_mod_right__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_exact_positive_quotient_bounds__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_exact_positive_quotient_bounds__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_factor_prime__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_factor_prime__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_filter_all_true__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_filter_all_true__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_list_prod_nodup__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_list_prod_nodup__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_mapped_product_mod__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_mapped_product_mod__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_modular_progress_even_step__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_even_step__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_modular_progress_odd_step__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_odd_step__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_modular_progress_zero_finish__modular_power_final = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_zero_finish__modular_power_final := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_phi_removal_start__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_phi_removal_start__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_power_totient_mod__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_power_totient_mod__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_prime_divisor_exists__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_divisor_exists__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_prime_from_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_from_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_prime_power_multiple_count__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_power_multiple_count__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_prime_power_relprime_iff__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_power_relprime_iff__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_prime_to_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_to_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_prime_two__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_two__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_product_permutation__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_product_permutation__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_progress_advance_nondivisor__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_advance_nondivisor__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_progress_terminal_one__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_terminal_one__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_progress_terminal_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_terminal_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_relprime_product_divide__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_relprime_product_divide__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_remaining_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_remaining_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_residue_bounds__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_bounds__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_residue_map_injective__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_injective__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_residue_map_member__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_member__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_residue_map_nodup__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_nodup__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_residue_map_permutation__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_permutation__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_residue_mod_member__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_mod_member__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_residue_product_coprime__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_product_coprime__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_totient_coprime_prime_power__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_coprime_prime_power__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_totient_inverse_theorem__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_inverse_theorem__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_totient_multiplicative__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_multiplicative__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_totient_of_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_of_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_WalkFoundations.ETI.euler_totient_prime_power__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_prime_power__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerModularPowerProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerModularPowerProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPhi = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhi := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPhiFactorCompletion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiFactorCompletion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPhiFactorCompletion_divide = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiFactorCompletion_divide := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPhiProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPhiRemovalProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiRemovalProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPhiRemovalProgress_complete = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiRemovalProgress_complete := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPhiResidual = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiResidual := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerPrime = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPrime := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerTheoremInverse = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerTheoremInverse := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.EulerTotientValue = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerTotientValue := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.ModularPower = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.ModularPower := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.NoPrimeDivisorBelow = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.NoPrimeDivisorBelow := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.bounded_residue_product_int__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.bounded_residue_product_int__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_active_frontier_bound__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_active_frontier_bound__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_completed_progress__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_completed_progress__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_coprime_residue_member__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_coprime_residue_member__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_crt_residue_pair_injective__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_residue_pair_injective__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_crt_solution_mod_left__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_solution_mod_left__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_crt_solution_mod_right__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_solution_mod_right__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_exact_positive_quotient_bounds__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_exact_positive_quotient_bounds__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_factor_prime__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_factor_prime__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_filter_all_true__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_filter_all_true__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_list_prod_nodup__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_list_prod_nodup__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_mapped_product_mod__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_mapped_product_mod__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_modular_progress_even_step__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_even_step__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_modular_progress_odd_step__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_odd_step__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_modular_progress_zero_finish__modular_power_final = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_zero_finish__modular_power_final := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_phi_removal_start__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_phi_removal_start__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_power_totient_mod__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_power_totient_mod__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_prime_divisor_exists__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_divisor_exists__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_prime_from_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_from_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_prime_power_multiple_count__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_power_multiple_count__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_prime_power_relprime_iff__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_power_relprime_iff__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_prime_to_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_to_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_prime_two__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_two__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_product_permutation__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_product_permutation__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_progress_advance_nondivisor__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_advance_nondivisor__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_progress_terminal_one__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_terminal_one__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_progress_terminal_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_terminal_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_relprime_product_divide__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_relprime_product_divide__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_remaining_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_remaining_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_residue_bounds__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_bounds__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_residue_map_injective__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_injective__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_residue_map_member__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_member__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_residue_map_nodup__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_nodup__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_residue_map_permutation__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_permutation__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_residue_mod_member__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_mod_member__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_residue_product_coprime__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_product_coprime__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_totient_coprime_prime_power__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_coprime_prime_power__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_totient_inverse_theorem__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_inverse_theorem__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_totient_multiplicative__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_multiplicative__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_totient_of_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_of_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderInputBridge.ETI.euler_totient_prime_power__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_prime_power__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.minimal_success_divides = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.minimal_success_divides := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.ord_search_exact = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.ord_search_exact := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.order_input_implies_order_power_law = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_input_implies_order_power_law := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.order_search_minimal = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_search_minimal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.order_search_terminal_spec = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_search_terminal_spec := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_add_mod_left_one = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_add_mod_left_one := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_divmod_remainder = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_divmod_remainder := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_mod_base = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_mod_base := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_mod_base_nat = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_mod_base_nat := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_multiple_mod_one = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_multiple_mod_one := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.success_of_period_divides = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.success_of_period_divides := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerModularPowerProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerModularPowerProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPhi = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhi := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPhiFactorCompletion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiFactorCompletion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPhiFactorCompletion_divide = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiFactorCompletion_divide := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPhiProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPhiRemovalProgress = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiRemovalProgress := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPhiRemovalProgress_complete = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiRemovalProgress_complete := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPhiResidual = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPhiResidual := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerPrime = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerPrime := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerTheoremInverse = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerTheoremInverse := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.EulerTotientValue = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.EulerTotientValue := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.ModularPower = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.ModularPower := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.NoPrimeDivisorBelow = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.NoPrimeDivisorBelow := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.bounded_residue_product_int__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.bounded_residue_product_int__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_active_frontier_bound__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_active_frontier_bound__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_completed_progress__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_completed_progress__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_coprime_residue_member__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_coprime_residue_member__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_crt_residue_pair_injective__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_residue_pair_injective__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_crt_solution_mod_left__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_solution_mod_left__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_crt_solution_mod_right__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_crt_solution_mod_right__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_exact_positive_quotient_bounds__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_exact_positive_quotient_bounds__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_factor_prime__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_factor_prime__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_filter_all_true__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_filter_all_true__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_list_prod_nodup__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_list_prod_nodup__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_mapped_product_mod__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_mapped_product_mod__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_modular_progress_even_step__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_even_step__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_modular_progress_odd_step__modular_power_loop = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_odd_step__modular_power_loop := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_modular_progress_zero_finish__modular_power_final = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_modular_progress_zero_finish__modular_power_final := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_phi_removal_start__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_phi_removal_start__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_power_totient_mod__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_power_totient_mod__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_prime_divisor_exists__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_divisor_exists__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_prime_from_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_from_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_prime_power_multiple_count__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_power_multiple_count__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_prime_power_relprime_iff__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_power_relprime_iff__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_prime_to_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_to_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_prime_two__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_prime_two__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_product_permutation__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_product_permutation__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_progress_advance_nondivisor__euler_phi_factor_completion = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_advance_nondivisor__euler_phi_factor_completion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_progress_terminal_one__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_terminal_one__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_progress_terminal_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_progress_terminal_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_relprime_product_divide__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_relprime_product_divide__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_remaining_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_remaining_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_residue_bounds__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_bounds__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_residue_map_injective__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_injective__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_residue_map_member__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_member__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_residue_map_nodup__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_nodup__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_residue_map_permutation__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_map_permutation__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_residue_mod_member__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_mod_member__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_residue_product_coprime__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_residue_product_coprime__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_totient_coprime_prime_power__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_coprime_prime_power__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_totient_inverse_theorem__inverse_final_result = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_inverse_theorem__inverse_final_result := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_totient_multiplicative__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_multiplicative__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_totient_of_prime__euler_phi_final_results = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_of_prime__euler_phi_final_results := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition.ETI.euler_totient_prime_power__euler_phi_setup_removal = @SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.euler_totient_prime_power__euler_phi_setup_removal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.CanonicalKey = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.CanonicalKey := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.EquivalenceLaws = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.EquivalenceLaws := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.FiniteQuotient = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.FiniteQuotient := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrbitCoversRange = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrbitCoversRange := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrbitHit = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrbitHit := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrbitRepresentativeSystem = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrbitRepresentativeSystem := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrbitSeparated = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrbitSeparated := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.minimal_success_divides = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.minimal_success_divides := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.ord_search_exact = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.ord_search_exact := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.order_input_implies_order_power_law = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.order_input_implies_order_power_law := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.order_search_minimal = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.order_search_minimal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.order_search_terminal_spec = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.order_search_terminal_spec := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.pow_add_mod_left_one = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_add_mod_left_one := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.pow_divmod_remainder = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_divmod_remainder := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.pow_mod_base = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_mod_base := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.pow_mod_base_nat = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_mod_base_nat := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.pow_multiple_mod_one = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.pow_multiple_mod_one := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.OrderExact.success_of_period_divides = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.OrderExact.success_of_period_divides := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.StratumCovers = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.StratumCovers := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.StratumRepresentativeSystem = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.StratumRepresentativeSystem := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.UnitOrbitList = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.UnitOrbitList := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.UnitOrbitRelatedb = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.UnitOrbitRelatedb := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.canonical_key_equal_on_class = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.canonical_key_equal_on_class := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.canonical_key_idempotent = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.canonical_key_idempotent := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.canonical_key_in_and_related = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.canonical_key_in_and_related := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.catches_all_gives_orbit_hit = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.catches_all_gives_orbit_hit := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.find_extensional_bool = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.find_extensional_bool := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.finite_quotient_covers = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_covers := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.finite_quotient_forall_universe = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_forall_universe := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.finite_quotient_key_in = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_key_in := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.finite_quotient_nodup = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_nodup := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.finite_quotient_separated = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.finite_quotient_separated := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.nodup_map_on = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.nodup_map_on := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.orbit_advance = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.orbit_advance := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.orbit_hit_transitive = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.orbit_hit_transitive := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.orbit_hit_zero = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.orbit_hit_zero := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.order_input_exact_order_criterion = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.order_input_exact_order_criterion := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.representative_system_catches_all = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_catches_all := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.representative_system_implies_orbit_bounds = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_implies_orbit_bounds := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.representative_system_implies_spec = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_implies_spec := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.representative_system_lower_bound = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_lower_bound := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.representative_system_zlength_lower_bound = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.representative_system_zlength_lower_bound := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.separated_witnesses_length = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.separated_witnesses_length := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.stratum_representatives_lower_bound = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.stratum_representatives_lower_bound := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_equivalence_on_units = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_equivalence_on_units := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_hit_in_list = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_hit_in_list := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_hit_symmetric = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_hit_symmetric := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_list_exact = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_exact := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_list_forall_range = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_forall_range := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_list_forall_unit = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_forall_unit := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_list_length = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_length := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_list_member_is_hit = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_member_is_hit := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_list_nodup = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_nodup := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_list_zlength = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_list_zlength := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.unit_orbit_relatedb_true_iff = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.unit_orbit_relatedb_true_iff := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OQ.zero_singleton_stratum_system = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient.zero_singleton_stratum_system := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.minimal_success_divides = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.minimal_success_divides := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.ord_search_exact = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.ord_search_exact := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.order_input_implies_order_power_law = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_input_implies_order_power_law := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.order_search_minimal = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_search_minimal := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.order_search_terminal_spec = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.order_search_terminal_spec := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.pow_add_mod_left_one = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_add_mod_left_one := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.pow_divmod_remainder = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_divmod_remainder := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.pow_mod_base = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_mod_base := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.pow_mod_base_nat = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_mod_base_nat := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.pow_multiple_mod_one = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.pow_multiple_mod_one := rfl
example : @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_GcdStratumTransport.OE.success_of_period_divides = @SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExact.P090_OrderExact.success_of_period_divides := rfl
