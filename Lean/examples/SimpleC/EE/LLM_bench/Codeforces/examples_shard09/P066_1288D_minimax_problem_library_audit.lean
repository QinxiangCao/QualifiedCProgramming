import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib
import Lean.Util.CollectAxioms

-- All 27 source library Qed declarations.
run_cmd do
  for decl in #[
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.row_mask_set_next__row_mask_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.row_mask_clear_next__row_mask_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.row_mask_complete_unique__representative_update,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.representative_insert__representative_update,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.representative_skip__representative_update,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.no_cover_outer_missing__cover_search,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.no_cover_inner_missing__cover_search,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.no_cover_inner_noncover__cover_search,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.row_mask_prefix_exists__feasible_outcomes,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.row_masks_lor_full__feasible_outcomes,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.row_masks_cover_pair__feasible_outcomes,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.completed_no_cover_excludes_feasible__feasible_outcomes,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.quot_nonnegative__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.half_positive__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.half_less_than_input__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.Znth_concat_uniform__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.matrix_entries_bounded_from_flat__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.matrix_entry_bounds__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.combined_entry_bounds__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.pair_score_bounds__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.pair_at_least_score_lower_bound__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.pair_score_implies_pair_at_least__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.pair_at_least_zero__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.optimal_pair_score_exists__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.optimal_pair_score_bounds__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.feasible_threshold_optimal_bound__solver_semantics,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.optimal_pair_to_spec__solver_semantics
  ] do
    for ax in ← Lean.collectAxioms decl do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "P066 source proof {decl} depends on unexpected axiom {ax}"
