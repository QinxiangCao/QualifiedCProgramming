import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_orbit_quotient

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient

run_cmd do
  let proved := #[
    ``orbit_hit_zero,
    ``catches_all_gives_orbit_hit,
    ``representative_system_catches_all,
    ``separated_witnesses_length,
    ``representative_system_lower_bound,
    ``representative_system_zlength_lower_bound,
    ``representative_system_implies_orbit_bounds,
    ``representative_system_implies_spec,
    ``order_input_exact_order_criterion,
    ``stratum_representatives_lower_bound,
    ``zero_singleton_stratum_system,
    ``unit_orbit_list_length,
    ``unit_orbit_list_zlength,
    ``nodup_map_on,
    ``find_extensional_bool,
    ``canonical_key_in_and_related,
    ``canonical_key_equal_on_class,
    ``canonical_key_idempotent,
    ``finite_quotient_nodup,
    ``finite_quotient_key_in,
    ``finite_quotient_forall_universe,
    ``finite_quotient_covers,
    ``finite_quotient_separated,
    ``orbit_advance,
    ``unit_orbit_list_forall_range,
    ``unit_orbit_list_forall_unit,
    ``unit_orbit_list_member_is_hit,
    ``unit_orbit_list_nodup,
    ``unit_orbit_hit_in_list,
    ``unit_orbit_list_exact,
    ``orbit_hit_transitive,
    ``unit_orbit_hit_symmetric,
    ``unit_orbit_relatedb_true_iff,
    ``unit_orbit_equivalence_on_units]
  for decl in proved do
    let axioms ← Lean.collectAxioms decl
    if axioms.contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "P090_OrbitQuotient: all 34 source Qed checked recursively; no sorryAx dependency."
