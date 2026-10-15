import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_unit_orbit_partition

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_UnitOrbitPartition

run_cmd do
  let proved := #[
    ``unit_residueb_true_iff,
    ``unit_residues_member_iff,
    ``unit_residues_nodup,
    ``unit_residues_zlength,
    ``unit_orbit_equivb_true_iff,
    ``unit_orbit_equiv_laws,
    ``unit_representatives_nodup,
    ``unit_representatives_forall_unit,
    ``unit_representatives_cover,
    ``unit_representatives_separated,
    ``unit_representatives_stratum_system,
    ``nodup_concat_map_disjoint,
    ``unit_orbit_blocks_nodup,
    ``unit_orbit_blocks_member_iff,
    ``unit_orbit_blocks_permutation,
    ``concat_map_constant_length,
    ``unit_representatives_product_count,
    ``unit_representatives_order_divides_phi,
    ``unit_representatives_quotient_count,
    ``unit_representatives_exact_package,
    ``reduced_unit_representatives_exact]
  for decl in proved do
    let axioms ← Lean.collectAxioms decl
    if axioms.contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "P090_UnitOrbitPartition: all 21 source Qed checked recursively; no sorryAx dependency."
