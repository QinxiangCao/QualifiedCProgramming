import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_divisor_cycle_bridge
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
namespace P090_GlobalOrbitBridge

theorem exact_nonunit_systems_aligned (m x : Int) (divisors : List Int) (blocks : List (List Int)) :
    ExactNonUnitDivisorSystems m x divisors blocks → AlignedStratumSystems m x (divisors.map (fun d => m /ᶻ d)) blocks := by
  intro hs
  induction hs with
  | nil => exact .nil
  | cons hh ht ih => exact .cons hh.2.2.1 ih

theorem exact_nonunit_blocks_length (m x : Int) (divisors : List Int) (blocks : List (List Int)) :
    ExactNonUnitDivisorSystems m x divisors blocks → Zlength blocks.flatten = (divisors.map (CycleTerm x)).foldr Int.add 0 := by
  intro hs
  induction hs with
  | nil => rfl
  | cons hh ht ih =>
    simp only [List.flatten_cons,List.map_cons,List.foldr_cons,Zlength_app,ih,hh.2.2.2]
    rfl

theorem aligned_system_member_has_key (m x room : Int) (keys : List Int) (blocks : List (List Int)) :
    AlignedStratumSystems m x keys blocks → room ∈ blocks.flatten → ∃ key, key ∈ keys ∧ Z.gcd room m = key := by
  intro hs
  induction hs with
  | nil => simp
  | @cons key reps keys blocks hh ht ih =>
    intro hr
    obtain hr | hr := List.mem_append.mp hr
    · exact ⟨key,List.mem_cons_self, (Forall.iff_forall_mem.mp hh.2.1 room hr).2⟩
    · obtain ⟨k,hk,hg⟩ := ih hr
      exact ⟨k,List.mem_cons_of_mem _ hk,hg⟩

theorem aligned_systems_concat_forall_range (m x : Int) (keys : List Int) (blocks : List (List Int)) :
    AlignedStratumSystems m x keys blocks → Forall (fun room => 0 ≤ room ∧ room < m) blocks.flatten := by
  intro hs
  induction hs with
  | nil => exact .nil
  | cons hh ht ih =>
    apply Forall.iff_forall_mem.mpr
    intro room hr
    obtain hr | hr := List.mem_append.mp hr
    · exact (Forall.iff_forall_mem.mp hh.2.1 room hr).1
    · exact Forall.iff_forall_mem.mp ih room hr

theorem aligned_systems_concat_nodup (m x : Int) (keys : List Int) (blocks : List (List Int)) :
    NoDup keys → AlignedStratumSystems m x keys blocks → NoDup blocks.flatten := by
  intro hn hs
  induction hs with
  | nil => simp
  | @cons key reps keys blocks hh ht ih =>
    obtain ⟨hnot,hnt⟩ := List.nodup_cons.mp hn
    apply List.Nodup.append hh.1 (ih hnt)
    intro room hr hrt
    have hg := (Forall.iff_forall_mem.mp hh.2.1 room hr).2
    obtain ⟨k,hk,hkg⟩ := aligned_system_member_has_key m x room keys blocks ht hrt
    exact hnot (by rwa [← hg,hkg])

theorem orbit_hit_preserves_gcd_key (m x start room key : Int) :
    0 < m → Z.gcd x m = 1 → Z.gcd start m = key → OrbitHit m x start room → Z.gcd room m = key := by
  rintro hm hx hs ⟨time,ht,rfl⟩
  rw [gcd_stratum_preserved m x start time hm ht hx,hs]

theorem aligned_systems_concat_separated (m x : Int) (keys : List Int) (blocks : List (List Int)) :
    0 < m → Z.gcd x m = 1 → NoDup keys → AlignedStratumSystems m x keys blocks → OrbitSeparated m x blocks.flatten := by
  intro hm hx hn hs
  induction hs with
  | nil => intro l r room hl; simp at hl
  | @cons key reps keys blocks hh ht ih =>
    obtain ⟨hnot,hnt⟩ := List.nodup_cons.mp hn
    intro l r room hl hr hlhit hrhit
    obtain hl | hl := List.mem_append.mp hl
    · obtain hr | hr := List.mem_append.mp hr
      · exact hh.2.2.2 l r room hl hr hlhit hrhit
      · have hlg := (Forall.iff_forall_mem.mp hh.2.1 l hl).2
        obtain ⟨k,hk,hrg⟩ := aligned_system_member_has_key m x r keys blocks ht hr
        have hlroom := orbit_hit_preserves_gcd_key m x l room key hm hx hlg hlhit
        have hrroom := orbit_hit_preserves_gcd_key m x r room k hm hx hrg hrhit
        exact False.elim (hnot (by rwa [← hlroom,hrroom]))
    · obtain hr | hr := List.mem_append.mp hr
      · have hrg := (Forall.iff_forall_mem.mp hh.2.1 r hr).2
        obtain ⟨k,hk,hlg⟩ := aligned_system_member_has_key m x l keys blocks ht hl
        have hlroom := orbit_hit_preserves_gcd_key m x l room k hm hx hlg hlhit
        have hrroom := orbit_hit_preserves_gcd_key m x r room key hm hx hrg hrhit
        exact False.elim (hnot (by rwa [← hrroom,hlroom]))
      · exact ih hnt l r room hl hr hlhit hrhit

theorem aligned_system_for_key (m x key : Int) (keys : List Int) (blocks : List (List Int)) :
    NoDup keys → AlignedStratumSystems m x keys blocks → key ∈ keys →
    ∃ representatives, representatives ∈ blocks ∧ StratumRepresentativeSystem m x key representatives := by
  intro hn hs
  induction hs with
  | nil => simp
  | @cons head reps keys blocks hh ht ih =>
    intro hk
    obtain rfl | hk := List.mem_cons.mp hk
    · exact ⟨reps,List.mem_cons_self,hh⟩
    · obtain ⟨rs,hrs,hss⟩ := ih (List.nodup_cons.mp hn).2 hk
      exact ⟨rs,List.mem_cons_of_mem _ hrs,hss⟩

theorem global_cover_from_strata (m x : Int) (keys : List Int) (blocks : List (List Int)) :
    NoDup keys → AlignedStratumSystems m x keys blocks → (∀ start, (0 ≤ start ∧ start < m) → Z.gcd start m ∈ keys) →
    OrbitCoversRange m x blocks.flatten := by
  intro hn hs hc start hstart
  obtain ⟨reps,hrs,hss⟩ := aligned_system_for_key m x (Z.gcd start m) keys blocks hn hs (hc start hstart)
  obtain ⟨r,hr,hhit⟩ := hss.2.2.1 start hstart rfl
  exact ⟨r,List.mem_flatten.mpr ⟨reps,hrs,hr⟩,hhit⟩

theorem aligned_strata_form_global_representative_system (m x : Int) (keys : List Int) (blocks : List (List Int)) :
    0 < m → Z.gcd x m = 1 → NoDup keys → AlignedStratumSystems m x keys blocks →
    (∀ start, (0 ≤ start ∧ start < m) → Z.gcd start m ∈ keys) → OrbitRepresentativeSystem m x blocks.flatten := by
  intro hm hx hn hs hc
  exact ⟨aligned_systems_concat_nodup m x keys blocks hn hs,aligned_systems_concat_forall_range m x keys blocks hs,
    global_cover_from_strata m x keys blocks hn hs hc,aligned_systems_concat_separated m x keys blocks hm hx hn hs⟩

theorem divisor_classification_gives_key_membership (m : Int) (divisors : List Int) :
    DivisorStrataClassify m divisors → ∀ start, (0 ≤ start ∧ start < m) → Z.gcd start m ∈ m::divisors.map (fun d => m /ᶻ d) := by
  intro hc start hs
  obtain hz | ⟨d,hd,hgd⟩ := hc start hs
  · exact List.mem_cons.mpr (Or.inl hz)
  · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨d,hd,hgd.symm⟩))

theorem exact_divisor_strata_global_system (m x : Int) (divisors zero_block : List Int) (nonunit_blocks : List (List Int)) :
    0 < m → Z.gcd x m = 1 → ExactZeroStratumSystem m x zero_block →
    ExactNonUnitDivisorSystems m x divisors nonunit_blocks → DistinctGlobalStratumKeys m divisors → DivisorStrataClassify m divisors →
    OrbitRepresentativeSystem m x (zero_block++nonunit_blocks.flatten) ∧
    Zlength (zero_block++nonunit_blocks.flatten) = 1+(divisors.map (CycleTerm x)).foldr Int.add 0 := by
  rintro hm hx ⟨hz,hzl⟩ hn hk hc
  have ha := exact_nonunit_systems_aligned m x divisors nonunit_blocks hn
  refine ⟨aligned_strata_form_global_representative_system m x (m::divisors.map (fun d => m /ᶻ d))
    (zero_block::nonunit_blocks) hm hx hk (.cons hz ha) (divisor_classification_gives_key_membership m divisors hc),?_⟩
  rw [Zlength_app,hzl,exact_nonunit_blocks_length m x divisors nonunit_blocks hn]

theorem exact_divisor_strata_imply_spec (m x : Int) (divisors zero_block : List Int) (nonunit_blocks : List (List Int)) :
    0 < m → Z.gcd x m = 1 → ExactZeroStratumSystem m x zero_block →
    ExactNonUnitDivisorSystems m x divisors nonunit_blocks → DistinctGlobalStratumKeys m divisors → DivisorStrataClassify m divisors →
    Spec m x (1+(divisors.map (CycleTerm x)).foldr Int.add 0) := by
  intro hm hx hz hn hk hc
  obtain ⟨hs,hl⟩ := exact_divisor_strata_global_system m x divisors zero_block nonunit_blocks hm hx hz hn hk hc
  have ht := representative_system_implies_spec m x ((divisors.map (CycleTerm x)).foldr Int.add 0) (zero_block++nonunit_blocks.flatten) hs (by omega)
  simpa only [add_comm] using ht

theorem exact_divisor_strata_global_bounds (m x : Int) (divisors zero_block : List Int) (nonunit_blocks : List (List Int)) :
    0 < m → Z.gcd x m = 1 → ExactZeroStratumSystem m x zero_block →
    ExactNonUnitDivisorSystems m x divisors nonunit_blocks → DistinctGlobalStratumKeys m divisors → DivisorStrataClassify m divisors →
    let traps := zero_block++nonunit_blocks.flatten
    NoDup traps ∧ CatchesAll m x traps ∧ Zlength traps = 1+(divisors.map (CycleTerm x)).foldr Int.add 0 ∧
    ∀ other, CatchesAll m x other → Zlength traps ≤ Zlength other := by
  intro hm hx hz hn hk hc
  obtain ⟨hs,hl⟩ := exact_divisor_strata_global_system m x divisors zero_block nonunit_blocks hm hx hz hn hk hc
  exact ⟨hs.1,representative_system_catches_all m x _ hs,hl,
    fun other => representative_system_zlength_lower_bound m x _ other hs⟩

theorem concrete_divisor_strata_imply_spec (m x : Int) (zero_block : List Int) (nonunit_blocks : List (List Int)) :
    let divisors := (positive_divisor_list m).filter (fun d => !(d==1))
    0 < m → Z.gcd x m = 1 → ExactZeroStratumSystem m x zero_block →
    ExactNonUnitDivisorSystems m x divisors nonunit_blocks → DistinctGlobalStratumKeys m divisors → DivisorStrataClassify m divisors →
    Spec m x (RoomZeroCycleTotal m x) :=
  exact_divisor_strata_imply_spec m x _ zero_block nonunit_blocks
end P090_GlobalOrbitBridge
export P090_GlobalOrbitBridge (exact_nonunit_systems_aligned exact_nonunit_blocks_length aligned_system_member_has_key
  aligned_systems_concat_forall_range aligned_systems_concat_nodup orbit_hit_preserves_gcd_key aligned_systems_concat_separated
  aligned_system_for_key global_cover_from_strata aligned_strata_form_global_representative_system
  divisor_classification_gives_key_membership exact_divisor_strata_global_system exact_divisor_strata_imply_spec
  exact_divisor_strata_global_bounds concrete_divisor_strata_imply_spec)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
