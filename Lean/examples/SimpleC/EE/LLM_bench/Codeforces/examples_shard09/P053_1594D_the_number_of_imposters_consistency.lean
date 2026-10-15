import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_counts

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem extend_consistent__scan_and_component_closure (n : Int) (comments : List Comment)
    (before after vertices base : List Int) (flip : Int)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength comments) → let ((u,v),_) := comment_at comments i; (1 ≤ u ∧ u ≤ n) ∧ (1 ≤ v ∧ v ≤ n))
    (hn : NewColourSet n before after vertices) (hcb : ColouredClosed comments before)
    (hca : ColouredClosed comments after) (hp : ParityRespected comments after) (hcv : ColourValues n after)
    (hbase : ConsistentOn n comments before base) (hf : flip = 0 ∨ flip = 1) :
    ConsistentOn n comments after (vertices.foldr (fun v r => replace_Znth (v-1) (Z.lxor (Znth v after 0) flip) r) base) := by
  have hlen := hbase.1.1
  have hmem := fold_replace_member__scan_and_component_closure vertices n base (fun v => Z.lxor (Znth v after 0) flip)
  have hout := fold_replace_outside__scan_and_component_closure vertices n base (fun v => Z.lxor (Znth v after 0) flip)
  refine ⟨⟨fold_replace_length__scan_and_component_closure _ _ _ _ hlen, ?_, ?_⟩, ?_⟩
  · intro v hv hc
    by_cases hm : v ∈ vertices
    · rw [hmem v hlen hn.2.1 hv hm]
      apply lxor_bit__scan_and_component_closure _ _ _ hf
      have hh := hcv.2 v hv
      omega
    · rw [hout v hlen hn.2.1 hv hm]
      apply hbase.1.2.1 v hv
      rwa [hn.2.2.2 v hv hm] at hc
  · intro v hv hc
    have hm : v ∉ vertices := fun hm => ((hn.2.2.1 v hv).mp hm).2 hc
    rw [hout v hlen hn.2.1 hv hm]
    apply hbase.1.2.2 v hv
    rwa [hn.2.2.2 v hv hm] at hc
  · intro i hi
    rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
    dsimp
    intro hua hva
    have hbounds := hb i hi
    rw [hq] at hbounds
    obtain ⟨hu,hv⟩ := hbounds
    have hedge := new_component_edge_closed__scan_and_component_closure n comments before after vertices i u v w hn hcb hca hi hq hu hv
    by_cases hum : u ∈ vertices
    · have hvm := hedge.mp hum
      rw [hmem v hlen hn.2.1 hv hvm,hmem u hlen hn.2.1 hu hum]
      have hpar := hp i hi
      rw [hq] at hpar
      rw [hpar hua hva]
      exact lxor_shuffle__scan_and_component_closure _ _ _
    · have hvm : v ∉ vertices := fun hh => hum (hedge.mpr hh)
      rw [hout v hlen hn.2.1 hv hvm,hout u hlen hn.2.1 hu hum]
      have hpar := hbase.2 i hi
      rw [hq] at hpar
      exact hpar (by rwa [hn.2.2.2 u hu hum] at hua) (by rwa [hn.2.2.2 v hv hvm] at hva)

theorem fold_replace_sum_general__scan_and_component_closure (vertices : List Int) (n : Int) (base : List Int)
    (f : Int → Int) (hlen : Zlength base = n) (hnd : vertices.Nodup)
    (hb : Forall (fun x => 1 ≤ x ∧ x ≤ n) vertices) :
    (vertices.foldr (fun x r => replace_Znth (x-1) (f x) r) base).foldr (· + ·) 0 =
    base.foldr (· + ·) 0 - (vertices.map (fun x => Znth (x-1) base 0)).foldr (· + ·) 0 +
      (vertices.map f).foldr (· + ·) 0 := by
  induction vertices with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot,hndt⟩ := List.nodup_cons.mp hnd
    have hbx := Forall.iff_forall_mem.mp hb x (by simp)
    have hbt : Forall (fun x => 1 ≤ x ∧ x ≤ n) xs := Forall.iff_forall_mem.mpr (fun y hy => Forall.iff_forall_mem.mp hb y (by simp [hy]))
    have htlen := fold_replace_length__scan_and_component_closure xs n base f hlen
    have hiht := ih hndt hbt
    simp only [List.foldr_cons,List.map_cons]
    rw [sum_replace__scan_and_component_closure _ _ _ ⟨by omega,by omega⟩,
      fold_replace_outside__scan_and_component_closure xs n base f x hlen hbt hbx hnot, hiht]
    omega

theorem restrict_consistent__scan_and_component_closure (n : Int) (comments : List Comment)
    (before after vertices roles : List Int)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength comments) → let ((u,v),_) := comment_at comments i; (1 ≤ u ∧ u ≤ n) ∧ (1 ≤ v ∧ v ≤ n))
    (hn : NewColourSet n before after vertices) (hr : ConsistentOn n comments after roles) :
    ConsistentOn n comments before (vertices.foldr (fun v r => replace_Znth (v-1) 0 r) roles) := by
  have hlen := hr.1.1
  have hmem := fold_replace_member__scan_and_component_closure vertices n roles (fun _ => 0)
  have hout := fold_replace_outside__scan_and_component_closure vertices n roles (fun _ => 0)
  have hnot (v : Int) (hv : 1 ≤ v ∧ v ≤ n) (hc : Znth v before 0 ≠ -1) : v ∉ vertices := fun hm => hc ((hn.2.2.1 v hv).mp hm).1
  refine ⟨⟨fold_replace_length__scan_and_component_closure _ _ _ _ hlen, ?_, ?_⟩, ?_⟩
  · intro v hv hc
    have hm := hnot v hv hc
    rw [hout v hlen hn.2.1 hv hm]
    exact hr.1.2.1 v hv (by rwa [hn.2.2.2 v hv hm])
  · intro v hv hc
    by_cases hm : v ∈ vertices
    · exact hmem v hlen hn.2.1 hv hm
    · rw [hout v hlen hn.2.1 hv hm]
      exact hr.1.2.2 v hv (by rwa [hn.2.2.2 v hv hm])
  · intro i hi
    rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
    dsimp
    intro huc hvc
    have hbounds := hb i hi
    rw [hq] at hbounds
    obtain ⟨hu,hv⟩ := hbounds
    have hum := hnot u hu huc
    have hvm := hnot v hv hvc
    rw [hout v hlen hn.2.1 hv hvm,hout u hlen hn.2.1 hu hum]
    have hpar := hr.2 i hi
    rw [hq] at hpar
    exact hpar (by rwa [hn.2.2.2 u hu hum]) (by rwa [hn.2.2.2 v hv hvm])

theorem consistent_on_vertices__scan_and_component_closure (n : Int) (comments : List Comment)
    (before after vertices roles : List Int) (hn : NewColourSet n before after vertices)
    (hr : ConsistentOn n comments after roles) : RolesConsistentOnVertices n comments vertices roles := by
  have hb := Forall.iff_forall_mem.mp hn.2.1
  have hc (v : Int) (hm : v ∈ vertices) : Znth v after 0 ≠ -1 := ((hn.2.2.1 v (hb v hm)).mp hm).2
  refine ⟨hr.1.1, ?_, ?_⟩
  · intro v hv
    exact hr.1.2.1 v (hb v hv) (hc v hv)
  · intro i hi
    rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
    dsimp
    intro hum hvm
    have hp := hr.2 i hi
    rw [hq] at hp
    exact hp (hc u hum) (hc v hvm)

theorem component_roles_sum__scan_and_component_closure (n : Int) (comments : List Comment)
    (before after vertices roles : List Int) (c0 c1 : Int)
    (hn : NewColourSet n before after vertices) (hcv : ColourValues n after)
    (h0 : ColourCount after vertices 0 c0) (h1 : ColourCount after vertices 1 c1)
    (hl : ComponentTwoChoicesLocal n comments after vertices) (hr : ConsistentOn n comments after roles) :
    ∃ flip : Int, (flip = 0 ∨ flip = 1) ∧
      (vertices.map (fun v => Znth (v-1) roles 0)).foldr (· + ·) 0 = if flip = 0 then c1 else c0 := by
  obtain ⟨flip,hf,hpoint⟩ := hl roles (consistent_on_vertices__scan_and_component_closure _ _ _ _ _ _ hn hr)
  refine ⟨flip,hf,?_⟩
  have heq : vertices.map (fun v => Znth (v-1) roles 0) = vertices.map (fun v => Z.lxor (Znth v after 0) flip) :=
    List.map_congr_left hpoint
  rw [heq]
  exact component_bit_sum__scan_and_component_closure n after vertices c0 c1 flip hcv hn.2.1
    (fun v hv => ((hn.2.2.1 v (Forall.iff_forall_mem.mp hn.2.1 v hv)).mp hv).2) h0 h1 hf

theorem sum_map_zero__scan_and_component_closure (xs : List Int) :
    (xs.map (fun _ => (0:Int))).foldr (· + ·) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa using ih

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
