import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_trace_uniqueness
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem p081_cell_index_bounds (n m : Int) (p : Cell) (hm : 0≤m)
    (hr : 0≤p.1 ∧ p.1<n) (hc : 0≤p.2 ∧ p.2<m) : 0≤p.1*m+p.2 ∧ p.1*m+p.2<n*m := by
  constructor
  · nlinarith [mul_nonneg hr.1 hm,hc.1]
  · nlinarith [hr.2,hc.2]

theorem conflict_component_crosses_candidate__solver_final (n m : Int) (output : List Int) (output_grid candidate : List (List Int))
    (first : Int) (p q : Cell) (oi oj color oside : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) → first=p.1*m+p.2 →
    (0≤oi ∧ oi<n) → (0≤oj ∧ oj<m) → 1≤oside → oi+oside≤n → oj+oside≤m →
    (oi≤q.1 ∧ q.1<oi+oside) → (oj≤q.2 ∧ q.2<oj+oside) → oi*m+oj<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    Znth (oi*m+oj) output 0=color → Znth first (Flatten candidate) 0=color → Znth first output 0≠color → AdjCell p q →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath output_grid q x ↔ (oi≤x.1 ∧ x.1<oi+oside) ∧ (oj≤x.2 ∧ x.2<oj+oside))) →
    ∃ candidate_side, 1≤candidate_side ∧ oi+candidate_side≤n ∧ oj+candidate_side≤m ∧ oside<candidate_side ∧
      (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
        (SameColorPath candidate (oi,oj) x ↔ (oi≤x.1 ∧ x.1<oi+candidate_side) ∧ (oj≤x.2 ∧ x.2<oj+candidate_side))) ∧
      (oi≤p.1 ∧ p.1<oi+candidate_side) ∧ (oj≤p.2 ∧ p.2<oj+candidate_side) := by
  intro hn hm ho ht hpr hpc hqr hqc hf hoi hoj hos hoin hojm hqoi hqoj ha hp hoa hcf hof hadj hoc
  obtain ⟨cs,hcs,hcin,hcjm,hcc⟩ := candidate_component_at_output_member__solver_final n m output candidate output_grid q oi oj oside first
    hn hm ho ht hqr hqc hoi hoj hos hoin hojm hqoi hqoj ha hp hoc
  have hc := square_tiling_rows__solver_final n m candidate ht
  have hcl := hc.1
  have hcw := p081_rows_first_length n m (Flatten candidate) candidate (by omega) hc
  have hacolor : Znth oj (Znth oi candidate []) 0=color := by
    rw [rows_of_flat_Znth__solver_final n m (Flatten candidate) candidate oi oj hc hoi hoj]
    rw [← hp (oi*m+oj) ⟨(p081_cell_index_bounds n m (oi,oj) (by omega) hoi hoj).1,ha⟩]
    exact hoa
  have hpcolor : Znth p.2 (Znth p.1 candidate []) 0=color := by
    rw [rows_of_flat_Znth__solver_final n m (Flatten candidate) candidate p.1 p.2 hc hpr hpc,← hf]
    exact hcf
  have hnot : ¬ ((oi≤p.1 ∧ p.1<oi+oside) ∧ (oj≤p.2 ∧ p.2<oj+oside)) := by
    intro hrect
    have hqp := same_color_path_endpoint_color__solver_final output_grid q p ((hoc p hpr hpc).mpr hrect)
    have hqa := same_color_path_endpoint_color__solver_final output_grid q (oi,oj) ((hoc (oi,oj) hoi hoj).mpr (by dsimp; omega))
    apply hof
    rw [hf,← rows_of_flat_Znth__solver_final n m output output_grid p.1 p.2 ho hpr hpc]
    exact hqp.trans (hqa.symm.trans ((rows_of_flat_Znth__solver_final n m output output_grid oi oj ho hoi hoj).trans hoa))
  have hlong : oside≤cs := by
    by_contra hlt
    have hshort : cs<oside := by omega
    have hb : first≤oi*m+(oj+cs) := by
      by_contra hgt
      have h := candidate_component_not_short_before_member__solver_final n m output candidate output_grid q oi oj oside cs first
        hn hm ho ht hqr hqc hoi hoj hos hoin hojm hqoi hqoj hcs hcin hcjm (by omega) hp hoc hcc
      omega
    have hnotleft : q≠(p.1,p.2-1) := by
      intro he
      have hrow := congrArg Prod.fst he
      have hcol := congrArg Prod.snd he
      dsimp at hrow hcol
      have hprlo : oi≤p.1 := by omega
      by_cases hpreq : p.1=oi
      · have : oj+oside≤p.2 := by omega
        rw [hpreq] at hf
        omega
      · have : oi<p.1 := by omega
        nlinarith [hpc.1]
    rcases earlier_rectangle_crossing_geometry__solver_final m oi oj oside cs first p q hm hoj.1 hojm hcs hcjm ha hf hpc hqoi hqoj hadj hnotleft hb with hins | he
    · exact hnot (by omega)
    · have hrow : p.1=oi := by
        rcases lt_trichotomy p.1 oi with hlt | heq | hgt
        · nlinarith [hpc.2]
        · exact heq
        · nlinarith [hpc.1]
      have hcol : p.2=oj+cs := by rw [hrow] at hf; omega
      have hbound := exact_component_boundary_color__solver_final candidate (oi,oj) (oi,oj+cs-1) p oi oj cs n m hcl hcw
        hoi hoj hoi (by dsimp; omega) hpr hpc (by dsimp; omega) (by dsimp; omega) (by omega)
        (by simp [AdjCell,Z.abs,hrow,hcol,show oj+cs-1-(oj+cs)=(-1 : Int) by omega]) hcc
      exact hbound (hpcolor.trans hacolor.symm)
  have hcq := (hcc q hqr hqc).mpr (by omega)
  have hcp := same_color_path_append__solver_final candidate (oi,oj) q p hcq (by omega) (by omega)
    (hpcolor.trans hacolor.symm) (adjcell_sym__solver_final p q hadj)
  have hpcand := (hcc p hpr hpc).mp hcp
  have hstrict : oside<cs := by
    by_contra hnlt
    exact hnot (by omega)
  exact ⟨cs,hcs,hcin,hcjm,hstrict,hcc,hpcand⟩

theorem trace_existing_component_origin_before__solver_final (n m start : Int) (prior : List Int) (next : Int)
    (output : List Int) (output_grid : List (List Int)) (p : Cell) :
    1≤n → 1≤m → GreedyPlacementTrace n m start prior → GreedyPlacementTrace n m next output → start≤next →
    RowsOfFlat n m output output_grid → (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → Znth (p.1*m+p.2) prior 0≠0 →
    ∃ (anchor : Int) (before painted : List Int) (i j color side : Int), anchor=i*m+j ∧ anchor<start ∧
      GreedyPlacementTrace n m anchor before ∧ SettledSquareState before n m i j color side ∧
      PaintRectanglePrefix before painted m i j side color (side*side) ∧
      (0≤i ∧ i<n) ∧ (0≤j ∧ j<m) ∧ (i≤p.1 ∧ p.1<i+side) ∧ (j≤p.2 ∧ p.2<j+side) ∧
      Znth p.2 (Znth p.1 output_grid []) 0=color ∧
      ∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
        (SameColorPath output_grid p q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side)) := by
  intro hn hm hprior hout hs hrows hpr hpc hnz
  have hk := p081_cell_index_bounds n m p (by omega) hpr hpc
  have ho := greedy_trace_prefix_persistence__solver_final n m start next prior output hn hm hs hprior hout (p.1*m+p.2) hk hnz
  have hgnz : Znth p.2 (Znth p.1 output_grid []) 0≠0 := by
    rw [rows_of_flat_Znth__solver_final n m output output_grid p.1 p.2 hrows hpr hpc,ho]
    exact hnz
  obtain ⟨anchor,before,painted,i,j,color,side,ha,han,htr,hset,hpaint,hi,hj,hpri,hpci,hcolor,hcomp,hpersist⟩ :=
    trace_colored_component_origin__solver_final n m next output output_grid p hn hm hout hrows hpr hpc hgnz
  have hal : anchor<start := by
    by_contra hge
    have he := greedy_trace_prefix_persistence__solver_final n m start anchor prior before hn hm (by omega) hprior htr (p.1*m+p.2) hk hnz
    have hzero := hset.1.2.1.2.2.2.1 p.1 p.2 hpri hpci
    exact hnz (he.symm.trans hzero)
  exact ⟨anchor,before,painted,i,j,color,side,ha,hal,htr,hset,hpaint,hi,hj,hpri,hpci,hcolor,hcomp⟩

theorem lower_conflict_has_crossing_component__solver_final (n m start : Int) (prior : List Int) (next : Int)
    (output : List Int) (output_grid candidate : List (List Int)) (first : Int) (p : Cell) (lower : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m start prior → GreedyPlacementTrace n m next output → start≤next → start≤first →
    RowsOfFlat n m output output_grid → SquareTiling n m candidate → (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) →
    first=p.1*m+p.2 → 65≤lower → (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    Znth first (Flatten candidate) 0=lower → Znth first output 0≠lower →
    (NeighborConflict prior n m p.1 p.2 lower 0 ∨ ∃ override, lower<override ∧ NeighborConflict prior n m p.1 p.2 lower override) →
    ∃ (q : Cell) (earlier : Int) (before painted : List Int) (oi oj side candidate_side : Int),
      earlier=oi*m+oj ∧ earlier<start ∧ GreedyPlacementTrace n m earlier before ∧ SettledSquareState before n m oi oj lower side ∧
      PaintRectanglePrefix before painted m oi oj side lower (side*side) ∧ (0≤oi ∧ oi<n) ∧ (0≤oj ∧ oj<m) ∧
      (oi≤q.1 ∧ q.1<oi+side) ∧ (oj≤q.2 ∧ q.2<oj+side) ∧ Znth q.2 (Znth q.1 output_grid []) 0=lower ∧
      (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
        (SameColorPath output_grid q x ↔ (oi≤x.1 ∧ x.1<oi+side) ∧ (oj≤x.2 ∧ x.2<oj+side))) ∧
      1≤candidate_side ∧ oi+candidate_side≤n ∧ oj+candidate_side≤m ∧ side<candidate_side ∧
      (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
        (SameColorPath candidate (oi,oj) x ↔ (oi≤x.1 ∧ x.1<oi+candidate_side) ∧ (oj≤x.2 ∧ x.2<oj+candidate_side))) ∧
      (oi≤p.1 ∧ p.1<oi+candidate_side) ∧ (oj≤p.2 ∧ p.2<oj+candidate_side) := by
  intro hn hm hprior hout hs hsf hrows ht hpr hpc hf hl hp hcf hof hconf
  have hneighbor : ∃ q : Cell, (0≤q.1 ∧ q.1<n) ∧ (0≤q.2 ∧ q.2<m) ∧ AdjCell (p.1,p.2) q ∧ Znth (q.1*m+q.2) prior 0=lower := by
    rcases hconf with hz | ⟨override,hlt,hconf⟩
    · exact conflict_zero_has_painted_neighbour__solver_final prior n m p.1 p.2 lower hn hm hpr hpc hl hz
    · obtain ⟨q,hqr,hqc,hadj,hnotleft,hq⟩ := smaller_conflict_has_painted_neighbour__solver_final prior n m p.1 p.2 lower override hn hm hpr hpc (by omega) hlt hconf
      exact ⟨q,hqr,hqc,hadj,hq⟩
  obtain ⟨q,hqr,hqc,hadj,hqprior⟩ := hneighbor
  have hk := p081_cell_index_bounds n m q (by omega) hqr hqc
  have hnz : Znth (q.1*m+q.2) prior 0≠0 := by omega
  obtain ⟨earlier,before,painted,oi,oj,found,side,he,hest,htr,hset,hpaint,hoi,hoj,hqoi,hqoj,hfound,hcomp⟩ :=
    trace_existing_component_origin_before__solver_final n m start prior next output output_grid q hn hm hprior hout hs hrows hqr hqc hnz
  have hqcolor : Znth q.2 (Znth q.1 output_grid []) 0=lower := by
    rw [rows_of_flat_Znth__solver_final n m output output_grid q.1 q.2 hrows hqr hqc,
      greedy_trace_prefix_persistence__solver_final n m start next prior output hn hm hs hprior hout (q.1*m+q.2) hk hnz]
    exact hqprior
  have hecolor : found=lower := hfound.symm.trans hqcolor
  rw [hecolor] at hset hpaint
  have hside := hset.1.2.1.1
  have hin := hset.1.2.1.2.1
  have hjm := hset.1.2.1.2.2.1
  have hacolor : Znth (oi*m+oj) output 0=lower := by
    rw [← rows_of_flat_Znth__solver_final n m output output_grid oi oj hrows hoi hoj]
    exact (same_color_path_endpoint_color__solver_final output_grid q (oi,oj) ((hcomp (oi,oj) hoi hoj).mpr (by dsimp; omega))).trans hqcolor
  obtain ⟨cs,hcs,hcin,hcjm,hcross,hcc,hpcand⟩ := conflict_component_crosses_candidate__solver_final n m output output_grid candidate first p q oi oj lower side
    hn hm hrows ht hpr hpc hqr hqc hf hoi hoj hside hin hjm hqoi hqoj (by omega) hp hacolor hcf hof hadj hcomp
  exact ⟨q,earlier,before,painted,oi,oj,side,cs,he,hest,htr,hset,hpaint,hoi,hoj,hqoi,hqoj,hqcolor,hcomp,hcs,hcin,hcjm,hcross,hcc,hpcand⟩
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
