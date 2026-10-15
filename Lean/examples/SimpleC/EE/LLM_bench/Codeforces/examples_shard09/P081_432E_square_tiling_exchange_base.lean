import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_crossing
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

-- The continuation is the repeated explicit forall premise of the source exchange lemmas.
def P081ExchangeContinuation (n m : Int) (output : List Int) (output_grid candidate : List (List Int)) (first anchor : Int) : Prop :=
  ∀ (lower : Int) (target q : Cell) (earlier : Int) (origin_before painted : List Int) (oi oj side candidate_side : Int),
    65≤lower → Znth first (Flatten candidate) 0=lower → first=target.1*m+target.2 → earlier=oi*m+oj → earlier<anchor →
    GreedyPlacementTrace n m earlier origin_before → SettledSquareState origin_before n m oi oj lower side →
    PaintRectanglePrefix origin_before painted m oi oj side lower (side*side) → (0≤oi ∧ oi<n) → (0≤oj ∧ oj<m) →
    (oi≤q.1 ∧ q.1<oi+side) → (oj≤q.2 ∧ q.2<oj+side) → Znth q.2 (Znth q.1 output_grid []) 0=lower →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath output_grid q x ↔ (oi≤x.1 ∧ x.1<oi+side) ∧ (oj≤x.2 ∧ x.2<oj+side))) →
    1≤candidate_side → oi+candidate_side≤n → oj+candidate_side≤m → side<candidate_side →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath candidate (oi,oj) x ↔ (oi≤x.1 ∧ x.1<oi+candidate_side) ∧ (oj≤x.2 ∧ x.2<oj+candidate_side))) →
    (oi≤target.1 ∧ target.1<oi+candidate_side) → (oj≤target.2 ∧ target.2<oj+candidate_side) → Znth first output 0≤lower

theorem base_exchange_from_extend_ih__solver_final (n m next : Int) (output : List Int) (output_grid candidate : List (List Int))
    (first : Int) (before : List Int) (i j color side : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤first ∧ first<next) → first=i*m+j → (0≤i ∧ i<n) → (0≤j ∧ j<m) → GreedyPlacementTrace n m first before →
    SettledSquareState before n m i j color side → Znth first output 0=color →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    P081ExchangeContinuation n m output output_grid candidate first first → Znth first output 0≤Znth first (Flatten candidate) 0 := by
  intro hn hm hout hrows ht hfr hf hi hj hbefore hset hcolor hp hext
  let lower := Znth first (Flatten candidate) 0
  have hl : 65≤lower ∧ lower≤90 := square_tiling_flat_color__solver_final n m candidate first ht (by rw [hf]; exact p081_cell_index_bounds n m (i,j) (by omega) hi hj)
  by_cases hle : color≤lower
  · rw [hcolor]; exact hle
  · have hne : Znth first output 0≠lower := by omega
    have hconf : NeighborConflict before n m i j lower 0 := by
      by_contra hno
      exact hset.1.1.2 lower (by omega) ⟨hl,hno⟩
    obtain ⟨q,earlier,origin,painted,oi,oj,oside,cs,he,hlt,htr,hos,hop,hoi,hoj,hqoi,hqoj,hqcolor,hcomp,hcs,hcin,hcjm,hcross,hcc,hpr,hpc⟩ :=
      lower_conflict_has_crossing_component__solver_final n m first before next output output_grid candidate first (i,j) lower
        hn hm hbefore hout (by omega) (by omega) hrows ht hi hj hf hl.1 hp rfl hne (Or.inl hconf)
    exact hext lower (i,j) q earlier origin painted oi oj oside cs hl.1 rfl hf he hlt htr hos hop hoi hoj hqoi hqoj hqcolor hcomp hcs hcin hcjm hcross hcc hpr hpc

theorem shrink_exchange_from_extend_ih__solver_final (n m anchor next : Int) (output : List Int) (output_grid candidate : List (List Int))
    (first : Int) (before : List Int) (i j color side candidate_side : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    anchor=i*m+j → (0≤anchor ∧ anchor<next) → (0≤i ∧ i<n) → (0≤j ∧ j<m) → GreedyPlacementTrace n m anchor before →
    SettledSquareState before n m i j color side → (1≤candidate_side ∧ candidate_side<side) → first=i*m+(j+candidate_side) →
    Znth first output 0=color → (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    P081ExchangeContinuation n m output output_grid candidate first anchor → Znth first output 0≤Znth first (Flatten candidate) 0 := by
  intro hn hm hout hrows ht ha har hi hj hbefore hset hcs hf hcolor hp hext
  let lower := Znth first (Flatten candidate) 0
  have hplace := hset.1.2.1
  have hjm := hplace.2.2.1
  have hfc : 0≤j+candidate_side ∧ j+candidate_side<m := by omega
  have hl : 65≤lower ∧ lower≤90 := square_tiling_flat_color__solver_final n m candidate first ht
    (by rw [hf]; exact p081_cell_index_bounds n m (i,j+candidate_side) (by omega) hi hfc)
  by_cases hle : color≤lower
  · rw [hcolor]; exact hle
  · have hne : Znth first output 0≠lower := by omega
    obtain ⟨hplace',fallback,hfallback,hclt⟩ := hset.1.2.2 candidate_side hcs
    have hconf : NeighborConflict before n m i (j+candidate_side) lower color := by
      by_contra hno
      exact hfallback.2 lower (by omega) ⟨hl,hno⟩
    obtain ⟨q,earlier,origin,painted,oi,oj,oside,cs,he,hlt,htr,hos,hop,hoi,hoj,hqoi,hqoj,hqcolor,hcomp,hcss,hcin,hcjm,hcross,hcc,hpr,hpc⟩ :=
      lower_conflict_has_crossing_component__solver_final n m anchor before next output output_grid candidate first (i,j+candidate_side) lower
        hn hm hbefore hout (by omega) (by omega) hrows ht hi hfc hf hl.1 hp rfl hne (Or.inr ⟨color,by omega,hconf⟩)
    exact hext lower (i,j+candidate_side) q earlier origin painted oi oj oside cs hl.1 rfl hf he hlt htr hos hop hoi hoj hqoi hqoj hqcolor hcomp hcss hcin hcjm hcross hcc hpr hpc

theorem extend_first_is_frontier__solver_final (n m : Int) (output : List Int) (output_grid candidate : List (List Int))
    (first : Int) (p : Cell) (i j color side candidate_side : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 1≤side → i+side≤n → j+side≤m → side<candidate_side →
    i+candidate_side≤n → j+candidate_side≤m → (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → first=p.1*m+p.2 →
    (i≤p.1 ∧ p.1<i+candidate_side) → (j≤p.2 ∧ p.2<j+candidate_side) → i*m+j<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    Znth (i*m+j) output 0=color → Znth first (Flatten candidate) 0=color → Znth first output 0≠color →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath output_grid (i,j) x ↔ (i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side))) →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath candidate (i,j) x ↔ (i≤x.1 ∧ x.1<i+candidate_side) ∧ (j≤x.2 ∧ x.2<j+candidate_side))) → first=i*m+(j+side) := by
  intro hn hm ho ht hi hj hs hin hjm hlt hcin hcjm hpr hpc hf hpri hpci ha hp hoa hcf hof hoc hcc
  have hcut := component_prefix_cut__solver_final n m (Flatten candidate) output candidate output_grid i j candidate_side i j side first p
    hn hm (square_tiling_rows__solver_final n m candidate ht) ho hi hj (by omega) hcin hcjm hs hi.1 hj.1 hin hjm
    (by omega) (by omega) hpri hpci hf ha (fun k hk => (hp k hk).symm) (by rw [hcf]; exact Ne.symm hof) hcc hoc
  rw [hf,hcut.2.1,hcut.2.2]
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
