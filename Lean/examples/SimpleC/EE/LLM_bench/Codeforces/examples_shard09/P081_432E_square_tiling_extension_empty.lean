import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_component_disjointness
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem extension_candidate_square_empty__solver_final (n m anchor next : Int) (before output : List Int)
    (output_grid candidate : List (List Int)) (first i j color side candidate_side : Int) :
    1≤n → 1≤m → anchor=i*m+j → (anchor<first ∧ first<next) → GreedyPlacementTrace n m anchor before →
    GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → CanPlace before n m i j side color →
    1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → side<candidate_side → first=i*m+(j+side) →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
      (SameColorPath candidate (i,j) z ↔ (i≤z.1 ∧ z.1<i+candidate_side) ∧ (j≤z.2 ∧ z.2<j+candidate_side))) →
    ∀ r c, (i≤r ∧ r<i+side+1) → (j≤c ∧ c<j+side+1) → Znth (r*m+c) before 0=0 := by
  intro hn hm ha hfr hbefore hout hrows ht hi hj hplace hcs hcin hcjm hcross hf hp hcc r c hr hc
  by_contra hnz
  obtain ⟨earlier,origin,painted,oi,oj,found,oside,he,hlt,htr,hos,hop,hoi,hoj,hxoi,hxoj,hcolor,hcomp⟩ :=
    trace_existing_component_origin_before__solver_final n m anchor before next output output_grid (r,c)
      hn hm hbefore hout (by omega) hrows (by dsimp; omega) (by dsimp; omega) hnz
  have hoplace := hos.1.2.1
  exact earlier_component_excluded_from_candidate_square__solver_final n m output output_grid candidate first i j side candidate_side (r,c) oi oj oside (r,c)
    hn hm hrows ht hi hj hplace.1 hplace.2.1 hplace.2.2.1 hcs hcin hcjm hcross hf hp hcc hoi hoj hoplace.1 hoplace.2.1 hoplace.2.2.1
    hxoi hxoj (by omega) hcomp hxoi hxoj (by dsimp; omega) (by dsimp; omega)

theorem earlier_candidate_component_not_short__solver_final (n m : Int) (output : List Int) (output_grid candidate : List (List Int))
    (first current_i current_j current_side candidate_side : Int) (q : Cell) (oi oj oside : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤current_i ∧ current_i<n) → (0≤current_j ∧ current_j<m) → 1≤current_side → current_i+current_side≤n → current_j+current_side≤m →
    1≤candidate_side → current_i+candidate_side≤n → current_j+candidate_side≤m → current_side<candidate_side →
    first=current_i*m+(current_j+current_side) → (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
      (SameColorPath candidate (current_i,current_j) z ↔ (current_i≤z.1 ∧ z.1<current_i+candidate_side) ∧ (current_j≤z.2 ∧ z.2<current_j+candidate_side))) →
    (0≤oi ∧ oi<n) → (0≤oj ∧ oj<m) → 1≤oside → oi+oside≤n → oj+oside≤m →
    (oi≤q.1 ∧ q.1<oi+oside) → (oj≤q.2 ∧ q.2<oj+oside) → oi*m+oj<current_i*m+current_j →
    (∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
      (SameColorPath output_grid q z ↔ (oi≤z.1 ∧ z.1<oi+oside) ∧ (oj≤z.2 ∧ z.2<oj+oside))) →
    ∃ other_side, 1≤other_side ∧ oi+other_side≤n ∧ oj+other_side≤m ∧ oside≤other_side ∧
      ∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
        (SameColorPath candidate (oi,oj) z ↔ (oi≤z.1 ∧ z.1<oi+other_side) ∧ (oj≤z.2 ∧ z.2<oj+other_side)) := by
  intro hn hm hrows ht hci hcj hcs hcin hcjm hcan hcanin hcanjm hcross hf hp hcc hoi hoj hos hoin hojm hqoi hqoj ha hoc
  have hqr : 0≤q.1 ∧ q.1<n := by omega
  have hqc : 0≤q.2 ∧ q.2<m := by omega
  obtain ⟨other,ho,hon,hom,hocand⟩ := candidate_component_at_output_member__solver_final n m output candidate output_grid q oi oj oside first
    hn hm hrows ht hqr hqc hoi hoj hos hoin hojm hqoi hqoj (by omega) hp hoc
  have hd := exact_components_rectangles_disjoint__solver_final candidate n m oi oj other current_i current_j candidate_side
    hoi hoj hci hcj ho hon hom hcan hcanin hcanjm hocand hcc (by omega)
  have hbound : oi*m+(oj+other)<first := by
    rcases disjoint_rectangles_separate__solver_final oi oj other current_i current_j candidate_side ho hcan hd with habove | hbelow | hleft | hright
    · nlinarith [hcj.1]
    · nlinarith [hoj.1,hcj.2]
    · have hile : oi≤current_i := by
        by_contra hgt
        have : current_i<oi := by omega
        nlinarith [hoj.1,hcj.2]
      nlinarith
    · have hilt : oi<current_i := by
        by_contra hge
        have : current_i≤oi := by omega
        nlinarith [hcj.1]
      nlinarith [hcj.1]
  have hlong := candidate_component_not_short_before_member__solver_final n m output candidate output_grid q oi oj oside other first
    hn hm hrows ht hqr hqc hoi hoj hos hoin hojm hqoi hqoj ho hon hom hbound hp hoc hocand
  exact ⟨other,ho,hon,hom,hlong,hocand⟩
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
