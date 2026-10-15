import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_frontier_origin
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem p081_continuation_mono (n m : Int) (output : List Int) (og cg : List (List Int)) (first earlier anchor : Int)
    (hle : earlier≤anchor) (h : P081ExchangeContinuation n m output og cg first anchor) : P081ExchangeContinuation n m output og cg first earlier := by
  intro lower target q origin before painted oi oj side cs hl hcf hf he hlt ht hs hp hi hj hqr hqc hcolor hcomp hcs hcin hcjm hcross hcc htr htc
  exact h lower target q origin before painted oi oj side cs hl hcf hf he (by omega) ht hs hp hi hj hqr hqc hcolor hcomp hcs hcin hcjm hcross hcc htr htc

theorem existing_frontier_exchange_from_extend_ih__solver_final (n m anchor next : Int) (before output : List Int)
    (output_grid candidate : List (List Int)) (first i j color side : Int) :
    1≤n → 1≤m → anchor=i*m+j → GreedyPlacementTrace n m anchor before → GreedyPlacementTrace n m next output →
    (anchor<first ∧ first<next) → first=i*m+(j+side) → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → j+side<m → SettledSquareState before n m i j color side → Znth first before 0≠0 →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    Znth first (Flatten candidate) 0=color → Znth first output 0≠color →
    P081ExchangeContinuation n m output output_grid candidate first anchor → Znth first output 0≤color := by
  intro hn hm ha hbefore hout hfr hf hrows ht hi hj hfront hs hnz hp hcf hof hext
  have hside := hs.1.2.1.1
  have hfc : 0≤j+side ∧ j+side<m := by omega
  obtain ⟨earlier,origin,painted,oi,oj,found,oside,he,hlt,htr,hos,hop,hoi,hoj,hpoi,hpoj,hcolor,hcomp⟩ :=
    trace_existing_component_origin_before__solver_final n m anchor before next output output_grid (i,j+side) hn hm hbefore hout (by omega) hrows hi hfc (by rw [← hf]; exact hnz)
  have hfound : Znth first output 0=found := by
    rw [hf,← rows_of_flat_Znth__solver_final n m output output_grid i (j+side) hrows hi hfc]
    exact hcolor
  have hplace := hos.1.2.1
  have hdiff : Znth first output 0≠Znth first (Flatten candidate) 0 := by rw [hcf]; exact hof
  rcases first_cell_component_dichotomy__solver_final n m output candidate output_grid first (i,j+side) earlier oi oj found oside
    hn hm hrows ht hi hfc hf he hoi hoj hplace.1 hplace.2.1 hplace.2.2.1 hpoi hpoj hfound hcomp (by omega) hp hdiff
    with hbad | ⟨cs,hcs,hcin,hcjm,hshort,hpi,hpj,hcc⟩
  · omega
  · have hb := (trace_bounds_and_canonical__solver_final n m earlier origin hn hm htr).1
    rw [← hcf]
    exact shrink_exchange_from_extend_ih__solver_final n m earlier next output output_grid candidate first origin oi oj found oside cs
      hn hm hout hrows ht he (by omega) hoi hoj htr hos ⟨hcs,hshort⟩ (by change i=oi at hpi; change j+side=oj+cs at hpj; rw [hf,hpi,hpj])
      hfound hp (p081_continuation_mono n m output output_grid candidate first earlier anchor (by omega) hext)

theorem extend_fallback_from_ih__solver_final (n m anchor next : Int) (before painted output : List Int)
    (output_grid candidate : List (List Int)) (first : Int) (target q : Cell) (i j color side candidate_side fallback : Int) :
    1≤n → 1≤m → anchor=i*m+j → (anchor<first ∧ first<next) → GreedyPlacementTrace n m anchor before →
    GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    first=target.1*m+target.2 → (0≤target.1 ∧ target.1<n) → (0≤target.2 ∧ target.2<m) → (0≤i ∧ i<n) → (0≤j ∧ j<m) →
    SettledSquareState before n m i j color side → Znth anchor before 0=0 → PaintRectanglePrefix before painted m i j side color (side*side) →
    (i≤q.1 ∧ q.1<i+side) → (j≤q.2 ∧ q.2<j+side) → Znth q.2 (Znth q.1 output_grid []) 0=color →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath output_grid q x ↔ (i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side))) →
    1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → side<candidate_side →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath candidate (i,j) x ↔ (i≤x.1 ∧ x.1<i+candidate_side) ∧ (j≤x.2 ∧ x.2<j+candidate_side))) →
    (i≤target.1 ∧ target.1<i+candidate_side) → (j≤target.2 ∧ target.2<j+candidate_side) →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    Znth first (Flatten candidate) 0=color → Znth first output 0≠color → LeastLegalColor before n m i (j+side) color fallback → fallback≤color →
    P081ExchangeContinuation n m output output_grid candidate first anchor → Znth first output 0≤color := by
  intro hn hm ha hfr hbefore hout hrows ht hf htr htc hi hj hs hz hp hqi hqj hqcolor hcomp hcs hcin hcjm hcross hcc htri htci hprefix hcf hof hfall hfallle hext
  have hplace := hs.1.2.1
  have hside := hplace.1
  have hin := hplace.2.1
  have hjm := hplace.2.2.1
  have hqr : 0≤q.1 ∧ q.1<n := by omega
  have hqc : 0≤q.2 ∧ q.2<m := by omega
  have hoc := exact_component_reanchor__solver_final output_grid n m q (i,j) i j side hrows.1
    (p081_rows_first_length n m output output_grid (by omega) hrows) hside hi.1 hj.1 hin hjm hqr hqc hqi hqj hi hj (by dsimp; omega) (by dsimp; omega) hcomp
  have hoa : Znth (i*m+j) output 0=color := by
    rw [← rows_of_flat_Znth__solver_final n m output output_grid i j hrows hi hj]
    exact (same_color_path_endpoint_color__solver_final output_grid q (i,j) ((hcomp (i,j) hi hj).mpr (by dsimp; omega))).trans hqcolor
  have hfe := extend_first_is_frontier__solver_final n m output output_grid candidate first target i j color side candidate_side
    hn hm hrows ht hi hj hside hin hjm hcross hcin hcjm htr htc hf htri htci (by omega) hprefix hoa hcf hof hoc hcc
  have hfront : j+side<m := by omega
  have hb := trace_bounds_and_canonical__solver_final n m next output hn hm hout
  have hab := (trace_bounds_and_canonical__solver_final n m anchor before hn hm hbefore).1
  have hcolored := hb.2.2.2 first (by omega)
  have hnz : Znth first output 0≠0 := by omega
  by_cases hzero : Znth first before 0=0
  · rw [hfe]
    exact frontier_zero_fallback_bound__solver_final n m anchor next before painted output output_grid i j color side fallback
      hn hm ha hbefore hout (by omega) hrows hi hj hfront hz hs hp (by rw [← hfe]; exact hzero) (by rw [← hfe]; exact hnz) hfall hfallle
  · exact existing_frontier_exchange_from_extend_ih__solver_final n m anchor next before output output_grid candidate first i j color side
      hn hm ha hbefore hout hfr hfe hrows ht hi hj hfront hs hzero hprefix hcf hof hext
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
