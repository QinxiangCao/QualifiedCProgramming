import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_exchange_foundations
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem p081_grid_prefix (n m first : Int) (output candidate : List Int) (og cg : List (List Int))
    (ho : RowsOfFlat n m output og) (hc : RowsOfFlat n m candidate cg)
    (hp : ∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k candidate 0)
    (q : Cell) (hr : 0≤q.1 ∧ q.1<n) (hcol : 0≤q.2 ∧ q.2<m) (hk : q.1*m+q.2<first) :
    Znth q.2 (Znth q.1 og []) 0=Znth q.2 (Znth q.1 cg []) 0 := by
  rw [rows_of_flat_Znth__solver_final n m output og q.1 q.2 ho hr hcol,
    rows_of_flat_Znth__solver_final n m candidate cg q.1 q.2 hc hr hcol]
  exact hp _ ⟨by nlinarith [mul_nonneg hr.1 (show 0≤m by omega),hcol.1],hk⟩

theorem candidate_component_not_short_before__solver_final (n m : Int) (output candidate : List Int)
    (output_grid candidate_grid : List (List Int)) (i j side candidate_side first : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → RowsOfFlat n m candidate candidate_grid →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 1≤side → i+side≤n → j+side≤m →
    1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → i*m+(j+candidate_side)<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k candidate 0) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath output_grid (i,j) q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath candidate_grid (i,j) q ↔ (i≤q.1 ∧ q.1<i+candidate_side) ∧ (j≤q.2 ∧ q.2<j+candidate_side))) → side≤candidate_side := by
  intro hn hm ho hc hi hj hs hin hjm hcs hcin hcjm hb hp hoc hcc
  by_contra hnot
  have hshort : candidate_side<side := by omega
  have hbc : 0≤j+candidate_side ∧ j+candidate_side<m := by omega
  have hop := (hoc (i,j+candidate_side) hi hbc).mpr (by dsimp; omega)
  have hcolor := same_color_path_endpoint_color__solver_final output_grid (i,j) (i,j+candidate_side) hop
  have hd := exact_component_boundary_color__solver_final candidate_grid (i,j) (i,j+candidate_side-1)
    (i,j+candidate_side) i j candidate_side n m hc.1 (p081_rows_first_length n m candidate candidate_grid (by omega) hc)
    hi hj hi (by dsimp; omega) hi hbc (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
    (by simp [AdjCell,Z.abs,show j+candidate_side-1-(j+candidate_side)=(-1 : Int) by omega]) hcc
  apply hd
  have hpa := p081_grid_prefix n m first output candidate output_grid candidate_grid ho hc hp (i,j) hi hj (by dsimp; nlinarith)
  have hpb := p081_grid_prefix n m first output candidate output_grid candidate_grid ho hc hp (i,j+candidate_side) hi hbc (by dsimp; nlinarith)
  exact hpb.symm.trans (hcolor.trans hpa)

theorem component_top_left_prefix__solver_final (n m : Int) (output candidate : List Int)
    (output_grid candidate_grid : List (List Int)) (i j side r c candidate_side first : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → RowsOfFlat n m candidate candidate_grid →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 1≤side → i+side≤n → j+side≤m →
    1≤candidate_side → 0≤r → 0≤c → r+candidate_side≤n → c+candidate_side≤m →
    (r≤i ∧ i<r+candidate_side) → (c≤j ∧ j<c+candidate_side) → i*m+j<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k candidate 0) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath output_grid (i,j) q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath candidate_grid (i,j) q ↔ (r≤q.1 ∧ q.1<r+candidate_side) ∧ (c≤q.2 ∧ q.2<c+candidate_side))) → r=i ∧ c=j := by
  intro hn hm ho hc hi hj hs hin hjm hcs hr hcl hrn hcm hri hcj ha hp hoc hcc
  have hl := ho.1
  have hw := p081_rows_first_length n m output output_grid (by omega) ho
  have hpa := p081_grid_prefix n m first output candidate output_grid candidate_grid ho hc hp (i,j) hi hj (by dsimp; nlinarith)
  have extend (q : Cell) (hqr : 0≤q.1 ∧ q.1<n) (hqc : 0≤q.2 ∧ q.2<m)
      (hrect : (r≤q.1 ∧ q.1<r+candidate_side) ∧ (c≤q.2 ∧ q.2<c+candidate_side))
      (hqk : q.1*m+q.2<first) (hadj : AdjCell (i,j) q) :
      (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side) := by
    have hcp := (hcc q hqr hqc).mpr hrect
    have hcolor := same_color_path_endpoint_color__solver_final candidate_grid (i,j) q hcp
    have hpq := p081_grid_prefix n m first output candidate output_grid candidate_grid ho hc hp q hqr hqc hqk
    have he : Znth q.2 (Znth q.1 output_grid []) 0=Znth j (Znth i output_grid []) 0 := hpq.trans (hcolor.trans hpa.symm)
    exact (hoc q hqr hqc).mp (same_color_path_step__solver_final output_grid (i,j) q (by change 0≤i ∧ i<Zlength output_grid; rw [hl]; exact hi) (by change 0≤j ∧ j<Zlength (Znth 0 output_grid []); rw [hw]; exact hj) (by omega) (by omega) he hadj)
  constructor
  · by_contra hne
    have h := extend (i-1,j) (by dsimp; omega) hj (by dsimp; omega) (by dsimp; nlinarith)
      (by simp [AdjCell,Z.abs,show i-(i-1)=(1 : Int) by omega])
    dsimp at h
    omega
  · by_contra hne
    have h := extend (i,j-1) hi (by dsimp; omega) (by dsimp; omega) (by dsimp; nlinarith)
      (by simp [AdjCell,Z.abs,show j-(j-1)=(1 : Int) by omega])
    dsimp at h
    omega

theorem component_prefix_cut__solver_final (n m : Int) (output candidate : List Int)
    (output_grid candidate_grid : List (List Int)) (i j side r c candidate_side first : Int) (p : Cell) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → RowsOfFlat n m candidate candidate_grid →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 1≤side → i+side≤n → j+side≤m →
    1≤candidate_side → 0≤r → 0≤c → r+candidate_side≤n → c+candidate_side≤m →
    (r≤i ∧ i<r+candidate_side) → (c≤j ∧ j<c+candidate_side) →
    (i≤p.1 ∧ p.1<i+side) → (j≤p.2 ∧ p.2<j+side) → first=p.1*m+p.2 → i*m+j<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k candidate 0) → Znth first output 0≠Znth first candidate 0 →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath output_grid (i,j) q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath candidate_grid (i,j) q ↔ (r≤q.1 ∧ q.1<r+candidate_side) ∧ (c≤q.2 ∧ q.2<c+candidate_side))) →
    candidate_side<side ∧ p.1=i ∧ p.2=j+candidate_side := by
  intro hn hm ho hc hi hj hs hin hjm hcs hr hcl hrn hcm hri hcj hpr hpc hf ha hp hd hoc hcc
  obtain ⟨hre,hce⟩ := component_top_left_prefix__solver_final n m output candidate output_grid candidate_grid i j side r c candidate_side first
    hn hm ho hc hi hj hs hin hjm hcs hr hcl hrn hcm hri hcj ha hp hoc hcc
  subst r c
  have hqr : 0≤p.1 ∧ p.1<n := by omega
  have hqc : 0≤p.2 ∧ p.2<m := by omega
  have hnot : ¬ ((i≤p.1 ∧ p.1<i+candidate_side) ∧ (j≤p.2 ∧ p.2<j+candidate_side)) := by
    intro hrect
    have hocp := same_color_path_endpoint_color__solver_final output_grid (i,j) p ((hoc p hqr hqc).mpr ⟨hpr,hpc⟩)
    have hccp := same_color_path_endpoint_color__solver_final candidate_grid (i,j) p ((hcc p hqr hqc).mpr hrect)
    have hpa := p081_grid_prefix n m first output candidate output_grid candidate_grid ho hc hp (i,j) hi hj (by dsimp; nlinarith)
    apply hd
    rw [hf,← rows_of_flat_Znth__solver_final n m output output_grid p.1 p.2 ho hqr hqc,
      ← rows_of_flat_Znth__solver_final n m candidate candidate_grid p.1 p.2 hc hqr hqc]
    exact hocp.trans (hpa.trans hccp.symm)
  have hshort : candidate_side<side := by omega
  have hle : first≤i*m+(j+candidate_side) := by
    by_contra hgt
    have h := candidate_component_not_short_before__solver_final n m output candidate output_grid candidate_grid i j side candidate_side first
      hn hm ho hc hi hj hs hin hjm hcs hrn hcm (by omega) hp hoc hcc
    omega
  have hge : i*m+(j+candidate_side)≤first := by
    by_cases he : p.1=i
    · have : j+candidate_side≤p.2 := by omega
      rw [hf,he]
      omega
    · have : i<p.1 := by omega
      nlinarith
  have hre : p.1=i := by
    by_contra hne
    have : i<p.1 := by omega
    nlinarith
  exact ⟨hshort,hre,by rw [hre] at hf; omega⟩

theorem candidate_component_at_output_anchor__solver_final (n m : Int) (output : List Int)
    (candidate output_grid : List (List Int)) (i j side first : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 1≤side → i+side≤n → j+side≤m → i*m+j<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath output_grid (i,j) q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) →
    ∃ candidate_side, 1≤candidate_side ∧ i+candidate_side≤n ∧ j+candidate_side≤m ∧
      ∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
        (SameColorPath candidate (i,j) q ↔ (i≤q.1 ∧ q.1<i+candidate_side) ∧ (j≤q.2 ∧ q.2<j+candidate_side)) := by
  intro hn hm ho ht hi hj hs hin hjm ha hp hoc
  have hc := square_tiling_rows__solver_final n m candidate ht
  obtain ⟨r,c,cs,hcs,hr,hcl,hrn,hcm,hri,hcj,hcc⟩ := square_tiling_component__solver_final n m candidate (i,j) ht hi hj
  obtain ⟨hre,hce⟩ := component_top_left_prefix__solver_final n m output (Flatten candidate) output_grid candidate i j side r c cs first
    hn hm ho hc hi hj hs hin hjm hcs hr hcl hrn hcm hri hcj ha hp hoc hcc
  subst r c
  exact ⟨cs,hcs,hrn,hcm,hcc⟩

theorem candidate_component_covers_output_prefix__solver_final (n m : Int) (output : List Int)
    (candidate output_grid : List (List Int)) (i j side candidate_side first : Int) (q : Cell) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 1≤side → i+side≤n → j+side≤m →
    1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → i*m+(j+candidate_side)<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath output_grid (i,j) x ↔ (i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side))) →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath candidate (i,j) x ↔ (i≤x.1 ∧ x.1<i+candidate_side) ∧ (j≤x.2 ∧ x.2<j+candidate_side))) →
    (i≤q.1 ∧ q.1<i+side) → (j≤q.2 ∧ q.2<j+side) →
    (i≤q.1 ∧ q.1<i+candidate_side) ∧ (j≤q.2 ∧ q.2<j+candidate_side) := by
  intro hn hm ho ht hi hj hs hin hjm hcs hcin hcjm hb hp hoc hcc hqr hqc
  have h := candidate_component_not_short_before__solver_final n m output (Flatten candidate) output_grid candidate i j side candidate_side first
    hn hm ho (square_tiling_rows__solver_final n m candidate ht) hi hj hs hin hjm hcs hcin hcjm hb hp hoc hcc
  omega
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
