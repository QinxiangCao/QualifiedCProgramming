import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_candidate_geometry
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem exact_component_reanchor__solver_final (grid : List (List Int)) (n m : Int) (p anchor : Cell) (r c side : Int) :
    Zlength grid=n → Zlength (Znth 0 grid [])=m → 1≤side → 0≤r → 0≤c → r+side≤n → c+side≤m →
    (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → (r≤p.1 ∧ p.1<r+side) → (c≤p.2 ∧ p.2<c+side) →
    (0≤anchor.1 ∧ anchor.1<n) → (0≤anchor.2 ∧ anchor.2<m) →
    (r≤anchor.1 ∧ anchor.1<r+side) → (c≤anchor.2 ∧ anchor.2<c+side) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath grid p q ↔ (r≤q.1 ∧ q.1<r+side) ∧ (c≤q.2 ∧ q.2<c+side))) →
    ∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath grid anchor q ↔ (r≤q.1 ∧ q.1<r+side) ∧ (c≤q.2 ∧ q.2<c+side)) := by
  intro hl hw hs hr hc hrn hcm hpr hpc hpri hpci har hac hari haci hcomp q hqr hqc
  have hcolor (x : Cell) (hxr : r≤x.1 ∧ x.1<r+side) (hxc : c≤x.2 ∧ x.2<c+side) :
      Znth x.2 (Znth x.1 grid []) 0=Znth p.2 (Znth p.1 grid []) 0 :=
    same_color_path_endpoint_color__solver_final grid p x ((hcomp x (by omega) (by omega)).mpr ⟨hxr,hxc⟩)
  constructor
  · intro hpath
    refine same_color_path_closed__solver_final grid (Znth p.2 (Znth p.1 grid []) 0)
      (fun x => (r≤x.1 ∧ x.1<r+side) ∧ (c≤x.2 ∧ x.2<c+side)) anchor q hpath ⟨hari,haci⟩ ?_ (hcolor anchor hari haci)
    intro x y hx hyr hyc hycol hadj
    have hpx := (hcomp x (by omega) (by omega)).mpr hx
    have hpy := same_color_path_append__solver_final grid p x y hpx hyr hyc hycol hadj
    exact (hcomp y (by omega) (by omega)).mp hpy
  · intro hrect
    exact rectangle_connected__solver_final grid r c side (Znth p.2 (Znth p.1 grid []) 0) anchor q hs hr hc
      (by omega) (by omega) hari haci hrect.1 hrect.2 hcolor

theorem first_cell_component_dichotomy__solver_final (n m : Int) (output : List Int) (candidate output_grid : List (List Int))
    (first : Int) (p : Cell) (anchor i j color side : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → first=p.1*m+p.2 → anchor=i*m+j →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 1≤side → i+side≤n → j+side≤m →
    (i≤p.1 ∧ p.1<i+side) → (j≤p.2 ∧ p.2<j+side) → Znth first output 0=color →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath output_grid p q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) → anchor≤first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) → Znth first output 0≠Znth first (Flatten candidate) 0 →
    anchor=first ∨ ∃ candidate_side, 1≤candidate_side ∧ i+candidate_side≤n ∧ j+candidate_side≤m ∧
      candidate_side<side ∧ p.1=i ∧ p.2=j+candidate_side ∧
      ∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
        (SameColorPath candidate (i,j) q ↔ (i≤q.1 ∧ q.1<i+candidate_side) ∧ (j≤q.2 ∧ q.2<j+candidate_side)) := by
  intro hn hm ho ht hpr hpc hf ha hi hj hs hin hjm hpri hpci hcolor hcomp hal hp hd
  by_cases he : anchor=first
  · exact Or.inl he
  · right
    have hac : i*m+j<first := by omega
    have hoc := exact_component_reanchor__solver_final output_grid n m p (i,j) i j side ho.1
      (p081_rows_first_length n m output output_grid (by omega) ho) hs hi.1 hj.1 hin hjm hpr hpc hpri hpci hi hj (by dsimp; omega) (by dsimp; omega) hcomp
    obtain ⟨cs,hcs,hcin,hcjm,hcc⟩ := candidate_component_at_output_anchor__solver_final n m output candidate output_grid i j side first
      hn hm ho ht hi hj hs hin hjm hac hp hoc
    have hcut := component_prefix_cut__solver_final n m output (Flatten candidate) output_grid candidate i j side i j cs first p
      hn hm ho (square_tiling_rows__solver_final n m candidate ht) hi hj hs hin hjm hcs hi.1 hj.1 hcin hcjm
      (by omega) (by omega) hpri hpci hf hac hp hd hoc hcc
    exact ⟨cs,hcs,hcin,hcjm,hcut.1,hcut.2.1,hcut.2.2,hcc⟩

theorem candidate_component_at_output_member__solver_final (n m : Int) (output : List Int) (candidate output_grid : List (List Int))
    (p : Cell) (i j side first : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → (0≤i ∧ i<n) → (0≤j ∧ j<m) →
    1≤side → i+side≤n → j+side≤m → (i≤p.1 ∧ p.1<i+side) → (j≤p.2 ∧ p.2<j+side) → i*m+j<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath output_grid p q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) →
    ∃ candidate_side, 1≤candidate_side ∧ i+candidate_side≤n ∧ j+candidate_side≤m ∧
      ∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
        (SameColorPath candidate (i,j) q ↔ (i≤q.1 ∧ q.1<i+candidate_side) ∧ (j≤q.2 ∧ q.2<j+candidate_side)) := by
  intro hn hm ho ht hpr hpc hi hj hs hin hjm hpri hpci ha hp hcomp
  have hoc := exact_component_reanchor__solver_final output_grid n m p (i,j) i j side ho.1
    (p081_rows_first_length n m output output_grid (by omega) ho) hs hi.1 hj.1 hin hjm hpr hpc hpri hpci hi hj (by dsimp; omega) (by dsimp; omega) hcomp
  exact candidate_component_at_output_anchor__solver_final n m output candidate output_grid i j side first hn hm ho ht hi hj hs hin hjm ha hp hoc

theorem candidate_component_not_short_before_member__solver_final (n m : Int) (output : List Int) (candidate output_grid : List (List Int))
    (p : Cell) (i j side candidate_side first : Int) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → (0≤i ∧ i<n) → (0≤j ∧ j<m) →
    1≤side → i+side≤n → j+side≤m → (i≤p.1 ∧ p.1<i+side) → (j≤p.2 ∧ p.2<j+side) →
    1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → i*m+(j+candidate_side)<first →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath output_grid p q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath candidate (i,j) q ↔ (i≤q.1 ∧ q.1<i+candidate_side) ∧ (j≤q.2 ∧ q.2<j+candidate_side))) → side≤candidate_side := by
  intro hn hm ho ht hpr hpc hi hj hs hin hjm hpri hpci hcs hcin hcjm hb hp hcomp hcc
  have hoc := exact_component_reanchor__solver_final output_grid n m p (i,j) i j side ho.1
    (p081_rows_first_length n m output output_grid (by omega) ho) hs hi.1 hj.1 hin hjm hpr hpc hpri hpci hi hj (by dsimp; omega) (by dsimp; omega) hcomp
  exact candidate_component_not_short_before__solver_final n m output (Flatten candidate) output_grid candidate i j side candidate_side first
    hn hm ho (square_tiling_rows__solver_final n m candidate ht) hi hj hs hin hjm hcs hcin hcjm hb hp hoc hcc
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
