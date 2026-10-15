import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_partial_spec
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

theorem trace_colored_origin__solver_final (n m next : Int) (flat : List Int) (k : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next flat → (0≤k ∧ k<n*m) → Znth k flat 0≠0 →
    ∃ anchor before painted i j color side off,
      anchor=i*m+j ∧ anchor<next ∧ GreedyPlacementTrace n m anchor before ∧ SettledSquareState before n m i j color side ∧
      PaintRectanglePrefix before painted m i j side color (side*side) ∧ (0≤off ∧ off<side*side) ∧
      k=(i+off /ᶻ side)*m+(j+off mod side) ∧ Znth k flat 0=color := by
  intro hn hm ht
  induction ht with
  | GreedyTrace_zero flat hl hz => intro hk hnz; exact False.elim (hnz (hz k hk))
  | GreedyTrace_skip next flat ht hn hc ih =>
    intro hk hnz
    obtain ⟨anchor,before,painted,i,j,color,side,off,ha,hlt,ht,hs,hp,hoff,hmap,hcol⟩ := ih hk hnz
    exact ⟨anchor,before,painted,i,j,color,side,off,ha,by omega,ht,hs,hp,hoff,hmap,hcol⟩
  | GreedyTrace_place next before after i j color side ht he hi hj hz hs hp ih =>
    intro hk hnz
    have hl := (trace_bounds_and_canonical__solver_final n m next before hn hm ht).2.1
    rcases hp.2 k (by omega) with ⟨⟨off,hoff,hmap⟩,hcol⟩ | ⟨hout,hsame⟩
    · exact ⟨i*m+j,before,after,i,j,color,side,off,rfl,by omega,he ▸ ht,hs,hp,hoff,hmap,hcol⟩
    · have hbnz : Znth k before 0≠0 := by rw [←hsame]; exact hnz
      obtain ⟨anchor,origin,painted,oi,oj,ocol,oside,off,ha,hlt,ht,hs,hp,hoff,hmap,hcol⟩ := ih hk hbnz
      exact ⟨anchor,origin,painted,oi,oj,ocol,oside,off,ha,by omega,ht,hs,hp,hoff,hmap,hsame.trans hcol⟩

theorem trace_colored_component_origin__solver_final (n m next : Int) (flat : List Int) (grid : List (List Int)) (p : Cell) :
    1≤n → 1≤m → GreedyPlacementTrace n m next flat → RowsOfFlat n m flat grid →
    (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → Znth p.2 (Znth p.1 grid []) 0≠0 →
    ∃ anchor before painted i j color side,
      anchor=i*m+j ∧ anchor<next ∧ GreedyPlacementTrace n m anchor before ∧ SettledSquareState before n m i j color side ∧
      PaintRectanglePrefix before painted m i j side color (side*side) ∧ (0≤i ∧ i<n) ∧ (0≤j ∧ j<m) ∧
      (i≤p.1 ∧ p.1<i+side) ∧ (j≤p.2 ∧ p.2<j+side) ∧ Znth p.2 (Znth p.1 grid []) 0=color ∧
      (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
        (SameColorPath grid p q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side))) ∧
      (∀ k, (0≤k ∧ k<n*m) → Znth k before 0≠0 → Znth k flat 0=Znth k before 0) := by
  intro hn hm ht
  induction ht generalizing grid p with
  | GreedyTrace_zero flat hl hz =>
    intro hrows hpr hpc hpnz
    apply False.elim; apply hpnz
    rw [rows_of_flat_Znth__solver_final n m flat grid p.1 p.2 hrows hpr hpc]
    apply hz
    constructor <;> nlinarith
  | GreedyTrace_skip next flat ht hn hc ih =>
    intro hrows hpr hpc hpnz
    obtain ⟨anchor,before,painted,i,j,color,side,ha,hlt,ht,hs,hp,hi,hj,hpir,hpic,hcol,hcomp,hpersist⟩ := ih grid p hrows hpr hpc hpnz
    exact ⟨anchor,before,painted,i,j,color,side,ha,by omega,ht,hs,hp,hi,hj,hpir,hpic,hcol,hcomp,hpersist⟩
  | GreedyTrace_place next before after i j color side ht he hi hj hz hs hp ih =>
    intro hrows hpr hpc hpnz
    have hl := (trace_bounds_and_canonical__solver_final n m next before hn hm ht).2.1
    have hplace := hs.1.2.1
    by_cases hpin : (i≤p.1 ∧ p.1<i+side) ∧ (j≤p.2 ∧ p.2<j+side)
    · refine ⟨i*m+j,before,after,i,j,color,side,rfl,by omega,he ▸ ht,hs,hp,hi,hj,hpin.1,hpin.2,?_,?_,?_⟩
      · rw [rows_of_flat_Znth__solver_final n m after grid p.1 p.2 hrows hpr hpc]
        exact (paint_rectangle_coordinate__solver_final before after n m i j side color p.1 p.2 hm hi hj hpr hpc hplace hl hp).1 hpin
      · intro q hqr hqc
        exact sealed_component_unique__solver_final before after n m i j side color grid p q hn hm hi hj hl hplace hp hrows hpin.1 hpin.2 hqr hqc
      · intro k hk hnz
        exact paint_preserves_nonzero__solver_final before after n m i j side color hplace hp k (by omega) hnz
    · have hpsame := (paint_rectangle_coordinate__solver_final before after n m i j side color p.1 p.2 hm hi hj hpr hpc hplace hl hp).2 hpin
      obtain ⟨bg,hb⟩ := rows_of_flat_from_length__solver_final n m before hn hm hl
      have hpbnz : Znth p.2 (Znth p.1 bg []) 0≠0 := by
        rw [rows_of_flat_Znth__solver_final n m before bg p.1 p.2 hb hpr hpc,←hpsame,
          ←rows_of_flat_Znth__solver_final n m after grid p.1 p.2 hrows hpr hpc]
        exact hpnz
      obtain ⟨anchor,origin,painted,oi,oj,ocol,oside,ha,hlt,hot,hos,hop,hoi,hoj,hpir,hpic,hcol,hcomp,hpersist⟩ := ih bg p hb hpr hpc hpbnz
      refine ⟨anchor,origin,painted,oi,oj,ocol,oside,ha,by omega,hot,hos,hop,hoi,hoj,hpir,hpic,?_,?_,?_⟩
      · rw [rows_of_flat_Znth__solver_final n m after grid p.1 p.2 hrows hpr hpc,hpsame,
          ←rows_of_flat_Znth__solver_final n m before bg p.1 p.2 hb hpr hpc]
        exact hcol
      · exact old_component_preserved__solver_final before after n m i j side color bg grid p oi oj oside hn hm hi hj hl hplace hp hb hrows hpr hpc hpin hpnz hos.1.2.1.1 hoi.1 hoj.1 hos.1.2.1.2.1 hos.1.2.1.2.2.1 hpir hpic hcomp
      · intro k hk hnz
        have hbeq := hpersist k hk hnz
        have hbnz : Znth k before 0≠0 := by rw [hbeq]; exact hnz
        exact (paint_preserves_nonzero__solver_final before after n m i j side color hplace hp k (by omega) hbnz).trans hbeq
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
