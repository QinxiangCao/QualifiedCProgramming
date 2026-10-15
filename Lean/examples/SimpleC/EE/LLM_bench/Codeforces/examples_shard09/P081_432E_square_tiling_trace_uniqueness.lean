import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_candidate_members
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem conflict_zero_has_painted_neighbour__solver_final (flat : List Int) (n m i j color : Int) :
    1≤n → 1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → 65≤color → NeighborConflict flat n m i j color 0 →
    ∃ q : Cell, (0≤q.1 ∧ q.1<n) ∧ (0≤q.2 ∧ q.2<m) ∧ AdjCell (i,j) q ∧ Znth (q.1*m+q.2) flat 0=color := by
  intro hn hm hi hj hc hconf
  rcases hconf with ⟨hit,ht⟩ | ⟨hib,hb⟩ | ⟨hjr,hr⟩ | ⟨hjl,hl⟩ | ⟨hz,hbad⟩
  · exact ⟨(i-1,j),by dsimp; omega,hj,by simp [AdjCell,Z.abs,show i-(i-1)=(1 : Int) by omega],ht⟩
  · exact ⟨(i+1,j),by dsimp; omega,hj,by simp [AdjCell,Z.abs,show i-(i+1)=(-1 : Int) by omega],hb⟩
  · exact ⟨(i,j+1),hi,by dsimp; omega,by simp [AdjCell,Z.abs,show j-(j+1)=(-1 : Int) by omega],by simpa only [add_assoc] using hr⟩
  · exact ⟨(i,j-1),hi,by dsimp; omega,by simp [AdjCell,Z.abs,show j-(j-1)=(1 : Int) by omega],by simpa only [if_pos rfl,add_sub_assoc] using hl⟩
  · omega

theorem conflict_zero_has_earlier_component__solver_final (n m anchor : Int) (before : List Int)
    (before_grid : List (List Int)) (i j color : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m anchor before → RowsOfFlat n m before before_grid →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 65≤color → NeighborConflict before n m i j color 0 →
    ∃ (q : Cell) (earlier : Int) (origin_before painted : List Int) (oi oj oside : Int),
      earlier=oi*m+oj ∧ earlier<anchor ∧ GreedyPlacementTrace n m earlier origin_before ∧
      SettledSquareState origin_before n m oi oj color oside ∧
      PaintRectanglePrefix origin_before painted m oi oj oside color (oside*oside) ∧
      (0≤oi ∧ oi<n) ∧ (0≤oj ∧ oj<m) ∧ (oi≤q.1 ∧ q.1<oi+oside) ∧ (oj≤q.2 ∧ q.2<oj+oside) ∧ AdjCell (i,j) q ∧
      (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
        (SameColorPath before_grid q x ↔ (oi≤x.1 ∧ x.1<oi+oside) ∧ (oj≤x.2 ∧ x.2<oj+oside))) ∧
      (∀ k, (0≤k ∧ k<n*m) → Znth k origin_before 0≠0 → Znth k before 0=Znth k origin_before 0) := by
  intro hn hm ht hrows hi hj hc hconf
  obtain ⟨q,hqr,hqc,hadj,hqflat⟩ := conflict_zero_has_painted_neighbour__solver_final before n m i j color hn hm hi hj hc hconf
  have hqgrid := (rows_of_flat_Znth__solver_final n m before before_grid q.1 q.2 hrows hqr hqc).trans hqflat
  obtain ⟨earlier,origin,painted,oi,oj,found,oside,he,hlt,hot,hos,hop,hoi,hoj,hqoi,hqoj,hqcolor,hcomp,hpersist⟩ :=
    trace_colored_component_origin__solver_final n m anchor before before_grid q hn hm ht hrows hqr hqc (by omega)
  have hfound : found=color := hqcolor.symm.trans hqgrid
  rw [hfound] at hos hop
  exact ⟨q,earlier,origin,painted,oi,oj,oside,he,hlt,hot,hos,hop,hoi,hoj,hqoi,hqoj,hadj,hcomp,hpersist⟩

theorem greedy_trace_state_unique__solver_final (n m next : Int) (left right : List Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next left → GreedyPlacementTrace n m next right → left=right := by
  intro hn hm hl hr
  suffices go : ∀ next' right, next=next' → GreedyPlacementTrace n m next' right → left=right from go next right rfl hr
  clear hr
  induction hl with
  | GreedyTrace_zero left hlen hz =>
    intro next' right he hr
    cases hr with
    | GreedyTrace_zero right hrlen hrz =>
      apply (ListLib.list_eq_ext left right 0).mpr
      simp only [ListLib.Zlength,ListLib.Znth]
      refine ⟨by omega,?_⟩
      intro k hk
      exact (hz k (by omega)).trans (hrz k (by omega)).symm
    | GreedyTrace_skip next flat ht hnext hcell => omega
    | GreedyTrace_place next before after i j color side ht hnxt hi hj hzero hs hp =>
      have hb := (trace_bounds_and_canonical__solver_final n m next before hn hm ht).1
      omega
  | GreedyTrace_skip next left ht hnext hcell ih =>
    intro next' right he hr
    cases hr with
    | GreedyTrace_zero right hrlen hrz => omega
    | GreedyTrace_skip nxt flat hrt hrnext hrcell => exact ih nxt right (by omega) hrt
    | GreedyTrace_place nxt before after i j color side hrt hnxt hi hj hzero hs hp =>
      have hb := ih nxt before (by omega) hrt
      have hni : next=nxt := by omega
      rw [← hni,← hb] at hzero
      omega
  | GreedyTrace_place next before after i j color side ht hnxt hi hj hzero hs hp ih =>
    intro next' right he hr
    cases hr with
    | GreedyTrace_zero right hrlen hrz =>
      have hb := (trace_bounds_and_canonical__solver_final n m next before hn hm ht).1
      omega
    | GreedyTrace_skip nxt flat hrt hrnext hrcell =>
      have hb := ih nxt right (by omega) hrt
      have hni : next=nxt := by omega
      subst nxt
      rw [← hb] at hrcell
      omega
    | GreedyTrace_place nxt before' after' i' j' color' side' hrt hnxt' hi' hj' hzero' hs' hp' =>
      have hb := ih nxt before' (by omega) hrt
      rw [← hb] at hs' hp'
      have hidx : i*m+j=i'*m+j' := by omega
      have hir : i=i' := by
        rcases lt_trichotomy i i' with hlt | heq | hgt
        · nlinarith [hj.1,hj.2,hj'.1,hj'.2]
        · exact heq
        · nlinarith [hj.1,hj.2,hj'.1,hj'.2]
      have hjc : j=j' := by rw [hir] at hidx; omega
      subst i' j'
      have hcolor := least_legal_color_unique__solver_final before n m i j 0 color color' hs.1.1 hs'.1.1
      subst color'
      have hside := settled_side_unique__solver_final before n m i j color side side' hs hs'
      subst side'
      exact paint_rectangle_unique__solver_final before after right m i j side color (side*side) hp hp'

theorem greedy_trace_prefix_persistence__solver_final (n m start final : Int) (before output : List Int) :
    1≤n → 1≤m → start≤final → GreedyPlacementTrace n m start before → GreedyPlacementTrace n m final output →
    ∀ k, (0≤k ∧ k<n*m) → Znth k before 0≠0 → Znth k output 0=Znth k before 0 := by
  intro hn hm hle hstart hfinal
  induction hfinal generalizing start before with
  | GreedyTrace_zero output hlen hz =>
    intro k hk hnz
    have hb := (trace_bounds_and_canonical__solver_final n m start before hn hm hstart).1
    have he : start=0 := by omega
    subst start
    have h := greedy_trace_state_unique__solver_final n m 0 before output hn hm hstart (.GreedyTrace_zero output hlen hz)
    rw [h]
  | GreedyTrace_skip next output ht hnext hcell ih =>
    intro k hk hnz
    by_cases he : start=next+1
    · subst start
      have h := greedy_trace_state_unique__solver_final n m (next+1) before output hn hm hstart (.GreedyTrace_skip next output ht hnext hcell)
      rw [h]
    · exact ih start before (by omega) hstart k hk hnz
  | GreedyTrace_place next current output i j color side ht hnxt hi hj hzero hs hp ih =>
    intro k hk hnz
    by_cases he : start=next+1
    · subst start
      have h := greedy_trace_state_unique__solver_final n m (next+1) before output hn hm hstart
        (.GreedyTrace_place next current output i j color side ht hnxt hi hj hzero hs hp)
      rw [h]
    · have hcur := ih start before (by omega) hstart k hk hnz
      have hlen := (trace_bounds_and_canonical__solver_final n m next current hn hm ht).2.1
      exact (paint_preserves_nonzero__solver_final current output n m i j side color hs.1.2.1 hp k (by omega) (by rw [hcur]; exact hnz)).trans hcur

theorem earlier_rectangle_crossing_geometry__solver_final (m oi oj side candidate_side first : Int) (p q : Cell) :
    1≤m → 0≤oj → oj+side≤m → 1≤candidate_side → oj+candidate_side≤m → oi*m+oj<first →
    first=p.1*m+p.2 → (0≤p.2 ∧ p.2<m) → (oi≤q.1 ∧ q.1<oi+side) → (oj≤q.2 ∧ q.2<oj+side) →
    AdjCell p q → q≠(p.1,p.2-1) → first≤oi*m+(oj+candidate_side) →
    ((oi≤p.1 ∧ p.1<oi+candidate_side) ∧ (oj≤p.2 ∧ p.2<oj+candidate_side)) ∨ first=oi*m+(oj+candidate_side) := by
  intro hm hoj hos hcs hcsb ha hf hpc hqr hqc hadj hnotleft hb
  by_cases hins : (oi≤p.1 ∧ p.1<oi+candidate_side) ∧ (oj≤p.2 ∧ p.2<oj+candidate_side)
  · exact Or.inl hins
  · right
    have hpr : oi≤p.1 := by
      by_contra hlt
      have : p.1<oi := by omega
      nlinarith [hpc.2]
    rcases adjcell_cases__solver_final p q hadj with ⟨hr,hc⟩ | ⟨hr,hc⟩ | ⟨hr,hc⟩ | ⟨hr,hc⟩
    · have hpclo : oj≤p.2 := by omega
      have hprhi : p.1<oi+candidate_side := by
        by_contra hge
        have : oi+candidate_side≤p.1 := by omega
        nlinarith [hpc.1]
      have hpchi : oj+candidate_side≤p.2 := by omega
      have he : p.1=oi := by nlinarith
      rw [he] at hf
      omega
    · nlinarith [hqr.1,hpc.1]
    · by_cases he : p.1=oi
      · rw [he] at hf
        have hpclo : oj≤p.2 := by omega
        omega
      · have : oi<p.1 := by omega
        nlinarith [hpc.1]
    · apply False.elim
      apply hnotleft
      exact Prod.ext hr hc
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
