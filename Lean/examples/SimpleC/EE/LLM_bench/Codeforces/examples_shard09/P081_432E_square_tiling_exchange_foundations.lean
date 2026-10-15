import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_frontier
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem smaller_conflict_has_painted_neighbour__solver_final (flat : List Int) (n m i j smaller override : Int) :
    1≤n → 1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → 0≤smaller → smaller<override →
    NeighborConflict flat n m i j smaller override → ∃ q : Cell,
      (0≤q.1 ∧ q.1<n) ∧ (0≤q.2 ∧ q.2<m) ∧ AdjCell (i,j) q ∧ q≠(i,j-1) ∧ Znth (q.1*m+q.2) flat 0=smaller := by
  intro hn hm hi hj hsmall hlt hc
  rcases hc with ⟨htop,ht⟩ | ⟨hbottom,hb⟩ | ⟨hright,hr⟩ | ⟨hleft,hl⟩ | ⟨hjzero,hov⟩
  · refine ⟨(i-1,j),by dsimp; omega,hj,?_,?_,ht⟩
    · simp [AdjCell,Z.abs,show i-(i-1)=(1 : Int) by omega]
    · intro he
      have h := congrArg Prod.fst he
      dsimp at h
      omega
  · refine ⟨(i+1,j),by dsimp; omega,hj,?_,?_,hb⟩
    · simp [AdjCell,Z.abs,show i-(i+1)=(-1 : Int) by omega]
    · intro he
      have h := congrArg Prod.fst he
      dsimp at h
      omega
  · refine ⟨(i,j+1),hi,by dsimp; omega,?_,?_,?_⟩
    · simp [AdjCell,Z.abs,show j-(j+1)=(-1 : Int) by omega]
    · intro he
      have h := congrArg Prod.snd he
      dsimp at h
      omega
    · simpa only [add_assoc] using hr
  · have hnz : override≠0 := by omega
    simp only [if_neg hnz] at hl
    omega
  · omega

theorem smaller_conflict_has_earlier_component__solver_final (n m anchor : Int) (before : List Int)
    (before_grid : List (List Int)) (i j smaller override : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m anchor before → RowsOfFlat n m before before_grid →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 65≤smaller → smaller<override → NeighborConflict before n m i j smaller override →
    ∃ (q : Cell) (earlier : Int) (origin_before painted : List Int) (oi oj oside : Int),
      earlier=oi*m+oj ∧ earlier<anchor ∧ GreedyPlacementTrace n m earlier origin_before ∧
      SettledSquareState origin_before n m oi oj smaller oside ∧
      PaintRectanglePrefix origin_before painted m oi oj oside smaller (oside*oside) ∧
      (0≤oi ∧ oi<n) ∧ (0≤oj ∧ oj<m) ∧ (oi≤q.1 ∧ q.1<oi+oside) ∧ (oj≤q.2 ∧ q.2<oj+oside) ∧
      AdjCell (i,j) q ∧ q≠(i,j-1) ∧
      (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
        (SameColorPath before_grid q x ↔ (oi≤x.1 ∧ x.1<oi+oside) ∧ (oj≤x.2 ∧ x.2<oj+oside))) ∧
      (∀ k, (0≤k ∧ k<n*m) → Znth k origin_before 0≠0 → Znth k before 0=Znth k origin_before 0) := by
  intro hn hm ht hrows hi hj hsmall hlt hconf
  obtain ⟨q,hqr,hqc,hadj,hnotleft,hqflat⟩ := smaller_conflict_has_painted_neighbour__solver_final before n m i j smaller override hn hm hi hj (by omega) hlt hconf
  have hqgrid := (rows_of_flat_Znth__solver_final n m before before_grid q.1 q.2 hrows hqr hqc).trans hqflat
  obtain ⟨earlier,origin,painted,oi,oj,color,oside,he,hlt,hot,hos,hop,hoi,hoj,hqoi,hqoj,hqcolor,hcomp,hpersist⟩ :=
    trace_colored_component_origin__solver_final n m anchor before before_grid q hn hm ht hrows hqr hqc (by omega)
  have heq : color=smaller := hqcolor.symm.trans hqgrid
  rw [heq] at hos hop
  exact ⟨q,earlier,origin,painted,oi,oj,oside,he,hlt,hot,hos,hop,hoi,hoj,hqoi,hqoj,hadj,hnotleft,hcomp,hpersist⟩

theorem nonnegative_anchor_strong_induction__solver_final (P : Int → Prop) :
    (∀ anchor, 0≤anchor → (∀ earlier, (0≤earlier ∧ earlier<anchor) → P earlier) → P anchor) →
    ∀ anchor, 0≤anchor → P anchor := by
  intro hstep
  have go : ∀ fuel : Nat, ∀ anchor : Int, anchor.toNat=fuel → 0≤anchor → P anchor := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro anchor he ha
      apply hstep anchor ha
      intro earlier hb
      exact ih earlier.toNat (by omega) earlier rfl hb.1
  intro anchor ha
  exact go anchor.toNat anchor rfl ha

theorem local_first_difference_implies_lex__solver_final (upto : Int) (left right : List Int) :
    0≤upto → (∀ first, (0≤first ∧ first<upto) →
      (∀ k, (0≤k ∧ k<first) → Znth k left 0=Znth k right 0) → Znth first left 0≤Znth first right 0) → LexPrefixLe upto left right := by
  intro hu
  revert left right
  apply nonnegative_anchor_strong_induction__solver_final
    (fun current => ∀ left right : List Int, (∀ first, (0≤first ∧ first<current) →
      (∀ k, (0≤k ∧ k<first) → Znth k left 0=Znth k right 0) → Znth first left 0≤Znth first right 0) → LexPrefixLe current left right) _ upto hu
  intro current hc ih left right hlocal
  by_cases hz : current=0
  · subst current
    exact Or.inl (by intro k hk; omega)
  · have hprev := ih (current-1) (by omega) left right (fun first hf hp => hlocal first (by omega) hp)
    rcases hprev with heq | ⟨first,hfirst,hsame,hless⟩
    · have hbound := hlocal (current-1) (by omega) heq
      have hl := lex_first_difference__solver_final (current-1) left right (by omega) (Or.inl heq) hbound
      simpa only [sub_add_cancel] using hl
    · exact Or.inr ⟨first,by omega,hsame,hless⟩

theorem square_tiling_component__solver_final (n m : Int) (grid : List (List Int)) (p : Cell) :
    SquareTiling n m grid → (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → ∃ r c side,
      1≤side ∧ 0≤r ∧ 0≤c ∧ r+side≤n ∧ c+side≤m ∧ (r≤p.1 ∧ p.1<r+side) ∧ (c≤p.2 ∧ p.2<c+side) ∧
      ∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
        (SameColorPath grid p q ↔ (r≤q.1 ∧ q.1<r+side) ∧ (c≤q.2 ∧ q.2<c+side)) := by
  intro ht hp hc
  obtain ⟨r,c,side,hs,hpr,hpc,hr,hc,hrb,hcb,hcomp⟩ := ht.2.2 p hp hc
  exact ⟨r,c,side,hs,hr,hc,hrb,hcb,hpr,hpc,hcomp⟩

theorem exact_component_boundary_color__solver_final (grid : List (List Int)) (anchor inside outside : Cell) (r c side n m : Int) :
    Zlength grid=n → Zlength (Znth 0 grid [])=m →
    (0≤anchor.1 ∧ anchor.1<n) → (0≤anchor.2 ∧ anchor.2<m) →
    (0≤inside.1 ∧ inside.1<n) → (0≤inside.2 ∧ inside.2<m) →
    (0≤outside.1 ∧ outside.1<n) → (0≤outside.2 ∧ outside.2<m) →
    (r≤inside.1 ∧ inside.1<r+side) → (c≤inside.2 ∧ inside.2<c+side) →
    ¬((r≤outside.1 ∧ outside.1<r+side) ∧ (c≤outside.2 ∧ outside.2<c+side)) → AdjCell inside outside →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath grid anchor q ↔ (r≤q.1 ∧ q.1<r+side) ∧ (c≤q.2 ∧ q.2<c+side))) →
    Znth outside.2 (Znth outside.1 grid []) 0≠Znth anchor.2 (Znth anchor.1 grid []) 0 := by
  intro hl hw har hac hir hic hor hoc hrir hric hout hadj hcomp heq
  have hip := (hcomp inside hir hic).mpr ⟨hrir,hric⟩
  have hop := same_color_path_append__solver_final grid anchor inside outside hip (by omega) (by omega) heq hadj
  exact hout ((hcomp outside hor hoc).mp hop)

theorem square_anchor_le_member__solver_final (m i j side r c : Int) :
    1≤m → 0≤j → c<m → (i≤r ∧ r<i+side) → (j≤c ∧ c<j+side) → i*m+j≤r*m+c := by
  intro hm hj hcm hr hc
  nlinarith
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
