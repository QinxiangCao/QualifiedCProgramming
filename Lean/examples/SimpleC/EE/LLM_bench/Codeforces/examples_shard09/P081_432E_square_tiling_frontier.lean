import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_origins
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem paint_frontier_conflict_equiv__solver_final (before after : List Int) (n m i j side color tested : Int) :
    1≤n → 1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → 65≤color → j+side<m → Zlength before=n*m →
    CanPlace before n m i j side color → PaintRectanglePrefix before after m i j side color (side*side) →
    (NeighborConflict after n m i (j+side) tested 0 ↔ NeighborConflict before n m i (j+side) tested color) := by
  intro hn hm hi hj hcolor hfront hl hplace hp
  have hs := hplace.1
  have hib := hplace.2.1
  have hjb := hplace.2.2.1
  have htop : 0<i → Znth ((i-1)*m+(j+side)) after 0=Znth ((i-1)*m+(j+side)) before 0 := by
    intro hit
    apply (paint_rectangle_coordinate__solver_final before after n m i j side color (i-1) (j+side) hm hi hj (by omega) (by omega) hplace hl hp).2
    omega
  have hbottom : i+1<n → Znth ((i+1)*m+(j+side)) after 0=Znth ((i+1)*m+(j+side)) before 0 := by
    intro hit
    apply (paint_rectangle_coordinate__solver_final before after n m i j side color (i+1) (j+side) hm hi hj (by omega) (by omega) hplace hl hp).2
    omega
  have hright : j+side+1<m → Znth (i*m+(j+side)+1) after 0=Znth (i*m+(j+side)+1) before 0 := by
    intro hit
    rw [add_assoc]
    apply (paint_rectangle_coordinate__solver_final before after n m i j side color i (j+side+1) hm hi hj hi (by omega) hplace hl hp).2
    omega
  have hleft : Znth (i*m+(j+side)-1) after 0=color := by
    rw [show i*m+(j+side)-1=i*m+(j+side-1) by ring]
    exact (paint_rectangle_coordinate__solver_final before after n m i j side color i (j+side-1) hm hi hj hi (by omega) hplace hl hp).1 (by omega)
  have ht : (0<i ∧ Znth ((i-1)*m+(j+side)) after 0=tested) ↔ (0<i ∧ Znth ((i-1)*m+(j+side)) before 0=tested) :=
    and_congr_right (fun hit => by rw [htop hit])
  have hb : (i+1<n ∧ Znth ((i+1)*m+(j+side)) after 0=tested) ↔ (i+1<n ∧ Znth ((i+1)*m+(j+side)) before 0=tested) :=
    and_congr_right (fun hit => by rw [hbottom hit])
  have hh : (j+side+1<m ∧ Znth (i*m+(j+side)+1) after 0=tested) ↔ (j+side+1<m ∧ Znth (i*m+(j+side)+1) before 0=tested) :=
    and_congr_right (fun hit => by rw [hright hit])
  have hnz : color≠0 := by omega
  have hfrontnz : j+side≠0 := by omega
  simp only [NeighborConflict,ite_true,if_neg hnz,hleft,ht,hb,hh,hfrontnz,false_and,or_false]

theorem least_legal_color_unique__solver_final (flat : List Int) (n m i j left c1 c2 : Int) :
    LeastLegalColor flat n m i j left c1 → LeastLegalColor flat n m i j left c2 → c1=c2 := by
  rintro ⟨hl1,hmin1⟩ ⟨hl2,hmin2⟩
  have hc1 := hl1.1
  have hc2 := hl2.1
  rcases lt_trichotomy c1 c2 with hlt | he | hgt
  · exact False.elim (hmin2 c1 (by omega) hl1)
  · exact he
  · exact False.elim (hmin1 c2 (by omega) hl2)

theorem settled_side_unique__solver_final (flat : List Int) (n m i j color side1 side2 : Int) :
    SettledSquareState flat n m i j color side1 → SettledSquareState flat n m i j color side2 → side1=side2 := by
  rintro ⟨⟨hleast1,hplace1,hprev1⟩,hstop1⟩ ⟨⟨hleast2,hplace2,hprev2⟩,hstop2⟩
  have notlt : ∀ a b, CanPlace flat n m i j a color →
      (∀ prev, (1≤prev ∧ prev<b) → CanPlace flat n m i j (prev+1) color ∧
        ∃ fallback, LeastLegalColor flat n m i (j+prev) color fallback ∧ color<fallback) →
      (j+a=m ∨ ¬CanPlace flat n m i j (a+1) color ∨ ∃ stopped, LeastLegalColor flat n m i (j+a) color stopped ∧ stopped≤color) → ¬a<b := by
    intro a b ha hb hstop hlt
    obtain ⟨hext,fallback,hf,hgt⟩ := hb a ⟨ha.1,hlt⟩
    rcases hstop with hbound | hcannot | ⟨stopped,hst,hle⟩
    · have h := hext.2.2.1; omega
    · exact hcannot hext
    · have heq := least_legal_color_unique__solver_final flat n m i (j+a) color fallback stopped hf hst
      omega
  have h1 := notlt side1 side2 hplace1 hprev2 hstop1
  have h2 := notlt side2 side1 hplace2 hprev1 hstop2
  omega

theorem paint_rectangle_unique__solver_final (before after1 after2 : List Int) (m i j side color done : Int) :
    PaintRectanglePrefix before after1 m i j side color done → PaintRectanglePrefix before after2 m i j side color done → after1=after2 := by
  rintro ⟨hl1,hcells1⟩ ⟨hl2,hcells2⟩
  apply (ListLib.list_eq_ext after1 after2 0).mpr
  simp only [ListLib.Zlength,ListLib.Znth]
  refine ⟨by omega,?_⟩
  intro k hk
  have hkb : 0≤k ∧ k<Zlength before := by omega
  rcases hcells1 k hkb with ⟨hmem1,hcol1⟩ | ⟨hout1,hsame1⟩ <;>
    rcases hcells2 k hkb with ⟨hmem2,hcol2⟩ | ⟨hout2,hsame2⟩
  · exact hcol1.trans hcol2.symm
  · obtain ⟨off,hoff,he⟩ := hmem1
    exact False.elim (hout2 off hoff he)
  · obtain ⟨off,hoff,he⟩ := hmem2
    exact False.elim (hout1 off hoff he)
  · exact hsame1.trans hsame2.symm

theorem greedy_side_length_exchange__solver_final (chosen fallback candidate : Int) :
    chosen<fallback → fallback≤candidate → chosen≤candidate := by omega

theorem lex_prefix_skip__solver_final (next : Int) (flat candidate : List Int) :
    0≤next → LexPrefixLe next flat candidate → Znth next flat 0≤Znth next candidate 0 → LexPrefixLe (next+1) flat candidate :=
  lex_first_difference__solver_final next flat candidate

theorem lex_prefix_place__solver_final (next : Int) (before after candidate : List Int) :
    0≤next → LexPrefixLe next before candidate →
    (∀ k, (0≤k ∧ k<next) → Znth k after 0=Znth k before 0) →
    Znth next after 0≤Znth next candidate 0 → LexPrefixLe (next+1) after candidate := by
  intro hn hl hsame hc
  apply lex_first_difference__solver_final next after candidate hn _ hc
  rcases hl with he | ⟨first,hfirst,hprefix,hless⟩
  · exact Or.inl (fun k hk => (hsame k hk).trans (he k hk))
  · exact Or.inr ⟨first,hfirst,(fun k hk => (hsame k (by omega)).trans (hprefix k hk)),(hsame first hfirst).trans_lt hless⟩

theorem greedy_trace_structural_state__solver_final (n m next : Int) (flat : List Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next flat → ∃ grid,
      RowsOfFlat n m flat grid ∧ (∀ k, (0≤k ∧ k<next) → 65≤Znth k flat 0 ∧ Znth k flat 0≤90) ∧
      (∀ k, (0≤k ∧ k<n*m) → Znth k flat 0=0 ∨ (65≤Znth k flat 0 ∧ Znth k flat 0≤90)) ∧ PartialSquareComponents n m grid := by
  intro hn hm ht
  obtain ⟨hb,hl,hcanon,hprefix⟩ := trace_bounds_and_canonical__solver_final n m next flat hn hm ht
  obtain ⟨grid,hrows,hcomp⟩ := greedy_trace_components__solver_final n m next flat hn hm ht
  exact ⟨grid,hrows,hprefix,(fun k hk => hcanon k (by omega)),hcomp⟩

theorem greedy_trace_partial_from_lex__solver_final (n m next : Int) (flat : List Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next flat →
    (∀ candidate, SquareTiling n m candidate → LexPrefixLe next flat (Flatten candidate)) → PartialTilingState n m next flat := by
  intro hn hm ht hl
  obtain ⟨grid,hrows,hprefix,hcanon,hcomp⟩ := greedy_trace_structural_state__solver_final n m next flat hn hm ht
  exact ⟨grid,hrows,hprefix,hcanon,hcomp,hl⟩
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
