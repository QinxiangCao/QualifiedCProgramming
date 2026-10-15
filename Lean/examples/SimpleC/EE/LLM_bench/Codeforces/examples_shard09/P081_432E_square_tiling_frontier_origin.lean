import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_exchange_base
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem trace_skip_interval__solver_final (n m start finish : Int) (flat : List Int) :
    GreedyPlacementTrace n m start flat → 0≤start → start≤finish → finish≤n*m →
    (∀ k, (start≤k ∧ k<finish) → 65≤Znth k flat 0 ∧ Znth k flat 0≤90) → GreedyPlacementTrace n m finish flat := by
  intro ht hs hle hf hc
  have go : ∀ distance : Int, 0≤distance → ∀ left right state, distance=right-left →
      GreedyPlacementTrace n m left state → 0≤left → left≤right → right≤n*m →
      (∀ k, (left≤k ∧ k<right) → 65≤Znth k state 0 ∧ Znth k state 0≤90) → GreedyPlacementTrace n m right state := by
    apply nonnegative_anchor_strong_induction__solver_final
    intro distance hd ih left right state he htr hl hr hnm hcol
    by_cases heq : left=right
    · simpa only [heq] using htr
    · exact ih (distance-1) (by omega) (left+1) right state (by omega)
        (.GreedyTrace_skip left state htr (by omega) (hcol left (by omega))) (by omega) (by omega) hnm (fun k hk => hcol k (by omega))
  exact go (finish-start) (by omega) start finish flat rfl ht hs hle hf hc

theorem placed_trace_at_frontier__solver_final (n m anchor : Int) (before painted : List Int) (i j color side : Int) :
    1≤n → 1≤m → anchor=i*m+j → GreedyPlacementTrace n m anchor before → (0≤i ∧ i<n) → (0≤j ∧ j<m) →
    Znth anchor before 0=0 → SettledSquareState before n m i j color side →
    PaintRectanglePrefix before painted m i j side color (side*side) → GreedyPlacementTrace n m (i*m+(j+side)) painted := by
  intro hn hm ha ht hi hj hz hs hp
  have hplace := hs.1.2.1
  have hside := hplace.1
  have hin := hplace.2.1
  have hjm := hplace.2.2.1
  have hb := trace_bounds_and_canonical__solver_final n m anchor before hn hm ht
  have hplaced : GreedyPlacementTrace n m (anchor+1) painted := .GreedyTrace_place anchor before painted i j color side ht ha hi hj hz hs hp
  refine trace_skip_interval__solver_final n m (anchor+1) (i*m+(j+side)) painted hplaced (by omega) (by omega) (by nlinarith [hi.2]) ?_
  intro k hk
  have hcol : 0≤k-i*m ∧ k-i*m<m := by omega
  have he := (paint_rectangle_coordinate__solver_final before painted n m i j side color i (k-i*m) hm hi hj hi hcol hplace hb.2.1 hp).1 (by omega)
  rw [show i*m+(k-i*m)=k by ring] at he
  rw [he]
  exact hs.1.1.1.1

theorem least_legal_frontier_equiv__solver_final (before painted : List Int) (n m i j side color chosen : Int) :
    1≤n → 1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → 65≤color → j+side<m → Zlength before=n*m →
    CanPlace before n m i j side color → PaintRectanglePrefix before painted m i j side color (side*side) →
    (LeastLegalColor painted n m i (j+side) 0 chosen ↔ LeastLegalColor before n m i (j+side) color chosen) := by
  intro hn hm hi hj hc hf hl hplace hp
  have hconf := fun tested => paint_frontier_conflict_equiv__solver_final before painted n m i j side color tested hn hm hi hj hc hf hl hplace hp
  simp only [LeastLegalColor,LegalColor,hconf]

theorem frontier_zero_is_new_origin__solver_final (n m anchor next : Int) (before painted output : List Int)
    (output_grid : List (List Int)) (i j color side : Int) :
    1≤n → 1≤m → anchor=i*m+j → GreedyPlacementTrace n m anchor before → GreedyPlacementTrace n m next output →
    i*m+(j+side)<next → RowsOfFlat n m output output_grid → (0≤i ∧ i<n) → (0≤j ∧ j<m) → j+side<m →
    Znth anchor before 0=0 → SettledSquareState before n m i j color side →
    PaintRectanglePrefix before painted m i j side color (side*side) → Znth (i*m+(j+side)) before 0=0 →
    Znth (i*m+(j+side)) output 0≠0 →
    ∃ (found found_side : Int) (found_after : List Int), SettledSquareState painted n m i (j+side) found found_side ∧
      PaintRectanglePrefix painted found_after m i (j+side) found_side found (found_side*found_side) ∧ Znth (i*m+(j+side)) output 0=found := by
  intro hn hm ha hbefore hout hfn hrows hi hj hf hz hs hp hbf hnonzero
  have hplace := hs.1.2.1
  have hside := hplace.1
  have hfc : 0≤j+side ∧ j+side<m := by omega
  have hlen := (trace_bounds_and_canonical__solver_final n m anchor before hn hm hbefore).2.1
  have hpzero : Znth (i*m+(j+side)) painted 0=0 := by
    rw [(paint_rectangle_coordinate__solver_final before painted n m i j side color i (j+side) hm hi hj hi hfc hplace hlen hp).2 (by omega)]
    exact hbf
  have hfront := placed_trace_at_frontier__solver_final n m anchor before painted i j color side hn hm ha hbefore hi hj hz hs hp
  have hgnz : Znth (j+side) (Znth i output_grid []) 0≠0 := by
    rw [rows_of_flat_Znth__solver_final n m output output_grid i (j+side) hrows hi hfc]
    exact hnonzero
  obtain ⟨fa,fb,fp,fi,fj,found,fs,hfa,hfan,hft,hfs,hfp,hfi,hfj,hpri,hpci,hpcolor,hcomp,hpersist⟩ :=
    trace_colored_component_origin__solver_final n m next output output_grid (i,j+side) hn hm hout hrows hi hfc hgnz
  have hfplace := hfs.1.2.1
  have hfside := hfplace.1
  have hfle : fa≤i*m+(j+side) := by
    rw [hfa]
    exact square_anchor_le_member__solver_final m fi fj fs i (j+side) hm hfj.1 hfc.2 hpri hpci
  have hfge : i*m+(j+side)≤fa := by
    by_contra hlt
    have hfblen := (trace_bounds_and_canonical__solver_final n m fa fb hn hm hft).2.1
    have hfpainted : Znth (i*m+(j+side)) fp 0=found :=
      (paint_rectangle_coordinate__solver_final fb fp n m fi fj fs found i (j+side) hm hfi hfj hi hfc hfplace hfblen hfp).1 ⟨hpri,hpci⟩
    have hfzero : Znth fa fb 0=0 := by
      rw [hfa]
      exact hfplace.2.2.2.1 fi fj (by omega) (by omega)
    have hfafter : GreedyPlacementTrace n m (fa+1) fp := .GreedyTrace_place fa fb fp fi fj found fs hft hfa hfi hfj hfzero hfs hfp
    have hfrange := hfs.1.1.1.1
    have hper := greedy_trace_prefix_persistence__solver_final n m (fa+1) (i*m+(j+side)) fp painted hn hm (by omega) hfafter hfront
      (i*m+(j+side)) (p081_cell_index_bounds n m (i,j+side) (by omega) hi hfc) (by rw [hfpainted]; omega)
    rw [hpzero,hfpainted] at hper
    omega
  have hfe : fa=i*m+(j+side) := by omega
  have hfbe : fb=painted := greedy_trace_state_unique__solver_final n m (i*m+(j+side)) fb painted hn hm (by rw [← hfe]; exact hft) hfront
  have hfire : fi=i := by
    rcases lt_trichotomy fi i with hlt | he | hgt
    · nlinarith [hfj.1,hfj.2,hfc.1,hfc.2]
    · exact he
    · nlinarith [hfj.1,hfj.2,hfc.1,hfc.2]
  have hfje : fj=j+side := by rw [hfire] at hfa; omega
  rw [hfbe,hfire,hfje] at hfs hfp
  refine ⟨found,fs,fp,hfs,hfp,?_⟩
  rw [← rows_of_flat_Znth__solver_final n m output output_grid i (j+side) hrows hi hfc]
  exact hpcolor

theorem frontier_zero_fallback_bound__solver_final (n m anchor next : Int) (before painted output : List Int)
    (output_grid : List (List Int)) (i j color side fallback : Int) :
    1≤n → 1≤m → anchor=i*m+j → GreedyPlacementTrace n m anchor before → GreedyPlacementTrace n m next output →
    i*m+(j+side)<next → RowsOfFlat n m output output_grid → (0≤i ∧ i<n) → (0≤j ∧ j<m) → j+side<m →
    Znth anchor before 0=0 → SettledSquareState before n m i j color side →
    PaintRectanglePrefix before painted m i j side color (side*side) → Znth (i*m+(j+side)) before 0=0 →
    Znth (i*m+(j+side)) output 0≠0 → LeastLegalColor before n m i (j+side) color fallback → fallback≤color → Znth (i*m+(j+side)) output 0≤color := by
  intro hn hm ha hbefore hout hfn hrows hi hj hf hz hs hp hbf hnz hfall hle
  obtain ⟨found,fs,fp,hfs,hfp,hcolor⟩ := frontier_zero_is_new_origin__solver_final n m anchor next before painted output output_grid i j color side
    hn hm ha hbefore hout hfn hrows hi hj hf hz hs hp hbf hnz
  have hlen := (trace_bounds_and_canonical__solver_final n m anchor before hn hm hbefore).2.1
  have hfound := (least_legal_frontier_equiv__solver_final before painted n m i j side color found hn hm hi hj hs.1.1.1.1.1 hf hlen hs.1.2.1 hp).mp hfs.1.1
  have he := least_legal_color_unique__solver_final before n m i (j+side) color found fallback hfound hfall
  rw [hcolor,he]
  exact hle
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
