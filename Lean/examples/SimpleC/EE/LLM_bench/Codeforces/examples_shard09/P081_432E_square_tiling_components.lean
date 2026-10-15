import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_paths
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem p081_rows_first_length (n m : Int) (flat : List Int) (grid : List (List Int)) (hn : 0<n)
    (hrows : RowsOfFlat n m flat grid) : Zlength (Znth 0 grid [])=m :=
  (Forall.iff_forall_mem.mp hrows.2.1) _ (Znth_In_range__solver_final grid 0 [] (by have := hrows.1; omega))

theorem p081_app_Znth1 {A : Type} (d : A) (l l' : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) :
    Znth i (l++l') d=Znth i l d := ListLib.app_Znth1 d l l' i hi

theorem sealed_component_unique__solver_final (before after : List Int) (n m i j side color : Int)
    (grid : List (List Int)) (p q : Cell) :
    1≤n → 1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → Zlength before=n*m →
    CanPlace before n m i j side color → PaintRectanglePrefix before after m i j side color (side*side) →
    RowsOfFlat n m after grid → (i≤p.1 ∧ p.1<i+side) → (j≤p.2 ∧ p.2<j+side) →
    (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
    (SameColorPath grid p q ↔ (i≤q.1 ∧ q.1<i+side) ∧ (j≤q.2 ∧ q.2<j+side)) := by
  intro hn hm hi hj hl hplace hp hrows hpr hpc hqr hqc
  have hs := hplace.1
  have hib := hplace.2.1
  have hjb := hplace.2.2.1
  have hhor := hplace.2.2.2.2.1
  have hver := hplace.2.2.2.2.2
  have hgl := hrows.1
  have hw := p081_rows_first_length n m after grid (by omega) hrows
  have hpainted : ∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (i≤x.1 ∧ x.1<i+side) → (j≤x.2 ∧ x.2<j+side) → Znth x.2 (Znth x.1 grid []) 0=color := by
    intro x hxr hxc hxinr hxinc
    rw [rows_of_flat_Znth__solver_final n m after grid x.1 x.2 hrows hxr hxc]
    exact (paint_rectangle_coordinate__solver_final before after n m i j side color x.1 x.2 hm hi hj hxr hxc hplace hl hp).1 ⟨hxinr,hxinc⟩
  constructor
  · intro hpath
    apply same_color_path_closed__solver_final grid color
      (fun x => (i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side)) p q hpath ⟨hpr,hpc⟩
    · intro x y hxin hyr hyc hycol hadj
      have hyr' : 0≤y.1 ∧ y.1<n := by omega
      have hyc' : 0≤y.2 ∧ y.2<m := by omega
      by_cases hin : (i≤y.1 ∧ y.1<i+side) ∧ (j≤y.2 ∧ y.2<j+side)
      · exact hin
      · have hyflat := (rows_of_flat_Znth__solver_final n m after grid y.1 y.2 hrows hyr' hyc').symm.trans hycol
        rw [(paint_rectangle_coordinate__solver_final before after n m i j side color y.1 y.2 hm hi hj hyr' hyc' hplace hl hp).2 hin] at hyflat
        rcases adjcell_cases__solver_final x y hadj with ⟨her,hec⟩ | ⟨her,hec⟩ | ⟨her,hec⟩ | ⟨her,hec⟩
        · have hb : y.1=i+side := by omega
          have hclear := (hhor y.2 (by omega)).2 (by omega)
          exact False.elim (hclear (by simpa only [hb] using hyflat))
        · have hb : y.1=i-1 := by omega
          have hclear := (hhor y.2 (by omega)).1 (by omega)
          exact False.elim (hclear (by simpa only [hb] using hyflat))
        · have hb : y.2=j+side := by omega
          have hclear := (hver y.1 (by omega)).2 (by omega)
          exact False.elim (hclear (by simpa only [hb,add_assoc] using hyflat))
        · have hb : y.2=j-1 := by omega
          have hclear := (hver y.1 (by omega)).1 (by omega)
          exact False.elim (hclear (by simpa only [hb,sub_eq_add_neg,add_assoc] using hyflat))
    · exact hpainted p (by omega) (by omega) hpr hpc
  · intro hqin
    apply rectangle_connected__solver_final grid i j side color p q hs hi.1 hj.1 (by omega) (by omega) hpr hpc hqin.1 hqin.2
    intro x hxr hxc
    exact hpainted x (by omega) (by omega) hxr hxc

theorem same_color_path_append__solver_final (grid : List (List Int)) (p x y : Cell) :
    SameColorPath grid p x → (0≤y.1 ∧ y.1<Zlength grid) → (0≤y.2 ∧ y.2<Zlength (Znth 0 grid [])) →
    Znth y.2 (Znth y.1 grid []) 0=Znth p.2 (Znth p.1 grid []) 0 → AdjCell x y → SameColorPath grid p y := by
  rintro ⟨path,hne,hfirst,hlast,hall,hsteps⟩ hyr hyc hycol hadj
  have hlen : 0<Zlength path := by
    cases path with
    | nil => contradiction
    | cons x xs => have h:=Zlength_nonneg xs; simp only [Zlength_cons]; omega
  refine ⟨path++[y],by simp,?_,?_,?_,?_⟩
  · rw [p081_app_Znth1 (0,0) path [y] 0 (by omega)]
    exact hfirst
  · simp only [Zlength_app,Zlength_cons,Zlength_nil,zero_add,add_sub_cancel_right]
    rw [app_Znth2 (0,0) path [y] (Zlength path) (by omega),sub_self]
    rfl
  · rw [Forall.iff_forall_mem] at hall ⊢
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hall z hz
    · have he : z=y := List.mem_singleton.mp hz
      subst z
      exact ⟨hyr,hyc,hycol⟩
  · intro k hk
    simp only [Zlength_app,Zlength_cons,Zlength_nil] at hk
    by_cases hlastk : k=Zlength path-1
    · subst k
      rw [p081_app_Znth1 (0,0) path [y] (Zlength path-1) (by omega),sub_add_cancel,app_Znth2 (0,0) path [y] (Zlength path) (by omega),sub_self]
      simpa only [hlast,Znth0_cons] using hadj
    · rw [p081_app_Znth1 (0,0) path [y] k (by omega),p081_app_Znth1 (0,0) path [y] (k+1) (by omega)]
      exact hsteps k (by omega)

theorem same_color_path_endpoint_color__solver_final (grid : List (List Int)) (p q : Cell) :
    SameColorPath grid p q → Znth q.2 (Znth q.1 grid []) 0=Znth p.2 (Znth p.1 grid []) 0 := by
  rintro ⟨path,hne,hfirst,hlast,hall,hsteps⟩
  have hlen : 0<Zlength path := by
    cases path with
    | nil => contradiction
    | cons x xs => have h:=Zlength_nonneg xs; simp only [Zlength_cons]; omega
  have hc := ((Forall.iff_forall_mem.mp hall) _ (Znth_In_range__solver_final path (Zlength path-1) (0,0) (by omega))).2.2
  simpa only [hlast] using hc

theorem adjcell_sym__solver_final (p q : Cell) : AdjCell p q → AdjCell q p := by
  intro h
  unfold AdjCell at *
  rw [show q.1-p.1= -(p.1-q.1) by ring,show q.2-p.2= -(p.2-q.2) by ring,Z.abs_neg,Z.abs_neg]
  exact h

theorem old_component_preserved__solver_final (before after : List Int) (n m i j side color : Int)
    (before_grid after_grid : List (List Int)) (p : Cell) (r c old_side : Int) :
    1≤n → 1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → Zlength before=n*m →
    CanPlace before n m i j side color → PaintRectanglePrefix before after m i j side color (side*side) →
    RowsOfFlat n m before before_grid → RowsOfFlat n m after after_grid →
    (0≤p.1 ∧ p.1<n) → (0≤p.2 ∧ p.2<m) → ¬((i≤p.1 ∧ p.1<i+side) ∧ (j≤p.2 ∧ p.2<j+side)) →
    Znth p.2 (Znth p.1 after_grid []) 0≠0 → 1≤old_side → 0≤r → 0≤c → r+old_side≤n → c+old_side≤m →
    (r≤p.1 ∧ p.1<r+old_side) → (c≤p.2 ∧ p.2<c+old_side) →
    (∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath before_grid p q ↔ (r≤q.1 ∧ q.1<r+old_side) ∧ (c≤q.2 ∧ q.2<c+old_side))) →
    ∀ q : Cell, (0≤q.1 ∧ q.1<n) → (0≤q.2 ∧ q.2<m) →
      (SameColorPath after_grid p q ↔ (r≤q.1 ∧ q.1<r+old_side) ∧ (c≤q.2 ∧ q.2<c+old_side)) := by
  intro hn hm hi hj hl hplace hpaint hbefore hafter hpr hpc hpout hpnz hos hr hc hrb hcb hpor hpoc hold q hqr hqc
  have hbl := hbefore.1
  have hal := hafter.1
  have hbw := p081_rows_first_length n m before before_grid (by omega) hbefore
  have haw := p081_rows_first_length n m after after_grid (by omega) hafter
  have hsame : ∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      ¬((i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side)) →
      Znth x.2 (Znth x.1 after_grid []) 0=Znth x.2 (Znth x.1 before_grid []) 0 := by
    intro x hxr hxc hxout
    rw [rows_of_flat_Znth__solver_final n m after after_grid x.1 x.2 hafter hxr hxc,
      rows_of_flat_Znth__solver_final n m before before_grid x.1 x.2 hbefore hxr hxc]
    exact (paint_rectangle_coordinate__solver_final before after n m i j side color x.1 x.2 hm hi hj hxr hxc hplace hl hpaint).2 hxout
  have hpsame := hsame p hpr hpc hpout
  have hpbnz : Znth p.2 (Znth p.1 before_grid []) 0≠0 := by rw [←hpsame]; exact hpnz
  have holdout : ∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (r≤x.1 ∧ x.1<r+old_side) → (c≤x.2 ∧ x.2<c+old_side) →
      ¬((i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side)) := by
    intro x hxr hxc hxor hxoc hxin
    have hcol := same_color_path_endpoint_color__solver_final before_grid p x ((hold x hxr hxc).mpr ⟨hxor,hxoc⟩)
    have hz : Znth x.2 (Znth x.1 before_grid []) 0=0 := by
      rw [rows_of_flat_Znth__solver_final n m before before_grid x.1 x.2 hbefore hxr hxc]
      exact hplace.2.2.2.1 x.1 x.2 hxin.1 hxin.2
    exact hpbnz (hcol.symm.trans hz)
  have holdcol : ∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (r≤x.1 ∧ x.1<r+old_side) → (c≤x.2 ∧ x.2<c+old_side) →
      Znth x.2 (Znth x.1 after_grid []) 0=Znth p.2 (Znth p.1 after_grid []) 0 := by
    intro x hxr hxc hxor hxoc
    rw [hsame x hxr hxc (holdout x hxr hxc hxor hxoc),hpsame]
    exact same_color_path_endpoint_color__solver_final before_grid p x ((hold x hxr hxc).mpr ⟨hxor,hxoc⟩)
  constructor
  · intro hpath
    apply same_color_path_closed__solver_final after_grid (Znth p.2 (Znth p.1 after_grid []) 0)
      (fun x => (r≤x.1 ∧ x.1<r+old_side) ∧ (c≤x.2 ∧ x.2<c+old_side)) p q hpath ⟨hpor,hpoc⟩ _ rfl
    intro x y hxo hyr hyc hycol hadj
    have hyr' : 0≤y.1 ∧ y.1<n := by omega
    have hyc' : 0≤y.2 ∧ y.2<m := by omega
    have hxr : 0≤x.1 ∧ x.1<n := by omega
    have hxc : 0≤x.2 ∧ x.2<m := by omega
    by_cases hyn : (i≤y.1 ∧ y.1<i+side) ∧ (j≤y.2 ∧ y.2<j+side)
    · have hyx := same_color_path_step__solver_final after_grid y x hyr hyc (by omega) (by omega)
        ((holdcol x hxr hxc hxo.1 hxo.2).trans hycol.symm) (adjcell_sym__solver_final x y hadj)
      have hxn := (sealed_component_unique__solver_final before after n m i j side color after_grid y x hn hm hi hj hl hplace hpaint hafter hyn.1 hyn.2 hxr hxc).mp hyx
      exact False.elim (holdout x hxr hxc hxo.1 hxo.2 hxn)
    · have hyb : Znth y.2 (Znth y.1 before_grid []) 0=Znth p.2 (Znth p.1 before_grid []) 0 := by
        rw [←hsame y hyr' hyc' hyn,←hpsame]
        exact hycol
      have hpy := same_color_path_append__solver_final before_grid p x y ((hold x hxr hxc).mpr hxo)
        (by omega) (by omega) hyb hadj
      exact (hold y hyr' hyc').mp hpy
  · intro hqo
    apply rectangle_connected__solver_final after_grid r c old_side (Znth p.2 (Znth p.1 after_grid []) 0) p q hos hr hc
      (by omega) (by omega) hpor hpoc hqo.1 hqo.2
    intro x hxor hxoc
    exact holdcol x (by omega) (by omega) hxor hxoc

theorem partial_components_place__solver_final (before after : List Int) (n m i j side color : Int)
    (before_grid after_grid : List (List Int)) :
    1≤n → 1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → Zlength before=n*m →
    CanPlace before n m i j side color → PaintRectanglePrefix before after m i j side color (side*side) →
    RowsOfFlat n m before before_grid → RowsOfFlat n m after after_grid →
    PartialSquareComponents n m before_grid → PartialSquareComponents n m after_grid := by
  intro hn hm hi hj hl hplace hp hb ha hcomponents p hpr hpc hpnz
  by_cases hpin : (i≤p.1 ∧ p.1<i+side) ∧ (j≤p.2 ∧ p.2<j+side)
  · refine ⟨i,j,side,hplace.1,hi.1,hj.1,hplace.2.1,hplace.2.2.1,hpin.1,hpin.2,?_⟩
    intro q hqr hqc
    exact sealed_component_unique__solver_final before after n m i j side color after_grid p q hn hm hi hj hl hplace hp ha hpin.1 hpin.2 hqr hqc
  · have hsame := (paint_rectangle_coordinate__solver_final before after n m i j side color p.1 p.2 hm hi hj hpr hpc hplace hl hp).2 hpin
    have hbefore : Znth p.2 (Znth p.1 before_grid []) 0≠0 := by
      rw [rows_of_flat_Znth__solver_final n m before before_grid p.1 p.2 hb hpr hpc,←hsame,
        ←rows_of_flat_Znth__solver_final n m after after_grid p.1 p.2 ha hpr hpc]
      exact hpnz
    obtain ⟨r,c,old_side,hos,hr,hc,hrb,hcb,hpor,hpoc,hold⟩ := hcomponents p hpr hpc hbefore
    refine ⟨r,c,old_side,hos,hr,hc,hrb,hcb,hpor,hpoc,?_⟩
    exact old_component_preserved__solver_final before after n m i j side color before_grid after_grid p r c old_side hn hm hi hj hl hplace hp hb ha hpr hpc hpin hpnz hos hr hc hrb hcb hpor hpoc hold

theorem greedy_trace_components__solver_final (n m next : Int) (flat : List Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next flat → ∃ grid, RowsOfFlat n m flat grid ∧ PartialSquareComponents n m grid := by
  intro hn hm ht
  induction ht with
  | GreedyTrace_zero flat hl hz =>
    obtain ⟨grid,hrows⟩ := rows_of_flat_from_length__solver_final n m flat hn hm hl
    refine ⟨grid,hrows,?_⟩
    intro p hpr hpc hpnz
    apply False.elim
    apply hpnz
    rw [rows_of_flat_Znth__solver_final n m flat grid p.1 p.2 hrows hpr hpc]
    apply hz
    constructor <;> nlinarith
  | GreedyTrace_skip next flat ht hn hc ih => exact ih
  | GreedyTrace_place next before after i j color side ht he hi hj hz hs hp ih =>
    obtain ⟨bg,hb,hbc⟩ := ih
    have hl := (trace_bounds_and_canonical__solver_final n m next before hn hm ht).2.1
    have hal : Zlength after=n*m := by have := hp.1; omega
    obtain ⟨ag,ha⟩ := rows_of_flat_from_length__solver_final n m after hn hm hal
    exact ⟨ag,ha,partial_components_place__solver_final before after n m i j side color bg ag hn hm hi hj hl hs.1.2.1 hp hb ha hbc⟩
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
