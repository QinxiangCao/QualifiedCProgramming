import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_rows
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem p081_abs_eq (a : Int) : Z.abs a = abs a := by
  simp only [Z.abs,Int.ofNat_eq_coe,Int.natCast_natAbs]

theorem adjcell_cases__solver_final (p q : Cell) : AdjCell p q →
    (q.1=p.1+1 ∧ q.2=p.2) ∨ (q.1=p.1-1 ∧ q.2=p.2) ∨
    (q.1=p.1 ∧ q.2=p.2+1) ∨ (q.1=p.1 ∧ q.2=p.2-1) := by
  intro h
  unfold AdjCell at h
  simp only [p081_abs_eq] at h
  by_cases hr : 0≤p.1-q.1
  · rw [abs_of_nonneg hr] at h
    by_cases hc : 0≤p.2-q.2
    · rw [abs_of_nonneg hc] at h; omega
    · rw [abs_of_neg (by omega : p.2-q.2<0)] at h; omega
  · rw [abs_of_neg (by omega : p.1-q.1<0)] at h
    by_cases hc : 0≤p.2-q.2
    · rw [abs_of_nonneg hc] at h; omega
    · rw [abs_of_neg (by omega : p.2-q.2<0)] at h; omega

theorem same_color_path_step__solver_final (grid : List (List Int)) (p q : Cell) :
    (0≤p.1 ∧ p.1<Zlength grid) → (0≤p.2 ∧ p.2<Zlength (Znth 0 grid [])) →
    (0≤q.1 ∧ q.1<Zlength grid) → (0≤q.2 ∧ q.2<Zlength (Znth 0 grid [])) →
    Znth q.2 (Znth q.1 grid []) 0=Znth p.2 (Znth p.1 grid []) 0 → AdjCell p q → SameColorPath grid p q := by
  intro hpr hpc hqr hqc hcol hadj
  refine ⟨[p,q],by simp,rfl,rfl,.cons ⟨hpr,hpc,rfl⟩ (.cons ⟨hqr,hqc,hcol⟩ .nil),?_⟩
  intro k hk
  have he : k=0 := by change 0≤k ∧ k<1 at hk; omega
  subst k
  exact hadj

theorem same_color_path_refl__solver_final (grid : List (List Int)) (p : Cell) :
    (0≤p.1 ∧ p.1<Zlength grid) → (0≤p.2 ∧ p.2<Zlength (Znth 0 grid [])) → SameColorPath grid p p := by
  intro hpr hpc
  refine ⟨[p],by simp,rfl,rfl,.cons ⟨hpr,hpc,rfl⟩ .nil,?_⟩
  intro k hk
  change 0≤k ∧ k<0 at hk
  omega

theorem same_color_path_prepend__solver_final (grid : List (List Int)) (p p' q : Cell) :
    (0≤p.1 ∧ p.1<Zlength grid) → (0≤p.2 ∧ p.2<Zlength (Znth 0 grid [])) →
    Znth p'.2 (Znth p'.1 grid []) 0=Znth p.2 (Znth p.1 grid []) 0 → AdjCell p p' →
    SameColorPath grid p' q → SameColorPath grid p q := by
  rintro hpr hpc hc hadj ⟨path,hne,hfirst,hlast,hall,hsteps⟩
  have hlen : 0<Zlength path := by
    cases path with
    | nil => contradiction
    | cons a l => have h:=Zlength_nonneg l; simp only [Zlength_cons]; omega
  refine ⟨p::path,by simp,rfl,?_,?_,?_⟩
  · simp only [Zlength_cons,add_sub_cancel_right]
    rw [Znth_cons (0,0) (Zlength path) p path hlen]
    exact hlast
  · constructor
    · exact ⟨hpr,hpc,rfl⟩
    · rw [Forall.iff_forall_mem] at hall ⊢
      intro x hx
      obtain ⟨hr,hc',hcol⟩ := hall x hx
      exact ⟨hr,hc',hcol.trans hc⟩
  · intro k hk
    simp only [Zlength_cons] at hk
    by_cases hz : k=0
    · subst k
      change AdjCell p (Znth 0 path (0,0))
      rw [hfirst]
      exact hadj
    · rw [Znth_cons (0,0) k p path (by omega),Znth_cons (0,0) (k+1) p path (by omega)]
      have h := hsteps (k-1) (by omega)
      simpa only [sub_add_cancel,add_sub_cancel_right] using h

theorem manhattan_row_up__solver_final (pr pc qr qc : Int) : pr<qr →
    Z.abs (pr+1-qr)+Z.abs (pc-qc)<Z.abs (pr-qr)+Z.abs (pc-qc) := by
  intro h
  simp only [p081_abs_eq]
  rw [abs_of_nonpos (by omega : pr+1-qr≤0),abs_of_neg (by omega : pr-qr<0)]
  omega

theorem manhattan_row_down__solver_final (pr pc qr qc : Int) : qr<pr →
    Z.abs (pr-1-qr)+Z.abs (pc-qc)<Z.abs (pr-qr)+Z.abs (pc-qc) := by
  intro h
  simp only [p081_abs_eq]
  rw [abs_of_nonneg (by omega : 0≤pr-1-qr),abs_of_nonneg (by omega : 0≤pr-qr)]
  omega

theorem manhattan_col_up__solver_final (pr pc qr qc : Int) : pc<qc →
    Z.abs (pr-qr)+Z.abs (pc+1-qc)<Z.abs (pr-qr)+Z.abs (pc-qc) := by
  intro h
  simp only [p081_abs_eq]
  rw [abs_of_nonpos (by omega : pc+1-qc≤0),abs_of_neg (by omega : pc-qc<0)]
  omega

theorem manhattan_col_down__solver_final (pr pc qr qc : Int) : qc<pc →
    Z.abs (pr-qr)+Z.abs (pc-1-qc)<Z.abs (pr-qr)+Z.abs (pc-qc) := by
  intro h
  simp only [p081_abs_eq]
  rw [abs_of_nonneg (by omega : 0≤pc-1-qc),abs_of_nonneg (by omega : 0≤pc-qc)]
  omega

theorem rectangle_connected__solver_final (grid : List (List Int)) (r c side color : Int) (p q : Cell) :
    1≤side → 0≤r → 0≤c → r+side≤Zlength grid → c+side≤Zlength (Znth 0 grid []) →
    (r≤p.1 ∧ p.1<r+side) → (c≤p.2 ∧ p.2<c+side) →
    (r≤q.1 ∧ q.1<r+side) → (c≤q.2 ∧ q.2<c+side) →
    (∀ x : Cell, (r≤x.1 ∧ x.1<r+side) → (c≤x.2 ∧ x.2<c+side) → Znth x.2 (Znth x.1 grid []) 0=color) →
    SameColorPath grid p q := by
  intro hs hr hc hrb hcb hpr hpc hqr hqc hp
  have go : ∀ fuel : Nat, ∀ p : Cell, (Z.abs (p.1-q.1)+Z.abs (p.2-q.2)).toNat<fuel →
      (r≤p.1 ∧ p.1<r+side) → (c≤p.2 ∧ p.2<c+side) → SameColorPath grid p q := by
    intro fuel
    induction fuel with
    | zero => intro p hf hpr hpc; omega
    | succ fuel ih =>
      intro p hf hpr hpc
      have step : ∀ p' : Cell, (r≤p'.1 ∧ p'.1<r+side) → (c≤p'.2 ∧ p'.2<c+side) →
          AdjCell p p' → Z.abs (p'.1-q.1)+Z.abs (p'.2-q.2)<Z.abs (p.1-q.1)+Z.abs (p.2-q.2) → SameColorPath grid p q := by
        intro p' hp'r hp'c hadj hd
        apply same_color_path_prepend__solver_final grid p p' q (by omega) (by omega)
          ((hp p' hp'r hp'c).trans (hp p hpr hpc).symm) hadj
        apply ih p' _ hp'r hp'c
        have hn0 : 0≤Z.abs (p.1-q.1)+Z.abs (p.2-q.2) := add_nonneg (Z.abs_nonneg _) (Z.abs_nonneg _)
        have hn1 : 0≤Z.abs (p'.1-q.1)+Z.abs (p'.2-q.2) := add_nonneg (Z.abs_nonneg _) (Z.abs_nonneg _)
        omega
      by_cases her : p.1=q.1
      · by_cases hec : p.2=q.2
        · have he : p=q := Prod.ext her hec
          subst p
          exact same_color_path_refl__solver_final grid q (by omega) (by omega)
        · by_cases hl : p.2<q.2
          · apply step (p.1,p.2+1) (by simpa using hpr) (by dsimp; omega)
            · simp [AdjCell,Z.abs,show p.2-(p.2+1)=(-1 : Int) by omega]
            · exact manhattan_col_up__solver_final _ _ _ _ hl
          · apply step (p.1,p.2-1) (by simpa using hpr) (by dsimp; omega)
            · simp [AdjCell,Z.abs,show p.2-(p.2-1)=(1 : Int) by omega]
            · exact manhattan_col_down__solver_final _ _ _ _ (by omega)
      · by_cases hl : p.1<q.1
        · apply step (p.1+1,p.2) (by dsimp; omega) (by simpa using hpc)
          · simp [AdjCell,Z.abs,show p.1-(p.1+1)=(-1 : Int) by omega]
          · exact manhattan_row_up__solver_final _ _ _ _ hl
        · apply step (p.1-1,p.2) (by dsimp; omega) (by simpa using hpc)
          · simp [AdjCell,Z.abs,show p.1-(p.1-1)=(1 : Int) by omega]
          · exact manhattan_row_down__solver_final _ _ _ _ (by omega)
  exact go _ p (Nat.lt_succ_self _) hpr hpc

theorem path_region_induction__solver_final (grid : List (List Int)) (color : Int) (region : Cell → Prop) (path : List Cell) :
    path≠[] → Forall (fun x => (0≤x.1 ∧ x.1<Zlength grid) ∧ (0≤x.2 ∧ x.2<Zlength (Znth 0 grid [])) ∧ Znth x.2 (Znth x.1 grid []) 0=color) path →
    region (Znth 0 path (0,0)) →
    (∀ x y, region x → (0≤y.1 ∧ y.1<Zlength grid) → (0≤y.2 ∧ y.2<Zlength (Znth 0 grid [])) → Znth y.2 (Znth y.1 grid []) 0=color → AdjCell x y → region y) →
    (∀ k, (0≤k ∧ k<Zlength path-1) → AdjCell (Znth k path (0,0)) (Znth (k+1) path (0,0))) → Forall region path := by
  intro hne hall hfirst hclosed hsteps
  induction path with
  | nil => contradiction
  | cons x tail ih =>
    refine .cons hfirst ?_
    cases tail with
    | nil => exact .nil
    | cons y ys =>
      cases hall with | cons hx htail =>
        refine ih (by simp) htail ?_ ?_
        · cases htail with | cons hy hys =>
            apply hclosed x y hfirst hy.1 hy.2.1 hy.2.2
            exact hsteps 0 (by have h:=Zlength_nonneg ys; simp only [Zlength_cons]; omega)
        · intro k hk
          have h := hsteps (k+1) (by simp only [Zlength_cons] at *; omega)
          rw [Znth_cons (0,0) (k+1) x (y::ys) (by omega),Znth_cons (0,0) (k+1+1) x (y::ys) (by omega)] at h
          simpa only [add_sub_cancel_right] using h

theorem same_color_path_closed__solver_final (grid : List (List Int)) (color : Int) (region : Cell → Prop) (p q : Cell) :
    SameColorPath grid p q → region p →
    (∀ x y, region x → (0≤y.1 ∧ y.1<Zlength grid) → (0≤y.2 ∧ y.2<Zlength (Znth 0 grid [])) → Znth y.2 (Znth y.1 grid []) 0=color → AdjCell x y → region y) →
    Znth p.2 (Znth p.1 grid []) 0=color → region q := by
  rintro ⟨path,hne,hfirst,hlast,hall,hsteps⟩ hp hclosed hcolor
  have hforall : Forall (fun x : Cell => (0≤x.1 ∧ x.1<Zlength grid) ∧ (0≤x.2 ∧ x.2<Zlength (Znth 0 grid [])) ∧ Znth x.2 (Znth x.1 grid []) 0=color) path := by
    rw [Forall.iff_forall_mem] at hall ⊢
    intro x hx
    obtain ⟨hr,hc,hcol⟩ := hall x hx
    exact ⟨hr,hc,hcol.trans hcolor⟩
  have hr := path_region_induction__solver_final grid color region path hne hforall (hfirst ▸ hp) hclosed hsteps
  rw [Forall.iff_forall_mem] at hr
  rw [← hlast]
  apply hr
  apply Znth_In_range__solver_final
  have hp : 0<Zlength path := by
    cases path with
    | nil => contradiction
    | cons x xs => have h:=Zlength_nonneg xs; simp only [Zlength_cons]; omega
  omega
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
