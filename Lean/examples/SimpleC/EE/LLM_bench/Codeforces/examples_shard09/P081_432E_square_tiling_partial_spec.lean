import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_components
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

theorem Forall_from_Znth__solver_final {A : Type} (P : A → Prop) (l : List A) (d : A) :
    (∀ i, (0≤i ∧ i<Zlength l) → P (Znth i l d)) → Forall P l := by
  intro hall
  rw [Forall.iff_forall_mem]
  intro x hx
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hp := hall (i : Int) (by change 0≤(i : Int) ∧ (i : Int)<(l.length : Int); omega)
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he] using hp

theorem Zlength_concat_rect__solver_final {A : Type} (rows : List (List A)) (m : Int) :
    Forall (fun row => Zlength row=m) rows → Zlength (concat rows)=Zlength rows*m := by
  intro hr
  induction hr with
  | nil => simp only [concat,List.flatten_nil,Zlength_nil,zero_mul]
  | @cons row rows hw hrows ih =>
    simp only [concat,List.flatten_cons,Zlength_app,Zlength_cons,hw,ih]
    ring

theorem p081_forall_flatten {A : Type} (P : A → Prop) (rows : List (List A)) :
    Forall P rows.flatten ↔ Forall (Forall P) rows := by
  simp only [Forall.iff_forall_mem]
  constructor
  · intro h row hr x hx
    exact h x (List.mem_flatten.mpr ⟨row,hr,hx⟩)
  · intro h x hx
    obtain ⟨row,hr,hx⟩ := List.mem_flatten.mp hx
    exact h row hr x hx

theorem complete_partial_tiling_implies_spec__solver_final (n m : Int) (flat : List Int) :
    1≤n → 1≤m → Zlength flat=n*m → PartialTilingState n m (n*m) flat →
    ∃ out, Flatten out=flat ∧ Spec n m out := by
  rintro hn hm hl ⟨out,hrows,hprefix,hcolors,hcomponents,hlex⟩
  have hgl := hrows.1
  have hw := hrows.2.1
  have hflat := hrows.2.2
  have hfc : Forall (fun c : Int => 65≤c ∧ c≤90) (Flatten out) := by
    rw [hflat]
    apply Forall_from_Znth__solver_final _ flat 0
    intro k hk
    exact hprefix k (by omega)
  have hrc : Forall (Forall (fun c : Int => 65≤c ∧ c≤90)) out := (p081_forall_flatten _ out).mp hfc
  refine ⟨out,hflat,?_,?_⟩
  · refine ⟨⟨hgl,hw⟩,hrc,?_⟩
    intro p hpr hpc
    have hcol : 65≤Znth p.2 (Znth p.1 out []) 0 ∧ Znth p.2 (Znth p.1 out []) 0≤90 := by
      rw [rows_of_flat_Znth__solver_final n m flat out p.1 p.2 hrows hpr hpc]
      apply hprefix
      constructor <;> nlinarith
    obtain ⟨r,c,side,hs,hr,hc,hrb,hcb,hpor,hpoc,hcomp⟩ := hcomponents p hpr hpc (by omega)
    exact ⟨r,c,side,hs,hpor,hpoc,hr,hc,hrb,hcb,hcomp⟩
  · intro candidate hcand
    have hcl : Zlength (Flatten candidate)=n*m := by
      have h := Zlength_concat_rect__solver_final candidate m hcand.1.2
      change Zlength (Flatten candidate)=Zlength candidate*m at h
      simpa only [hcand.1.1] using h
    have hol : Zlength (Flatten out)=n*m := hflat ▸ hl
    rcases hlex candidate hcand with heq | ⟨first,hfirst,hsame,hless⟩
    · left
      apply (ListLib.list_eq_ext (Flatten out) (Flatten candidate) 0).mpr
      simp only [ListLib.Zlength,ListLib.Znth]
      refine ⟨by omega,?_⟩
      intro k hk
      rw [hflat]
      exact heq k (by omega)
    · right; left
      refine ⟨first,by omega,?_,?_⟩
      · intro k hk
        rw [hflat]
        exact hsame k hk
      · rw [hflat]
        exact hless

theorem square_tiling_rows__solver_final (n m : Int) (grid : List (List Int)) :
    SquareTiling n m grid → RowsOfFlat n m (Flatten grid) grid := by
  intro ht
  exact ⟨ht.1.1,ht.1.2,rfl⟩

theorem square_tiling_flat_color__solver_final (n m : Int) (grid : List (List Int)) (k : Int) :
    SquareTiling n m grid → (0≤k ∧ k<n*m) → (65≤Znth k (Flatten grid) 0 ∧ Znth k (Flatten grid) 0≤90) := by
  intro ht hk
  have hl : Zlength (Flatten grid)=n*m := by
    have h := Zlength_concat_rect__solver_final grid m ht.1.2
    change Zlength (Flatten grid)=Zlength grid*m at h
    simpa only [ht.1.1] using h
  have hc := (p081_forall_flatten _ grid).mpr ht.2.1
  exact (Forall.iff_forall_mem.mp hc) _ (Znth_In_range__solver_final (Flatten grid) k 0 (by omega))

theorem paint_preserves_nonzero__solver_final (before after : List Int) (n m i j side color : Int) :
    CanPlace before n m i j side color → PaintRectanglePrefix before after m i j side color (side*side) →
    ∀ k, (0≤k ∧ k<Zlength before) → Znth k before 0≠0 → Znth k after 0=Znth k before 0 := by
  intro hplace hpaint k hk hnz
  rcases hpaint.2 k hk with ⟨⟨off,hoff,hmap⟩,hpainted⟩ | ⟨hout,hsame⟩
  · have hs := hplace.1
    have hd : 0≤off /ᶻ side := Int.fdiv_nonneg hoff.1 (by omega)
    have hmod : 0≤off mod side ∧ off mod side<side := ⟨Int.fmod_nonneg hoff.1 (by omega),Int.fmod_lt_of_pos off (by omega)⟩
    have he : off mod side+side*(off /ᶻ side)=off := Int.fmod_add_mul_fdiv off side
    have hdivlt : off /ᶻ side<side := by nlinarith
    apply False.elim
    apply hnz
    rw [hmap]
    exact hplace.2.2.2.1 _ _ (by omega) (by omega)
  · exact hsame
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
