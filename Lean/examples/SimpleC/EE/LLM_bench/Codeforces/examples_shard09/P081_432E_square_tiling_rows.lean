import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_paint
import ListLib.General.Length
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

theorem rows_of_flat_nat__solver_final (count width : Nat) (flat : List Int) :
    flat.length = count*width → ∃ grid : List (List Int), grid.length=count ∧
    Forall (fun row => row.length=width) grid ∧ concat grid=flat := by
  intro hlen
  induction count generalizing flat with
  | zero =>
    have he : flat=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst flat
    exact ⟨[],rfl,.nil,rfl⟩
  | succ count ih =>
    simp only [Nat.succ_mul] at hlen
    have hw : width ≤ flat.length := by omega
    obtain ⟨rows,hr,hwid,hcat⟩ := ih (flat.drop width) (by simp only [List.length_drop]; omega)
    refine ⟨flat.take width::rows,by simp [hr],.cons ?_ hwid,?_⟩
    · simp only [List.length_take,Nat.min_eq_left hw]
    · simpa only [concat,List.flatten_cons,hcat] using List.take_append_drop width flat

theorem rows_of_flat_from_length__solver_final (n m : Int) (flat : List Int) :
    1 ≤ n → 1 ≤ m → Zlength flat=n*m → ∃ grid, RowsOfFlat n m flat grid := by
  intro hn hm hl
  have hn' : (n.toNat : Int)=n := Int.toNat_of_nonneg (by omega)
  have hm' : (m.toNat : Int)=m := Int.toNat_of_nonneg (by omega)
  have hl' : flat.length=n.toNat*m.toNat := by
    have h : (flat.length : Int)=(n.toNat : Int)*(m.toNat : Int) := by simpa only [hn',hm'] using hl
    exact_mod_cast h
  obtain ⟨grid,hgl,hrows,hcat⟩ := rows_of_flat_nat__solver_final n.toNat m.toNat flat hl'
  refine ⟨grid,?_,?_,hcat⟩
  · simp only [Zlength,hgl,Int.ofNat_eq_coe,hn']
  · rw [Forall.iff_forall_mem] at hrows ⊢
    intro row hr
    simp only [Zlength,hrows row hr,Int.ofNat_eq_coe,hm']

theorem paint_rectangle_index_ge_anchor__solver_final (m i j side off : Int) :
    1 ≤ m → 0 ≤ j → 1 ≤ side → 0 ≤ off → i*m+j ≤ (i+off /ᶻ side)*m+(j+off mod side) := by
  intro hm hj hs ho
  have hd : 0 ≤ off /ᶻ side := Int.fdiv_nonneg ho (by omega)
  have hr : 0 ≤ off mod side := Int.fmod_nonneg ho (by omega)
  nlinarith

theorem paint_rectangle_membership__solver_final (before after : List Int) (n m i j side color : Int) :
    1 ≤ m → (0 ≤ i ∧ i<n) → (0 ≤ j ∧ j<m) → Zlength before=n*m →
    CanPlace before n m i j side color → PaintRectanglePrefix before after m i j side color (side*side) →
    Zlength after=n*m ∧ (∀ index, (0 ≤ index ∧ index<i*m+j) → Znth index after 0=Znth index before 0) ∧
    Znth (i*m+j) after 0=color := by
  rintro hm hi hj hlen ⟨hs,hib,hjb,hempty,hhor,hver⟩ ⟨hal,hpaint⟩
  have hanchor : 0 ≤ i*m+j ∧ i*m+j<n*m := by constructor <;> nlinarith
  refine ⟨by omega,?_,?_⟩
  · intro index hindex
    rcases hpaint index (by omega) with ⟨⟨off,hoff,he⟩,hc⟩ | ⟨hout,hsame⟩
    · have hb := paint_rectangle_index_ge_anchor__solver_final m i j side off hm hj.1 hs hoff.1
      omega
    · exact hsame
  · rcases hpaint (i*m+j) (by omega) with ⟨hmem,hc⟩ | ⟨hout,hsame⟩
    · exact hc
    · have h := hout 0 (by constructor <;> nlinarith)
      exact False.elim (h (by simp [Z.div,Z.modulo]))

theorem trace_bounds_and_canonical__solver_final (n m next : Int) (flat : List Int) :
    1 ≤ n → 1 ≤ m → GreedyPlacementTrace n m next flat →
    (0 ≤ next ∧ next≤n*m) ∧ Zlength flat=n*m ∧ CanonicalGrid flat ∧
    (∀ k, (0 ≤ k ∧ k<next) → 65≤Znth k flat 0 ∧ Znth k flat 0≤90) := by
  intro hn hm ht
  induction ht with
  | GreedyTrace_zero flat hlen hz =>
    refine ⟨⟨by omega,by nlinarith⟩,hlen,?_,?_⟩
    · intro k hk
      exact Or.inl (hz k (by omega))
    · intro k hk; omega
  | GreedyTrace_skip next flat ht hnext hcell ih =>
    refine ⟨by omega,ih.2.1,ih.2.2.1,?_⟩
    intro k hk
    by_cases he : k=next
    · simpa only [he] using hcell
    · exact ih.2.2.2 k (by omega)
  | GreedyTrace_place next before after i j color side ht he hi hj hanchor hs hp ih =>
    subst next
    have hc := hs.1.1.1.1
    have hplace := hs.1.2.1
    obtain ⟨hlen,hbefore,hafter⟩ := paint_rectangle_membership__solver_final before after n m i j side color hm hi hj ih.2.1 hplace hp
    refine ⟨⟨by nlinarith,by nlinarith⟩,hlen,?_,?_⟩
    · intro k hk
      rcases hp.2 k (by have := ih.2.1; omega) with ⟨hm,hcol⟩ | ⟨hout,hsame⟩
      · rw [hcol]; exact Or.inr hc
      · rw [hsame]; exact ih.2.2.1 k (by have := ih.2.1; omega)
    · intro k hk
      by_cases he : k=i*m+j
      · rw [he,hafter]; exact hc
      · rw [hbefore k (by omega)]
        exact ih.2.2.2 k (by omega)

theorem Znth_concat_rect__solver_final (grid : List (List Int)) (m r c : Int) :
    (0 ≤ r ∧ r<Zlength grid) → (0 ≤ c ∧ c<m) → Forall (fun row => Zlength row=m) grid →
    Znth c (Znth r grid []) 0=Znth (r*m+c) (concat grid) 0 := by
  intro hr hc hrows
  induction grid generalizing r with
  | nil => simp [Zlength] at hr; omega
  | cons row rows ih =>
    cases hrows with | cons hrow hrows =>
      simp only [concat,List.flatten_cons]
      by_cases hz : r=0
      · subst r
        simp only [Znth0_cons,zero_mul,zero_add]
        exact (ListLib.app_Znth1 0 row (concat rows) c (show 0≤c ∧ c<Zlength row from by omega)).symm
      · have hr1 : 1≤r := by omega
        rw [Znth_cons [] r row rows (by omega),app_Znth2 0 row (concat rows) (r*m+c) (by nlinarith)]
        rw [show r*m+c-Zlength row=(r-1)*m+c by rw [hrow]; ring]
        exact ih (r-1) (by simp only [Zlength_cons] at hr; omega) hrows

theorem rows_of_flat_Znth__solver_final (n m : Int) (flat : List Int) (grid : List (List Int)) (r c : Int) :
    RowsOfFlat n m flat grid → (0≤r ∧ r<n) → (0≤c ∧ c<m) →
    Znth c (Znth r grid []) 0=Znth (r*m+c) flat 0 := by
  rintro ⟨hl,hw,hflat⟩ hr hc
  rw [← hflat]
  exact Znth_concat_rect__solver_final grid m r c (by omega) hc hw

theorem rows_of_flat_unique__solver_final (n m : Int) (flat : List Int) (left right : List (List Int)) :
    RowsOfFlat n m flat left → RowsOfFlat n m flat right → left=right := by
  rintro ⟨hl,hw,hflat⟩ ⟨hr,hw',hflat'⟩
  apply (ListLib.list_eq_ext left right []).mpr
  simp only [ListLib.Zlength,ListLib.Znth]
  refine ⟨by omega,?_⟩
  intro r hrange
  have hrange' : 0≤r ∧ r<Zlength right := by omega
  have hrow : Zlength (Znth r left [])=m := (Forall.iff_forall_mem.mp hw) _ (Znth_In_range__solver_final left r [] hrange)
  have hrow' : Zlength (Znth r right [])=m := (Forall.iff_forall_mem.mp hw') _ (Znth_In_range__solver_final right r [] hrange')
  apply (ListLib.list_eq_ext _ _ 0).mpr
  simp only [ListLib.Zlength,ListLib.Znth]
  refine ⟨by omega,?_⟩
  intro c hc
  rw [Znth_concat_rect__solver_final left m r c hrange (by omega) hw,Znth_concat_rect__solver_final right m r c hrange' (by omega) hw']
  exact congrArg (fun l => Znth (r*m+c) l 0) (hflat.trans hflat'.symm)

theorem p081_div_mod_pair (a b d : Int) (hb : 0≤b ∧ b<d) :
    (a*d+b) /ᶻ d=a ∧ (a*d+b) mod d=b := by
  constructor
  · change (a*d+b).fdiv d=a
    rw [add_comm,Int.add_mul_fdiv_right _ _ (by omega),Int.fdiv_eq_zero_of_lt hb.1 hb.2,zero_add]
  · change (a*d+b).fmod d=b
    rw [add_comm,Int.add_mul_fmod_self_right,Int.fmod_eq_of_lt hb.1 hb.2]

theorem paint_rectangle_coordinate__solver_final (before after : List Int) (n m i j side color r c : Int) :
    1≤m → (0≤i ∧ i<n) → (0≤j ∧ j<m) → (0≤r ∧ r<n) → (0≤c ∧ c<m) →
    CanPlace before n m i j side color → Zlength before=n*m →
    PaintRectanglePrefix before after m i j side color (side*side) →
    (((i≤r ∧ r<i+side) ∧ (j≤c ∧ c<j+side)) → Znth (r*m+c) after 0=color) ∧
    (¬((i≤r ∧ r<i+side) ∧ (j≤c ∧ c<j+side)) → Znth (r*m+c) after 0=Znth (r*m+c) before 0) := by
  rintro hm hi hj hr hc ⟨hs,hib,hjb,he,hh,hv⟩ hl ⟨hal,hpaint⟩
  have hidx : 0≤r*m+c ∧ r*m+c<Zlength before := by constructor <;> nlinarith
  have hp := hpaint (r*m+c) hidx
  constructor
  · intro hin
    rcases hp with ⟨hmem,hcolor⟩ | ⟨hout,hsame⟩
    · exact hcolor
    · have hb : 0≤c-j ∧ c-j<side := by omega
      obtain ⟨hd,hmod⟩ := p081_div_mod_pair (r-i) (c-j) side hb
      have ho := hout ((r-i)*side+(c-j)) (by constructor <;> nlinarith)
      apply False.elim
      apply ho
      rw [hd,hmod]
      ring
  · intro hout
    rcases hp with ⟨⟨off,hoff,heq⟩,hcolor⟩ | ⟨hne,hsame⟩
    · have hd : 0≤off /ᶻ side := Int.fdiv_nonneg hoff.1 (by omega)
      have hmod : 0≤off mod side ∧ off mod side<side := ⟨Int.fmod_nonneg hoff.1 (by omega),Int.fmod_lt_of_pos off (by omega)⟩
      have hdecomp : off mod side+side*(off /ᶻ side)=off := Int.fmod_add_mul_fdiv off side
      have hdivlt : off /ᶻ side<side := by nlinarith
      have hcol : 0≤j+off mod side ∧ j+off mod side<m := by omega
      have hrowleft := (p081_div_mod_pair r c m hc).1
      have hrowright := (p081_div_mod_pair (i+off /ᶻ side) (j+off mod side) m hcol).1
      rw [heq,hrowright] at hrowleft
      apply False.elim
      apply hout
      constructor
      · omega
      · constructor <;> nlinarith
    · exact hsame

theorem lex_first_difference__solver_final (next : Int) (left right : List Int) :
    0≤next → LexPrefixLe next left right → Znth next left 0≤Znth next right 0 → LexPrefixLe (next+1) left right := by
  intro hn hl hc
  rcases hl with he | ⟨first,hfirst,hs,hlt⟩
  · by_cases hat : Znth next left 0=Znth next right 0
    · left
      intro k hk
      by_cases hkn : k=next
      · simpa only [hkn] using hat
      · exact he k (by omega)
    · exact Or.inr ⟨next,by omega,he,by omega⟩
  · exact Or.inr ⟨first,by omega,hs,hlt⟩
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
