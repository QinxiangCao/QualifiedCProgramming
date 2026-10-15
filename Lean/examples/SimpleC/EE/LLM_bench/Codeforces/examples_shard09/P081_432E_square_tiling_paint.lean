import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_definitions
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

theorem neighbor_conflict_five_colour_choice__colour_selection (flat : List Int) (n m i j left_override : Int) :
    ∃ color, (65 ≤ color ∧ color ≤ 69) ∧ ¬ NeighborConflict flat n m i j color left_override := by
  classical
  by_contra hn
  push_neg at hn
  have h65 := hn 65 (by omega)
  have h66 := hn 66 (by omega)
  have h67 := hn 67 (by omega)
  have h68 := hn 68 (by omega)
  have h69 := hn 69 (by omega)
  unfold NeighborConflict at *
  by_cases hz : left_override = 0 <;> simp only [hz,ite_true,ite_false] at * <;> omega

theorem can_place_one_iff_legal_color__solver_colour_search (flat : List Int) (n m i j color : Int) :
    1 ≤ n → 1 ≤ m → (0 ≤ i ∧ i < n) → (0 ≤ j ∧ j < m) →
    Znth (i*m+j) flat 0 = 0 → (65 ≤ color ∧ color ≤ 90) →
    (CanPlace flat n m i j 1 color ↔ LegalColor flat n m i j 0 color) := by
  intro hn hm hi hj hz hc
  constructor
  · rintro ⟨hs,hr,hc',hempty,hhor,hver⟩
    refine ⟨hc,?_⟩
    have htop := (hhor j (by omega)).1
    have hbottom := (hhor j (by omega)).2
    have hleft := (hver i (by omega)).1
    have hright := (hver i (by omega)).2
    simp only [NeighborConflict,ite_true]
    omega
  · rintro ⟨hc,hfree⟩
    refine ⟨by omega,by omega,by omega,?_,?_,?_⟩
    · intro r q hr hq
      have hre : r=i := by omega
      have hqe : q=j := by omega
      simpa only [hre,hqe] using hz
    · intro q hq
      have hqe : q=j := by omega
      subst q
      constructor
      · intro ht he
        exact hfree (Or.inl ⟨ht,he⟩)
      · intro hb he
        exact hfree (Or.inr (Or.inl ⟨hb,he⟩))
    · intro r hr
      have hre : r=i := by omega
      subst r
      constructor
      · intro hl he
        apply hfree
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hl,by simpa using he⟩)))
      · intro hh he
        exact hfree (Or.inr (Or.inr (Or.inl ⟨hh,he⟩)))

theorem five_colour_neighbour_available__solver_colour_search (flat : List Int) (n m i j : Int) :
    1 ≤ n → 1 ≤ m → (0 ≤ i ∧ i < n) → (0 ≤ j ∧ j < m) → Znth (i*m+j) flat 0 = 0 →
    ∃ color, (65 ≤ color ∧ color ≤ 69) ∧ CanPlace flat n m i j 1 color := by
  intro hn hm hi hj hz
  obtain ⟨color,hc,hfree⟩ := neighbor_conflict_five_colour_choice__colour_selection flat n m i j 0
  exact ⟨color,hc,(can_place_one_iff_legal_color__solver_colour_search flat n m i j color hn hm hi hj hz (by omega)).mpr ⟨by omega,hfree⟩⟩

theorem greedy_side_extend__solver_greedy_side (flat : List Int) (n m i j color side fallback : Int) :
    GreedySideState flat n m i j color side → CanPlace flat n m i j (side+1) color →
    LeastLegalColor flat n m i (j+side) color fallback → color < fallback →
    GreedySideState flat n m i j color (side+1) := by
  rintro ⟨hcur,hprev⟩ hn hf hlt
  refine ⟨hn,?_⟩
  intro prev hp
  by_cases hl : prev < side
  · exact hprev prev (by omega)
  · have he : prev=side := by omega
    subst prev
    exact ⟨hn,fallback,hf,hlt⟩

theorem replace_nth_length__solver_paint (A : Type) (n : Nat) (l : List A) (value : A) :
    (replace_nth n l value).length = l.length := by
  induction l generalizing n with
  | nil => simp [replace_nth]
  | cons head tail ih => cases n <;> simp [replace_nth,ih]

theorem zlength_replace_Znth__solver_paint (A : Type) (index : Int) (value : A) (l : List A) :
    Zlength (replace_Znth index value l) = Zlength l := Zlength_replace_Znth l index value

theorem paint_rectangle_prefix_replace_step__solver_paint (before current : List Int) (m i j side color done : Int) :
    0 ≤ done → (0 ≤ (i+done /ᶻ side)*m+(j+done mod side) ∧ (i+done /ᶻ side)*m+(j+done mod side) < Zlength current) →
    PaintRectanglePrefix before current m i j side color done →
    PaintRectanglePrefix before (replace_Znth ((i+done /ᶻ side)*m+(j+done mod side)) color current) m i j side color (done+1) := by
  rintro hd hnew ⟨hlen,hpaint⟩
  refine ⟨by rw [Zlength_replace_Znth,hlen],?_⟩
  intro index hi
  by_cases he : index = (i+done /ᶻ side)*m+(j+done mod side)
  · subst index
    exact Or.inl ⟨⟨done,by omega,rfl⟩,Znth_replace_Znth_Same 0 current _ color hnew⟩
  · have hdif := Znth_replace_Znth_Diff 0 current _ index color hnew (by omega) (Ne.symm he)
    rcases hpaint index hi with ⟨⟨off,hoff,ho⟩,hc⟩ | ⟨hout,hs⟩
    · exact Or.inl ⟨⟨off,by omega,ho⟩,hdif.trans hc⟩
    · refine Or.inr ⟨?_,hdif.trans hs⟩
      intro off ho
      by_cases hb : off < done
      · exact hout off (by omega)
      · have ho' : off=done := by omega
        simpa only [ho'] using he

theorem canonical_grid_replace__solver_paint (flat : List Int) (index color : Int) :
    (0 ≤ index ∧ index < Zlength flat) → (65 ≤ color ∧ color ≤ 90) → CanonicalGrid flat →
    CanonicalGrid (replace_Znth index color flat) := by
  intro hi hc hg k hk
  rw [Zlength_replace_Znth] at hk
  by_cases he : k=index
  · subst k
    rw [Znth_replace_Znth_Same 0 flat index color hi]
    exact Or.inr hc
  · rw [Znth_replace_Znth_Diff 0 flat index k color hi hk (Ne.symm he)]
    exact hg k hk

theorem paint_prefix_replace__solver_paint (before current : List Int) (m i j side color r q : Int) :
    1 ≤ side → (i ≤ r ∧ r < i+side) → (j ≤ q ∧ q < j+side) →
    (0 ≤ r*m+q ∧ r*m+q < Zlength current) →
    PaintRectanglePrefix before current m i j side color ((r-i)*side+(q-j)) →
    PaintRectanglePrefix before (replace_Znth (r*m+q) color current) m i j side color ((r-i)*side+((q+1)-j)) := by
  intro hs hr hq hi hp
  have hd : ((r-i)*side+(q-j)) /ᶻ side = r-i := by
    change ((r-i)*side+(q-j)).fdiv side = r-i
    rw [add_comm,Int.add_mul_fdiv_right _ _ (by omega),Int.fdiv_eq_zero_of_lt (by omega) (by omega)]
    omega
  have hm : ((r-i)*side+(q-j)) mod side = q-j := by
    change ((r-i)*side+(q-j)).fmod side = q-j
    rw [add_comm,Int.add_mul_fmod_self_right,Int.fmod_eq_of_lt (by omega) (by omega)]
  have hcoord : (i+((r-i)*side+(q-j)) /ᶻ side)*m+(j+((r-i)*side+(q-j)) mod side)=r*m+q := by rw [hd,hm]; ring
  have step := paint_rectangle_prefix_replace_step__solver_paint before current m i j side color ((r-i)*side+(q-j)) (by nlinarith) (by simpa only [hcoord] using hi) hp
  simpa only [hcoord,show (r-i)*side+(q-j)+1=(r-i)*side+((q+1)-j) by ring] using step

theorem Znth_In_range__solver_final {A : Type} (l : List A) (i : Int) (d : A) :
    (0 ≤ i ∧ i < Zlength l) → In (Znth i l d) l := by
  intro hi
  have hk : i.toNat < l.length := by
    cases i with
    | ofNat n => exact Int.ofNat_lt.mp hi.2
    | negSucc n => omega
  simpa only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using List.getElem_mem hk
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
