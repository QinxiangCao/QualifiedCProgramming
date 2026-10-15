import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_definitions
import ListLib.General.Length

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem Znth_In__scan_conflict (A : Type) (l : List A) (d : A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := by
  have hn : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  simp only [Znth, List.getD, List.getElem?_eq_getElem hn, Option.getD_some]
  exact List.getElem_mem hn

theorem p053_Zlength_sublist (lo hi : Int) (l : List Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := ListLib.Zlength_sublist lo hi l hlo hhi

theorem p053_app_Znth1 {A : Type} (d : A) (pref tail : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength pref) : Znth i (pref ++ tail) d = Znth i pref d :=
  ListLib.app_Znth1 d pref tail i hi

theorem OnSet_fold_upper_bound__outer_loop_component_commit (n : Int) (cs r : List Int)
    (ho : OnSet n cs r) : r.foldr (· + ·) 0 ≤ n := by
  rcases ho with ⟨hlen, hcol, huncol⟩
  have hv : Forall (fun x : Int => 0 ≤ x ∧ x ≤ 1) r := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem hx
    have hk' : 0 ≤ (k : Int) ∧ (k : Int) < n := by simp only [Zlength, Int.ofNat_eq_coe] at hlen; omega
    have hv : Znth (k : Int) r 0 = x := by simp [Znth, List.getD, List.getElem?_eq_getElem hk, he]
    by_cases hc : Znth ((k : Int) + 1) cs 0 = -1
    · have hh := huncol ((k : Int) + 1) ⟨by omega, by omega⟩ hc
      rw [show (k : Int) + 1 - 1 = k by omega, hv] at hh
      omega
    · have hh := hcol ((k : Int) + 1) ⟨by omega, by omega⟩ hc
      rw [show (k : Int) + 1 - 1 = k by omega, hv] at hh
      omega
  have hb : ∀ l : List Int, Forall (fun x => 0 ≤ x ∧ x ≤ 1) l →
      l.foldr (· + ·) 0 ≤ (l.length : Int) := by
    intro l hl
    induction hl with
    | nil => simp
    | @cons x tail hx ht ih => simp only [List.foldr_cons, List.length_cons, Nat.cast_add, Nat.cast_one]; omega
  have hh := hb r hv
  simp only [Zlength, Int.ofNat_eq_coe] at hlen
  omega

theorem MaxImpostersOn_upper_bound__outer_loop_component_commit (n : Int) (comments : List Comment)
    (cs : List Int) (t : Int) (hm : MaxImpostersOn n comments cs t) : t ≤ n := by
  rcases hm with ⟨x, ⟨⟨r, hc, hr⟩, hub⟩, ht⟩
  have hb := OnSet_fold_upper_bound__outer_loop_component_commit n cs r hc.1
  change x = t at ht
  omega

theorem Zlength_replace_Znth__forward_star_build_step {A : Type} (l : List A) (i : Int) (v : A) :
    Zlength (replace_Znth i v l) = Zlength l := Zlength_replace_Znth l i v

theorem AdjChain_ext__forward_star_build_step (ns ns' : List Int) (cur : Int) (es : List Int)
    (hc : AdjChain ns cur es) (he : ∀ e, e ∈ es → Znth e ns' 0 = Znth e ns 0) :
    AdjChain ns' cur es := by
  induction hc with
  | adj_end => exact adj_end
  | adj_cons e rest hpos htail ih =>
    apply adj_cons _ _ hpos
    rw [he e (by simp)]
    exact ih (by intro x hx; exact he x (List.mem_cons_of_mem _ hx))

theorem triple_src__forward_star_build_step (q : Comment) :
    (let ((u, _), _) := q; u) = fst (fst q) := by rcases q with ⟨⟨u, v⟩, w⟩; rfl

theorem triple_dst__forward_star_build_step (q : Comment) :
    (let ((_, v), _) := q; v) = snd (fst q) := by rcases q with ⟨⟨u, v⟩, w⟩; rfl

theorem triple_wt__forward_star_build_step (q : Comment) :
    (let ((_, _), w) := q; w) = snd q := by rcases q with ⟨⟨u, v⟩, w⟩; rfl

theorem fold_right_add_zero_of_Znth_zero__outer_loop_entry (r : List Int)
    (hz : ∀ i, (0 ≤ i ∧ i < Zlength r) → Znth i r 0 = 0) : r.foldr (· + ·) 0 = 0 := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    have ha : a = 0 := hz 0 ⟨le_rfl, by simp only [Zlength_cons]; have := Zlength_nonneg r; omega⟩
    have ht : r.foldr (· + ·) 0 = 0 := by
      apply ih
      intro i hi
      have hh := hz (i + 1) ⟨by omega, by simp only [Zlength_cons]; omega⟩
      rwa [Znth_cons 0 (i + 1) a r (by omega), show i + 1 - 1 = i by omega] at hh
    simp [ha, ht]

theorem Zlength_zeros__outer_loop_entry (n : Int) (hn : 0 ≤ n) : Zlength (zeros n) = n := by
  simp [zeros, Zlength, «repeat», Int.ofNat_eq_coe, Int.toNat_of_nonneg hn]

theorem Znth_zeros__outer_loop_entry (n i : Int) : Znth i (zeros n) 0 = 0 := by
  exact Znth_repeat 0 n.toNat i

theorem fold_right_add_zeros__outer_loop_entry (n : Int) : (zeros n).foldr (· + ·) 0 = 0 := by
  apply fold_right_add_zero_of_Znth_zero__outer_loop_entry
  intro i hi
  exact Znth_zeros__outer_loop_entry n i

theorem max_imposters_on_empty__outer_loop_entry (n : Int) (comments : List Comment) (cs : List Int)
    (hn : 0 ≤ n) (hlen : Zlength cs = n + 1)
    (hall : ∀ v, (1 ≤ v ∧ v ≤ n) → Znth v cs 0 = -1)
    (hbounds : ∀ i, (0 ≤ i ∧ i < Zlength comments) →
      let ((u, v), _) := comment_at comments i; (1 ≤ u ∧ u ≤ n) ∧ (1 ≤ v ∧ v ≤ n)) :
    MaxImpostersOn n comments cs 0 := by
  refine ⟨0, ⟨⟨zeros n, ?_, (fold_right_add_zeros__outer_loop_entry n).symm⟩, ?_⟩, rfl⟩
  · constructor
    · exact ⟨Zlength_zeros__outer_loop_entry n hn,
        by intro v hv hc; exact Or.inl (Znth_zeros__outer_loop_entry n _),
        by intro v hv hc; exact Znth_zeros__outer_loop_entry n _⟩
    · intro i hi
      have hb := hbounds i hi
      rcases he : comment_at comments i with ⟨⟨u, v⟩, w⟩
      rw [he] at hb
      dsimp at hb ⊢
      intro hu hv
      exact False.elim (hu (hall u hb.1))
  · intro b hb
    rcases hb with ⟨r, ⟨⟨hrlen, hbits, hrzero⟩, hedge⟩, he⟩
    have hr : r.foldr (· + ·) 0 = 0 := by
      apply fold_right_add_zero_of_Znth_zero__outer_loop_entry
      intro i hi
      have hv := hrzero (i + 1) ⟨by omega, by omega⟩ (hall _ ⟨by omega, by omega⟩)
      rwa [show i + 1 - 1 = i by omega] at hv
    change b ≤ 0
    omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
