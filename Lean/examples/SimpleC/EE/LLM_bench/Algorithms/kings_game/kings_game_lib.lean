import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_lib
open AUXLib


open MaxMinLib

def minister : Type := Int × Int
def mk_minister (left right : Int) : minister := (left, right)
def minister_left (p : minister) : Int := p.1
def minister_right (p : minister) : Int := p.2
def minister_product (p : minister) : Int := minister_left p * minister_right p
def default_minister : minister := mk_minister 1 1

def minister_flatten (ps : List minister) : List Int :=
  ps.flatMap (fun p => [minister_left p, minister_right p])
def FlatMinisters (flat : List Int) (ps : List minister) : Prop := flat = minister_flatten ps

def MinisterHandsBound (ps : List minister) : Prop :=
  Forall (fun p => (1 ≤ minister_left p ∧ minister_left p ≤ 10) ∧ (1 ≤ minister_right p ∧ minister_right p ≤ 10)) ps

def MinisterPermutation : List minister → List minister → Prop := List.Perm
def MinisterProductLe (p q : minister) : Prop := minister_product p ≤ minister_product q

def MinisterSorted (ps : List minister) : Prop :=
  ∀ i j, 0 ≤ i → i ≤ j → j < Zlength ps → MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister)

def PrefixLeftProduct (ps : List minister) (i : Int) : Int :=
  ((sublist 0 i ps).map minister_left).foldr (· * ·) 1

def MinisterReward (king_left : Int) (ps : List minister) (i : Int) : Int :=
  Z.div (king_left * PrefixLeftProduct ps i) (minister_right (Znth i ps default_minister))

def OrderMaxReward (king_left : Int) (ps : List minister) (reward : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun i : Int => 0 ≤ i ∧ i < Zlength ps) (fun i => MinisterReward king_left ps i) reward

def ValidOrderReward (input : List minister) (king_left : Int) (candidate : List minister × Int) : Prop :=
  MinisterPermutation input candidate.1 ∧ OrderMaxReward king_left candidate.1 candidate.2

def KingsGameOptimum (input : List minister) (king_left optimum : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (ValidOrderReward input king_left) Prod.snd optimum

def KingsGameResult (input : List minister) (king_left : Int) (output : List minister) : Prop :=
  MinisterPermutation input output ∧ MinisterSorted output ∧
    ∃ reward, OrderMaxReward king_left output reward ∧ KingsGameOptimum input king_left reward

def minister_swap (ps : List minister) (i j : Int) : List minister :=
  replace_Znth j (Znth i ps default_minister) (replace_Znth i (Znth j ps default_minister) ps)

def minister_swap_flat (flat : List Int) (i j : Int) : List Int :=
  let il := Znth (2 * i) flat 0
  let ir := Znth (2 * i + 1) flat 0
  let jl := Znth (2 * j) flat 0
  let jr := Znth (2 * j + 1) flat 0
  replace_Znth (2 * j + 1) ir (replace_Znth (2 * j) il (replace_Znth (2 * i + 1) jr (replace_Znth (2 * i) jl flat)))

def BubbleOuterProperty (ps : List minister) (n pass : Int) : Prop :=
  Zlength ps = n ∧
  (∀ i j, n - pass ≤ i → i ≤ j → j < n → MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister)) ∧
  (∀ i j, 0 ≤ i → i < n - pass → n - pass ≤ j → j < n → MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister))

def BubbleScanProperty (ps : List minister) (n pass j : Int) : Prop :=
  (0 ≤ j ∧ j < n - pass) ∧ ∀ k, 0 ≤ k → k ≤ j → MinisterProductLe (Znth k ps default_minister) (Znth j ps default_minister)

private theorem forall_nth {A : Type} {P : A → Prop} (l : List A) (d : A) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  induction hp generalizing i with
  | nil => simp [Zlength] at hi; omega
  | @cons a l ha ht ih =>
    rw [Zlength_cons] at hi
    by_cases he : i = 0
    · subst i; simpa only [Znth0_cons] using ha
    · rw [Znth_cons d i a l (by omega)]
      exact ih (i-1) ⟨by omega, by omega⟩

private theorem nth_mem {A : Type} (l : List A) (d : A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l :=
  forall_nth l d i (Forall.iff_forall_mem.mpr (by intro x hx; exact hx)) hi

private theorem mem_nth {A : Type} (l : List A) (d : A) (x : A) (hx : x ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l d = x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, ⟨by omega, by rw [Zlength_cons]; have := Zlength_nonneg l; omega⟩, rfl⟩
    · rcases ih hx with ⟨i, hi, he⟩
      refine ⟨i+1, ⟨by omega, by rw [Zlength_cons]; omega⟩, ?_⟩
      rw [Znth_cons d (i+1) a l (by omega)]
      simpa only [show i+1-1 = i by omega] using he

theorem minister_flatten_Zlength__flat_bubble (ps : List minister) :
    Zlength (minister_flatten ps) = 2*Zlength ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Zlength (minister_left p :: minister_right p :: minister_flatten ps) = _
    rw [Zlength_cons, Zlength_cons, Zlength_cons, ih]; omega

theorem minister_flatten_Znth_pair__flat_bubble (ps : List minister) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) :
    Znth (2*i) (minister_flatten ps) 0 = minister_left (Znth i ps default_minister) ∧
    Znth (2*i+1) (minister_flatten ps) 0 = minister_right (Znth i ps default_minister) := by
  induction ps generalizing i with
  | nil => simp [Zlength] at hi; omega
  | cons p ps ih =>
    rw [Zlength_cons] at hi
    by_cases he : i = 0
    · subst i; exact ⟨rfl, rfl⟩
    · change Znth (2*i) (minister_left p :: minister_right p :: minister_flatten ps) 0 = _ ∧
        Znth (2*i+1) (minister_left p :: minister_right p :: minister_flatten ps) 0 = _
      rw [Znth_cons 0 (2*i) _ _ (by omega), Znth_cons 0 (2*i-1) _ _ (by omega),
        Znth_cons 0 (2*i+1) _ _ (by omega), Znth_cons 0 (2*i+1-1) _ _ (by omega),
        Znth_cons default_minister i p ps (by omega)]
      rw [show 2*i-1-1 = 2*(i-1) by omega, show 2*i+1-1-1 = 2*(i-1)+1 by omega]
      exact ih (i-1) ⟨by omega, by omega⟩

theorem minister_hands_bound_Znth__flat_bubble (ps : List minister) (i : Int)
    (hb : MinisterHandsBound ps) (hi : 0 ≤ i ∧ i < Zlength ps) :
    (1 ≤ minister_left (Znth i ps default_minister) ∧ minister_left (Znth i ps default_minister) ≤ 10) ∧
    (1 ≤ minister_right (Znth i ps default_minister) ∧ minister_right (Znth i ps default_minister) ≤ 10) :=
  forall_nth ps default_minister i hb hi

theorem flat_ministers_Zlength__flat_bubble (flat : List Int) (ps : List minister)
    (hf : FlatMinisters flat ps) : Zlength flat = 2*Zlength ps := by
  rw [hf]; exact minister_flatten_Zlength__flat_bubble ps

theorem flat_minister_product_bounds__flat_bubble (flat : List Int) (ps : List minister) (i : Int)
    (hf : FlatMinisters flat ps) (hb : MinisterHandsBound ps) (hi : 0 ≤ i ∧ i < Zlength ps) :
    1 ≤ Znth (2*i) flat 0 * Znth (2*i+1) flat 0 ∧ Znth (2*i) flat 0 * Znth (2*i+1) flat 0 ≤ 100 := by
  rw [hf]
  rcases minister_flatten_Znth_pair__flat_bubble ps i hi with ⟨hl, hr⟩
  rw [hl, hr]
  rcases minister_hands_bound_Znth__flat_bubble ps i hb hi with ⟨hl, hr⟩
  constructor <;> nlinarith

theorem flat_minister_product_eq__flat_bubble (flat : List Int) (ps : List minister) (i : Int)
    (hf : FlatMinisters flat ps) (hi : 0 ≤ i ∧ i < Zlength ps) :
    Znth (2*i) flat 0 * Znth (2*i+1) flat 0 = minister_product (Znth i ps default_minister) := by
  rw [hf]
  rcases minister_flatten_Znth_pair__flat_bubble ps i hi with ⟨hl, hr⟩
  rw [hl, hr]; rfl

theorem minister_flatten_replace_nth__flat_bubble (ps : List minister) (p : minister) (n : Nat)
    (hn : n < ps.length) :
    (replace_nth n ps p).flatMap (fun q => [minister_left q, minister_right q]) =
      replace_nth (2*n+1) (replace_nth (2*n) (ps.flatMap (fun q => [minister_left q, minister_right q])) (minister_left p)) (minister_right p) := by
  induction ps generalizing n with
  | nil => simp at hn
  | cons q ps ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega, show 2*(n+1) = (2*n)+1+1 by omega]
      simpa only [replace_nth, List.flatMap_cons, List.cons_append, List.nil_append] using
        congrArg (fun l => minister_left q :: minister_right q :: l) (ih n (by simpa using hn))

theorem minister_flatten_replace_Znth__flat_bubble (ps : List minister) (p : minister) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) :
    minister_flatten (replace_Znth i p ps) = replace_Znth (2*i+1) (minister_right p)
      (replace_Znth (2*i) (minister_left p) (minister_flatten ps)) := by
  unfold minister_flatten replace_Znth
  rw [show (2*i).toNat = 2*i.toNat by omega, show (2*i+1).toNat = 2*i.toNat+1 by omega]
  exact minister_flatten_replace_nth__flat_bubble ps p i.toNat (by change 0 ≤ i ∧ i < (ps.length : Int) at hi; omega)

private theorem replace_at_prefix {A : Type} (pre : List A) (x y : A) (rest : List A) :
    replace_Znth (Zlength pre) y (pre++x::rest) = pre++y::rest := by
  rw [replace_Znth_app_r _ _ pre _ (by omega), replace_Znth_nothing _ pre _ (by omega), Int.sub_self]
  rfl

theorem replace_Znth_swap_form_minister__flat_bubble (l1 l2 l3 : List minister) (xi xj : minister) :
    replace_Znth (Zlength l1+1+Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1++xi::l2++xj::l3)) = l1++xj::l2++xi::l3 := by
  simp only [List.append_assoc, List.cons_append]
  rw [replace_at_prefix l1 xi xj (l2++xj::l3)]
  have hl := Zlength_nonneg l2
  rw [replace_Znth_app_r _ _ l1 _ (by omega), replace_Znth_nothing _ l1 _ (by omega)]
  rw [show Zlength l1+1+Zlength l2-Zlength l1 = Zlength l2+1 by omega,
    replace_Znth_cons _ _ xj _ (by omega), show Zlength l2+1-1 = Zlength l2 by omega,
    replace_at_prefix l2 xj xi l3]

private theorem cons_replace_perm (ps : List minister) (x d : minister) (n : Nat) (hn : n < ps.length) :
    (x::ps).Perm (ps.getD n d :: replace_nth n ps x) := by
  induction ps generalizing n with
  | nil => simp at hn
  | cons y ys ih =>
    cases n with
    | zero => exact List.Perm.swap y x ys
    | succ n =>
      change (x::y::ys).Perm (ys.getD n d :: y :: replace_nth n ys x)
      exact (List.Perm.swap y x ys).trans
        ((List.Perm.cons y (ih n (by simpa using hn))).trans (List.Perm.swap _ _ _))

private theorem swap_nth_perm (ps : List minister) (d : minister) (i j : Nat)
    (hi : i < ps.length) (hj : j < ps.length) :
    ps.Perm (replace_nth j (replace_nth i ps (ps.getD j d)) (ps.getD i d)) := by
  induction ps generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact List.Perm.refl _
      | succ j =>
        exact cons_replace_perm xs x d j (by simpa using hj)
    | succ i =>
      cases j with
      | zero =>
        exact cons_replace_perm xs x d i (by simpa using hi)
      | succ j =>
        exact List.Perm.cons x (ih i j (by simpa using hi) (by simpa using hj))

theorem minister_swap_permutation_lt__flat_bubble (ps : List minister) (i j : Int)
    (hi : 0 ≤ i ∧ i < j) (hj : j < Zlength ps) : MinisterPermutation ps (minister_swap ps i j) := by
  exact swap_nth_perm ps default_minister i.toNat j.toNat
    (by change j < (ps.length : Int) at hj; omega) (by change j < (ps.length : Int) at hj; omega)

theorem replace_nth_comm_minister__flat_bubble (ni nj : Nat) (ps : List minister) (a b : minister)
    (hn : ni ≠ nj) : replace_nth nj (replace_nth ni ps a) b = replace_nth ni (replace_nth nj ps b) a := by
  induction ps generalizing ni nj with
  | nil => simp [replace_nth]
  | cons x xs ih =>
    cases ni <;> cases nj <;> simp only [replace_nth]
    · contradiction
    · exact congrArg (List.cons x) (ih _ _ (by omega))

theorem replace_Znth_comm_minister__flat_bubble (ps : List minister) (i j : Int) (a b : minister)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a ps) = replace_Znth i a (replace_Znth j b ps) :=
  replace_nth_comm_minister__flat_bubble i.toNat j.toNat ps a b (by omega)

theorem minister_swap_permutation__flat_bubble (ps : List minister) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    MinisterPermutation ps (minister_swap ps i j) :=
  swap_nth_perm ps default_minister i.toNat j.toNat
    (by change 0 ≤ i ∧ i < (ps.length : Int) at hi; omega) (by change 0 ≤ j ∧ j < (ps.length : Int) at hj; omega)

theorem minister_swap_Zlength__flat_bubble (ps : List minister) (i j : Int) :
    Zlength (minister_swap ps i j) = Zlength ps := by
  simp only [minister_swap, Zlength_replace_Znth]

theorem minister_swap_hands_bound__flat_bubble (ps : List minister) (i j : Int)
    (hb : MinisterHandsBound ps) (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    MinisterHandsBound (minister_swap ps i j) := hb.perm (minister_swap_permutation__flat_bubble ps i j hi hj)

theorem minister_flatten_swap__flat_bubble (ps : List minister) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    minister_flatten (minister_swap ps i j) =
      replace_Znth (2*j+1) (minister_right (Znth i ps default_minister))
      (replace_Znth (2*j) (minister_left (Znth i ps default_minister))
      (replace_Znth (2*i+1) (minister_right (Znth j ps default_minister))
      (replace_Znth (2*i) (minister_left (Znth j ps default_minister)) (minister_flatten ps)))) := by
  unfold minister_swap
  rw [minister_flatten_replace_Znth__flat_bubble _ _ j (by rw [Zlength_replace_Znth]; exact hj),
    minister_flatten_replace_Znth__flat_bubble _ _ i hi]

theorem flat_ministers_swap__flat_bubble (flat : List Int) (ps : List minister) (i j : Int)
    (hf : FlatMinisters flat ps) (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    FlatMinisters (minister_swap_flat flat i j) (minister_swap ps i j) := by
  unfold FlatMinisters
  rw [hf, minister_flatten_swap__flat_bubble ps i j hi hj]
  rcases minister_flatten_Znth_pair__flat_bubble ps i hi with ⟨hil, hir⟩
  rcases minister_flatten_Znth_pair__flat_bubble ps j hj with ⟨hjl, hjr⟩
  simp only [minister_swap_flat, hil, hir, hjl, hjr]

theorem minister_swap_flat_preprocess_form__flat_bubble (flat : List Int) (n i j : Int)
    (hl : Zlength flat = 2*n) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n) :
    replace_Znth (2*j+1) (Znth (2*i+1) flat 0)
      (replace_Znth (2*j) (Znth (2*i) flat 0)
      (replace_Znth (2*i+1) (Znth (2*j+1) (replace_Znth (2*i) (Znth (2*j) flat 0) flat) 0)
      (replace_Znth (2*i) (Znth (2*j) flat 0) flat))) = minister_swap_flat flat i j := by
  rw [Znth_replace_Znth_Diff 0 flat (2*i) (2*j+1) _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)]
  rfl

theorem minister_swap_Znth_left__flat_bubble (ps : List minister) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    Znth i (minister_swap ps i j) default_minister = Znth j ps default_minister := by
  unfold minister_swap
  by_cases he : i = j
  · subst j; rw [replace_Znth_Znth, replace_Znth_Znth]
  · rw [Znth_replace_Znth_Diff default_minister _ j i _
      (by rw [Zlength_replace_Znth]; exact hj) (by rw [Zlength_replace_Znth]; exact hi) (by omega),
      Znth_replace_Znth_Same default_minister ps i _ hi]

theorem minister_swap_Znth_right__flat_bubble (ps : List minister) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    Znth j (minister_swap ps i j) default_minister = Znth i ps default_minister := by
  unfold minister_swap
  rw [Znth_replace_Znth_Same default_minister _ j _ (by rw [Zlength_replace_Znth]; exact hj)]

theorem minister_swap_Znth_other__flat_bubble (ps : List minister) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) (hk : 0 ≤ k ∧ k < Zlength ps)
    (hki : k ≠ i) (hkj : k ≠ j) :
    Znth k (minister_swap ps i j) default_minister = Znth k ps default_minister := by
  unfold minister_swap
  rw [Znth_replace_Znth_Diff default_minister _ j k _
      (by rw [Zlength_replace_Znth]; exact hj) (by rw [Zlength_replace_Znth]; exact hk) (by omega),
      Znth_replace_Znth_Diff default_minister ps i k _ hi hk (by omega)]

theorem bubble_outer_initial__flat_bubble (ps : List minister) (n : Int) (hl : Zlength ps = n) :
    BubbleOuterProperty ps n 0 := by
  refine ⟨hl, ?_, ?_⟩ <;> intro i j <;> unfold MinisterProductLe <;> intros <;> omega

theorem bubble_scan_initial__flat_bubble (ps : List minister) (n pass : Int) (h : 0 < n-pass) :
    BubbleScanProperty ps n pass 0 := by
  refine ⟨⟨by omega, h⟩, ?_⟩
  intro k hk hk0
  rw [show k = 0 by omega]; exact le_refl _

theorem bubble_scan_step_no_swap__flat_bubble (ps : List minister) (n pass j : Int)
    (hl : Zlength ps = n) (hn : j+1 < n-pass) (hs : BubbleScanProperty ps n pass j)
    (hkey : MinisterProductLe (Znth j ps default_minister) (Znth (j+1) ps default_minister)) :
    BubbleScanProperty ps n pass (j+1) := by
  refine ⟨⟨by have := hs.1; omega, hn⟩, ?_⟩
  intro k hk hkj
  by_cases he : k = j+1
  · rw [he]; exact le_refl _
  · exact le_trans (hs.2 k hk (by omega)) hkey

theorem bubble_outer_swap_prefix__flat_bubble (ps : List minister) (n pass j : Int)
    (hl : Zlength ps = n) (hp : 0 ≤ pass) (hj : 0 ≤ j) (hn : j+1 < n-pass)
    (hs : BubbleOuterProperty ps n pass) : BubbleOuterProperty (minister_swap ps j (j+1)) n pass := by
  have hj0 : 0 ≤ j ∧ j < Zlength ps := ⟨hj, by omega⟩
  have hj1 : 0 ≤ j+1 ∧ j+1 < Zlength ps := ⟨by omega, by omega⟩
  refine ⟨by rw [minister_swap_Zlength__flat_bubble]; exact hl, ?_, ?_⟩
  · intro x y hx hxy hy
    rw [minister_swap_Znth_other__flat_bubble ps j (j+1) x hj0 hj1 ⟨by omega, by omega⟩ (by omega) (by omega),
      minister_swap_Znth_other__flat_bubble ps j (j+1) y hj0 hj1 ⟨by omega, by omega⟩ (by omega) (by omega)]
    exact hs.2.1 x y hx hxy hy
  · intro x y hx0 hx hy0 hy
    rw [minister_swap_Znth_other__flat_bubble ps j (j+1) y hj0 hj1 ⟨by omega, by omega⟩ (by omega) (by omega)]
    by_cases he : x = j
    · subst x; rw [minister_swap_Znth_left__flat_bubble ps j (j+1) hj0 hj1]
      exact hs.2.2 (j+1) y (by omega) hn hy0 hy
    · by_cases he1 : x = j+1
      · subst x; rw [minister_swap_Znth_right__flat_bubble ps j (j+1) hj0 hj1]
        exact hs.2.2 j y hj (by omega) hy0 hy
      · rw [minister_swap_Znth_other__flat_bubble ps j (j+1) x hj0 hj1 ⟨hx0, by omega⟩ he he1]
        exact hs.2.2 x y hx0 hx hy0 hy

theorem bubble_scan_step_swap__flat_bubble (ps : List minister) (n pass j : Int)
    (hl : Zlength ps = n) (hp : 0 ≤ pass) (hj : 0 ≤ j) (hn : j+1 < n-pass)
    (hs : BubbleScanProperty ps n pass j)
    (hkey : MinisterProductLe (Znth (j+1) ps default_minister) (Znth j ps default_minister)) :
    BubbleScanProperty (minister_swap ps j (j+1)) n pass (j+1) := by
  have hj0 : 0 ≤ j ∧ j < Zlength ps := ⟨hj, by omega⟩
  have hj1 : 0 ≤ j+1 ∧ j+1 < Zlength ps := ⟨by omega, by omega⟩
  refine ⟨⟨by omega, hn⟩, ?_⟩
  intro k hk hkj
  rw [minister_swap_Znth_right__flat_bubble ps j (j+1) hj0 hj1]
  by_cases he : k = j
  · subst k; rw [minister_swap_Znth_left__flat_bubble ps j (j+1) hj0 hj1]; exact hkey
  · by_cases he1 : k = j+1
    · subst k; rw [minister_swap_Znth_right__flat_bubble ps j (j+1) hj0 hj1]; exact le_refl _
    · rw [minister_swap_Znth_other__flat_bubble ps j (j+1) k hj0 hj1 ⟨hk, by omega⟩ he he1]
      exact hs.2 k hk (by omega)

theorem bubble_outer_finish_pass__flat_bubble (ps : List minister) (n pass j : Int)
    (hj : j = n-1-pass) (ho : BubbleOuterProperty ps n pass) (hs : BubbleScanProperty ps n pass j) :
    BubbleOuterProperty ps n (pass+1) := by
  have hr := hs.1
  refine ⟨ho.1, ?_, ?_⟩
  · intro x y hx hxy hy
    by_cases he : x = n-(pass+1)
    · by_cases he1 : y = n-(pass+1)
      · rw [he, he1]; exact le_refl _
      · exact ho.2.2 x y (by omega) (by omega) (by omega) hy
    · exact ho.2.1 x y (by omega) hxy hy
  · intro x y hx0 hx hy0 hy
    by_cases he : y = j
    · rw [he]; exact hs.2 x hx0 (by omega)
    · exact ho.2.2 x y hx0 (by omega) (by omega) hy

theorem bubble_outer_final_sorted__greedy_optimum (ps : List minister) (n pass : Int)
    (hge : pass ≥ n-1) (hle : pass ≤ n-1) (ho : BubbleOuterProperty ps n pass) : MinisterSorted ps := by
  intro i j hi hij hj
  by_cases he : i = 0
  · by_cases he1 : j = 0
    · rw [he, he1]; exact le_refl _
    · exact ho.2.2 i j hi (by omega) (by omega) (by rw [← ho.1]; exact hj)
  · exact ho.2.1 i j (by omega) hij (by rw [← ho.1]; exact hj)

theorem minister_sorted_cons__greedy_optimum (x : minister) (xs : List minister)
    (hs : MinisterSorted (x::xs)) : Forall (MinisterProductLe x) xs ∧ MinisterSorted xs := by
  constructor
  · apply Forall.iff_forall_mem.mpr
    intro y hy
    rcases mem_nth xs default_minister y hy with ⟨i, hi, he⟩
    have hh := hs 0 (i+1) (by omega) (by omega) (by rw [Zlength_cons]; omega)
    rw [Znth0_cons, Znth_cons default_minister (i+1) x xs (by omega), show i+1-1 = i by omega, he] at hh
    exact hh
  · intro i j hi hij hj
    have hh := hs (i+1) (j+1) (by omega) (by omega) (by rw [Zlength_cons]; omega)
    rw [Znth_cons default_minister (i+1) x xs (by omega),
      Znth_cons default_minister (j+1) x xs (by omega), show i+1-1 = i by omega, show j+1-1 = j by omega] at hh
    exact hh

theorem minister_reward_cons_zero__greedy_optimum (king : Int) (x : minister) (xs : List minister) :
    MinisterReward king (x::xs) 0 = Z.div king (minister_right x) := by
  simp [MinisterReward, PrefixLeftProduct, Znth0_cons, sublist]

theorem minister_reward_cons_succ__greedy_optimum (king : Int) (x : minister) (xs : List minister)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength xs) :
    MinisterReward king (x::xs) (i+1) = MinisterReward (king*minister_left x) xs i := by
  unfold MinisterReward PrefixLeftProduct
  rw [sublist_cons1 (i+1) x xs (by omega), Znth_cons default_minister (i+1) x xs (by omega),
    show i+1-1 = i by omega]
  simp only [List.map_cons, List.foldr_cons, mul_assoc]

theorem minister_reward_two_cons_tail__greedy_optimum (king : Int) (x y : minister) (xs : List minister)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength xs) :
    MinisterReward king (x::y::xs) (i+2) = MinisterReward (king*minister_left x*minister_left y) xs i := by
  rw [show i+2 = (i+1)+1 by omega,
    minister_reward_cons_succ__greedy_optimum king x (y::xs) (i+1) ⟨by omega, by rw [Zlength_cons]; omega⟩,
    minister_reward_cons_succ__greedy_optimum _ y xs i hi]

private theorem reward_one (king : Int) (x y : minister) (xs : List minister) :
    MinisterReward king (x::y::xs) 1 = Z.div (king*minister_left x) (minister_right y) := by
  have hn := Zlength_nonneg xs
  rw [show (1 : Int) = 0+1 by omega,
    minister_reward_cons_succ__greedy_optimum king x (y::xs) 0 ⟨by omega, by rw [Zlength_cons]; omega⟩,
    minister_reward_cons_zero__greedy_optimum]

private theorem div_mono (a b c : Int) (hc : 0 < c) (h : a ≤ b) : Z.div a c ≤ Z.div b c := by
  unfold Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg a (by omega), Int.fdiv_eq_ediv_of_nonneg b (by omega)]
  exact Int.ediv_le_ediv hc h

theorem positive_cross_div_le__greedy_optimum (king lx rx ly ry : Int)
    (hk : 0 ≤ king) (hrx : 0 < rx) (hry : 0 < ry) (hkey : lx*rx ≤ ly*ry) :
    Z.div (king*lx) ry ≤ Z.div (king*ly) rx := by
  unfold Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega : 0 ≤ ry), Int.fdiv_eq_ediv_of_nonneg _ (by omega : 0 ≤ rx)]
  calc
    king*lx / ry = (king*lx*rx)/(ry*rx) := (Int.mul_ediv_mul_of_pos_left (king*lx) ry hrx).symm
    _ ≤ (king*ly*ry)/(ry*rx) := by
      apply Int.ediv_le_ediv (mul_pos hry hrx)
      have hh := mul_le_mul_of_nonneg_left hkey hk
      nlinarith
    _ = king*ly/rx := by
      rw [mul_comm ry rx]
      exact Int.mul_ediv_mul_of_pos_left (king*ly) rx hry

theorem positive_adjacent_exchange_bound__greedy_optimum (king : Int) (x y : minister) (xs : List minister) (cap : Int)
    (hk : 0 ≤ king) (hxl : 1 ≤ minister_left x) (hxr : 1 ≤ minister_right x)
    (hyl : 1 ≤ minister_left y) (hyr : 1 ≤ minister_right y) (hkey : MinisterProductLe x y)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength (y::x::xs)) → MinisterReward king (y::x::xs) i ≤ cap) :
    ∀ i, (0 ≤ i ∧ i < Zlength (x::y::xs)) → MinisterReward king (x::y::xs) i ≤ cap := by
  intro i hi
  have hl := Zlength_nonneg xs
  have hb1 := hb 1 ⟨by omega, by rw [Zlength_cons, Zlength_cons]; omega⟩
  rw [reward_one] at hb1
  by_cases he : i = 0
  · subst i
    rw [minister_reward_cons_zero__greedy_optimum]
    exact le_trans (div_mono _ _ _ (by omega) (by nlinarith)) hb1
  · by_cases he1 : i = 1
    · subst i
      rw [reward_one]
      exact le_trans (positive_cross_div_le__greedy_optimum _ _ _ _ _ hk (by omega) (by omega) hkey) hb1
    · have hit : 0 ≤ i-2 ∧ i-2 < Zlength xs := by rw [Zlength_cons, Zlength_cons] at hi; omega
      have hbi := hb i (by simpa only [Zlength_cons] using hi)
      rw [show i = (i-2)+2 by omega,
        minister_reward_two_cons_tail__greedy_optimum _ _ _ _ _ hit] at hbi ⊢
      have heq : king*minister_left x*minister_left y = king*minister_left y*minister_left x := by ring
      rw [heq]; exact hbi

theorem positive_move_minimum_to_front_bound__greedy_optimum (pre : List minister) (x : minister)
    (post : List minister) (king cap : Int) (hk : 0 ≤ king)
    (hh : MinisterHandsBound (x::(pre++post))) (hm : Forall (MinisterProductLe x) pre)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength (pre++x::post)) → MinisterReward king (pre++x::post) i ≤ cap) :
    ∀ i, (0 ≤ i ∧ i < Zlength (x::(pre++post))) → MinisterReward king (x::(pre++post)) i ≤ cap := by
  induction pre generalizing king with
  | nil => exact hb
  | cons y pre ih =>
    cases hh with
    | cons hx hyrest =>
      cases hyrest with
      | cons hy hrest =>
        cases hm with
        | cons hxy hmin =>
          have htail : ∀ q, (0 ≤ q ∧ q < Zlength (pre++x::post)) →
              MinisterReward (king*minister_left y) (pre++x::post) q ≤ cap := by
            intro q hq
            have hh := hb (q+1) ⟨by omega, by change q+1 < Zlength (y::(pre++x::post)); rw [Zlength_cons]; omega⟩
            simp only [List.cons_append] at hh
            rw [minister_reward_cons_succ__greedy_optimum king y (pre++x::post) q hq] at hh
            exact hh
          have hmoved := ih (king*minister_left y) (mul_nonneg hk (by have := hy.1.1; omega)) (.cons hx hrest) hmin htail
          have hbefore : ∀ q, (0 ≤ q ∧ q < Zlength (y::x::(pre++post))) →
              MinisterReward king (y::x::(pre++post)) q ≤ cap := by
            intro q hq
            by_cases he : q = 0
            · subst q
              have hh := hb 0 ⟨by omega, by change 0 < Zlength (y::(pre++x::post)); rw [Zlength_cons]; have := Zlength_nonneg (pre++x::post); omega⟩
              simp only [List.cons_append] at hh
              rw [minister_reward_cons_zero__greedy_optimum] at hh ⊢
              exact hh
            · have hqt : 0 ≤ q-1 ∧ q-1 < Zlength (x::(pre++post)) := by rw [Zlength_cons] at hq; omega
              rw [show q = (q-1)+1 by omega, minister_reward_cons_succ__greedy_optimum _ _ _ _ hqt]
              exact hmoved (q-1) hqt
          exact positive_adjacent_exchange_bound__greedy_optimum king x y (pre++post) cap hk
            hx.1.1 hx.2.1 hy.1.1 hy.2.1 hxy hbefore

theorem positive_sorted_global_bound__greedy_optimum (sorted other : List minister) (king cap : Int)
    (hk : 0 ≤ king) (hh : MinisterHandsBound sorted) (hs : MinisterSorted sorted)
    (hp : List.Perm sorted other)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength other) → MinisterReward king other i ≤ cap) :
    ∀ i, (0 ≤ i ∧ i < Zlength sorted) → MinisterReward king sorted i ≤ cap := by
  induction sorted generalizing other king with
  | nil => intro i hi; simp [Zlength] at hi; omega
  | cons x xs ih =>
    have hx : x ∈ other := hp.mem_iff.mp (by simp)
    rcases List.append_of_mem hx with ⟨pre, post, rfl⟩
    have hpt : xs.Perm (pre++post) := (hp.trans List.perm_middle).cons_inv
    rcases minister_sorted_cons__greedy_optimum x xs hs with ⟨hmin, hsort⟩
    have hminpre : Forall (MinisterProductLe x) pre := by
      have hm := hmin.perm hpt
      apply Forall.iff_forall_mem.mpr
      intro y hy; exact hm.mem (List.mem_append_left post hy)
    have hfront : MinisterHandsBound (x::(pre++post)) := hh.perm (List.Perm.cons x hpt)
    have hmoved := positive_move_minimum_to_front_bound__greedy_optimum pre x post king cap hk hfront hminpre hb
    cases hh with
    | cons hx hh =>
      have htail : ∀ q, (0 ≤ q ∧ q < Zlength (pre++post)) →
          MinisterReward (king*minister_left x) (pre++post) q ≤ cap := by
        intro q hq
        have hh := hmoved (q+1) ⟨by omega, by rw [Zlength_cons]; omega⟩
        rw [minister_reward_cons_succ__greedy_optimum _ _ _ _ hq] at hh
        exact hh
      have hsortedtail := ih (pre++post) (king*minister_left x) (mul_nonneg hk (by have := hx.1.1; omega)) hh hsort hpt htail
      intro i hi
      by_cases he : i = 0
      · subst i
        have hh := hmoved 0 ⟨by omega, by rw [Zlength_cons]; have := Zlength_nonneg (pre++post); omega⟩
        rw [minister_reward_cons_zero__greedy_optimum] at hh ⊢
        exact hh
      · have hit : 0 ≤ i-1 ∧ i-1 < Zlength xs := by rw [Zlength_cons] at hi; omega
        rw [show i = (i-1)+1 by omega, minister_reward_cons_succ__greedy_optimum _ _ _ _ hit]
        exact hsortedtail (i-1) hit

theorem finite_nonempty_index_max__greedy_optimum (n : Int) (f : Int → Int) (hn : 1 ≤ n) :
    ∃ m, max_value_of_subset (· ≤ ·) (fun i : Int => 0 ≤ i ∧ i < n) f m := by
  have hfinite : ∀ k : Nat, ∃ m, max_value_of_subset (· ≤ ·)
      (fun i : Int => 0 ≤ i ∧ i < (k+1 : Nat)) f m := by
    intro k
    induction k with
    | zero =>
      refine ⟨f 0, 0, ⟨⟨by omega, by omega⟩, ?_⟩, rfl⟩
      intro b hb
      rw [show b = 0 by omega]
    | succ k ih =>
      rcases ih with ⟨m, a, ⟨ha, hm⟩, he⟩
      by_cases hh : m ≤ f (k+1)
      · refine ⟨f (k+1), (k+1 : Nat), ⟨⟨by omega, by omega⟩, ?_⟩, rfl⟩
        intro b hb
        by_cases hb1 : b = (k+1 : Nat)
        · rw [hb1]
        · have ho := hm b ⟨hb.1, by omega⟩
          dsimp at ho he ⊢
          omega
      · refine ⟨m, a, ⟨⟨ha.1, by omega⟩, ?_⟩, he⟩
        intro b hb
        by_cases hb1 : b = (k+1 : Nat)
        · dsimp at he ⊢; rw [hb1]; simp only [Nat.cast_add, Nat.cast_one]; omega
        · exact hm b ⟨hb.1, by omega⟩
  have he : ((n-1).toNat+1 : Nat) = n := by omega
  simpa only [he] using hfinite (n-1).toNat

theorem positive_sorted_realizes_kings_optimum__greedy_optimum (input output : List minister) (king : Int)
    (hk : 0 ≤ king) (hn : 1 ≤ Zlength output) (hh : MinisterHandsBound output)
    (hs : MinisterSorted output) (hp : MinisterPermutation input output) : KingsGameResult input king output := by
  rcases finite_nonempty_index_max__greedy_optimum (Zlength output) (fun i => MinisterReward king output i) hn with ⟨reward, horder⟩
  refine ⟨hp, hs, reward, horder, (output, reward), ⟨⟨hp, horder⟩, ?_⟩, rfl⟩
  rintro ⟨other, other_reward⟩ ⟨hperm, hother⟩
  have hbound : ∀ i, (0 ≤ i ∧ i < Zlength other) → MinisterReward king other i ≤ other_reward := by
    rcases hother with ⟨j, ⟨hj, hm⟩, he⟩
    intro i hi
    have hh := hm i hi
    dsimp at hh he; omega
  have hsorted := positive_sorted_global_bound__greedy_optimum output other king other_reward hk hh hs (hp.symm.trans hperm) hbound
  rcases horder with ⟨j, ⟨hj, hm⟩, he⟩
  have hh := hsorted j hj
  dsimp at he ⊢; omega

end SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_lib
