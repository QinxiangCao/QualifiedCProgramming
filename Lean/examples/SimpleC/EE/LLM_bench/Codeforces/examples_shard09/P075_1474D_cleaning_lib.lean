import Mathlib.Logic.Relation
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib
open AUXLib


def CleanStep (a b : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength a - 1) ∧ Znth i a 0 > 0 ∧ Znth (i+1) a 0 > 0 ∧
    b = replace_Znth (i+1) (Znth (i+1) a 0 - 1) (replace_Znth i (Znth i a 0 - 1) a)

def Cleanable (a : List Int) : Prop :=
  ∃ (base : List Int) (st : List (List Int)),
    (base = a ∨ ∃ i, (0 ≤ i ∧ i < Zlength a - 1) ∧ base = replace_Znth (i+1) (Znth i a 0) (replace_Znth i (Znth (i+1) a 0) a)) ∧
    st ≠ [] ∧ Znth 0 st [] = base ∧ Forall (fun x => x = 0) (Znth (Zlength st - 1) st []) ∧
    ∀ q, (0 ≤ q ∧ q < Zlength st - 1) → CleanStep (Znth q st []) (Znth (q+1) st [])

def Pre (a : List Int) : Prop := True
def Spec (a : List Int) (out : Int) : Prop := (out = 1 ∧ Cleanable a) ∨ (out = 0 ∧ ¬ Cleanable a)

def PrefixResidualState (values residuals flags : List Int) : Prop :=
  Znth 0 residuals 0 = 0 ∧ Znth 0 flags 0 = 1 ∧
    (∀ k, (1 ≤ k ∧ k < Zlength residuals) → Znth k residuals 0 = Znth (k-1) values 0 - Znth (k-1) residuals 0) ∧
    ∀ k, (0 ≤ k ∧ k < Zlength flags) → (Znth k flags 0 = 0 ∨ Znth k flags 0 = 1) ∧
      (Znth k flags 0 = 1 ↔ ∀ j, (0 ≤ j ∧ j ≤ k) → 0 ≤ Znth j residuals 0)

def SuffixResidualState (values : List Int) (start : Int) (residuals flags : List Int) : Prop :=
  Znth (Zlength residuals-1) residuals 0 = 0 ∧ Znth (Zlength flags-1) flags 0 = 1 ∧
    (∀ q, (0 ≤ q ∧ q < Zlength residuals-1) → Znth q residuals 0 = Znth (start+q-1) values 0 - Znth (q+1) residuals 0) ∧
    ∀ q, (0 ≤ q ∧ q < Zlength flags) → (Znth q flags 0 = 0 ∨ Znth q flags 0 = 1) ∧
      (Znth q flags 0 = 1 ↔ ∀ j, (q ≤ j ∧ j < Zlength residuals) → 0 ≤ Znth j residuals 0)

def DirectResidualSuccess (pre_values okpre_values : List Int) (n : Int) : Prop :=
  Znth n okpre_values 0 = 1 ∧ Znth n pre_values 0 = 0

def SwapResidualSuccess (values pre_values suf_values okpre_values oksuf_values : List Int) (i : Int) : Prop :=
  Znth (i-1) okpre_values 0 = 1 ∧ Znth (i+1) oksuf_values 0 = 1 ∧
    (let x := Znth i values 0 - Znth (i-1) pre_values 0
     let y := Znth (i-1) values 0 - x
     0 ≤ x ∧ 0 ≤ y ∧ y = Znth (i+1) suf_values 0)

def CheckedSwapPrefix (values pre_values suf_values okpre_values oksuf_values : List Int) (upto : Int) : Prop :=
  ¬ DirectResidualSuccess pre_values okpre_values (Zlength values) ∧
    ∀ i, (1 ≤ i ∧ i < upto) → ¬ SwapResidualSuccess values pre_values suf_values okpre_values oksuf_values i

-- These seven source Lemma ... Defined declarations are computational
-- definitions; preserve their transparent recursive bodies and public names.
def residual_ok_from__final_result (prev : Int) : List Int → Prop
  | [] => prev=0
  | x::xs => 0 ≤ x-prev ∧ residual_ok_from__final_result (x-prev) xs

def ResidualOK__final_result (xs : List Int) : Prop := residual_ok_from__final_result 0 xs

-- Both relations are the reflexive transitive closure of the same CleanStep.
def CleanReach__final_result : List Int → List Int → Prop := Relation.ReflTransGen CleanStep

def DirectCleanable__final_result (a : List Int) : Prop :=
  ∃ st : List (List Int), st≠[] ∧ Znth 0 st []=a ∧
    Forall (fun x => x=0) (Znth (Zlength st-1) st []) ∧
    ∀ q, (0 ≤ q ∧ q < Zlength st-1) → CleanStep (Znth q st []) (Znth (q+1) st [])

def residuals_from__final_result (prev : Int) : List Int → List Int
  | [] => [prev]
  | x::xs => prev::residuals_from__final_result (x-prev) xs

def canonical_residuals__final_result (a : List Int) : List Int := residuals_from__final_result 0 a

def swap1__final_result (a : List Int) (i : Int) : List Int :=
  replace_Znth i (Znth (i-1) a 0) (replace_Znth (i-1) (Znth i a 0) a)

private theorem zlength_snoc {A : Type} (l : List A) (x : A) : Zlength (l++[x])=Zlength l+1 := by
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

private theorem znth_snoc {A : Type} (d : A) (l : List A) (x : A) : Znth (Zlength l) (l++[x]) d=x := by
  rw [app_Znth2 d l [x] (Zlength l) (le_refl _),sub_self]
  rfl

private theorem znth_app_left {A : Type} (d : A) (l l' : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i (l++l') d=Znth i l d := by
  have hn : i.toNat < l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

theorem checked_swap_prefix_init (values pre_values suf_values okpre_values oksuf_values : List Int)
    (hn : ¬DirectResidualSuccess pre_values okpre_values (Zlength values)) :
    CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values 1 := ⟨hn,by intros; omega⟩

theorem checked_swap_prefix_step (values pre_values suf_values okpre_values oksuf_values : List Int)
    (upto : Int) (hs : CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values upto)
    (hc : ¬SwapResidualSuccess values pre_values suf_values okpre_values oksuf_values upto) :
    CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (upto+1) := by
  refine ⟨hs.1,?_⟩
  intro i hi
  by_cases he : i=upto
  · subst i; exact hc
  · exact hs.2 i (by omega)

theorem prefix_residual_flag_boolean (values residuals flags : List Int) (k : Int)
    (hs : PrefixResidualState values residuals flags) (hk : 0 ≤ k ∧ k < Zlength flags) :
    Znth k flags 0=0 ∨ Znth k flags 0=1 := (hs.2.2.2 k hk).1

theorem suffix_residual_flag_boolean (values : List Int) (start : Int) (residuals flags : List Int) (k : Int)
    (hs : SuffixResidualState values start residuals flags) (hk : 0 ≤ k ∧ k < Zlength flags) :
    Znth k flags 0=0 ∨ Znth k flags 0=1 := (hs.2.2.2 k hk).1

theorem prefix_residual_state_init__prefix_construction (values : List Int) : PrefixResidualState values [0] [1] := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro k hk
    change 1 ≤ k ∧ k < 1 at hk
    omega
  · intro k hk
    have he : k=0 := by change 0 ≤ k ∧ k < 1 at hk; omega
    subst k
    refine ⟨Or.inr rfl,?_⟩
    constructor
    · intro _ j hj
      have he : j=0 := by omega
      subst j
      exact le_refl _
    · intros; rfl

theorem prefix_residual_init_bound__prefix_construction (k : Int) (hk : 0 ≤ k ∧ k < 1) :
    (-1000000000)*k ≤ Znth k [0] 0 ∧ Znth k [0] 0 ≤ 1000000000*k := by
  have he : k=0 := by omega
  subst k
  decide

theorem replace_Znth_app_last__prefix_construction (l : List Int) (old value : Int) :
    replace_Znth (Zlength l) value (l++[old])=l++[value] := by
  simp only [replace_Znth,Zlength,Int.toNat_ofNat]
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.cons_append,List.length_cons,replace_nth] using congrArg (a::·) ih

theorem prefix_residual_extend_core__prefix_construction (values residuals flags : List Int) (i r f : Int)
    (hi : 1 ≤ i) (hrl : Zlength residuals=i) (hfl : Zlength flags=i)
    (hs : PrefixResidualState values residuals flags) (hr : r=Znth (i-1) values 0-Znth (i-1) residuals 0)
    (hf : f=0 ∨ f=1) (hiff : f=1 ↔ ∀ j, (0 ≤ j ∧ j ≤ i) → 0 ≤ Znth j (residuals++[r]) 0) :
    PrefixResidualState values (residuals++[r]) (flags++[f]) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [znth_app_left 0 residuals [r] 0 (by omega)]; exact hs.1
  · rw [znth_app_left 0 flags [f] 0 (by omega)]; exact hs.2.1
  · intro k hk
    rw [zlength_snoc,hrl] at hk
    by_cases he : k=i
    · subst k
      rw [← hrl,znth_snoc]
      rw [znth_app_left 0 residuals [r] _ (by omega),hrl]
      exact hr
    · rw [znth_app_left 0 residuals [r] k (by omega),znth_app_left 0 residuals [r] (k-1) (by omega)]
      exact hs.2.2.1 k (by omega)
  · intro k hk
    rw [zlength_snoc,hfl] at hk
    by_cases he : k=i
    · subst k
      rw [← hfl,znth_snoc,hfl]
      exact ⟨hf,hiff⟩
    · rw [znth_app_left 0 flags [f] k (by omega)]
      obtain ⟨hb,hflags⟩ := hs.2.2.2 k (by omega)
      refine ⟨hb,?_⟩
      constructor
      · intro h j hj
        rw [znth_app_left 0 residuals [r] j (by omega)]
        exact hflags.mp h j hj
      · intro h
        apply hflags.mpr
        intro j hj
        have hh := h j hj
        rwa [znth_app_left 0 residuals [r] j (by omega)] at hh

theorem prefix_residual_extend_bound__prefix_construction (values residuals : List Int) (i r n : Int)
    (hn : n=Zlength values) (hi : 1 ≤ i ∧ i ≤ n) (hrl : Zlength residuals=i)
    (hv : ∀ k, (0 ≤ k ∧ k < n) → 1 ≤ Znth k values 0 ∧ Znth k values 0 ≤ 1000000000)
    (hb : ∀ k, (0 ≤ k ∧ k < i) → (-1000000000)*k ≤ Znth k residuals 0 ∧ Znth k residuals 0 ≤ 1000000000*k)
    (hr : r=Znth (i-1) values 0-Znth (i-1) residuals 0) (k : Int) (hk : 0 ≤ k ∧ k < i+1) :
    (-1000000000)*k ≤ Znth k (residuals++[r]) 0 ∧ Znth k (residuals++[r]) 0 ≤ 1000000000*k := by
  by_cases he : k=i
  · subst k
    rw [← hrl,znth_snoc,hrl]
    have hh := hb (i-1) (by omega)
    have hvv := hv (i-1) (by omega)
    omega
  · rw [znth_app_left 0 residuals [r] k (by omega)]
    exact hb k (by omega)

theorem prefix_residual_extend_prior_false__prefix_construction (values residuals flags : List Int) (i r : Int)
    (hi : 1 ≤ i) (hrl : Zlength residuals=i) (hfl : Zlength flags=i)
    (hs : PrefixResidualState values residuals flags) (hr : r=Znth (i-1) values 0-Znth (i-1) residuals 0)
    (hf : Znth (i-1) flags 0=0) : PrefixResidualState values (residuals++[r]) (flags++[0]) := by
  apply prefix_residual_extend_core__prefix_construction values residuals flags i r 0 hi hrl hfl hs hr (Or.inl rfl)
  constructor
  · omega
  · intro hall
    have he : Znth (i-1) flags 0=1 := (hs.2.2.2 (i-1) (by omega)).2.mpr (by
      intro j hj
      have hh := hall j (by omega)
      rwa [znth_app_left 0 residuals [r] j (by omega)] at hh)
    omega

theorem prefix_residual_extend_success__prefix_construction (values residuals flags : List Int) (i r : Int)
    (hi : 1 ≤ i) (hrl : Zlength residuals=i) (hfl : Zlength flags=i)
    (hs : PrefixResidualState values residuals flags) (hr : r=Znth (i-1) values 0-Znth (i-1) residuals 0)
    (hf : Znth (i-1) flags 0≠0) (hr0 : 0 ≤ r) : PrefixResidualState values (residuals++[r]) (flags++[1]) := by
  apply prefix_residual_extend_core__prefix_construction values residuals flags i r 1 hi hrl hfl hs hr (Or.inr rfl)
  constructor
  · intro _ j hj
    by_cases he : j=i
    · subst j; rw [← hrl,znth_snoc]; exact hr0
    · rw [znth_app_left 0 residuals [r] j (by omega)]
      obtain ⟨hb,hiff⟩ := hs.2.2.2 (i-1) (by omega)
      exact hiff.mp (hb.resolve_left hf) j (by omega)
  · intros; rfl

theorem prefix_residual_extend_current_false__prefix_construction (values residuals flags : List Int) (i r : Int)
    (hi : 1 ≤ i) (hrl : Zlength residuals=i) (hfl : Zlength flags=i)
    (hs : PrefixResidualState values residuals flags) (hr : r=Znth (i-1) values 0-Znth (i-1) residuals 0)
    (hrneg : r < 0) : PrefixResidualState values (residuals++[r]) (flags++[0]) := by
  apply prefix_residual_extend_core__prefix_construction values residuals flags i r 0 hi hrl hfl hs hr (Or.inl rfl)
  constructor
  · omega
  · intro hall
    have hh := hall i (by omega)
    rw [← hrl,znth_snoc] at hh
    omega

theorem suffix_residual_state_terminal_init__suffix_setup (values : List Int) :
    SuffixResidualState values (Zlength values+1) [0] [1] := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro q hq
    change 0 ≤ q ∧ q < 1-1 at hq
    omega
  · intro q hq
    have he : q=0 := by change 0 ≤ q ∧ q < 1 at hq; omega
    subst q
    refine ⟨Or.inr rfl,?_⟩
    constructor
    · intro _ j hj
      have he : j=0 := by change 0 ≤ j ∧ j < 1 at hj; omega
      subst j
      exact le_refl _
    · intros; rfl

theorem replace_Znth_app_last__suffix_step (pref : List Int) (old value : Int) :
    replace_Znth (Zlength pref) value (pref++[old])=pref++[value] := replace_Znth_app_last__prefix_construction pref old value

theorem suffix_residual_prepend_core__suffix_step (values : List Int) (start : Int)
    (residuals flags : List Int) (new_residual new_flag : Int)
    (hlen : Zlength residuals=Zlength flags) (hpos : 0<Zlength residuals)
    (hs : SuffixResidualState values (start+1) residuals flags)
    (hr : new_residual=Znth (start-1) values 0-Znth 0 residuals 0)
    (hb : new_flag=0 ∨ new_flag=1)
    (hf : new_flag=1 ↔ Znth 0 flags 0=1 ∧ 0≤new_residual) :
    SuffixResidualState values start (new_residual::residuals) (new_flag::flags) := by
  rcases hs with ⟨he,he',hrec,hflags⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [Zlength_cons,Znth_cons 0 _ _ _ (by omega)]
    convert he using 1 <;> congr 1 <;> omega
  · rw [Zlength_cons,Znth_cons 0 _ _ _ (by omega)]
    convert he' using 1 <;> congr 1 <;> omega
  · intro q hq
    simp only [Zlength_cons] at hq
    by_cases hz : q=0
    · subst q
      simpa only [Znth_cons 0 1 new_residual residuals (by omega),sub_self,Int.zero_add,Int.add_zero] using hr
    · rw [Znth_cons 0 q new_residual residuals (by omega),Znth_cons 0 (q+1) new_residual residuals (by omega)]
      have h := hrec (q-1) (by omega)
      simpa only [show start+1+(q-1)-1=start+q-1 by omega,Int.sub_add_cancel,Int.add_sub_cancel] using h
  · intro q hq
    simp only [Zlength_cons] at hq ⊢
    by_cases hz : q=0
    · subst q
      change (new_flag=0 ∨ new_flag=1) ∧ (new_flag=1 ↔ _)
      refine ⟨hb,⟨?_,?_⟩⟩
      · intro hn j hj
        rcases hf.mp hn with ⟨ho,hnon⟩
        by_cases hj0 : j=0
        · subst j; exact hnon
        · rw [Znth_cons 0 j new_residual residuals (by omega)]
          exact (hflags 0 (by omega)).2.mp ho (j-1) (by omega)
      · intro hall
        apply hf.mpr
        refine ⟨(hflags 0 (by omega)).2.mpr ?_,hall 0 (by omega)⟩
        intro j hj
        have h := hall (j+1) (by omega)
        rw [Znth_cons 0 (j+1) new_residual residuals (by omega)] at h
        simpa using h
    · rw [Znth_cons 0 q new_flag flags (by omega)]
      rcases hflags (q-1) (by omega) with ⟨hb',hf'⟩
      refine ⟨hb',⟨?_,?_⟩⟩
      · intro ho j hj
        rw [Znth_cons 0 j new_residual residuals (by omega)]
        exact hf'.mp ho (j-1) (by omega)
      · intro hall
        apply hf'.mpr
        intro j hj
        have h := hall (j+1) (by omega)
        rw [Znth_cons 0 (j+1) new_residual residuals (by omega)] at h
        simpa using h

theorem suffix_residual_prepend_bound__suffix_step (n i : Int) (residuals : List Int) (new_residual : Int)
    (hlen : Zlength residuals=n+1-i)
    (hnew : -1000000000*(n-i+1)≤new_residual ∧ new_residual≤1000000000*(n-i+1))
    (hold : ∀q, (0≤q ∧ q<Zlength residuals) →
      -1000000000*(n-i-q)≤Znth q residuals 0 ∧ Znth q residuals 0≤1000000000*(n-i-q))
    (q : Int) (hq : 0≤q ∧ q<Zlength (new_residual::residuals)) :
    -1000000000*(n-(i-1)-q)≤Znth q (new_residual::residuals) 0 ∧
      Znth q (new_residual::residuals) 0≤1000000000*(n-(i-1)-q) := by
  simp only [Zlength_cons] at hq
  by_cases hz : q=0
  · subst q; change _≤new_residual ∧ new_residual≤_; omega
  · rw [Znth_cons 0 q new_residual residuals (by omega)]
    have h := hold (q-1) (by omega)
    constructor <;> omega

theorem Zlength_replace_Znth__final_result {A : Type} (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l)=Zlength l := by
  simp only [Zlength,replace_Znth]
  congr 1
  generalize n.toNat=m
  induction l generalizing m with
  | nil => cases m <;> rfl
  | cons x xs ih =>
    cases m with
    | zero => rfl
    | succ m => simpa only [replace_nth,List.length_cons] using congrArg Nat.succ (ih m)

theorem residual_ok_reverse_clean_step__final_result (a b : List Int) (prev : Int)
    (hs : CleanStep a b) (hok : residual_ok_from__final_result prev b) :
    residual_ok_from__final_result prev a := by
  induction a generalizing b prev with
  | nil => rcases hs with ⟨i,hi,_⟩; simp only [Zlength_nil] at hi; omega
  | cons x xs ih =>
    rcases hs with ⟨i,hi,hx,hy,heq⟩
    by_cases hz : i=0
    · subst i
      cases xs with
      | nil => simp only [Zlength_cons,Zlength_nil] at hi; omega
      | cons y ys =>
        have hb : b=(x-1)::(y-1)::ys := heq
        rw [hb] at hok
        rcases hok with ⟨h1,h2,ht⟩
        change 0≤x-prev ∧ 0≤y-(x-prev) ∧ residual_ok_from__final_result (y-(x-prev)) ys
        refine ⟨by omega,by omega,?_⟩
        convert ht using 1 <;> omega
    · have hip : 0<i := by omega
      let bt := replace_Znth i (Znth i xs 0-1) (replace_Znth (i-1) (Znth (i-1) xs 0-1) xs)
      have hb : b=x::bt := by
        rw [heq,replace_Znth_cons i _ _ _ hip,replace_Znth_cons (i+1) _ _ _ (by omega),
          Znth_cons 0 i x xs hip,Znth_cons 0 (i+1) x xs (by omega)]
        simp only [Int.add_sub_cancel,bt]
      have hstep : CleanStep xs bt := by
        refine ⟨i-1,?_,?_,?_,?_⟩
        · simp only [Zlength_cons] at hi; omega
        · rw [Znth_cons 0 i x xs hip] at hx; exact hx
        · rw [Znth_cons 0 (i+1) x xs (by omega)] at hy
          simpa only [Int.add_sub_cancel,Int.sub_add_cancel] using hy
        · simp only [Int.sub_add_cancel,bt]
      rw [hb] at hok
      exact ⟨hok.1,ih bt (x-prev) hstep hok.2⟩

private theorem clean_step_cons_zero {a b : List Int} (hs : CleanStep a b) :
    CleanStep (0::a) (0::b) := by
  rcases hs with ⟨i,hi,hx,hy,heq⟩
  refine ⟨i+1,?_,?_,?_,?_⟩
  · simp only [Zlength_cons]; omega
  · rw [Znth_cons 0 (i+1) 0 a (by omega)]; simpa using hx
  · rw [Znth_cons 0 (i+1+1) 0 a (by omega)]; simpa using hy
  · rw [replace_Znth_cons (i+1) _ _ _ (by omega),replace_Znth_cons (i+1+1) _ _ _ (by omega),
      Znth_cons 0 (i+1) 0 a (by omega),Znth_cons 0 (i+1+1) 0 a (by omega)]
    simpa only [Int.add_sub_cancel] using congrArg (List.cons 0) heq

theorem clean_reach_cons_zero__final_result (a b : List Int) (h : CleanReach__final_result a b) :
    CleanReach__final_result (0::a) (0::b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (clean_step_cons_zero hs)

theorem residual_ok_reach_zero__final_result (len : Nat) (a : List Int)
    (hlen : a.length=len) (hok : ResidualOK__final_result a) :
    ∃z, Forall (fun v => v=0) z ∧ CleanReach__final_result a z := by
  induction len generalizing a with
  | zero =>
    have ha : a=[] := List.length_eq_zero_iff.mp hlen
    subst a
    exact ⟨[],Forall.nil,.refl⟩
  | succ len ih =>
    cases a with
    | nil => simp at hlen
    | cons x xs =>
      cases xs with
      | nil =>
        have hx : x=0 := by change 0≤x-0 ∧ x-0=0 at hok; omega
        subst x
        exact ⟨[0],Forall.cons rfl Forall.nil,.refl⟩
      | cons y ys =>
        change 0≤x-0 ∧ 0≤y-(x-0) ∧ residual_ok_from__final_result (y-(x-0)) ys at hok
        have hx : x=(x.toNat:Int) := by omega
        rw [hx] at hok ⊢
        generalize x.toNat=m at hok ⊢
        have htail_len : (y::ys).length=len := by simpa using hlen
        clear hlen hx x
        induction m generalizing y ys with
        | zero =>
          have htail : ResidualOK__final_result (y::ys) := by
            simpa only [ResidualOK__final_result,residual_ok_from__final_result,Int.natCast_zero,sub_zero] using hok.2
          rcases ih (y::ys) htail_len htail with ⟨z,hz,hreach⟩
          exact ⟨0::z,Forall.cons rfl hz,clean_reach_cons_zero__final_result _ _ hreach⟩
        | succ m ihm =>
          have hnext : ResidualOK__final_result ((m:Int)::(y-1)::ys) := by
            change 0≤(m:Int)-0 ∧ 0≤y-1-((m:Int)-0) ∧ residual_ok_from__final_result (y-1-((m:Int)-0)) ys
            refine ⟨by omega,by omega,?_⟩
            convert hok.2.2 using 1 <;> omega
          rcases ihm (y-1) ys hnext htail_len with ⟨z,hz,hreach⟩
          refine ⟨z,hz,Relation.ReflTransGen.head ?_ hreach⟩
          refine ⟨0,?_,?_,?_,?_⟩
          · simp only [Zlength_cons]; have := Zlength_nonneg ys; omega
          · change (m.succ:Int)>0; omega
          · change y>0; omega
          · change (m:Int)::(y-1)::ys=((m.succ:Int)-1)::(y-1)::ys
            congr 2 <;> omega

theorem residual_ok_all_zero__final_result (a : List Int) (h : Forall (fun v => v=0) a) :
    ResidualOK__final_result a := by
  induction h with
  | nil => rfl
  | cons he ht ih =>
    subst_vars
    exact ⟨by omega,ih⟩

theorem trace_residual_ok__final_result (st : List (List Int)) (hne : st≠[])
    (hsteps : ∀q, (0≤q ∧ q<Zlength st-1) → CleanStep (Znth q st []) (Znth (q+1) st []))
    (hlast : ResidualOK__final_result (Znth (Zlength st-1) st [])) :
    ResidualOK__final_result (Znth 0 st []) := by
  induction st with
  | nil => exact False.elim (hne rfl)
  | cons a st ih =>
    cases st with
    | nil => exact hlast
    | cons b tl =>
      have hpos := Zlength_nonneg tl
      have hab : CleanStep a b := hsteps 0 (by simp only [Zlength_cons]; omega)
      have htail : ResidualOK__final_result b := by
        apply ih (by simp)
        · intro q hq
          have h := hsteps (q+1) (by simp only [Zlength_cons] at hq ⊢; omega)
          rw [Znth_cons [] (q+1) a (b::tl) (by omega),Znth_cons [] (q+1+1) a (b::tl) (by omega)] at h
          simpa only [Int.add_sub_cancel] using h
        · rw [Znth_cons [] (Zlength (a::b::tl)-1) a (b::tl) (by simp only [Zlength_cons]; omega)] at hlast
          convert hlast using 1 <;> congr 2 <;> simp only [Zlength_cons] <;> omega
      exact residual_ok_reverse_clean_step__final_result a b 0 hab htail

theorem clean_reach_trace__final_result (a z : List Int) (h : CleanReach__final_result a z) :
    ∃st : List (List Int), st≠[] ∧ Znth 0 st []=a ∧ Znth (Zlength st-1) st []=z ∧
      ∀q, (0≤q ∧ q<Zlength st-1) → CleanStep (Znth q st []) (Znth (q+1) st []) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[z],by simp,rfl,rfl,by intro q hq; simp only [Zlength_cons,Zlength_nil] at hq; omega⟩
  | @head a b hab hbc ih =>
    rcases ih with ⟨st,hne,hfirst,hlast,hsteps⟩
    have hpos : 0<Zlength st := by cases st with | nil => contradiction | cons b tl => simp only [Zlength_cons]; have := Zlength_nonneg tl; omega
    refine ⟨a::st,by simp,rfl,?_,?_⟩
    · rw [Znth_cons [] (Zlength (a::st)-1) a st (by simp only [Zlength_cons]; omega)]
      convert hlast using 1 <;> congr 1 <;> simp only [Zlength_cons] <;> omega
    · intro q hq
      simp only [Zlength_cons] at hq
      by_cases hz : q=0
      · subst q
        change CleanStep a (Znth 0 st [])
        rw [hfirst]; exact hab
      · rw [Znth_cons [] q a st (by omega),Znth_cons [] (q+1) a st (by omega)]
        have h := hsteps (q-1) (by omega)
        simpa only [Int.sub_add_cancel,Int.add_sub_cancel] using h

theorem direct_cleanable_implies_residual_ok__final_result (a : List Int)
    (h : ∃st : List (List Int), st≠[] ∧ Znth 0 st []=a ∧ Forall (fun x=>x=0) (Znth (Zlength st-1) st []) ∧
      ∀q, (0≤q ∧ q<Zlength st-1) → CleanStep (Znth q st []) (Znth (q+1) st [])) :
    ResidualOK__final_result a := by
  rcases h with ⟨st,hne,hfirst,hzero,hsteps⟩
  rw [←hfirst]
  exact trace_residual_ok__final_result st hne hsteps (residual_ok_all_zero__final_result _ hzero)

theorem residual_ok_from_recurrence__final_result (a : List Int) (prev : Int) (r : Int → Int)
    (hr0 : r 0=prev)
    (hrec : ∀k, (0≤k ∧ k<Zlength a) → r (k+1)=Znth k a 0-r k ∧ 0≤r (k+1))
    (hend : r (Zlength a)=0) : residual_ok_from__final_result prev a := by
  induction a generalizing prev r with
  | nil => change r 0=0 at hend; change prev=0; omega
  | cons x xs ih =>
    have hpos := Zlength_nonneg xs
    have h1 := hrec 0 (by simp only [Zlength_cons]; omega)
    change r 1=x-r 0 ∧ 0≤r 1 at h1
    refine ⟨by omega,?_⟩
    apply ih (x-prev) (fun k=>r (k+1)) (by change r 1=x-prev; omega)
    · intro k hk
      have h := hrec (k+1) (by simp only [Zlength_cons]; omega)
      rw [Znth_cons 0 (k+1) x xs (by omega)] at h
      simpa only [Int.add_sub_cancel] using h
    · simpa only [Zlength_cons] using hend

theorem residual_ok_recurrence_facts__final_result (a : List Int) (prev : Int) (r : Int → Int)
    (hprev : 0≤prev) (hr0 : r 0=prev)
    (hrec : ∀k, (0≤k ∧ k<Zlength a) → r (k+1)=Znth k a 0-r k)
    (hok : residual_ok_from__final_result prev a) :
    (∀k, (0≤k ∧ k≤Zlength a) → 0≤r k) ∧ r (Zlength a)=0 := by
  induction a generalizing prev r with
  | nil =>
    refine ⟨?_,?_⟩
    · intro k hk
      simp only [Zlength_nil] at hk
      have : k=0 := by omega
      subst k
      omega
    · change prev=0 at hok; change r 0=0; omega
  | cons x xs ih =>
    have hpos := Zlength_nonneg xs
    have h1 := hrec 0 (by simp only [Zlength_cons]; omega)
    change r 1=x-r 0 at h1
    rcases hok with ⟨hnext,htail⟩
    have hrec' : ∀k, (0≤k ∧ k<Zlength xs) → r (k+1+1)=Znth k xs 0-r (k+1) := by
      intro k hk
      have h := hrec (k+1) (by simp only [Zlength_cons]; omega)
      rw [Znth_cons 0 (k+1) x xs (by omega)] at h
      simpa only [Int.add_sub_cancel] using h
    rcases ih (x-prev) (fun k=>r (k+1)) hnext (by change r 1=x-prev; omega) hrec' htail with ⟨hn,he⟩
    refine ⟨?_,?_⟩
    · intro k hk
      simp only [Zlength_cons] at hk
      by_cases hz : k=0
      · subst k; omega
      · have h := hn (k-1) (by omega); simpa only [Int.sub_add_cancel] using h
    · simpa only [Zlength_cons] using he

theorem direct_cleanable_residual_ok_iff__final_result (a : List Int) :
    DirectCleanable__final_result a ↔ ResidualOK__final_result a := by
  refine ⟨direct_cleanable_implies_residual_ok__final_result a,?_⟩
  intro hok
  rcases residual_ok_reach_zero__final_result a.length a rfl hok with ⟨z,hz,hreach⟩
  rcases clean_reach_trace__final_result a z hreach with ⟨st,hne,hfirst,hlast,hsteps⟩
  exact ⟨st,hne,hfirst,hlast ▸ hz,hsteps⟩

theorem cleanable_direct_iff__final_result (values pre_values okpre_values : List Int)
    (hlen : Zlength pre_values=Zlength values+1) (hoklen : Zlength okpre_values=Zlength values+1)
    (hs : PrefixResidualState values pre_values okpre_values) :
    DirectCleanable__final_result values ↔ DirectResidualSuccess pre_values okpre_values (Zlength values) := by
  rcases hs with ⟨hp0,ho0,hrec,hflags⟩
  rw [direct_cleanable_residual_ok_iff__final_result]
  have hrec' : ∀k, (0≤k ∧ k<Zlength values) →
      Znth (k+1) pre_values 0=Znth k values 0-Znth k pre_values 0 := by
    intro k hk
    simpa only [Int.add_sub_cancel] using hrec (k+1) (by omega)
  have hpos := Zlength_nonneg values
  have hf := (hflags (Zlength values) (by omega)).2
  constructor
  · intro hres
    rcases residual_ok_recurrence_facts__final_result values 0 (fun k=>Znth k pre_values 0)
      (by omega) hp0 hrec' hres with ⟨hn,he⟩
    exact ⟨hf.mpr hn,he⟩
  · rintro ⟨ho,he⟩
    apply residual_ok_from_recurrence__final_result values 0 (fun k=>Znth k pre_values 0) hp0
    · intro k hk; exact ⟨hrec' k hk,hf.mp ho (k+1) (by omega)⟩
    · exact he

theorem residuals_from_zero__final_result (a : List Int) (prev : Int) :
    Znth 0 (residuals_from__final_result prev a) 0=prev := by cases a <;> rfl

theorem residuals_from_recurrence__final_result (a : List Int) (prev k : Int)
    (hk : 0≤k ∧ k<Zlength a) :
    Znth (k+1) (residuals_from__final_result prev a) 0=Znth k a 0-Znth k (residuals_from__final_result prev a) 0 := by
  induction a generalizing prev k with
  | nil => simp only [Zlength_nil] at hk; omega
  | cons x xs ih =>
    by_cases hz : k=0
    · subst k
      simpa only [residuals_from__final_result,Znth_cons 0 1 prev _ (by omega)] using residuals_from_zero__final_result xs (x-prev)
    · simp only [Zlength_cons] at hk
      simp only [residuals_from__final_result]
      rw [Znth_cons 0 (k+1) prev _ (by omega),Znth_cons 0 k x xs (by omega),Znth_cons 0 k prev _ (by omega)]
      simpa only [Int.sub_add_cancel,Int.add_sub_cancel] using ih (x-prev) (k-1) (by omega)

theorem swap1_length__final_result (a : List Int) (i : Int) : Zlength (swap1__final_result a i)=Zlength a := by
  simp only [swap1__final_result,Zlength_replace_Znth__final_result]

theorem swap1_left__final_result (a : List Int) (i : Int) (hi : 1≤i ∧ i<Zlength a) :
    Znth (i-1) (swap1__final_result a i) 0=Znth i a 0 := by
  unfold swap1__final_result
  rw [Znth_replace_Znth_Diff 0 _ i (i-1) _ (by rw [Zlength_replace_Znth__final_result]; omega)
    (by rw [Zlength_replace_Znth__final_result]; omega) (by omega),
    Znth_replace_Znth_Same 0 a (i-1) _ (by omega)]

theorem swap1_right__final_result (a : List Int) (i : Int) (hi : 1≤i ∧ i<Zlength a) :
    Znth i (swap1__final_result a i) 0=Znth (i-1) a 0 := by
  unfold swap1__final_result
  exact Znth_replace_Znth_Same 0 _ i _ (by rw [Zlength_replace_Znth__final_result]; omega)

theorem swap1_other__final_result (a : List Int) (i k : Int) (hi : 1≤i ∧ i<Zlength a)
    (hk : 0≤k ∧ k<Zlength a) (hl : k≠i-1) (hr : k≠i) :
    Znth k (swap1__final_result a i) 0=Znth k a 0 := by
  unfold swap1__final_result
  rw [Znth_replace_Znth_Diff 0 _ i k _ (by rw [Zlength_replace_Znth__final_result]; omega)
    (by rw [Zlength_replace_Znth__final_result]; omega) (by omega),
    Znth_replace_Znth_Diff 0 a (i-1) k _ (by omega) hk (by omega)]

theorem cleanable_cases__final_result (a : List Int) :
    Cleanable a ↔ DirectCleanable__final_result a ∨
      ∃i, (1≤i ∧ i<Zlength a) ∧ DirectCleanable__final_result (swap1__final_result a i) := by
  constructor
  · rintro ⟨base,st,hbase,hne,hfirst,hlast,hsteps⟩
    rcases hbase with he | ⟨j,hj,he⟩
    · left; exact ⟨st,hne,hfirst.trans he,hlast,hsteps⟩
    · right
      refine ⟨j+1,by omega,st,hne,?_,hlast,hsteps⟩
      simpa only [swap1__final_result,Int.add_sub_cancel] using hfirst.trans he
  · rintro (⟨st,hne,hfirst,hlast,hsteps⟩ | ⟨i,hi,st,hne,hfirst,hlast,hsteps⟩)
    · exact ⟨a,st,Or.inl rfl,hne,hfirst,hlast,hsteps⟩
    · refine ⟨swap1__final_result a i,st,Or.inr ⟨i-1,by omega,?_⟩,hne,hfirst,hlast,hsteps⟩
      simp only [swap1__final_result,Int.sub_add_cancel]

theorem recurrence_unique_interval__final_result (f g : Int → Int) (lo hi : Int)
    (hlo : f lo=g lo)
    (hstep : ∀k, (lo≤k ∧ k<hi) → (f (k+1)=g (k+1) ↔ f k=g k))
    (k : Int) (hk : lo≤k ∧ k≤hi) : f k=g k := by
  have he : k=lo+((k-lo).toNat:Int) := by omega
  rw [he]
  have hb : lo+((k-lo).toNat:Int)≤hi := by omega
  generalize (k-lo).toNat=m at hb ⊢
  induction m with
  | zero => simpa using hlo
  | succ m ih =>
    have hp : lo+(m:Int)≤hi := by omega
    have hs := (hstep (lo+(m:Int)) (by omega)).mpr (ih hp)
    simpa only [Int.natCast_succ,Int.add_assoc] using hs

theorem recurrence_unique_interval_backward__final_result (f g : Int → Int) (lo hi : Int)
    (hhi : f hi=g hi)
    (hstep : ∀k, (lo≤k ∧ k<hi) → (f (k+1)=g (k+1) ↔ f k=g k))
    (k : Int) (hk : lo≤k ∧ k≤hi) : f k=g k := by
  have he : k+((hi-k).toNat:Int)=hi := by omega
  generalize (hi-k).toNat=m at he
  induction m generalizing k with
  | zero =>
    have : k=hi := by omega
    subst k
    exact hhi
  | succ m ih => exact (hstep k (by omega)).mp (ih (k+1) (by omega) (by omega))

theorem cleanable_one_swap_iff__final_result (values pref suf okpre oksuf : List Int) (i : Int)
    (hi : 1≤i ∧ i<Zlength values)
    (hplen : Zlength pref=Zlength values+1) (hslen : Zlength suf=Zlength values+1)
    (hoplen : Zlength okpre=Zlength values+1) (hoslen : Zlength oksuf=Zlength values+1)
    (hp : PrefixResidualState values pref okpre) (hs : SuffixResidualState values 1 suf oksuf) :
    DirectCleanable__final_result (swap1__final_result values i) ↔ SwapResidualSuccess values pref suf okpre oksuf i := by
  rcases hp with ⟨hp0,hop0,hprec,hpflags⟩
  rcases hs with ⟨hse,hose,hsrec,hsflags⟩
  have hsterm : Znth (Zlength values) suf 0=0 := by
    convert hse using 1 <;> congr 1 <;> omega
  rw [direct_cleanable_residual_ok_iff__final_result]
  let sw := swap1__final_result values i
  let r : Int → Int := fun k=>Znth k (canonical_residuals__final_result sw) 0
  have hswlen : Zlength sw=Zlength values := swap1_length__final_result values i
  have hr0 : r 0=0 := residuals_from_zero__final_result sw 0
  have hrrec : ∀k, (0≤k ∧ k<Zlength values) → r (k+1)=Znth k sw 0-r k := by
    intro k hk
    exact residuals_from_recurrence__final_result sw 0 k (by omega)
  have hprefixeq : ∀k, (0≤k ∧ k≤i-1) → r k=Znth k pref 0 := by
    apply recurrence_unique_interval__final_result r (fun k=>Znth k pref 0) 0 (i-1)
    · exact hr0.trans hp0.symm
    · intro k hk
      have hr := hrrec k (by omega)
      have hp := hprec (k+1) (by omega)
      simp only [Int.add_sub_cancel] at hp
      have hsw : Znth k sw 0=Znth k values 0 := swap1_other__final_result values i k hi (by omega) (by omega) (by omega)
      rw [hsw] at hr
      constructor <;> intro he <;> dsimp only at * <;> omega
  have hsforward : ∀k, (i+1≤k ∧ k<Zlength values) →
      Znth (k+1) suf 0=Znth k values 0-Znth k suf 0 := by
    intro k hk
    have h := hsrec k (by omega)
    rw [show 1+k-1=k by omega] at h
    omega
  have hri : r i=Znth i values 0-Znth (i-1) pref 0 := by
    have h := hrrec (i-1) (by omega)
    rw [Int.sub_add_cancel,swap1_left__final_result values i hi,hprefixeq (i-1) (by omega)] at h
    exact h
  have hri1 : r (i+1)=Znth (i-1) values 0-r i := by
    have h := hrrec i (by omega)
    rw [swap1_right__final_result values i hi] at h
    exact h
  have hsame : ∀k, (i+1≤k ∧ k<Zlength values) → (r (k+1)=Znth (k+1) suf 0 ↔ r k=Znth k suf 0) := by
    intro k hk
    rw [hrrec k (by omega),hsforward k hk,swap1_other__final_result values i k hi (by omega) (by omega) (by omega)]
    omega
  constructor
  · intro hres
    have hrec' : ∀k, (0≤k ∧ k<Zlength sw) → r (k+1)=Znth k sw 0-r k := by
      intro k hk; exact hrrec k (by omega)
    rcases residual_ok_recurrence_facts__final_result sw 0 r (by omega) hr0 hrec' hres with ⟨hrnon,hrend⟩
    have hsufeq : ∀k, (i+1≤k ∧ k≤Zlength values) → r k=Znth k suf 0 := by
      apply recurrence_unique_interval_backward__final_result r (fun k=>Znth k suf 0) (i+1) (Zlength values)
      · rw [hswlen] at hrend
        exact hrend.trans hsterm.symm
      · exact hsame
    refine ⟨?_,?_,?_,?_,?_⟩
    · apply (hpflags (i-1) (by omega)).2.mpr
      intro j hj
      rw [←hprefixeq j hj]
      exact hrnon j (by omega)
    · apply (hsflags (i+1) (by omega)).2.mpr
      intro j hj
      rw [←hsufeq j (by omega)]
      exact hrnon j (by omega)
    · change 0≤Znth i values 0-Znth (i-1) pref 0
      rw [←hri]
      exact hrnon i (by omega)
    · change 0≤Znth (i-1) values 0-(Znth i values 0-Znth (i-1) pref 0)
      rw [←hri,←hri1]
      exact hrnon (i+1) (by omega)
    · change Znth (i-1) values 0-(Znth i values 0-Znth (i-1) pref 0)=Znth (i+1) suf 0
      rw [←hri,←hri1]
      exact hsufeq (i+1) (by omega)
  · rintro ⟨hop,hos,hx,hy,he⟩
    change 0≤Znth i values 0-Znth (i-1) pref 0 at hx
    change 0≤Znth (i-1) values 0-(Znth i values 0-Znth (i-1) pref 0) at hy
    change Znth (i-1) values 0-(Znth i values 0-Znth (i-1) pref 0)=Znth (i+1) suf 0 at he
    have hsufeq : ∀k, (i+1≤k ∧ k≤Zlength values) → r k=Znth k suf 0 := by
      apply recurrence_unique_interval__final_result r (fun k=>Znth k suf 0) (i+1) (Zlength values)
      · rw [hri1,hri]; exact he
      · exact hsame
    apply residual_ok_from_recurrence__final_result sw 0 r hr0
    · intro k hk
      refine ⟨hrrec k (by omega),?_⟩
      by_cases hb : k+1≤i-1
      · rw [hprefixeq (k+1) (by omega)]
        exact (hpflags (i-1) (by omega)).2.mp hop (k+1) (by omega)
      · by_cases he : k+1=i
        · rw [he,hri]; exact hx
        · rw [hsufeq (k+1) (by omega)]
          exact (hsflags (i+1) (by omega)).2.mp hos (k+1) (by omega)
    · rw [hswlen,hsufeq (Zlength values) (by omega)]
      exact hsterm

theorem cleanable_residual_characterization__final_result (values pref suf okpre oksuf : List Int)
    (hplen : Zlength pref=Zlength values+1) (hslen : Zlength suf=Zlength values+1)
    (hoplen : Zlength okpre=Zlength values+1) (hoslen : Zlength oksuf=Zlength values+1)
    (hp : PrefixResidualState values pref okpre) (hs : SuffixResidualState values 1 suf oksuf) :
    Cleanable values ↔ DirectResidualSuccess pref okpre (Zlength values) ∨
      ∃i, (1≤i ∧ i<Zlength values) ∧ SwapResidualSuccess values pref suf okpre oksuf i := by
  rw [cleanable_cases__final_result,cleanable_direct_iff__final_result values pref okpre hplen hoplen hp]
  constructor
  · rintro (hd | ⟨i,hi,hw⟩)
    · exact Or.inl hd
    · exact Or.inr ⟨i,hi,(cleanable_one_swap_iff__final_result values pref suf okpre oksuf i hi hplen hslen hoplen hoslen hp hs).mp hw⟩
  · rintro (hd | ⟨i,hi,hw⟩)
    · exact Or.inl hd
    · exact Or.inr ⟨i,hi,(cleanable_one_swap_iff__final_result values pref suf okpre oksuf i hi hplen hslen hoplen hoslen hp hs).mpr hw⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib
