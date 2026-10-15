import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

import ListLib.General.Length
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_lib
open AUXLib


open MaxMinLib

def ContainerHeightNLogN (l : List Int) (i j : Int) : Int := min (Znth i l 0) (Znth j l 0)
def ContainerAreaNLogN (l : List Int) (i j : Int) : Int := (j-i) * ContainerHeightNLogN l i j
def ContainerPairNLogN (l : List Int) (i j : Int) : Prop := 0 ≤ i ∧ i < j ∧ j < Zlength l

def MaximumContainerArea (l : List Int) (ans : Int) : Prop :=
  ∃ i j, 0 ≤ i ∧ i < j ∧ j < Zlength l ∧ ans = (j-i) * min (Znth i l 0) (Znth j l 0) ∧
    ∀ p q, 0 ≤ p → p < q → q < Zlength l → (q-p) * min (Znth p l 0) (Znth q l 0) ≤ ans

def IndexedHeightsNLogN (l : List Int) : List (Int × Int) :=
  (List.range l.length).map (fun k : Nat => (l.getD k 0, (k : Int)))

def HeightIndexPermutationNLogN (l heights indices : List Int) : Prop :=
  Zlength heights = Zlength l ∧ Zlength indices = Zlength l ∧ List.Perm (heights.zip indices) (IndexedHeightsNLogN l)

def HeightIndexRangeDescendingNLogN (heights : List Int) (lo hi : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ Zlength heights ∧ ∀ p q, lo ≤ p → p ≤ q → q < hi → Znth q heights 0 ≤ Znth p heights 0

def SortedHeightIndexWorkspaceNLogN (l heights indices : List Int) : Prop :=
  HeightIndexPermutationNLogN l heights indices ∧ HeightIndexRangeDescendingNLogN heights 0 (Zlength heights)

def WorkspacePrefixNLogN (l heights indices : List Int) (k : Int) : Prop :=
  (∀ p, (0 ≤ p ∧ p < k) → Znth p heights 0 = Znth p l 0) ∧ (∀ p, (0 ≤ p ∧ p < k) → Znth p indices 0 = p)

def SameHeightIndexOutsideNLogN (before_h before_i after_h after_i : List Int) (lo hi : Int) : Prop :=
  Zlength after_h = Zlength before_h ∧ Zlength after_i = Zlength before_i ∧
    ∀ k, (0 ≤ k ∧ k < Zlength before_h) → (k < lo ∨ hi ≤ k) →
      Znth k after_h 0 = Znth k before_h 0 ∧ Znth k after_i 0 = Znth k before_i 0

def HeightIndexRangePermutationNLogN (before_h before_i after_h after_i : List Int) (lo hi : Int) : Prop :=
  List.Perm ((sublist lo hi after_h).zip (sublist lo hi after_i)) ((sublist lo hi before_h).zip (sublist lo hi before_i))

def HeightIndexRangeSortResultNLogN (before_h before_i after_h after_i : List Int) (lo hi : Int) : Prop :=
  Zlength before_h = Zlength before_i ∧ Zlength after_h = Zlength after_i ∧ 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ Zlength before_h ∧
    SameHeightIndexOutsideNLogN before_h before_i after_h after_i lo hi ∧
    HeightIndexRangePermutationNLogN before_h before_i after_h after_i lo hi ∧ HeightIndexRangeDescendingNLogN after_h lo hi

def MergePrefixStateNLogN (source_h source_i dest0_h dest0_i dest_h dest_i : List Int) (left middle right p q output : Int) : Prop :=
  HeightIndexRangeDescendingNLogN source_h left middle ∧ HeightIndexRangeDescendingNLogN source_h middle right ∧
    (∀ t, (0 ≤ t ∧ t < Zlength dest0_h) → (t < left ∨ output ≤ t) → Znth t dest_h 0 = Znth t dest0_h 0 ∧ Znth t dest_i 0 = Znth t dest0_i 0) ∧
    List.Perm ((sublist left output dest_h).zip (sublist left output dest_i))
      (((sublist left p source_h).zip (sublist left p source_i)) ++ ((sublist middle q source_h).zip (sublist middle q source_i))) ∧
    (∀ u v, left ≤ u → u ≤ v → v < output → Znth v dest_h 0 ≤ Znth u dest_h 0) ∧
    (∀ u v, (left ≤ u ∧ u < output) → ((p ≤ v ∧ v < middle) ∨ (q ≤ v ∧ v < right)) → Znth v source_h 0 ≤ Znth u dest_h 0)

def HeightIndexRangeMergeResultNLogN (source_h source_i dest0_h dest0_i dest_h dest_i : List Int) (left middle right : Int) : Prop :=
  0 ≤ left ∧ left ≤ middle ∧ middle ≤ right ∧ right ≤ Zlength source_h ∧
    SameHeightIndexOutsideNLogN dest0_h dest0_i dest_h dest_i left right ∧
    List.Perm ((sublist left right dest_h).zip (sublist left right dest_i)) ((sublist left right source_h).zip (sublist left right source_i)) ∧
    HeightIndexRangeDescendingNLogN dest_h left right

def CopyHeightIndexPrefixNLogN (source_h source_i dest0_h dest0_i dest_h dest_i : List Int) (left right k : Int) : Prop :=
  (∀ p, (left ≤ p ∧ p < k) → Znth p dest_h 0 = Znth p source_h 0 ∧ Znth p dest_i 0 = Znth p source_i 0) ∧
    (∀ p, (0 ≤ p ∧ p < Zlength dest0_h) → (p < left ∨ k ≤ p) → Znth p dest_h 0 = Znth p dest0_h 0 ∧ Znth p dest_i 0 = Znth p dest0_i 0)

def ProcessedIndexEndpointsNLogN (indices : List Int) (k minimum maximum : Int) : Prop :=
  (∃ p, (0 ≤ p ∧ p < k) ∧ Znth p indices 0 = minimum) ∧
  (∃ p, (0 ≤ p ∧ p < k) ∧ Znth p indices 0 = maximum) ∧
  (∀ p, (0 ≤ p ∧ p < k) → (minimum ≤ Znth p indices 0 ∧ Znth p indices 0 ≤ maximum))

def ProcessedContainerPairNLogN (l indices : List Int) (k : Int) (ij : Int × Int) : Prop :=
  ContainerPairNLogN l ij.1 ij.2 ∧ ij.1 ∈ sublist 0 k indices ∧ ij.2 ∈ sublist 0 k indices

def ProcessedContainerMaximumNLogN (l indices : List Int) (k ans : Int) : Prop :=
  max_value_of_subset_with_default (· ≤ ·) (ProcessedContainerPairNLogN l indices k)
    (fun ij : Int × Int => ContainerAreaNLogN l ij.1 ij.2) 0 ans

private theorem sublen {A : Type} (l : List A) (lo hi : Int) (hh : 0 ≤ lo ∧ lo ≤ hi) (hl : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l hh hl

private theorem empty_sub {A : Type} (l : List A) (i : Int) : sublist i i l = [] := by
  simp [AUXLib.sublist]

theorem sublist_replace_Znth_before__merge_core (A : Type) (d : A) (l : List A) (lo hi : Int) (v : A)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hb : hi < Zlength l) :
    sublist lo hi (replace_Znth hi v l) = sublist lo hi l := by
  have hl : hi ≤ Zlength (replace_Znth hi v l) := by rw [Zlength_replace_Znth]; omega
  apply (ListLib.list_eq_ext _ _ d).mpr
  refine ⟨(sublen _ lo hi hr hl).trans (sublen l lo hi hr (by omega)).symm,?_⟩
  intro k hk
  have hk' : 0 ≤ k ∧ k < hi-lo := by
    change 0 ≤ k ∧ k < Zlength (sublist lo hi (replace_Znth hi v l)) at hk
    rw [sublen _ lo hi hr hl] at hk
    exact hk
  change Znth k (sublist lo hi (replace_Znth hi v l)) d = Znth k (sublist lo hi l) d
  rw [Znth_sublist d lo k hi _ hr.1 hk',Znth_sublist d lo k hi l hr.1 hk']
  exact Znth_replace_Znth_Diff d l hi (k+lo) v ⟨by omega,hb⟩ ⟨by omega,by omega⟩ (by omega)

theorem sublist_replace_Znth_extend__merge_core (A : Type) (d : A) (l : List A) (lo hi : Int) (v : A)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hb : hi < Zlength l) :
    sublist lo (hi+1) (replace_Znth hi v l) = sublist lo hi l ++ [v] := by
  rw [sublist_split lo (hi+1) hi _ hr ⟨by omega,by rw [Zlength_replace_Znth]; omega⟩]
  rw [sublist_replace_Znth_before__merge_core A d l lo hi v hr hb]
  rw [sublist_single d hi _ ⟨by omega,by rw [Zlength_replace_Znth]; omega⟩]
  rw [Znth_replace_Znth_Same d l hi v ⟨by omega,hb⟩]

theorem sublist_eq_by_Znth__sort_copy (A : Type) (l1 l2 : List A) (lo hi : Int) (d : A)
    (hlen : Zlength l1 = Zlength l2) (hr : 0 ≤ lo ∧ lo ≤ hi) (hb : hi ≤ Zlength l1)
    (he : ∀ k, lo ≤ k ∧ k < hi → Znth k l1 d = Znth k l2 d) : sublist lo hi l1 = sublist lo hi l2 := by
  apply (ListLib.list_eq_ext _ _ d).mpr
  refine ⟨(sublen l1 lo hi hr hb).trans (sublen l2 lo hi hr (by omega)).symm,?_⟩
  intro k hk
  have hk' : 0 ≤ k ∧ k < hi-lo := by
    change 0 ≤ k ∧ k < Zlength (sublist lo hi l1) at hk
    rw [sublen l1 lo hi hr hb] at hk
    exact hk
  change Znth k (sublist lo hi l1) d = Znth k (sublist lo hi l2) d
  rw [Znth_sublist d lo k hi l1 hr.1 hk',Znth_sublist d lo k hi l2 hr.1 hk']
  exact he (k+lo) ⟨by omega,by omega⟩

theorem combine_sublist_split__sort_copy (xs ys : List Int) (left middle right : Int)
    (hlen : Zlength xs = Zlength ys) (hr : 0 ≤ left ∧ left ≤ middle)
    (hm : middle ≤ right) (hb : right ≤ Zlength xs) :
    (sublist left right xs).zip (sublist left right ys) =
      (sublist left middle xs).zip (sublist left middle ys) ++ (sublist middle right xs).zip (sublist middle right ys) := by
  rw [sublist_split left right middle xs hr ⟨hm,hb⟩,sublist_split left right middle ys hr ⟨hm,by omega⟩]
  apply List.zip_append
  have hx := sublen xs left middle hr (by omega)
  have hy := sublen ys left middle hr (by omega)
  change ((sublist left middle xs).length : Int) = middle-left at hx
  change ((sublist left middle ys).length : Int) = middle-left at hy
  omega

private theorem zip_extend (xs ys : List Int) (lo hi : Int) (hr : 0 ≤ lo ∧ lo ≤ hi)
    (hh : hi < Zlength xs) (hy : hi < Zlength ys) :
    (sublist lo (hi+1) xs).zip (sublist lo (hi+1) ys) =
      (sublist lo hi xs).zip (sublist lo hi ys) ++ [(Znth hi xs 0,Znth hi ys 0)] := by
  rw [sublist_split lo (hi+1) hi xs hr ⟨by omega,by omega⟩,sublist_split lo (hi+1) hi ys hr ⟨by omega,by omega⟩]
  rw [sublist_single 0 hi xs ⟨by omega,hh⟩,sublist_single 0 hi ys ⟨by omega,hy⟩]
  rw [List.zip_append]
  · rfl
  · have h1 := sublen xs lo hi hr (by omega)
    have h2 := sublen ys lo hi hr (by omega)
    change ((sublist lo hi xs).length : Int) = hi-lo at h1
    change ((sublist lo hi ys).length : Int) = hi-lo at h2
    omega

private theorem zip_write_extend (xs ys : List Int) (lo hi x y : Int) (hr : 0 ≤ lo ∧ lo ≤ hi)
    (hh : hi < Zlength xs) (hy : hi < Zlength ys) :
    (sublist lo (hi+1) (replace_Znth hi x xs)).zip (sublist lo (hi+1) (replace_Znth hi y ys)) =
      (sublist lo hi xs).zip (sublist lo hi ys) ++ [(x,y)] := by
  rw [sublist_replace_Znth_extend__merge_core Int 0 xs lo hi x hr hh,
      sublist_replace_Znth_extend__merge_core Int 0 ys lo hi y hr hy]
  rw [List.zip_append]
  · rfl
  · have h1 := sublen xs lo hi hr (by omega)
    have h2 := sublen ys lo hi hr (by omega)
    change ((sublist lo hi xs).length : Int) = hi-lo at h1
    change ((sublist lo hi ys).length : Int) = hi-lo at h2
    omega

theorem merge_prefix_init__merge_core (source_h source_i dest0_h dest0_i : List Int) (left middle right : Int)
    (hl : 0 ≤ left) (hm : left ≤ middle) (hr : middle ≤ right)
    (hd1 : HeightIndexRangeDescendingNLogN source_h left middle)
    (hd2 : HeightIndexRangeDescendingNLogN source_h middle right) :
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest0_h dest0_i left middle right left middle left := by
  refine ⟨hd1,hd2,fun _ _ _ => ⟨rfl,rfl⟩,?_,?_,?_⟩
  · simp only [empty_sub,List.zip_nil_left,List.nil_append]; exact List.Perm.refl _
  · intro u v hu huv hv; omega
  · intro u v hu hv; omega

theorem merge_prefix_take_left__merge_core (source_h source_i dest0_h dest0_i dest_h dest_i : List Int)
    (left middle right p q output : Int)
    (hsi : Zlength source_i = Zlength source_h) (hd0h : Zlength dest0_h = Zlength source_h)
    (hd0i : Zlength dest0_i = Zlength source_h) (hdh : Zlength dest_h = Zlength dest0_h)
    (hdi : Zlength dest_i = Zlength dest0_i) (hl : 0 ≤ left) (hlp : left ≤ p)
    (hpm : p < middle) (hmq : middle ≤ q) (hqr : q ≤ right)
    (hr : right ≤ Zlength source_h) (ho : output = left+(p-left)+(q-middle))
    (hs : MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left middle right p q output)
    (hc : q = right ∨ Znth q source_h 0 ≤ Znth p source_h 0) :
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      (replace_Znth output (Znth p source_h 0) dest_h) (replace_Znth output (Znth p source_i 0) dest_i)
      left middle right (p+1) q (output+1) := by
  have hout : 0 ≤ output ∧ output < Zlength dest_h := ⟨by omega,by omega⟩
  have houti : 0 ≤ output ∧ output < Zlength dest_i := ⟨by omega,by omega⟩
  have heh : ∀ t, 0 ≤ t ∧ t < Zlength dest_h → t ≠ output →
      Znth t (replace_Znth output (Znth p source_h 0) dest_h) 0 = Znth t dest_h 0 := by
    intro t ht hn
    exact Znth_replace_Znth_Diff 0 dest_h output t _ hout ht (Ne.symm hn)
  have hei : ∀ t, 0 ≤ t ∧ t < Zlength dest_i → t ≠ output →
      Znth t (replace_Znth output (Znth p source_i 0) dest_i) 0 = Znth t dest_i 0 := by
    intro t ht hn
    exact Znth_replace_Znth_Diff 0 dest_i output t _ houti ht (Ne.symm hn)
  have heq := Znth_replace_Znth_Same 0 dest_h output (Znth p source_h 0) hout
  obtain ⟨hd1,hd2,houtside,hperm,hdescending,hpending⟩ := hs
  refine ⟨hd1,hd2,?_,?_,?_,?_⟩
  · intro t ht hregion
    rw [heh t ⟨ht.1,by omega⟩ (by omega),hei t ⟨ht.1,by omega⟩ (by omega)]
    apply houtside t ht
    rcases hregion with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rw [zip_write_extend dest_h dest_i left output _ _ ⟨hl,by omega⟩ hout.2 houti.2]
    rw [zip_extend source_h source_i left p ⟨by omega,by omega⟩ (by omega) (by omega)]
    apply (hperm.append_right _).trans
    simpa only [List.append_assoc] using (List.perm_append_comm.append_left (sublist left p source_h |>.zip (sublist left p source_i)))
  · intro u v hu huv hv
    by_cases hvo : v = output
    · subst v
      by_cases huo : u = output
      · subst u; exact le_refl _
      · rw [heq,heh u ⟨by omega,by omega⟩ huo]
        apply hpending u p ⟨hu,by omega⟩
        exact Or.inl ⟨by omega,by omega⟩
    · rw [heh v ⟨by omega,by omega⟩ hvo,heh u ⟨by omega,by omega⟩ (by omega)]
      exact hdescending u v hu huv (by omega)
  · intro u v hu hv
    by_cases huo : u = output
    · subst u
      rw [heq]
      rcases hv with hv | hv
      · exact hd1.2.2.2 p v hlp (by omega) hv.2
      · rcases hc with hc | hc
        · omega
        · exact (hd2.2.2.2 q v hmq hv.1 hv.2).trans hc
    · rw [heh u ⟨by omega,by omega⟩ huo]
      apply hpending u v ⟨hu.1,by omega⟩
      rcases hv with hv | hv
      · exact Or.inl ⟨by omega,hv.2⟩
      · exact Or.inr ⟨by omega,hv.2⟩

theorem merge_prefix_take_right__merge_core (source_h source_i dest0_h dest0_i dest_h dest_i : List Int)
    (left middle right p q output : Int)
    (hsi : Zlength source_i = Zlength source_h) (hd0h : Zlength dest0_h = Zlength source_h)
    (hd0i : Zlength dest0_i = Zlength source_h) (hdh : Zlength dest_h = Zlength dest0_h)
    (hdi : Zlength dest_i = Zlength dest0_i) (hl : 0 ≤ left) (hlp : left ≤ p)
    (hpm : p ≤ middle) (hmq : middle ≤ q) (hqr : q < right)
    (hr : right ≤ Zlength source_h) (ho : output = left+(p-left)+(q-middle))
    (hs : MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left middle right p q output)
    (hc : p = middle ∨ Znth p source_h 0 < Znth q source_h 0) :
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      (replace_Znth output (Znth q source_h 0) dest_h) (replace_Znth output (Znth q source_i 0) dest_i)
      left middle right p (q+1) (output+1) := by
  have hout : 0 ≤ output ∧ output < Zlength dest_h := ⟨by omega,by omega⟩
  have houti : 0 ≤ output ∧ output < Zlength dest_i := ⟨by omega,by omega⟩
  have heh : ∀ t, 0 ≤ t ∧ t < Zlength dest_h → t ≠ output →
      Znth t (replace_Znth output (Znth q source_h 0) dest_h) 0 = Znth t dest_h 0 := by
    intro t ht hn
    exact Znth_replace_Znth_Diff 0 dest_h output t _ hout ht (Ne.symm hn)
  have hei : ∀ t, 0 ≤ t ∧ t < Zlength dest_i → t ≠ output →
      Znth t (replace_Znth output (Znth q source_i 0) dest_i) 0 = Znth t dest_i 0 := by
    intro t ht hn
    exact Znth_replace_Znth_Diff 0 dest_i output t _ houti ht (Ne.symm hn)
  have heq := Znth_replace_Znth_Same 0 dest_h output (Znth q source_h 0) hout
  obtain ⟨hd1,hd2,houtside,hperm,hdescending,hpending⟩ := hs
  refine ⟨hd1,hd2,?_,?_,?_,?_⟩
  · intro t ht hregion
    rw [heh t ⟨ht.1,by omega⟩ (by omega),hei t ⟨ht.1,by omega⟩ (by omega)]
    apply houtside t ht
    rcases hregion with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rw [zip_write_extend dest_h dest_i left output _ _ ⟨hl,by omega⟩ hout.2 houti.2]
    rw [zip_extend source_h source_i middle q ⟨by omega,by omega⟩ (by omega) (by omega)]
    simpa only [List.append_assoc] using hperm.append_right [(Znth q source_h 0,Znth q source_i 0)]
  · intro u v hu huv hv
    by_cases hvo : v = output
    · subst v
      by_cases huo : u = output
      · subst u; exact le_refl _
      · rw [heq,heh u ⟨by omega,by omega⟩ huo]
        apply hpending u q ⟨hu,by omega⟩
        exact Or.inr ⟨by omega,by omega⟩
    · rw [heh v ⟨by omega,by omega⟩ hvo,heh u ⟨by omega,by omega⟩ (by omega)]
      exact hdescending u v hu huv (by omega)
  · intro u v hu hv
    by_cases huo : u = output
    · subst u
      rw [heq]
      rcases hv with hv | hv
      · rcases hc with hc | hc
        · omega
        · exact (hd1.2.2.2 p v hlp hv.1 hv.2).trans (le_of_lt hc)
      · exact hd2.2.2.2 q v hmq (by omega) hv.2
    · rw [heh u ⟨by omega,by omega⟩ huo]
      apply hpending u v ⟨hu.1,by omega⟩
      rcases hv with hv | hv
      · exact Or.inl ⟨by omega,hv.2⟩
      · exact Or.inr ⟨by omega,hv.2⟩

theorem merge_prefix_finish__merge_core (source_h source_i dest0_h dest0_i dest_h dest_i : List Int)
    (left middle right : Int)
    (hsi : Zlength source_i = Zlength source_h) (hd0h : Zlength dest0_h = Zlength source_h)
    (hd0i : Zlength dest0_i = Zlength source_h) (hdh : Zlength dest_h = Zlength dest0_h)
    (hdi : Zlength dest_i = Zlength dest0_i) (hl : 0 ≤ left) (hm : left ≤ middle)
    (hmr : middle ≤ right) (hr : right ≤ Zlength source_h)
    (hs : MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left middle right middle right right) :
    HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h dest_i left middle right := by
  refine ⟨hl,hm,hmr,hr,⟨hdh,hdi,hs.2.2.1⟩,?_,hl,by omega,by omega,hs.2.2.2.2.1⟩
  rw [combine_sublist_split__sort_copy source_h source_i left middle right hsi.symm ⟨hl,hm⟩ hmr hr]
  exact hs.2.2.2.1

theorem range_sort_left_desc__sort_recursion (work0_h work0_i work_mid_h work_mid_i work_h work_i : List Int)
    (left middle right : Int)
    (hleft : HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left middle)
    (hright : HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right) :
    HeightIndexRangeDescendingNLogN work_h left middle := by
  have hd := hleft.2.2.2.2.2.2.2
  have he := hright.2.2.2.2.2.1
  refine ⟨hd.1,hd.2.1,by have := he.1; have := hd.2.2.1; omega,?_⟩
  intro p q hp hpq hq
  have hl := hd.1
  rw [(he.2.2 p ⟨by omega,by have := hd.2.2.1; omega⟩ (Or.inl (by omega))).1,
      (he.2.2 q ⟨by omega,by have := hd.2.2.1; omega⟩ (Or.inl hq)).1]
  exact hd.2.2.2 p q hp hpq hq

theorem sort_range_after_merge_copy__sort_copy
    (before_h before_i mid_h mid_i work_h work_i buffer0_h buffer0_i buffer_h buffer_i out_h out_i : List Int)
    (left middle right : Int) (hoh : Zlength out_h = Zlength before_h) (hoi : Zlength out_i = Zlength before_i)
    (hbh : Zlength buffer_h = Zlength out_h) (hbi : Zlength buffer_i = Zlength out_i)
    (hl : HeightIndexRangeSortResultNLogN before_h before_i mid_h mid_i left middle)
    (hr : HeightIndexRangeSortResultNLogN mid_h mid_i work_h work_i middle right)
    (hm : HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left middle right)
    (hc : CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i out_h out_i left right right) :
    HeightIndexRangeSortResultNLogN before_h before_i out_h out_i left right := by
  obtain ⟨hbefore,hmid,hl0,hlm,hmb,⟨hmh,hmi,hol⟩,hpl,hdl⟩ := hl
  obtain ⟨hmid',hwork,hm0,hmr,hrm,⟨hwh,hwi,hor⟩,hpr,hdr⟩ := hr
  obtain ⟨hml0,hmlm,hmmr,hrw,hom,hpm,hdm⟩ := hm
  have heh := sublist_eq_by_Znth__sort_copy Int out_h buffer_h left right 0 hbh.symm ⟨hl0,by omega⟩ (by omega) (fun p hp => (hc.1 p hp).1)
  have hei := sublist_eq_by_Znth__sort_copy Int out_i buffer_i left right 0 hbi.symm ⟨hl0,by omega⟩ (by omega) (fun p hp => (hc.1 p hp).2)
  have hwl := sublist_eq_by_Znth__sort_copy Int work_h mid_h left middle 0 hwh ⟨hl0,hlm⟩ (by omega)
    (fun p hp => (hor p ⟨by omega,by omega⟩ (Or.inl hp.2)).1)
  have hwli := sublist_eq_by_Znth__sort_copy Int work_i mid_i left middle 0 hwi ⟨hl0,hlm⟩ (by omega)
    (fun p hp => (hor p ⟨by omega,by omega⟩ (Or.inl hp.2)).2)
  have hbr := sublist_eq_by_Znth__sort_copy Int mid_h before_h middle right 0 hmh ⟨hm0,hmr⟩ hrm
    (fun p hp => (hol p ⟨by omega,by omega⟩ (Or.inr hp.1)).1)
  have hbri := sublist_eq_by_Znth__sort_copy Int mid_i before_i middle right 0 hmi ⟨hm0,hmr⟩ (by omega)
    (fun p hp => (hol p ⟨by omega,by omega⟩ (Or.inr hp.1)).2)
  have hp : (sublist left right work_h).zip (sublist left right work_i) |>.Perm
      ((sublist left right before_h).zip (sublist left right before_i)) := by
    rw [combine_sublist_split__sort_copy work_h work_i left middle right hwork ⟨hl0,hlm⟩ hmr hrw,
        combine_sublist_split__sort_copy before_h before_i left middle right hbefore ⟨hl0,hlm⟩ hmr (by omega)]
    rw [hwl,hwli,← hbr,← hbri]
    exact hpl.append hpr
  refine ⟨hbefore,by omega,hl0,by omega,by omega,⟨hoh,hoi,?_⟩,?_,hdm.1,hdm.2.1,by omega,?_⟩
  · intro p hp hreg
    have hpw : 0 ≤ p ∧ p < Zlength work_h := ⟨hp.1,by omega⟩
    have hregR : p < middle ∨ right ≤ p := by rcases hreg with h | h; exact Or.inl (by omega); exact Or.inr h
    have hregL : p < left ∨ middle ≤ p := by rcases hreg with h | h; exact Or.inl h; exact Or.inr (by omega)
    exact ⟨(hc.2 p hpw hreg).1.trans ((hor p ⟨hp.1,by omega⟩ hregR).1.trans (hol p hp hregL).1),
      (hc.2 p hpw hreg).2.trans ((hor p ⟨hp.1,by omega⟩ hregR).2.trans (hol p hp hregL).2)⟩
  · unfold HeightIndexRangePermutationNLogN
    rw [heh,hei]
    exact hpm.trans hp
  · intro p q hp hpq hq
    rw [(hc.1 p ⟨hp,by omega⟩).1,(hc.1 q ⟨by omega,hq⟩).1]
    exact hdm.2.2.2 p q hp hpq hq

theorem workspace_prefix_snoc__max_init (l heights indices : List Int) (k : Int)
    (hh : Zlength heights = k) (hi : Zlength indices = k) (hp : WorkspacePrefixNLogN l heights indices k)
    (hk : 0 ≤ k ∧ k < Zlength l) :
    Zlength (heights ++ [Znth k l 0]) = k+1 ∧ Zlength (indices ++ [k]) = k+1 ∧
    WorkspacePrefixNLogN l (heights ++ [Znth k l 0]) (indices ++ [k]) (k+1) := by
  refine ⟨by rw [Zlength_app,Zlength_cons,Zlength_nil,hh]; omega,by rw [Zlength_app,Zlength_cons,Zlength_nil,hi]; omega,?_,?_⟩
  · intro p hpk
    by_cases hlt : p < k
    · have he : Znth p (heights ++ [Znth k l 0]) 0 = Znth p heights 0 := ListLib.app_Znth1 0 heights _ p (by change 0 ≤ p ∧ p < Zlength heights; omega)
      rw [he]; exact hp.1 p ⟨hpk.1,hlt⟩
    · have he : p = k := by omega
      subst p
      rw [app_Znth2 0 heights _ k (by omega),hh]
      simp only [Int.sub_self,Znth0_cons]
  · intro p hpk
    by_cases hlt : p < k
    · have he : Znth p (indices ++ [k]) 0 = Znth p indices 0 := ListLib.app_Znth1 0 indices _ p (by change 0 ≤ p ∧ p < Zlength indices; omega)
      rw [he]; exact hp.2 p ⟨hpk.1,hlt⟩
    · have he : p = k := by omega
      subst p
      rw [app_Znth2 0 indices _ k (by omega),hi]
      simp only [Int.sub_self,Znth0_cons]

theorem workspace_prefix_complete__max_sort_boundary (l heights indices : List Int) (k heightSize : Int)
    (hlo : k ≥ heightSize) (hhi : k ≤ heightSize) (hh : Zlength heights = k) (hi : Zlength indices = k)
    (hp : WorkspacePrefixNLogN l heights indices k) :
    Zlength heights = heightSize ∧ Zlength indices = heightSize ∧ WorkspacePrefixNLogN l heights indices heightSize := by
  have he : k = heightSize := by omega
  exact ⟨hh.trans he,hi.trans he,he ▸ hp⟩

private theorem nth_pair_mem (xs ys : List Int) (p : Int) (hl : Zlength xs = Zlength ys)
    (hp : 0 ≤ p ∧ p < Zlength xs) : (Znth p xs 0,Znth p ys 0) ∈ xs.zip ys := by
  have hx : p.toNat < xs.length := by change 0 ≤ p ∧ p < (xs.length : Int) at hp; omega
  have hh : xs.length = ys.length := by change (xs.length : Int) = (ys.length : Int) at hl; omega
  have hy : p.toNat < ys.length := by omega
  change (xs.getD p.toNat 0,ys.getD p.toNat 0) ∈ xs.zip ys
  rw [List.getD_eq_getElem xs 0 hx,List.getD_eq_getElem ys 0 hy]
  have hz : p.toNat < (xs.zip ys).length := by simp only [List.length_zip]; omega
  simpa only [List.getElem_zip] using List.getElem_mem (l := xs.zip ys) hz

theorem sorted_workspace_lookup__max_loop_setup (l sorted_h sorted_i : List Int) (k : Int)
    (hs : SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) (hk : 0 ≤ k ∧ k < Zlength l) :
    (0 ≤ Znth k sorted_i 0 ∧ Znth k sorted_i 0 < Zlength l) ∧
    Znth k sorted_h 0 = Znth (Znth k sorted_i 0) l 0 := by
  have hp := nth_pair_mem sorted_h sorted_i k (hs.1.1.trans hs.1.2.1.symm) ⟨hk.1,by rw [hs.1.1]; exact hk.2⟩
  have hm := hs.1.2.2.mem_iff.mp hp
  obtain ⟨m,hm,he⟩ := List.mem_map.mp hm
  have hmb := List.mem_range.mp hm
  have hi := congrArg Prod.snd he
  have hh := congrArg Prod.fst he
  dsimp only at hi hh
  rw [← hi,← hh]
  refine ⟨⟨by omega,?_⟩,?_⟩
  · change (m : Int) < (l.length : Int); omega
  · simp [Znth]

theorem sorted_index_bounds__max_init (l heights indices : List Int) (k : Int)
    (hs : SortedHeightIndexWorkspaceNLogN l heights indices) (hk : 0 ≤ k ∧ k < Zlength l) :
    0 ≤ Znth k indices 0 ∧ Znth k indices 0 < Zlength l := (sorted_workspace_lookup__max_loop_setup l heights indices k hs hk).1

theorem sorted_workspace_lookup__max_width_selection (l heights indices : List Int) (k : Int)
    (hs : SortedHeightIndexWorkspaceNLogN l heights indices) (hk : 0 ≤ k ∧ k < Zlength l) :
    (0 ≤ Znth k indices 0 ∧ Znth k indices 0 < Zlength l) ∧ Znth k heights 0 = Znth (Znth k indices 0) l 0 :=
  sorted_workspace_lookup__max_loop_setup l heights indices k hs hk

theorem sorted_workspace_lookup__max_endpoint_a (l heights indices : List Int) (k : Int)
    (hs : SortedHeightIndexWorkspaceNLogN l heights indices) (hk : 0 ≤ k ∧ k < Zlength heights) :
    (0 ≤ Znth k indices 0 ∧ Znth k indices 0 < Zlength l) ∧ Znth k heights 0 = Znth (Znth k indices 0) l 0 :=
  sorted_workspace_lookup__max_loop_setup l heights indices k hs ⟨hk.1,by rw [← hs.1.1]; exact hk.2⟩

theorem sorted_workspace_lookup__max_endpoint_b (l heights indices : List Int) (p k : Int)
    (hs : SortedHeightIndexWorkspaceNLogN l heights indices) (hp : 0 ≤ p ∧ p ≤ k) (hk : k < Zlength l) :
    (0 ≤ Znth p indices 0 ∧ Znth p indices 0 < Zlength l) ∧
    Znth p heights 0 = Znth (Znth p indices 0) l 0 ∧ Znth k heights 0 ≤ Znth p heights 0 := by
  have hl := sorted_workspace_lookup__max_loop_setup l heights indices p hs ⟨hp.1,by omega⟩
  exact ⟨hl.1,hl.2,hs.2.2.2.2 p k hp.1 hp.2 (by rw [hs.1.1]; exact hk)⟩

theorem workspace_prefix_indexed__max_loop_setup (l heights indices : List Int) (n : Int)
    (hl : Zlength l = n) (hh : Zlength heights = n) (hi : Zlength indices = n)
    (hp : WorkspacePrefixNLogN l heights indices n) : heights.zip indices = IndexedHeightsNLogN l := by
  have hh' : heights.length = l.length := by change (heights.length : Int) = n at hh; change (l.length : Int) = n at hl; omega
  have hi' : indices.length = l.length := by change (indices.length : Int) = n at hi; change (l.length : Int) = n at hl; omega
  apply List.ext_getElem
  · simp [IndexedHeightsNLogN,hh',hi']
  · intro k hk hk'
    have hk0 : k < l.length := by simpa [List.length_zip,hh',hi'] using hk
    have hkr : 0 ≤ (k : Int) ∧ (k : Int) < n := by change (l.length : Int) = n at hl; omega
    have hhp := hp.1 k hkr
    have hip := hp.2 k hkr
    change heights.getD k 0 = l.getD k 0 at hhp
    change indices.getD k 0 = (k : Int) at hip
    rw [List.getD_eq_getElem heights 0 (by omega),List.getD_eq_getElem l 0 hk0] at hhp
    rw [List.getD_eq_getElem indices 0 (by omega)] at hip
    simp only [List.getElem_zip,IndexedHeightsNLogN,List.getElem_map,List.getElem_range,hhp,hip]
    rw [List.getD_eq_getElem l 0 hk0]

theorem full_sort_workspace__max_loop_setup (l work0_h work0_i work_h work_i : List Int) (n : Int)
    (hl : Zlength l = n) (h0h : Zlength work0_h = n) (h0i : Zlength work0_i = n)
    (hp : WorkspacePrefixNLogN l work0_h work0_i n)
    (hs : HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i 0 n) :
    SortedHeightIndexWorkspaceNLogN l work_h work_i := by
  have hwh : Zlength work_h = n := hs.2.2.2.2.2.1.1.trans h0h
  have hwi : Zlength work_i = n := hs.2.2.2.2.2.1.2.1.trans h0i
  have hperm := hs.2.2.2.2.2.2.1
  unfold HeightIndexRangePermutationNLogN at hperm
  rw [sublist_self work_h n hwh.symm,sublist_self work_i n hwi.symm,
      sublist_self work0_h n h0h.symm,sublist_self work0_i n h0i.symm,
      workspace_prefix_indexed__max_loop_setup l work0_h work0_i n hl h0h h0i hp] at hperm
  exact ⟨⟨hwh.trans hl.symm,hwi.trans hl.symm,hperm⟩,by rw [hwh]; exact hs.2.2.2.2.2.2.2⟩

theorem in_prefix_iff_position__max_endpoint_b (A : Type) (l : List A) (d x : A) (k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength l) :
    x ∈ sublist 0 k l ↔ ∃ p, (0 ≤ p ∧ p < k) ∧ Znth p l d = x := by
  have hlen : Zlength (sublist 0 k l) = k := by simpa only [Int.sub_zero] using sublen l 0 k ⟨le_refl _,hk.1⟩ hk.2
  constructor
  · intro hx
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
    have hir : 0 ≤ (i : Int) ∧ (i : Int) < k := by change ((sublist 0 k l).length : Int) = k at hlen; omega
    refine ⟨i,hir,?_⟩
    have hh : Znth (i : Int) (sublist 0 k l) d = x := by
      change (sublist 0 k l).getD i d = x
      rw [List.getD_eq_getElem _ d hi,he]
    simpa only [Znth_sublist d 0 i k l (le_refl _) (by omega),Int.add_zero] using hh
  · rintro ⟨p,hp,he⟩
    have hn : p.toNat < (sublist 0 k l).length := by change ((sublist 0 k l).length : Int) = k at hlen; omega
    have hh : Znth p (sublist 0 k l) d ∈ sublist 0 k l := by
      change (sublist 0 k l).getD p.toNat d ∈ _
      rw [List.getD_eq_getElem _ d hn]
      exact List.getElem_mem hn
    simpa only [Znth_sublist d 0 p k l (le_refl _) (by omega),Int.add_zero,he] using hh

theorem processed_maximum_initial__max_loop_setup (l indices : List Int) (hlen : 1 ≤ Zlength indices) :
    ProcessedContainerMaximumNLogN l indices 1 0 := by
  right
  refine ⟨?_,rfl⟩
  intro ij hp
  have hi := (in_prefix_iff_position__max_endpoint_b Int indices 0 ij.1 1 ⟨by omega,hlen⟩).mp hp.2.1
  have hj := (in_prefix_iff_position__max_endpoint_b Int indices 0 ij.2 1 ⟨by omega,hlen⟩).mp hp.2.2
  obtain ⟨p,hp',hep⟩ := hi
  obtain ⟨q,hq',heq⟩ := hj
  have hp0 : p=0 := by omega
  have hq0 : q=0 := by omega
  rw [hp0] at hep
  rw [hq0] at heq
  have hh := hp.1.2.1
  omega

theorem processed_endpoint_bounds__max_width_selection (indices : List Int) (k minimum maximum n : Int)
    (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (hb : ∀ p, 0 ≤ p ∧ p < k → 0 ≤ Znth p indices 0 ∧ Znth p indices 0 < n) :
    0 ≤ minimum ∧ minimum ≤ maximum ∧ maximum < n := by
  obtain ⟨⟨p,hp,hmin⟩,⟨q,hq,hmax⟩,hall⟩ := he
  have hpb := hb p hp
  have hqb := hb q hq
  have hpp := hall p hp
  omega

theorem processed_pair_extend__max_area_update_a (l indices : List Int) (k : Int) (ij : Int × Int)
    (hk : 0 ≤ k) (hl : k < Zlength indices) :
    ProcessedContainerPairNLogN l indices (k+1) ij ↔ ContainerPairNLogN l ij.1 ij.2 ∧
      (ij.1 ∈ sublist 0 k indices ∨ ij.1 = Znth k indices 0) ∧
      (ij.2 ∈ sublist 0 k indices ∨ ij.2 = Znth k indices 0) := by
  unfold ProcessedContainerPairNLogN
  rw [sublist_split 0 (k+1) k indices ⟨le_refl _,hk⟩ ⟨by omega,by omega⟩,
      sublist_single 0 k indices ⟨hk,hl⟩]
  simp only [List.mem_append,List.mem_singleton]

theorem processed_endpoints_extend__max_endpoint_b (indices : List Int) (k minimum maximum : Int)
    (hk : 0 ≤ k) (he : ProcessedIndexEndpointsNLogN indices k minimum maximum) :
    ProcessedIndexEndpointsNLogN indices (k+1) (min minimum (Znth k indices 0)) (max maximum (Znth k indices 0)) := by
  obtain ⟨⟨p,hp,hmin⟩,⟨q,hq,hmax⟩,hall⟩ := he
  refine ⟨?_,?_,?_⟩
  · by_cases h : minimum ≤ Znth k indices 0
    · exact ⟨p,⟨hp.1,by omega⟩,by rw [min_eq_left h]; exact hmin⟩
    · exact ⟨k,⟨hk,by omega⟩,by rw [min_eq_right (by omega)]⟩
  · by_cases h : maximum ≤ Znth k indices 0
    · exact ⟨k,⟨hk,by omega⟩,by rw [max_eq_right h]⟩
    · exact ⟨q,⟨hq.1,by omega⟩,by rw [max_eq_left (by omega)]; exact hmax⟩
  · intro r hr
    by_cases h : r=k
    · subst r; exact ⟨min_le_right _ _,le_max_right _ _⟩
    · have hh := hall r ⟨hr.1,by omega⟩
      exact ⟨(min_le_left _ _).trans hh.1,hh.2.trans (le_max_left _ _)⟩

theorem processed_endpoints_extend__max_endpoint_a (indices : List Int) (k minimum maximum index new_min new_max : Int)
    (hk : 1 ≤ k) (hl : k < Zlength indices) (hi : index = Znth k indices 0)
    (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (hc : (index < minimum ∧ new_min = index ∧ new_max = maximum) ∨
      (maximum < index ∧ new_min = minimum ∧ new_max = index) ∨
      ((minimum ≤ index ∧ index ≤ maximum) ∧ new_min = minimum ∧ new_max = maximum)) :
    ProcessedIndexEndpointsNLogN indices (k+1) new_min new_max := by
  have hh := processed_endpoints_extend__max_endpoint_b indices k minimum maximum (by omega) he
  obtain ⟨p,hp,hpmin⟩ := he.1
  have hmm := he.2.2 p hp
  rw [← hi] at hh
  rcases hc with ⟨hc,hmin,hmax⟩ | ⟨hc,hmin,hmax⟩ | ⟨hc,hmin,hmax⟩
  · simpa only [min_eq_right (by omega : index ≤ minimum),max_eq_left (by omega : index ≤ maximum),hmin,hmax] using hh
  · simpa only [min_eq_left (by omega : minimum ≤ index),max_eq_right (by omega : maximum ≤ index),hmin,hmax] using hh
  · simpa only [min_eq_left hc.1,max_eq_left hc.2,hmin,hmax] using hh

theorem processed_endpoints_extend__max_endpoint_d (indices : List Int) (k index minimum maximum : Int)
    (hk : 0 ≤ k) (hi : index = Znth k indices 0) (hb : minimum ≤ index ∧ index ≤ maximum)
    (he : ProcessedIndexEndpointsNLogN indices k minimum maximum) :
    ProcessedIndexEndpointsNLogN indices (k+1) minimum maximum := by
  have hh := processed_endpoints_extend__max_endpoint_b indices k minimum maximum hk he
  simpa only [← hi,min_eq_left hb.1,max_eq_left hb.2] using hh

theorem sorted_workspace_lookup__max_endpoint_d (indices : List Int) (k minimum maximum x : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength indices) (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (hx : x ∈ sublist 0 k indices) : minimum ≤ x ∧ x ≤ maximum := by
  obtain ⟨p,hp,hpx⟩ := (in_prefix_iff_position__max_endpoint_b Int indices 0 x k hk).mp hx
  rw [← hpx]
  exact he.2.2 p hp

theorem map_snd_combine__max_final_result (xs ys : List Int) (hl : Zlength xs = Zlength ys) :
    (xs.zip ys).map Prod.snd = ys := by
  have hh : xs.length = ys.length := by change (xs.length : Int) = (ys.length : Int) at hl; omega
  exact List.map_snd_zip (by omega)

theorem sorted_workspace_lookup__max_endpoint_c (l heights indices : List Int)
    (hs : SortedHeightIndexWorkspaceNLogN l heights indices) : indices.Nodup := by
  have hp := hs.1.2.2.map Prod.snd
  rw [map_snd_combine__max_final_result heights indices (hs.1.1.trans hs.1.2.1.symm)] at hp
  have he : (IndexedHeightsNLogN l).map Prod.snd = (List.range l.length).map (fun k : Nat => (k : Int)) := by simp [IndexedHeightsNLogN,List.map_map]
  rw [he] at hp
  exact hp.nodup_iff.mpr (List.nodup_range.map (fun _ _ h => by omega))

theorem processed_endpoint_fresh__max_endpoint_c (indices : List Int) (k minimum maximum index : Int)
    (hk : 0 ≤ k) (hl : k < Zlength indices) (hn : indices.Nodup) (hi : index = Znth k indices 0)
    (he : ProcessedIndexEndpointsNLogN indices k minimum maximum) : index ≠ minimum ∧ index ≠ maximum := by
  have hf : ∀ p, (0 ≤ p ∧ p < k) → Znth p indices 0 ≠ index := by
    intro p hp hh
    have hpn : p.toNat < indices.length := by change k < (indices.length : Int) at hl; omega
    have hkn : k.toNat < indices.length := by change k < (indices.length : Int) at hl; omega
    have hh' : indices.getD p.toNat 0 = indices.getD k.toNat 0 := hh.trans hi
    rw [List.getD_eq_getElem _ 0 hpn,List.getD_eq_getElem _ 0 hkn] at hh'
    have hnat := List.getElem?_inj (j := k.toNat) hpn hn (by simp [hpn,hkn,hh'])
    omega
  obtain ⟨p,hp,hpmin⟩ := he.1
  obtain ⟨q,hq,hqmax⟩ := he.2.1
  exact ⟨fun h => hf p hp (hpmin.trans h.symm),fun h => hf q hq (hqmax.trans h.symm)⟩

theorem processed_endpoints_extend__max_endpoint_c (l heights indices : List Int) (k minimum maximum index : Int)
    (hk : 0 ≤ k) (hl : k < Zlength l) (hs : SortedHeightIndexWorkspaceNLogN l heights indices)
    (hi : index = Znth k indices 0) (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (hx : index = minimum ∨ index = maximum) : ProcessedIndexEndpointsNLogN indices (k+1) minimum maximum := by
  have hf := processed_endpoint_fresh__max_endpoint_c indices k minimum maximum index hk (by rw [hs.1.2.1]; exact hl)
    (sorted_workspace_lookup__max_endpoint_c l heights indices hs) hi he
  exact False.elim (hx.elim hf.1 hf.2)

theorem processed_max_extend__max_endpoint_c (l heights indices : List Int) (k minimum maximum index oldans newans : Int)
    (hk : 0 ≤ k) (hl : k < Zlength l) (hs : SortedHeightIndexWorkspaceNLogN l heights indices)
    (hi : index = Znth k indices 0) (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (ho : ProcessedContainerMaximumNLogN l indices k oldans) (hx : index = minimum ∨ index = maximum) :
    ProcessedContainerMaximumNLogN l indices (k+1) newans := by
  have hf := processed_endpoint_fresh__max_endpoint_c indices k minimum maximum index hk (by rw [hs.1.2.1]; exact hl)
    (sorted_workspace_lookup__max_endpoint_c l heights indices hs) hi he
  exact False.elim (hx.elim hf.1 hf.2)

private theorem default_nonneg {A : Type} {P : A → Prop} {f : A → Int} {v : Int}
    (h : max_value_of_subset_with_default (· ≤ ·) P f 0 v) : 0 ≤ v := by
  rcases h with ⟨hm,hn⟩ | ⟨hb,he⟩
  · exact hn
  · omega

private theorem default_bound {A : Type} {P : A → Prop} {f : A → Int} {v : Int}
    (h : max_value_of_subset_with_default (· ≤ ·) P f 0 v) (x : A) (hx : P x) : f x ≤ v := by
  rcases h with ⟨⟨a,⟨ha,hb⟩,he⟩,hn⟩ | ⟨hb,he⟩
  · have hh := hb x hx
    dsimp only at he hh
    omega
  · have hh := hb x hx
    omega

private theorem default_extend {A : Type} {P Q : A → Prop} {f : A → Int} {v : Int}
    (h : max_value_of_subset_with_default (· ≤ ·) P f 0 v)
    (hi : ∀ x, P x → Q x) (hb : ∀ x, Q x → f x ≤ v) :
    max_value_of_subset_with_default (· ≤ ·) Q f 0 v := by
  rcases h with ⟨⟨a,⟨ha,haB⟩,he⟩,hn⟩ | ⟨haB,he⟩
  · left
    refine ⟨⟨a,⟨hi a ha,?_⟩,he⟩,hn⟩
    intro x hx
    have hh := hb x hx
    try dsimp only at he
    omega
  · right
    refine ⟨?_,he⟩
    intro x hx
    have hh := hb x hx
    omega

private theorem default_update {A : Type} {P Q : A → Prop} {f : A → Int} {v cap : Int}
    (h : max_value_of_subset_with_default (· ≤ ·) P f 0 v)
    (hi : ∀ x, P x → Q x) (hb : ∀ x, Q x → P x ∨ f x ≤ cap)
    (hc : v < cap → ∃ x, Q x ∧ f x = cap) :
    max_value_of_subset_with_default (· ≤ ·) Q f 0 (max v cap) := by
  have hn := default_nonneg h
  by_cases hcv : cap ≤ v
  · rw [max_eq_left hcv]
    apply default_extend h hi
    intro x hx
    rcases hb x hx with hx | hx
    · exact default_bound h x hx
    · omega
  · rw [max_eq_right (by omega)]
    obtain ⟨x,hx,he⟩ := hc (by omega)
    left
    refine ⟨⟨x,⟨hx,?_⟩,he⟩,by omega⟩
    intro y hy
    have hh : f y ≤ cap := by
      rcases hb y hy with hy | hy
      · have hh := default_bound h y hy
        omega
      · exact hy
    try dsimp only
    omega

private theorem pair_mono (l indices : List Int) (k : Int) (hk : 0 ≤ k ∧ k < Zlength indices)
    (ij : Int × Int) (hp : ProcessedContainerPairNLogN l indices k ij) :
    ProcessedContainerPairNLogN l indices (k+1) ij :=
  (processed_pair_extend__max_area_update_a l indices k ij hk.1 hk.2).mpr ⟨hp.1,Or.inl hp.2.1,Or.inl hp.2.2⟩

private theorem previous_lookup (l heights indices : List Int) (p k : Int)
    (hs : SortedHeightIndexWorkspaceNLogN l heights indices) (hp : 0 ≤ p ∧ p < k) (hk : k < Zlength l) :
    (0 ≤ Znth p indices 0 ∧ Znth p indices 0 < Zlength l) ∧
    Znth k heights 0 ≤ Znth (Znth p indices 0) l 0 := by
  have hh := sorted_workspace_lookup__max_endpoint_b l heights indices p k hs ⟨hp.1,by omega⟩ hk
  exact ⟨hh.1,hh.2.1 ▸ hh.2.2⟩

theorem processed_max_extend__max_endpoint_b (l heights indices : List Int)
    (k index currentHeight minimum maximum old width : Int)
    (hk : 1 ≤ k) (hkl : k < Zlength l) (hs : SortedHeightIndexWorkspaceNLogN l heights indices)
    (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (ho : ProcessedContainerMaximumNLogN l indices k old)
    (hi : index = Znth k indices 0) (hh : currentHeight = Znth k heights 0)
    (hc : currentHeight = Znth index l 0) (hcn : 0 ≤ currentHeight) (hwn : 0 ≤ width)
    (hw : ∀ x, minimum ≤ x ∧ x ≤ maximum → |x-index| ≤ width)
    (hwa : width = |minimum-index| ∨ width = |maximum-index|) :
    ProcessedContainerMaximumNLogN l indices (k+1) (max old (width*currentHeight)) := by
  have hki : 0 ≤ k ∧ k < Zlength indices := ⟨by omega,by rw [hs.1.2.1]; exact hkl⟩
  have hindex := (sorted_workspace_lookup__max_loop_setup l heights indices k hs ⟨by omega,hkl⟩).1
  rw [← hi] at hindex
  apply default_update ho (pair_mono l indices k hki)
  · intro ij hp
    obtain ⟨a,b⟩ := ij
    obtain ⟨hlegal,ha,hb⟩ := (processed_pair_extend__max_area_update_a l indices k (a,b) hki.1 hki.2).mp hp
    dsimp only at hlegal ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl ⟨hlegal,ha,hb⟩
    · right
      have hbe : b = index := hb.trans hi.symm
      rw [hbe] at hlegal ⊢
      obtain ⟨p,hp,hpa⟩ := (in_prefix_iff_position__max_endpoint_b Int indices 0 a k ⟨hki.1,by omega⟩).mp ha
      have hpv := previous_lookup l heights indices p k hs hp hkl
      rw [hpa,← hh] at hpv
      have hab := he.2.2 p hp
      rw [hpa] at hab
      have hwidth := hw a hab
      have hal : a < index := hlegal.2.1
      rw [abs_of_nonpos (by omega : a-index ≤ 0)] at hwidth
      dsimp only [ContainerAreaNLogN,ContainerHeightNLogN]
      rw [← hc,min_eq_right hpv.2]
      exact mul_le_mul_of_nonneg_right (by omega) hcn
    · right
      have hae : a = index := ha.trans hi.symm
      rw [hae] at hlegal ⊢
      obtain ⟨p,hp,hpb⟩ := (in_prefix_iff_position__max_endpoint_b Int indices 0 b k ⟨hki.1,by omega⟩).mp hb
      have hpv := previous_lookup l heights indices p k hs hp hkl
      rw [hpb,← hh] at hpv
      have hbb := he.2.2 p hp
      rw [hpb] at hbb
      have hwidth := hw b hbb
      have hbl : index < b := hlegal.2.1
      rw [abs_of_nonneg (by omega : 0 ≤ b-index)] at hwidth
      dsimp only [ContainerAreaNLogN,ContainerHeightNLogN]
      rw [← hc,min_eq_left hpv.2]
      exact mul_le_mul_of_nonneg_right hwidth hcn
    · have hab := hlegal.2.1
      omega
  · intro hcap
    have hold := default_nonneg ho
    have candidate : ∀ x p, (0 ≤ p ∧ p < k) → Znth p indices 0 = x → width = |x-index| →
        ∃ ij, ProcessedContainerPairNLogN l indices (k+1) ij ∧ ContainerAreaNLogN l ij.1 ij.2 = width*currentHeight := by
      intro x p hp hpx hwx
      have hpxv := previous_lookup l heights indices p k hs hp hkl
      rw [hpx,← hh] at hpxv
      have hxmem := (in_prefix_iff_position__max_endpoint_b Int indices 0 x k ⟨hki.1,by omega⟩).mpr ⟨p,hp,hpx⟩
      have hne : x ≠ index := by
        intro hxi
        rw [hxi,sub_self,abs_zero] at hwx
        rw [hwx] at hcap
        omega
      by_cases hxi : x < index
      · refine ⟨(x,index),?_,?_⟩
        · apply (processed_pair_extend__max_area_update_a l indices k (x,index) hki.1 hki.2).mpr
          exact ⟨⟨hpxv.1.1,hxi,hindex.2⟩,Or.inl hxmem,Or.inr hi⟩
        · dsimp only [ContainerAreaNLogN,ContainerHeightNLogN]
          rw [← hc,min_eq_right hpxv.2,hwx,abs_of_nonpos (by omega : x-index ≤ 0)]
          congr 1 <;> omega
      · refine ⟨(index,x),?_,?_⟩
        · apply (processed_pair_extend__max_area_update_a l indices k (index,x) hki.1 hki.2).mpr
          exact ⟨⟨hindex.1,by omega,hpxv.1.2⟩,Or.inr hi,Or.inl hxmem⟩
        · dsimp only [ContainerAreaNLogN,ContainerHeightNLogN]
          rw [← hc,min_eq_left hpxv.2,hwx,abs_of_nonneg (by omega : 0 ≤ x-index)]
    rcases hwa with hwa | hwa
    · obtain ⟨p,hp,hpm⟩ := he.1
      exact candidate minimum p hp hpm hwa
    · obtain ⟨p,hp,hpm⟩ := he.2.1
      exact candidate maximum p hp hpm hwa

theorem processed_max_extend__max_endpoint_a (l heights indices : List Int)
    (k index currentHeight minimum maximum width oldMaximum : Int)
    (hs : SortedHeightIndexWorkspaceNLogN l heights indices)
    (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (ho : ProcessedContainerMaximumNLogN l indices k oldMaximum)
    (hk : 1 ≤ k) (hkl : k < Zlength l) (hi : index = Znth k indices 0)
    (hh : currentHeight = Znth k heights 0) (hcn : 0 ≤ currentHeight)
    (hw : (maximum < index ∧ width = index-minimum) ∨ (index < minimum ∧ width = maximum-index)) :
    ProcessedContainerMaximumNLogN l indices (k+1) (max oldMaximum (width*currentHeight)) := by
  have hl := sorted_workspace_lookup__max_loop_setup l heights indices k hs ⟨by omega,hkl⟩
  have hcurrent : currentHeight = Znth index l 0 := by rw [hh,hi]; exact hl.2
  obtain ⟨p,hp,hpm⟩ := he.1
  have hmm := he.2.2 p hp
  apply processed_max_extend__max_endpoint_b l heights indices k index currentHeight minimum maximum oldMaximum width hk hkl hs he ho hi hh hcurrent hcn
  · rcases hw with hw | hw <;> omega
  · intro x hx
    rcases hw with hw | hw
    · rw [abs_of_nonpos (by omega : x-index ≤ 0)]; omega
    · rw [abs_of_nonneg (by omega : 0 ≤ x-index)]; omega
  · rcases hw with hw | hw
    · left; rw [abs_of_nonpos (by omega : minimum-index ≤ 0)]; omega
    · right; rw [abs_of_nonneg (by omega : 0 ≤ maximum-index)]; exact hw.2

theorem processed_max_extend__max_endpoint_d (l indices : List Int)
    (k index currentHeight minimum maximum width maximumArea : Int)
    (hk : 0 ≤ k ∧ k < Zlength indices) (hi : index = Znth k indices 0)
    (hh : currentHeight = Znth index l 0) (hcn : 0 ≤ currentHeight) (hwn : 0 ≤ width)
    (hb : minimum ≤ index ∧ index ≤ maximum) (hleft : index-minimum ≤ width) (hright : maximum-index ≤ width)
    (he : ProcessedIndexEndpointsNLogN indices k minimum maximum)
    (ho : ProcessedContainerMaximumNLogN l indices k maximumArea) (hcap : width*currentHeight ≤ maximumArea) :
    ProcessedContainerMaximumNLogN l indices (k+1) maximumArea := by
  apply default_extend ho (pair_mono l indices k hk)
  intro ij hp
  obtain ⟨i,j⟩ := ij
  obtain ⟨hlegal,him,hjm⟩ := (processed_pair_extend__max_area_update_a l indices k (i,j) hk.1 hk.2).mp hp
  rcases him with him | him <;> rcases hjm with hjm | hjm
  · exact default_bound ho (i,j) ⟨hlegal,him,hjm⟩
  · have hji : j = index := hjm.trans hi.symm
    rw [hji] at hlegal ⊢
    have hib := sorted_workspace_lookup__max_endpoint_d indices k minimum maximum i ⟨hk.1,by omega⟩ he him
    change ContainerAreaNLogN l i index ≤ maximumArea
    dsimp only [ContainerAreaNLogN,ContainerHeightNLogN]
    rw [← hh]
    have hn : 0 ≤ index-i := by have := hlegal.2.1; omega
    exact ((mul_le_mul_of_nonneg_left (min_le_right _ _) hn).trans (mul_le_mul_of_nonneg_right (by omega) hcn)).trans hcap
  · have hii : i = index := him.trans hi.symm
    rw [hii] at hlegal ⊢
    have hjb := sorted_workspace_lookup__max_endpoint_d indices k minimum maximum j ⟨hk.1,by omega⟩ he hjm
    change ContainerAreaNLogN l index j ≤ maximumArea
    dsimp only [ContainerAreaNLogN,ContainerHeightNLogN]
    rw [← hh]
    have hn : 0 ≤ j-index := by have := hlegal.2.1; omega
    exact ((mul_le_mul_of_nonneg_left (min_le_left _ _) hn).trans (mul_le_mul_of_nonneg_right (by omega) hcn)).trans hcap
  · have hlt := hlegal.2.1
    dsimp only at him hjm hlt
    omega

theorem original_pair_in_indexed__max_final_result (l : List Int) (p : Int) (hp : 0 ≤ p ∧ p < Zlength l) :
    (Znth p l 0,p) ∈ IndexedHeightsNLogN l := by
  apply List.mem_map.mpr
  refine ⟨p.toNat,List.mem_range.mpr ?_,?_⟩
  · change 0 ≤ p ∧ p < (l.length : Int) at hp
    omega
  · change (l.getD p.toNat 0,(p.toNat : Int)) = (l.getD p.toNat 0,p)
    rw [Int.toNat_of_nonneg hp.1]

theorem original_index_in_indices__max_final_result (l heights indices : List Int) (p : Int)
    (hp : HeightIndexPermutationNLogN l heights indices) (hr : 0 ≤ p ∧ p < Zlength l) : p ∈ indices := by
  have hi := hp.2.2.mem_iff.mpr (original_pair_in_indexed__max_final_result l p hr)
  have hh : p ∈ (heights.zip indices).map Prod.snd := List.mem_map.mpr ⟨(Znth p l 0,p),hi,rfl⟩
  rw [map_snd_combine__max_final_result heights indices (hp.1.trans hp.2.1.symm)] at hh
  exact hh

theorem in_sublist_full__max_final_result (A : Type) (l : List A) (n : Int) (x : A)
    (hn : Zlength l = n) (hx : x ∈ l) : x ∈ sublist 0 n l := by
  rw [sublist_self l n hn.symm]
  exact hx

theorem original_pair_processed_full__max_final_result (l heights indices : List Int) (i j : Int)
    (hp : HeightIndexPermutationNLogN l heights indices) (hr : ContainerPairNLogN l i j) :
    ProcessedContainerPairNLogN l indices (Zlength l) (i,j) := by
  refine ⟨hr,?_,?_⟩
  · exact in_sublist_full__max_final_result Int indices (Zlength l) i hp.2.1
      (original_index_in_indices__max_final_result l heights indices i hp ⟨hr.1,by have := hr.2.1; have := hr.2.2; omega⟩)
  · exact in_sublist_full__max_final_result Int indices (Zlength l) j hp.2.1
      (original_index_in_indices__max_final_result l heights indices j hp ⟨by have := hr.1; have := hr.2.1; omega,hr.2.2⟩)

theorem processed_full_prefix_maximum__max_final_result (l heights indices : List Int) (ans : Int)
    (hl : 2 ≤ Zlength l) (hp : HeightIndexPermutationNLogN l heights indices)
    (hm : ProcessedContainerMaximumNLogN l indices (Zlength l) ans)
    (hn : ∀ p, 0 ≤ p ∧ p < Zlength l → 0 ≤ Znth p l 0) : MaximumContainerArea l ans := by
  have hbound : ∀ i j, ContainerPairNLogN l i j → ContainerAreaNLogN l i j ≤ ans := by
    intro i j hr
    exact default_bound hm (i,j) (original_pair_processed_full__max_final_result l heights indices i j hp hr)
  rcases hm with ⟨⟨⟨i,j⟩,⟨hm,hb⟩,he⟩,ha⟩ | ⟨hb,he⟩
  · exact ⟨i,j,hm.1.1,hm.1.2.1,hm.1.2.2,he.symm,fun p q hp hpq hq => hbound p q ⟨hp,hpq,hq⟩⟩
  · have he0 : ans = 0 := he.symm
    have hz := hbound 0 1 ⟨le_refl _,by omega,by omega⟩
    have h0 := hn 0 ⟨le_refl _,by omega⟩
    have h1 := hn 1 ⟨by omega,by omega⟩
    have hmin : 0 ≤ min (Znth 0 l 0) (Znth 1 l 0) := le_min h0 h1
    refine ⟨0,1,le_refl _,by omega,by omega,?_,fun p q hp hpq hq => hbound p q ⟨hp,hpq,hq⟩⟩
    dsimp only [ContainerAreaNLogN,ContainerHeightNLogN] at hz
    rw [Int.sub_zero,Int.one_mul] at hz ⊢
    omega

end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_lib
