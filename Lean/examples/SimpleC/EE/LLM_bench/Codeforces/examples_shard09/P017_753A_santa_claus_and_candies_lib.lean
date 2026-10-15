import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import AUXLib.ListLib.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Lift

set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib
open AUXLib


open MaxMinLib

def CandyAllocation (n : Int) (xs : List Int) : Prop :=
  Forall (fun x => x > 0) xs ∧ xs.Nodup ∧ xs.foldr (· + ·) 0 = n
def Pre (n : Int) : Prop := True
def Spec (n : Int) (out : List Int) : Prop :=
  max_object_of_subset (· ≤ ·) (CandyAllocation n) (fun ys => Zlength ys) out

def triangular (k : Int) : Int := Z.div (k * (k + 1)) 2

def CandyPrefix (i : Int) (xs : List Int) : Prop :=
  Zlength xs = i ∧ ∀ j, (0 ≤ j ∧ j < i) → Znth j xs 0 = j + 1

def GreedyCandyPlan (n k : Int) (xs : List Int) : Prop :=
  Zlength xs = k ∧ (∀ j, (0 ≤ j ∧ j < k - 1) → Znth j xs 0 = j + 1) ∧
  Znth (k - 1) xs 0 = k + (n - triangular k)

private theorem nth_app_left (xs ys : List Int) (j : Int) (hj : 0≤j ∧ j<Zlength xs) :
    Znth j (xs++ys) 0=Znth j xs 0 := by
  have hn : j.toNat<xs.length := by
    have he : Int.ofNat j.toNat=j := Int.toNat_of_nonneg hj.1
    apply Int.ofNat_lt.mp
    change Int.ofNat j.toNat<Int.ofNat xs.length
    rw [he]
    exact hj.2
  change (xs++ys).getD j.toNat 0=xs.getD j.toNat 0
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

theorem candy_prefix_last_value__arithmetic_and_prefix (i : Int) (xs : List Int) :
    CandyPrefix i xs → 1≤i → Znth (i-1) xs 0=i := by
  rintro ⟨hl,hv⟩ hi
  have h := hv (i-1) ⟨by omega,by omega⟩
  omega

theorem candy_prefix_snoc__arithmetic_and_prefix (i : Int) (xs : List Int) :
    CandyPrefix i xs → 0≤i → CandyPrefix (i+1) (xs++[i+1]) := by
  rintro ⟨hl,hv⟩ hi
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil,hl]; omega,?_⟩
  intro j hj
  by_cases hjl : j<i
  · rw [nth_app_left xs [i+1] j ⟨hj.1,by omega⟩]
    exact hv j ⟨hj.1,hjl⟩
  · have he : j=i := by omega
    subst j
    rw [app_Znth2 0 xs [i+1] i (by omega),hl,sub_self,Znth0_cons]

theorem triangular_succ__greedy_finalization (k : Int) : triangular (k+1)=triangular k+(k+1) := by
  unfold triangular Z.div
  rw [show (k+1)*(k+1+1)=k*(k+1)+(k+1)*2 by ring,Int.add_mul_fdiv_right _ _ (by decide)]

theorem triangular_monotone_nonneg__greedy_finalization (a b : Int) :
    (0≤a ∧ a≤b) → triangular a≤triangular b := by
  intro hab
  unfold triangular Z.div
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0:Int)≤2)]
  apply Int.ediv_le_ediv (by omega)
  nlinarith

/- Coq SumLib.Sum.sum restricted to the integer interval [lo, hi) is represented
   by the finite sum over Finset.Ico lo hi. Integer endpoints are retained,
   including negative and empty intervals. These two lemmas verify its empty
   and right-successor equations; the source theorem keeps its 0 ≤ k premise. -/
noncomputable def integer_range_sum (lo hi : Int) (f : Int→Int) : Int :=
  ∑ i ∈ Finset.Ico lo hi, f i

theorem integer_range_sum_empty (lo hi : Int) (f : Int→Int) (h : hi≤lo) :
    integer_range_sum lo hi f=0 := by
  simp only [integer_range_sum,Finset.Ico_eq_empty_of_le h,Finset.sum_empty]

theorem integer_range_sum_succ (lo hi : Int) (f : Int→Int) (h : lo≤hi) :
    integer_range_sum lo (hi+1) f=integer_range_sum lo hi f+f hi := by
  have he : Finset.Ico lo (hi+1)=insert hi (Finset.Ico lo hi) := by
    ext i
    simp only [Finset.mem_Ico,Finset.mem_insert]
    omega
  unfold integer_range_sum
  rw [he,Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
  omega

theorem sum_range_succ__greedy_finalization (k : Int) : 0≤k →
    integer_range_sum 0 k (fun i => i+1)=triangular k := by
  intro hk
  lift k to Nat using hk
  induction k with
  | zero => change integer_range_sum 0 0 (fun i => i+1)=triangular 0; rw [integer_range_sum_empty 0 0 _ (le_refl _)]; rfl
  | succ k ih =>
    have hc : ((k+1:Nat):Int)=(k:Int)+1 := by omega
    rw [hc,integer_range_sum_succ 0 (k:Int) _ (by omega),ih,triangular_succ__greedy_finalization]

private theorem linear_sum (xs : List Int) (b : Int)
    (h : ∀ j, (0≤j ∧ j<Zlength xs) → Znth j xs 0=b+j) :
    xs.foldr (·+·) 0=Zlength xs*b+triangular (Zlength xs-1) := by
  induction xs generalizing b with
  | nil => change 0=0*b+triangular (-1); simp only [zero_mul,zero_add]; rfl
  | cons a xs ih =>
    have hn := Zlength_nonneg xs
    have hh := h 0 (by simp only [Zlength_cons]; omega)
    simp only [Znth0_cons,add_zero] at hh
    have ht := ih (b+1) (by
      intro j hj
      have hv := h (j+1) (by simp only [Zlength_cons]; omega)
      rw [Znth_cons 0 (j+1) a xs (by omega),add_sub_cancel_right] at hv
      omega)
    have htri := triangular_succ__greedy_finalization (Zlength xs-1)
    simp only [sub_add_cancel] at htri
    simp only [List.foldr_cons,Zlength_cons,add_sub_cancel_right]
    rw [ht,htri]
    nlinarith

theorem candy_prefix_sum__greedy_finalization (k : Int) (xs : List Int) :
    0≤k → CandyPrefix k xs → xs.foldr (·+·) 0=triangular k := by
  rintro hk ⟨hl,hv⟩
  have h := linear_sum xs 1 (fun j hj => by have hh := hv j (by omega); omega)
  have ht := triangular_succ__greedy_finalization (k-1)
  simp only [sub_add_cancel] at ht
  rw [hl] at h
  nlinarith

theorem sum_replace_Znth__greedy_finalization (xs : List Int) (i v : Int) :
    (0≤i ∧ i<Zlength xs) → (replace_Znth i v xs).foldr (·+·) 0=xs.foldr (·+·) 0-Znth i xs 0+v := by
  induction xs generalizing i with
  | nil => intro hi; simp only [Zlength_nil] at hi; omega
  | cons a xs ih =>
    intro hi
    simp only [Zlength_cons] at hi
    by_cases he : i=0
    · subst i
      change v+xs.foldr (·+·) 0=a+xs.foldr (·+·) 0-a+v
      omega
    · rw [replace_Znth_cons i v a xs (by omega),Znth_cons 0 i a xs (by omega)]
      simp only [List.foldr_cons]
      rw [ih (i-1) ⟨by omega,by omega⟩]
      omega

theorem sum_permutation__greedy_finalization (xs ys : List Int) :
    List.Perm xs ys → xs.foldr (·+·) 0=ys.foldr (·+·) 0 := by
  intro hp
  induction hp <;> simp only [List.foldr_cons,List.foldr_nil] at * <;> omega

theorem sorted_distinct_sum_lower_general__greedy_finalization (b : Int) (xs : List Int) :
    increasing xs → NoDup xs → Forall (fun x => b≤x) xs →
    Zlength xs*b+triangular (Zlength xs-1)≤xs.foldr (·+·) 0 := by
  induction xs generalizing b with
  | nil => intros; change 0*b+triangular (-1)≤0; simp only [zero_mul,zero_add]; decide
  | cons a xs ih =>
    intro hi hn hb
    rcases List.nodup_cons.mp hn with ⟨hnot,hnt⟩
    rcases hb with ⟨hba,hbt⟩
    have ht : Forall (fun x => b+1≤x) xs := by
      apply Forall.iff_forall_mem.mpr
      intro x hx
      have ha := increasing_aux_head_le_all_In xs a x hi hx
      have hne : a≠x := by intro he; exact hnot (he ▸ hx)
      omega
    have hh := ih (b+1) (increasing_aux_tail_increasing xs a hi) hnt ht
    have htri := triangular_succ__greedy_finalization (Zlength xs-1)
    simp only [sub_add_cancel] at htri
    simp only [Zlength_cons,List.foldr_cons,add_sub_cancel_right]
    rw [htri]
    nlinarith

theorem distinct_positive_sum_lower__greedy_finalization (xs : List Int) :
    Forall (fun x => x>0) xs → NoDup xs → triangular (Zlength xs)≤xs.foldr (·+·) 0 := by
  intro hp hn
  have hperm := sort_list_perm xs
  have hs := sorted_distinct_sum_lower_general__greedy_finalization 1 (sort xs)
    (sort_list_increasing xs) (List.Nodup.perm hn hperm) (by
      apply Forall.iff_forall_mem.mpr
      intro x hx
      have hh := hp.mem (hperm.mem_iff.mpr hx)
      omega)
  have hlen : Zlength (sort xs)=Zlength xs := congrArg Int.ofNat hperm.length_eq.symm
  have hsum := sum_permutation__greedy_finalization xs (sort xs) hperm
  have htri := triangular_succ__greedy_finalization (Zlength xs-1)
  simp only [sub_add_cancel] at htri
  rw [hlen,←hsum] at hs
  nlinarith

private theorem nth_get (xs : List Int) (i : Nat) (hi : i<xs.length) :
    Znth (Int.ofNat i) xs 0=xs[i] := by
  change xs.getD i 0=xs[i]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]

theorem greedy_candy_plan_spec__greedy_finalization (n k used : Int) (written : List Int) :
    1≤k → used=triangular k → used≤n → n<used+(k+1) → CandyPrefix k written →
    let out := replace_Znth (k-1) (Znth (k-1) written 0+(n-used)) written
    GreedyCandyPlan n k out ∧ Spec n out := by
  intro hk hu hun hnext hp
  let out := replace_Znth (k-1) (Znth (k-1) written 0+(n-used)) written
  have hidx : 0≤k-1 ∧ k-1<Zlength written := by rw [hp.1]; omega
  have hlen : Zlength out=k := (Zlength_replace_Znth written _ _).trans hp.1
  have hpre : ∀ j, (0≤j ∧ j<k-1) → Znth j out 0=j+1 := by
    intro j hj
    rw [Znth_replace_Znth_Diff 0 written (k-1) j _ hidx ⟨hj.1,by rw [hp.1]; omega⟩ (by omega)]
    exact hp.2 j ⟨hj.1,by omega⟩
  have hlast : Znth (k-1) out 0=k+(n-triangular k) := by
    rw [Znth_replace_Znth_Same 0 written (k-1) _ hidx,
      candy_prefix_last_value__arithmetic_and_prefix k written hp hk,hu]
  have hgetbounds (i : Nat) (hi : i<out.length) : 0≤Int.ofNat i ∧ Int.ofNat i<k := by
    refine ⟨Int.natCast_nonneg _,?_⟩
    rw [←hlen]
    exact Int.ofNat_lt.mpr hi
  change GreedyCandyPlan n k out ∧ Spec n out
  refine ⟨⟨hlen,hpre,hlast⟩,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · apply Forall.iff_forall_mem.mpr
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨i,hi,rfl⟩
    have hib := hgetbounds i hi
    rw [←nth_get out i hi]
    by_cases hil : Int.ofNat i<k-1
    · rw [hpre _ ⟨hib.1,hil⟩]; omega
    · have he : Int.ofNat i=k-1 := by omega
      rw [he,hlast]; omega
  · apply List.nodup_iff_injective_getElem.mpr
    intro i j he
    have hib := hgetbounds i.val i.isLt
    have hjb := hgetbounds j.val j.isLt
    have heq : Znth (Int.ofNat i.val) out 0=Znth (Int.ofNat j.val) out 0 :=
      (nth_get out i.val i.isLt).trans (he.trans (nth_get out j.val j.isLt).symm)
    apply Fin.ext
    apply Int.ofNat_inj.mp
    by_cases hil : Int.ofNat i.val<k-1 <;> by_cases hjl : Int.ofNat j.val<k-1
    · rw [hpre _ ⟨hib.1,hil⟩,hpre _ ⟨hjb.1,hjl⟩] at heq; simp only [Int.ofNat_eq_coe] at *; omega
    · rw [hpre _ ⟨hib.1,hil⟩,show Int.ofNat j.val=k-1 by omega,hlast] at heq; simp only [Int.ofNat_eq_coe] at *; omega
    · rw [show Int.ofNat i.val=k-1 by omega,hlast,hpre _ ⟨hjb.1,hjl⟩] at heq; simp only [Int.ofNat_eq_coe] at *; omega
    · simp only [Int.ofNat_eq_coe] at *; omega
  · rw [sum_replace_Znth__greedy_finalization written (k-1) _ hidx,
      candy_prefix_sum__greedy_finalization k written (by omega) hp]
    omega
  · intro ys halloc
    have hlower := distinct_positive_sum_lower__greedy_finalization ys halloc.1 halloc.2.1
    rw [halloc.2.2] at hlower
    change Zlength ys≤Zlength out
    rw [hlen]
    by_contra h
    have hm := triangular_monotone_nonneg__greedy_finalization (k+1) (Zlength ys) ⟨by omega,by omega⟩
    rw [triangular_succ__greedy_finalization] at hm
    omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib
