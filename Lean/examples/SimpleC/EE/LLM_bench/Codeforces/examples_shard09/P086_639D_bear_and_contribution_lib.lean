import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
import ListLib.General.Length
import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_lib
open AUXLib

open MaxMinLib

def RaiseCost (b c «from» target cost : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun v => exists blogs comments, blogs ≥ 0 ∧ comments ≥ 0 ∧
 target = «from» + 5 * blogs + comments ∧ v = blogs * b + comments * c) (fun x => x) cost

def ChosenBloggers (values : List Int) (k : Int) (chosen : List Int) : Prop :=
  Zlength chosen = k ∧ List.Nodup chosen ∧
  Forall (fun i => (0 ≤ i ∧ i < Zlength values) ) chosen

def TieCost (values : List Int) (k b c cost : Int) : Prop :=
  exists (chosen costs : List Int) (target : Int),
    ChosenBloggers values k chosen ∧ Zlength costs = k ∧
    (forall i, (0 ≤ i ∧ i < k) →
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) ∧
    cost = List.foldr (· + ·) 0 costs

def Pre (k b c : Int) (values : List Int) : Prop :=
  
  True

def Spec (k b c : Int) (values : List Int) (out : Int) : Prop := min_value_of_subset (· ≤ ·) (TieCost values k b c) (fun x => x) out

def ZSum (l : List Int) : Int := List.foldr (· + ·) 0 l

def HeapParent (child : Int) : Int := Z.quot (child - 1) 2

def HeapOrderedFrom (l : List Int) (size lo : Int) : Prop :=
  forall child,
    0 < child →
    child < size →
    lo ≤ HeapParent child →
    Znth (HeapParent child) l 0 ≥ Znth child l 0

def HeapOrdered (l : List Int) (size : Int) : Prop :=
  HeapOrderedFrom l size 0

def ZipPerm (t0 b0 t1 b1 : List Int) : Prop :=
  Zlength b0 = Zlength t0 ∧
  Zlength t1 = Zlength t0 ∧
  Zlength b1 = Zlength t0 ∧
  List.Perm (List.zip t0 b0) (List.zip t1 b1)

def Nondecreasing (l : List Int) : Prop :=
  forall i j,
    0 ≤ i →
    i ≤ j →
    j < Zlength l →
    Znth i l 0 ≤ Znth j l 0

def HeapOrderExceptUp (l : List Int) (size child : Int) : Prop :=
  forall node,
    0 < node → node < size → node ≠ child →
    Znth (HeapParent node) l 0 ≥ Znth node l 0

def PushHoleGuard (l : List Int) (size child : Int) : Prop :=
  forall node,
    0 < node → node < size → HeapParent node = child →
    Znth (HeapParent child) l 0 ≥ Znth node l 0

def PushSiftState (l cur : List Int) (size child x : Int) : Prop :=
  Zlength cur = Zlength l ∧
  Znth child cur 0 = x ∧
  List.Perm (sublist 0 (size + 1) cur) (x :: sublist 0 size l) ∧
  HeapOrderExceptUp cur (size + 1) child ∧
  PushHoleGuard cur (size + 1) child

def HeapOrderExceptDown (l : List Int) (size index : Int) : Prop :=
  forall child,
    0 < child → child < size → HeapParent child ≠ index →
    Znth (HeapParent child) l 0 ≥ Znth child l 0

def PopHoleGuard (l : List Int) (size index : Int) : Prop :=
  index = 0 ∨
  (forall child,
     0 < child → child < size → HeapParent child = index →
     Znth (HeapParent index) l 0 ≥ Znth child l 0)

def PopSiftState (l cur : List Int) (size index : Int) : Prop :=
  Zlength cur = Zlength l ∧
  List.Perm (sublist 0 (size - 1) cur) (sublist 1 size l) ∧
  HeapOrderExceptDown cur (size - 1) index ∧
  PopHoleGuard cur (size - 1) index

def SiftState (t0 b0 t b : List Int) (size lo index : Int) : Prop :=
  ZipPerm t0 b0 t b ∧
  sublist size (Zlength t0) t = sublist size (Zlength t0) t0 ∧
  sublist size (Zlength b0) b = sublist size (Zlength b0) b0 ∧
  (forall child,
     0 < child → child < size → lo ≤ HeapParent child →
     HeapParent child ≠ index →
     Znth (HeapParent child) t 0 ≥ Znth child t 0) ∧
  (index = lo ∨
   (forall child,
      0 < child → child < size → HeapParent child = index →
      Znth (HeapParent index) t 0 ≥ Znth child t 0))

def HeapSortState (t : List Int) (n hi : Int) : Prop :=
  Nondecreasing (sublist (hi + 1) n t) ∧
  (forall p q,
     0 ≤ p → p ≤ hi → hi < q → q < n →
     Znth p t 0 ≤ Znth q t 0)

def ShiftedPrefix (values sh : List Int) (cnt : Int) : Prop :=
  forall i, (0 ≤ i ∧ i < cnt) → Znth i sh 0 = Znth i values 0 + 2000000000

def WCost (b c : Int) : Int := min b (5 * c)

def TargetPoint (s j : Int) : Int := s + Z.modulo (j - s) 5

def NormalizedBase (s j W c : Int) : Int :=
  (Z.modulo (j - s) 5) * c - (Z.div (TargetPoint s j - j) 5) * W

def CandPrefix (sh : List Int) (j W c cnt : Int) (t b : List Int) : Prop :=
  forall i, (0 ≤ i ∧ i < cnt) →
    Znth i t 0 = TargetPoint (Znth i sh 0) j ∧
    Znth i b 0 = NormalizedBase (Znth i sh 0) j W c

def SubMultiset (m l : List Int) : Prop :=
  exists rest, List.Perm l (m ++ rest)

def MinSubMultiset (l m : List Int) : Prop :=
  SubMultiset m l ∧
  (forall m',
     SubMultiset m' l → Zlength m' = Zlength m → ZSum m ≤ ZSum m')

def KSmallSum (l : List Int) (k s : Int) : Prop :=
  exists m, MinSubMultiset l m ∧ Zlength m = k ∧ s = ZSum m

def HeapContent (sb : List Int) (i : Int) (H : List Int) (hsum : Int) : Prop :=
  MinSubMultiset (sublist 0 i sb) H ∧ hsum = ZSum H

def TieCostAtResidue (values : List Int) (k b c j cost : Int) : Prop :=
  exists (chosen costs : List Int) (target : Int),
    Z.modulo target 5 = j ∧
    ChosenBloggers values k chosen ∧
    Zlength costs = k ∧
    (forall i, (0 ≤ i ∧ i < k) →
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) ∧
    cost = List.foldr (· + ·) 0 costs

def SweepValue (st sb : List Int) (k j W i v : Int) : Prop :=
  exists s,
    KSmallSum (sublist 0 (i + 1) sb) k s ∧
    v = s + k * (Z.div (Znth i st 0 - j) 5) * W

def BestState (P : Int → Prop) (best : Int) : Prop :=
  (best = -1 ∧ forall v, ¬ P v) ∨
  (0 ≤ best ∧ min_value_of_subset (· ≤ ·) P (fun x => x) best)

def ResidueBest (values : List Int) (k b c j best : Int) : Prop :=
  BestState
    (fun v => exists j', (0 ≤ j' ∧ j' < j) ∧ TieCostAtResidue values k b c j' v)
    best

def SweepSet
    (values : List Int) (k b c j : Int) (st sb : List Int) (W i : Int) (v : Int) : Prop :=
  (exists j', (0 ≤ j' ∧ j' < j) ∧ TieCostAtResidue values k b c j' v) ∨
  (exists i', k - 1 ≤ i' ∧ i' < i ∧ SweepValue st sb k j W i' v)

def SweepBest
    (values : List Int) (k b c j : Int) (st sb : List Int) (W i best : Int) : Prop :=
  BestState (SweepSet values k b c j st sb W i) best



private theorem Zlength_sublist0 {A : Type} (hi : Int) (l : List A)
    (h : 0 ≤ hi ∧ hi ≤ Zlength l) : Zlength (sublist 0 hi l) = hi :=
  ListLib.Zlength_sublist0 hi l h

private theorem list_eq_ext {A : Type} (l1 l2 : List A) (d : A) :
    l1 = l2 ↔ Zlength l1 = Zlength l2 ∧
      ∀ i, (0 ≤ i ∧ i < Zlength l1) → Znth i l1 d = Znth i l2 d :=
  ListLib.list_eq_ext l1 l2 d

private theorem Znth_sublist0 {A : Type} (d : A) (i hi : Int) (l : List A)
    (h : 0 ≤ i ∧ i < hi) : Znth i (sublist 0 hi l) d = Znth i l d :=
  ListLib.Znth_sublist0 d i hi l h

-- Reuse the already checked generic list swap proofs. The heap predicates
-- below remain the P086 predicates, with their original Coq statements.
theorem Zlength_replace_Znth__hpush_sift_up {A : Type} (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l) = Zlength l := AUXLib.Zlength_replace_Znth l n v

theorem replace_nth_comm__hpush_sift_up {A : Type} (ni nj : Nat) (l : List A) (a b : A) :
    ni ≠ nj → replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.replace_nth_comm ni nj l a b

theorem replace_Znth_swap_form__hpush_sift_up {A : Type} (l1 l2 l3 : List A) (xi xj : A) :
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3))))) =
      l1 ++ (xj :: (l2 ++ (xi :: l3))) :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.replace_Znth_swap_form l1 l2 l3 xi xj

theorem permutation_swap_Znth_lt__hpush_sift_up {A : Type} (l : List A) (i j : Int) (d : A)
    (hi : 0 ≤ i ∧ i < j) (hj : j < Zlength l) :
    List.Perm l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.permutation_swap_Znth_lt l i j d ⟨hi.1,hi.2,hj⟩

theorem permutation_swap_Znth__hpush_sift_up {A : Type} (l : List A) (i j : Int) (d : A) :
    (0 ≤ i ∧ i < Zlength l) → (0 ≤ j ∧ j < Zlength l) →
    List.Perm l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.permutation_swap_Znth l i j d

theorem sublist_replace_Znth_lt__hpush_sift_up (l : List Int) (n i v : Int)
    (hi : 0 ≤ i ∧ i < n) (hn : n ≤ Zlength l) :
    sublist 0 n (replace_Znth i v l) = replace_Znth i v (sublist 0 n l) := by
  have hs := Zlength_sublist0 n l (by omega : 0 ≤ n ∧ n ≤ Zlength l)
  have hl := Zlength_replace_Znth l i v
  apply (list_eq_ext _ _ 0).mpr
  refine ⟨by rw [Zlength_sublist0 n _ (by omega),Zlength_replace_Znth,hs],?_⟩
  intro k hk
  rw [Zlength_sublist0 n _ (by omega)] at hk
  rw [Znth_sublist0 0 k n (replace_Znth i v l) hk]
  by_cases he : k = i
  · subst k
    rw [Znth_replace_Znth_Same 0 l i v (by omega),Znth_replace_Znth_Same 0 _ i v (by omega)]
  · rw [Znth_replace_Znth_Diff 0 l i k v (by omega) (by omega) (Ne.symm he),
        Znth_replace_Znth_Diff 0 _ i k v (by omega) (by omega) (Ne.symm he),
        Znth_sublist0 0 k n l hk]

theorem sublist_replace_Znth_ge__hpush_sift_up (l : List Int) (n i v : Int)
    (hn : 0 ≤ n) (hni : n ≤ i) (hi : i < Zlength l) :
    sublist 0 n (replace_Znth i v l) = sublist 0 n l := by
  have hl := Zlength_replace_Znth l i v
  apply (list_eq_ext _ _ 0).mpr
  refine ⟨by rw [Zlength_sublist0 n _ (by omega),Zlength_sublist0 n l (by omega)],?_⟩
  intro k hk
  rw [Zlength_sublist0 n _ (by omega)] at hk
  rw [Znth_sublist0 0 k n _ hk,Znth_sublist0 0 k n l hk,
      Znth_replace_Znth_Diff 0 l i k v (by omega) (by omega) (by omega)]

theorem znth_replace_bounds__hpush_sift_up (l : List Int) (i v lo hi n : Int)
    (hi' : 0 ≤ i ∧ i < Zlength l) (hn : n ≤ Zlength l) (hv : lo ≤ v ∧ v ≤ hi)
    (hall : ∀ q, (0 ≤ q ∧ q < n) → q ≠ i → lo ≤ Znth q l 0 ∧ Znth q l 0 ≤ hi)
    (q : Int) (hq : 0 ≤ q ∧ q < n) :
    lo ≤ Znth q (replace_Znth i v l) 0 ∧ Znth q (replace_Znth i v l) 0 ≤ hi := by
  by_cases he : q = i
  · subst q; rwa [Znth_replace_Znth_Same 0 l i v hi']
  · rw [Znth_replace_Znth_Diff 0 l i q v hi' (by omega) (Ne.symm he)]
    exact hall q hq he

theorem heap_parent_range__hpush_sift_up (n : Int) (hn : 0 < n) :
    0 ≤ HeapParent n ∧ HeapParent n < n := by
  change 0 ≤ Z.quot (n-1) 2 ∧ Z.quot (n-1) 2 < n
  rw [show Z.quot (n-1) 2 = (n-1)/2 from Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

theorem heap_parent_zero__hpush_sift_up : HeapParent 0 = 0 := rfl

theorem push_sift_state_init__hpush_sift_up (l : List Int) (hs v : Int)
    (hhs0 : 0 ≤ hs) (hhs : hs < Zlength l) (hord : HeapOrdered l hs) :
    PushSiftState l (replace_Znth hs v l) hs hs v := by
  have hl := Zlength_replace_Znth l hs v
  refine ⟨hl,Znth_replace_Znth_Same 0 l hs v ⟨hhs0,hhs⟩,?_,?_,?_⟩
  · rw [sublist_split 0 (hs+1) hs _ (by omega) (by omega),
        sublist_replace_Znth_ge__hpush_sift_up l hs hs v hhs0 (by omega) hhs,
        sublist_single 0 hs _ (by omega),Znth_replace_Znth_Same 0 l hs v ⟨hhs0,hhs⟩]
    exact List.perm_append_comm
  · intro node hn0 hnlt hne
    have hp := heap_parent_range__hpush_sift_up node hn0
    rw [Znth_replace_Znth_Diff 0 l hs (HeapParent node) v (by omega) (by omega) (by omega),
        Znth_replace_Znth_Diff 0 l hs node v (by omega) (by omega) (Ne.symm hne)]
    exact hord node hn0 (by omega) hp.1
  · intro node hn0 hnlt hpar
    have hp := heap_parent_range__hpush_sift_up node hn0
    omega

theorem push_sift_state_swap__hpush_sift_up (l cur : List Int) (hs i p v : Int)
    (hhs0 : 0 ≤ hs) (hhs : hs < Zlength l) (hi0 : 0 < i) (hihs : i ≤ hs)
    (hp : p = HeapParent i) (hlt : Znth p cur 0 < Znth i cur 0)
    (hst : PushSiftState l cur hs i v) :
    PushSiftState l
      (replace_Znth i (Znth p cur 0) (replace_Znth p (Znth i cur 0) cur)) hs p v := by
  obtain ⟨hlen,hv,hperm,hex,hguard⟩ := hst
  have hpr := heap_parent_range__hpush_sift_up i hi0
  rw [← hp] at hpr
  let swapped := replace_Znth i (Znth p cur 0) (replace_Znth p (Znth i cur 0) cur)
  have hsw := SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.Znth_swap_Znth cur p i 0 (by omega) (by omega) (by omega)
  change Znth p swapped 0 = _ ∧ Znth i swapped 0 = _ ∧ _ at hsw
  have hlen' : Zlength swapped = Zlength cur := by simp only [swapped,Zlength_replace_Znth]
  refine ⟨hlen'.trans hlen,hsw.1.trans hv,?_,?_,?_⟩
  · have hsl := Zlength_sublist0 (hs+1) cur (by omega : 0 ≤ hs+1 ∧ hs+1 ≤ Zlength cur)
    rw [sublist_replace_Znth_lt__hpush_sift_up _ (hs+1) i _ (by omega) (by rw [Zlength_replace_Znth]; omega),
        sublist_replace_Znth_lt__hpush_sift_up cur (hs+1) p _ (by omega) (by omega),
        ← Znth_sublist0 0 i (hs+1) cur (by omega), ← Znth_sublist0 0 p (hs+1) cur (by omega)]
    exact (permutation_swap_Znth__hpush_sift_up _ p i 0 (by omega) (by omega)).symm.trans hperm
  · intro node hn0 hnlt hne
    have hpn := heap_parent_range__hpush_sift_up node hn0
    by_cases hni : node = i
    · subst node; rw [← hp,hsw.1,hsw.2.1]; omega
    · rw [hsw.2.2 node (by omega) hne hni]
      have hold := hex node hn0 hnlt hni
      by_cases hpp : HeapParent node = p
      · rw [hpp,hsw.1]; rw [hpp] at hold; omega
      · by_cases hpi : HeapParent node = i
        · rw [hpi,hsw.2.1]
          have h := hguard node hn0 hnlt hpi
          simpa only [← hp] using h
        · rw [hsw.2.2 (HeapParent node) (by omega) hpp hpi]
          exact hold
  · intro node hn0 hnlt hpar
    have hpn := heap_parent_range__hpush_sift_up node hn0
    by_cases hp0 : p = 0
    · have hg : HeapParent p = p := by rw [hp0]; rfl
      rw [hg,hsw.1]
      by_cases hni : node = i
      · subst node; rw [hsw.2.1]; omega
      · rw [hsw.2.2 node (by omega) (by omega) hni]
        have hold := hex node hn0 hnlt hni
        rw [hpar] at hold; omega
    · have hpp := heap_parent_range__hpush_sift_up p (by omega)
      rw [hsw.2.2 (HeapParent p) (by omega) (by omega) (by omega)]
      have hgp := hex p (by omega) (by omega) (by omega)
      by_cases hni : node = i
      · subst node; rw [hsw.2.1]; exact hgp
      · rw [hsw.2.2 node (by omega) (by omega) hni]
        have hold := hex node hn0 hnlt hni
        rw [hpar] at hold; omega

theorem push_sift_state_to_heap_ordered__hpush_sift_up (l cur : List Int) (hs i v : Int)
    (hst : PushSiftState l cur hs i v)
    (hedge : i = 0 ∨ Znth (HeapParent i) cur 0 ≥ Znth i cur 0) : HeapOrdered cur (hs+1) := by
  intro child hc0 hclt _
  by_cases he : child = i
  · subst child; rcases hedge with hi | hh
    · omega
    · exact hh
  · exact hst.2.2.2.1 child hc0 hclt he


theorem zlength_replace_Znth__hpop_sift_right_child {A : Type} (l : List A) (i : Int) (v : A) :
    Zlength (replace_Znth i v l) = Zlength l := Zlength_replace_Znth l i v

theorem replace_Znth_0_cons__hpop_sift_right_child {A : Type} (v x : A) (t : List A) :
    replace_Znth 0 v (x :: t) = v :: t := rfl

private theorem perm_move_head_nat (a : Int) (l : List Int) (j : Nat) (hj : j < l.length) :
    List.Perm (a :: l) (l.getD j 0 :: replace_nth j l a) := by
  induction l generalizing j a with
  | nil => simp at hj
  | cons b l ih =>
    cases j with
    | zero => exact List.Perm.swap b a l
    | succ j =>
      simp only [List.getD_cons_succ,replace_nth]
      exact (List.Perm.swap b a l).trans
        (((ih a j (by simpa using hj)).cons b).trans (List.Perm.swap _ _ _))

theorem perm_move_head__hpop_sift_right_child (a : Int) (l : List Int) (j : Int)
    (hj : 0 ≤ j ∧ j < Zlength l) :
    List.Perm (a :: l) (Znth j l 0 :: replace_Znth j a l) := by
  apply perm_move_head_nat
  simp only [Zlength,Int.ofNat_eq_coe] at hj
  omega

theorem perm_swap_replace_Znth__hpop_sift_right_child (l : List Int) (i j : Int)
    (hi : 0 ≤ i) (hij : i < j) (hj : j < Zlength l) :
    List.Perm (replace_Znth i (Znth j l 0) (replace_Znth j (Znth i l 0) l)) l :=
  (permutation_swap_Znth__hpush_sift_up l j i 0 (by omega) (by omega)).symm

theorem sublist0_replace_Znth__hpop_sift_right_child (l : List Int) (n i v : Int) :
    (0 ≤ i ∧ i < n) → n ≤ Zlength l →
    sublist 0 n (replace_Znth i v l) = replace_Znth i v (sublist 0 n l) :=
  sublist_replace_Znth_lt__hpush_sift_up l n i v

theorem heap_parent_left__hpop_sift_left_child (i : Int) : HeapParent (2*i+1) = i := by
  change (2*i+1-1).tdiv 2 = i
  rw [show 2*i+1-1=2*i by omega]
  exact Int.mul_tdiv_cancel_left i (by decide)

theorem heap_parent_child__hpop_sift_right_child (i child : Int) (hi : 0 ≤ i) (hc : 0 < child) :
    HeapParent (2*i+1) = i ∧ HeapParent (2*i+1+1) = i ∧
    0 ≤ HeapParent child ∧ HeapParent child < child := by
  refine ⟨heap_parent_left__hpop_sift_left_child i,?_,heap_parent_range__hpush_sift_up child hc⟩
  change (2*i+1+1-1).tdiv 2 = i
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

theorem heap_children_char__hpop_sift_left_child (index child : Int) (hc : 0 < child)
    (hp : HeapParent child = index) : child = 2*index+1 ∨ child = 2*index+2 := by
  change (child-1).tdiv 2 = index at hp
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hp
  omega

theorem heap_parent_children__hpop_sift_right_child (i child : Int) (hi : 0 ≤ i) (hc : 0 < child)
    (hp : HeapParent child = i) : child = 2*i+1 ∨ child = 2*i+1+1 := by
  have h := heap_children_char__hpop_sift_left_child i child hc hp
  omega

private theorem pop_sift_swap (l cur : List Int) (hs i j : Int)
    (hlen : hs ≤ Zlength cur) (hi : 0 ≤ i) (hij : i < j) (hj : j < hs-1)
    (hp : HeapParent j = i) (hlt : Znth i cur 0 < Znth j cur 0)
    (hsib : ∀ child, 0 < child → child < hs-1 → HeapParent child = i →
      Znth child cur 0 ≤ Znth j cur 0)
    (hst : PopSiftState l cur hs i) :
    PopSiftState l (replace_Znth i (Znth j cur 0) (replace_Znth j (Znth i cur 0) cur)) hs j := by
  obtain ⟨hc,hperm,hex,hguard⟩ := hst
  let swapped := replace_Znth i (Znth j cur 0) (replace_Znth j (Znth i cur 0) cur)
  have hsw := SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.Znth_swap_Znth cur j i 0 (by omega) (by omega) (by omega)
  change Znth j swapped 0 = _ ∧ Znth i swapped 0 = _ ∧ _ at hsw
  have hlen' : Zlength swapped = Zlength cur := by simp only [swapped,Zlength_replace_Znth]
  refine ⟨hlen'.trans hc,?_,?_,Or.inr ?_⟩
  · have hsl := Zlength_sublist0 (hs-1) cur (by omega)
    rw [sublist_replace_Znth_lt__hpush_sift_up _ (hs-1) i _ (by omega) (by rw [Zlength_replace_Znth]; omega),
        sublist_replace_Znth_lt__hpush_sift_up cur (hs-1) j _ (by omega) (by omega),
        ← Znth_sublist0 0 j (hs-1) cur (by omega),← Znth_sublist0 0 i (hs-1) cur (by omega)]
    exact (permutation_swap_Znth__hpush_sift_up _ j i 0 (by omega) (by omega)).symm.trans hperm
  · intro child hc0 hclt hpne
    have hpc := heap_parent_range__hpush_sift_up child hc0
    by_cases hci : child = i
    · subst child
      rw [hsw.2.1,hsw.2.2 (HeapParent i) (by omega) (by omega) (by omega)]
      rcases hguard with hi0 | hg
      · omega
      · exact hg j (by omega) hj hp
    · by_cases hcj : child = j
      · subst child; rw [hp,hsw.2.1,hsw.1]; omega
      · rw [hsw.2.2 child (by omega) hcj hci]
        by_cases hpi : HeapParent child = i
        · rw [hpi,hsw.2.1]; exact hsib child hc0 hclt hpi
        · rw [hsw.2.2 (HeapParent child) (by omega) hpne hpi]
          exact hex child hc0 hclt hpi
  · intro child hc0 hclt hpar
    have hpc := heap_parent_range__hpush_sift_up child hc0
    rw [hp,hsw.2.1,hsw.2.2 child (by omega) (by omega) (by omega)]
    have h := hex child hc0 hclt (by omega)
    simpa only [hpar] using h

theorem pop_sift_state_swap_right__hpop_sift_right_child (l cur : List Int) (hs i : Int)
    (hi : 0 ≤ i) (hlen : hs ≤ Zlength cur) (hl : 2*i+1 < hs-1) (hr : 2*i+1+1 < hs-1)
    (hgt : Znth (2*i+1+1) cur 0 > Znth i cur 0)
    (hsib : Znth (2*i+1+1) cur 0 ≥ Znth (2*i+1) cur 0)
    (hst : PopSiftState l cur hs i) :
    PopSiftState l (replace_Znth i (Znth (2*i+1+1) cur 0)
      (replace_Znth (2*i+1+1) (Znth i cur 0) cur)) hs (2*i+1+1) := by
  apply pop_sift_swap l cur hs i (2*i+1+1) hlen hi (by omega) hr
    (heap_parent_child__hpop_sift_right_child i 1 hi (by omega)).2.1 hgt ?_ hst
  intro child hc0 hclt hpar
  rcases heap_parent_children__hpop_sift_right_child i child hi hc0 hpar with h | h
  · simpa only [h] using hsib
  · simp only [h,le_refl]

theorem Zlength_replace_Znth__hpop_sift_left_child {A : Type} (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l) = Zlength l := Zlength_replace_Znth l n v

theorem heap_parent_bounds__hpop_sift_left_child (child : Int) :
    0 < child → 0 ≤ HeapParent child ∧ HeapParent child < child := heap_parent_range__hpush_sift_up child

theorem heap_root_is_max__hpop_sift_left_child (l : List Int) (size q : Int)
    (hord : HeapOrdered l size) (hq : 0 ≤ q ∧ q < size) : Znth q l 0 ≤ Znth 0 l 0 := by
  have h (n : Nat) : ∀ i : Int, i.toNat = n → (0 ≤ i ∧ i < size) → Znth i l 0 ≤ Znth 0 l 0 := by
    intro i hn hb
    induction n using Nat.strongRecOn generalizing i with
    | ind n ih =>
      by_cases h0 : i = 0
      · subst i; exact le_refl _
      · have hp := heap_parent_range__hpush_sift_up i (by omega)
        have hr := ih (HeapParent i).toNat (by omega) (HeapParent i) rfl ⟨hp.1,by omega⟩
        exact (hord i (by omega) hb.2 hp.1).trans hr
  exact h q.toNat q rfl hq

theorem replace_nth_comm__hpop_sift_left_child (ni nj : Nat) (l : List Int) (a b : Int) :
    ni ≠ nj → replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a :=
  replace_nth_comm__hpush_sift_up ni nj l a b

theorem replace_Znth_comm__hpop_sift_left_child (l : List Int) (i j a b : Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) := by
  apply replace_nth_comm__hpop_sift_left_child
  omega

theorem replace_Znth_swap_form__hpop_sift_left_child (l1 l2 l3 : List Int) (xi xj : Int) :
    replace_Znth (Zlength l1+1+Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3))))) =
      l1 ++ (xj :: (l2 ++ (xi :: l3))) := replace_Znth_swap_form__hpush_sift_up l1 l2 l3 xi xj

theorem permutation_swap_Znth_lt__hpop_sift_left_child (l : List Int) (i j d : Int)
    (hi : 0 ≤ i) (hij : i < j) (hj : j < Zlength l) :
    List.Perm l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  permutation_swap_Znth_lt__hpush_sift_up l i j d ⟨hi,hij⟩ hj

theorem permutation_swap_Znth__hpop_sift_left_child (l : List Int) (i j d : Int) :
    (0 ≤ i ∧ i < Zlength l) → (0 ≤ j ∧ j < Zlength l) →
    List.Perm l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  permutation_swap_Znth__hpush_sift_up l i j d

theorem sublist0_replace_Znth_inside__hpop_sift_left_child (l : List Int) (hi i value : Int) :
    (0 ≤ i ∧ i < hi) → hi ≤ Zlength l →
    sublist 0 hi (replace_Znth i value l) = replace_Znth i value (sublist 0 hi l) :=
  sublist_replace_Znth_lt__hpush_sift_up l hi i value

theorem pop_init_permutation__hpop_sift_left_child (l : List Int) (hs cap : Int)
    (hhs : 1 ≤ hs) (hcap : hs ≤ cap) (hlen : Zlength l = cap) :
    List.Perm (sublist 0 (hs-1) (replace_Znth 0 (Znth (hs-1) l 0) l)) (sublist 1 hs l) := by
  by_cases he : hs = 1
  · subst hs
    rw [Zsublist_nil _ 0 (1-1) (by omega),Zsublist_nil l 1 1 (by omega)]
  · cases l with
    | nil => simp only [Zlength_nil] at hlen; omega
    | cons a l =>
      rw [Zlength_cons] at hlen
      rw [Znth_cons 0 (hs-1) a l (by omega)]
      change List.Perm (sublist 0 (hs-1) (Znth (hs-1-1) l 0 :: l)) (sublist 1 hs (a::l))
      rw [sublist_cons1 (hs-1) _ l (by omega),sublist_cons2 1 hs a l (by omega) (by rw [Zlength_cons]; omega)]
      simp only [show (1:Int)-1=0 by omega,show hs-1-1=hs-2 by omega]
      rw [sublist_split 0 (hs-1) (hs-2) l (by omega) (by omega),
        show sublist (hs-2) (hs-1) l = [Znth (hs-2) l 0] by
          convert sublist_single 0 (hs-2) l (by omega) using 1 <;> congr 1 <;> omega]
      exact (List.perm_append_singleton _ _).symm

theorem pop_init_bounds__hpop_sift_left_child (l : List Int) (hs cap q : Int)
    (hhs : 1 ≤ hs) (hcap : hs ≤ cap) (hlen : Zlength l = cap)
    (hb : ∀ x, (0 ≤ x ∧ x < hs) → -1000000000000 ≤ Znth x l 0 ∧ Znth x l 0 ≤ 1000000000000)
    (hq : 0 ≤ q ∧ q < hs-1) :
    -1000000000000 ≤ Znth q (replace_Znth 0 (Znth (hs-1) l 0) l) 0 ∧
      Znth q (replace_Znth 0 (Znth (hs-1) l 0) l) 0 ≤ 1000000000000 := by
  by_cases he : q = 0
  · subst q; rw [Znth_replace_Znth_Same 0 l 0 _ (by omega)]; exact hb (hs-1) (by omega)
  · rw [Znth_replace_Znth_Diff 0 l 0 q _ (by omega) (by omega) (Ne.symm he)]
    exact hb q (by omega)

theorem pop_sift_state_init__hpop_sift_left_child (l : List Int) (hs cap : Int)
    (hhs : 1 ≤ hs) (hcap : hs ≤ cap) (hlen : Zlength l = cap) (hord : HeapOrdered l hs) :
    PopSiftState l (replace_Znth 0 (Znth (hs-1) l 0) l) hs 0 := by
  refine ⟨Zlength_replace_Znth _ _ _,pop_init_permutation__hpop_sift_left_child l hs cap hhs hcap hlen,?_,Or.inl rfl⟩
  intro child hc0 hclt hpne
  have hp := heap_parent_range__hpush_sift_up child hc0
  rw [Znth_replace_Znth_Diff 0 l 0 (HeapParent child) _ (by omega) (by omega) (Ne.symm hpne),
      Znth_replace_Znth_Diff 0 l 0 child _ (by omega) (by omega) (by omega)]
  exact hord child hc0 (by omega) hp.1

theorem pop_sift_state_swap_left__hpop_sift_left_child (l cur : List Int) (hs cap i : Int)
    (hl : Zlength l = cap) (hcur : Zlength cur = cap) (hhs : hs ≤ cap) (hi : 0 ≤ i)
    (hc : 2*i+1 < hs-1) (hlt : Znth (2*i+1) cur 0 > Znth i cur 0)
    (hsib : 2*i+2 < hs-1 → Znth (2*i+2) cur 0 ≤ Znth (2*i+1) cur 0)
    (hst : PopSiftState l cur hs i) :
    PopSiftState l (replace_Znth i (Znth (2*i+1) cur 0)
      (replace_Znth (2*i+1) (Znth i cur 0) cur)) hs (2*i+1) := by
  apply pop_sift_swap l cur hs i (2*i+1) (by omega) hi (by omega) hc
    (heap_parent_left__hpop_sift_left_child i) hlt ?_ hst
  intro child hc0 hclt hpar
  rcases heap_children_char__hpop_sift_left_child i child hc0 hpar with h | h
  · simp only [h,le_refl]
  · rw [h] at hclt ⊢; exact hsib hclt

theorem sublist_root__hpop_return (l : List Int) (hs : Int) (h1 : 1 ≤ hs) (h2 : hs ≤ Zlength l) :
    sublist 0 hs l = Znth 0 l 0 :: sublist 1 hs l := by
  rw [sublist_split 0 hs 1 l (by omega) (by omega),
    show sublist 0 1 l = [Znth 0 l 0] by simpa using sublist_single 0 0 l (by omega)]
  rfl

theorem pop_perm_extract_root__hpop_return (l cur : List Int) (hs i : Int)
    (hst : PopSiftState l cur hs i) (h1 : 1 ≤ hs) (h2 : hs ≤ Zlength l) :
    List.Perm (sublist 0 hs l) (Znth 0 l 0 :: sublist 0 (hs-1) cur) := by
  rw [sublist_root__hpop_return l hs h1 h2]
  exact hst.2.1.symm.cons _

theorem heap_parent_children__hpop_return (child i : Int) :
    0 < child → HeapParent child = i → child = 2*i+1 ∨ child = 2*i+2 :=
  heap_children_char__hpop_sift_left_child i child

theorem pop_sift_state_exit__hpop_return (l cur : List Int) (hs i : Int)
    (hst : PopSiftState l cur hs i) (hi : 0 ≤ i)
    (hl : 2*i+1 < hs-1 → Znth (2*i+1) cur 0 ≤ Znth i cur 0)
    (hr : 2*i+1+1 < hs-1 → Znth (2*i+1+1) cur 0 ≤ Znth i cur 0) : HeapOrdered cur (hs-1) := by
  intro child hc0 hclt _
  by_cases he : HeapParent child = i
  · rw [he]
    rcases heap_parent_children__hpop_sift_right_child i child hi hc0 he with h | h
    · rw [h] at hclt ⊢; exact hl hclt
    · rw [h] at hclt ⊢; exact hr hclt
  · exact hst.2.2.1 child hc0 hclt he

theorem Zlength_replace_Znth__sift_cand_step {A : Type} (n : Int) (v : A) (l : List A) :
    Zlength (replace_Znth n v l) = Zlength l := Zlength_replace_Znth l n v

theorem Zlist_eq_ext__sift_cand_step (l1 l2 : List Int) (hlen : Zlength l1 = Zlength l2)
    (he : ∀ k, (0 ≤ k ∧ k < Zlength l1) → Znth k l1 0 = Znth k l2 0) : l1=l2 :=
  (list_eq_ext l1 l2 0).mpr ⟨hlen,he⟩


theorem perm_cons_replace_nth__sift_cand_step {A : Type} (d : A) (t : List A) (h : A) (m : Nat)
    (hm : m < t.length) : List.Perm (t.getD m d :: replace_nth m t h) (h :: t) := by
  apply List.Perm.symm
  induction t generalizing m h with
  | nil => simp at hm
  | cons x t ih =>
    cases m with
    | zero => exact List.Perm.swap x h t
    | succ m =>
      simp only [List.getD_cons_succ,replace_nth]
      exact (List.Perm.swap x h t).trans
        (((ih h m (by simpa using hm)).cons x).trans (List.Perm.swap _ _ _))

theorem perm_replace_nth_swap__sift_cand_step {A : Type} (d : A) (l : List A) (i j : Nat)
    (hij : i < j) (hj : j < l.length) :
    List.Perm (replace_nth j (replace_nth i l (l.getD j d)) (l.getD i d)) l := by
  simpa only [replace_Znth,Znth,Int.toNat_natCast] using
    (permutation_swap_Znth_lt__hpush_sift_up l (Int.ofNat i) (Int.ofNat j) d (by simp only [Int.ofNat_eq_coe]; omega)
      (by simp only [Zlength,Int.ofNat_eq_coe]; omega)).symm

theorem perm_replace_Znth_swap__sift_cand_step {A : Type} (d : A) (l : List A) (i j : Int)
    (hi : 0 ≤ i) (hij : i < j) (hj : j < Zlength l) :
    List.Perm (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) l :=
  (permutation_swap_Znth_lt__hpush_sift_up l i j d ⟨hi,hij⟩ hj).symm

theorem combine_replace_nth__sift_cand_step {A B : Type} (l1 : List A) (l2 : List B)
    (n : Nat) (a : A) (b : B) :
    List.zip (replace_nth n l1 a) (replace_nth n l2 b) = replace_nth n (List.zip l1 l2) (a,b) := by
  induction l1 generalizing l2 n with
  | nil => cases n <;> cases l2 <;> rfl
  | cons x l1 ih =>
    cases l2 with
    | nil => cases n <;> rfl
    | cons y l2 => cases n <;> simp_all [replace_nth,List.zip_cons_cons]

theorem combine_replace_Znth__sift_cand_step {A B : Type} (l1 : List A) (l2 : List B)
    (n : Int) (a : A) (b : B) :
    List.zip (replace_Znth n a l1) (replace_Znth n b l2) = replace_Znth n (a,b) (List.zip l1 l2) :=
  combine_replace_nth__sift_cand_step l1 l2 n.toNat a b

private theorem getD_zip_equal {A B : Type} (l1 : List A) (l2 : List B) (n : Nat) (a : A) (b : B)
    (hlen : l1.length = l2.length) : (l1.zip l2).getD n (a,b) = (l1.getD n a,l2.getD n b) := by
  induction l1 generalizing l2 n with
  | nil => cases l2 <;> simp_all
  | cons x l1 ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y l2 =>
      cases n with
      | zero => rfl
      | succ n => simpa only [List.zip_cons_cons,List.getD_cons_succ] using ih l2 n (by simpa using hlen)

theorem Znth_combine__sift_cand_step (l1 l2 : List Int) (n : Int) (hlen : Zlength l2 = Zlength l1) :
    Znth n (List.zip l1 l2) (0,0) = (Znth n l1 0,Znth n l2 0) := by
  exact getD_zip_equal l1 l2 n.toNat 0 0 (Int.ofNat_inj.mp hlen.symm)

theorem zip_perm_swap__sift_cand_step (t0 b0 t b : List Int) (i j : Int)
    (hz : ZipPerm t0 b0 t b) (hi : 0 ≤ i) (hij : i < j) (hj : j < Zlength t) :
    ZipPerm t0 b0
      (replace_Znth j (Znth i t 0) (replace_Znth i (Znth j t 0) t))
      (replace_Znth j (Znth i b 0) (replace_Znth i (Znth j b 0) b)) := by
  obtain ⟨hb0,ht,hb,hperm⟩ := hz
  refine ⟨hb0,by simpa only [Zlength_replace_Znth] using ht,
    by simpa only [Zlength_replace_Znth] using hb,?_⟩
  rw [combine_replace_Znth__sift_cand_step,combine_replace_Znth__sift_cand_step,
    ← Znth_combine__sift_cand_step t b i (by omega),← Znth_combine__sift_cand_step t b j (by omega)]
  apply hperm.trans
  apply permutation_swap_Znth_lt__hpush_sift_up _ i j (0,0) ⟨hi,hij⟩
  have hl : Zlength (t.zip b) = Zlength t :=
    SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.Zlength_combine_eq t b (by omega)
  omega

theorem sublist_replace_Znth_lo__sift_cand_step (l : List Int) (i v lo hi : Int)
    (hi' : 0 ≤ i ∧ i < lo) (hlohi : lo ≤ hi) (hh : hi ≤ Zlength l) :
    sublist lo hi (replace_Znth i v l) = sublist lo hi l := by
  have hl := Zlength_replace_Znth l i v
  have hs : Zlength (sublist lo hi (replace_Znth i v l)) = hi-lo :=
    ListLib.Zlength_sublist lo hi _ (by omega) (by change hi ≤ Zlength (replace_Znth i v l); omega)
  have hs' : Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l (by omega) hh
  apply (list_eq_ext _ _ 0).mpr
  refine ⟨by omega,?_⟩
  intro k hk
  rw [hs] at hk
  rw [Znth_sublist 0 lo k hi _ (by omega) hk,Znth_sublist 0 lo k hi l (by omega) hk,
    Znth_replace_Znth_Diff 0 l i (k+lo) v (by omega) (by omega) (by omega)]

theorem Znth_swap_at_j__sift_cand_step (l : List Int) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hne : i ≠ j) :
    Znth j (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 = Znth i l 0 := by
  exact Znth_replace_Znth_Same 0 _ j _ (by rw [Zlength_replace_Znth]; exact hj)

theorem Znth_swap_at_i__sift_cand_step (l : List Int) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hne : i ≠ j) :
    Znth i (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 = Znth j l 0 := by
  rw [Znth_replace_Znth_Diff 0 _ j i _ (by rw [Zlength_replace_Znth]; exact hj)
    (by rw [Zlength_replace_Znth]; exact hi) (Ne.symm hne),Znth_replace_Znth_Same 0 l i _ hi]

theorem Znth_swap_other__sift_cand_step (l : List Int) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hk : 0 ≤ k ∧ k < Zlength l)
    (hki : k ≠ i) (hkj : k ≠ j) :
    Znth k (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 = Znth k l 0 := by
  rw [Znth_replace_Znth_Diff 0 _ j k _ (by rw [Zlength_replace_Znth]; exact hj)
    (by rw [Zlength_replace_Znth]; exact hk) (Ne.symm hkj),
    Znth_replace_Znth_Diff 0 l i k _ hi hk (Ne.symm hki)]

theorem heap_parent_spec__sift_cand_step (c : Int) (hc : 0 < c) :
    2*HeapParent c+1 ≤ c ∧ c ≤ 2*HeapParent c+2 := by
  have h := heap_children_char__hpop_sift_left_child (HeapParent c) c hc rfl
  omega

theorem heap_parent_lt__sift_cand_step (c : Int) :
    0 < c → 0 ≤ HeapParent c ∧ HeapParent c < c := heap_parent_range__hpush_sift_up c

theorem heap_parent_child__sift_cand_step (c r : Int) (hr : 0 ≤ r)
    (hc : c = 2*r+1 ∨ c = 2*r+2) : HeapParent c = r := by
  obtain ⟨hl,hrr,_⟩ := heap_parent_child__hpop_sift_right_child r 1 hr (by omega)
  rcases hc with h | h
  · simpa only [h] using hl
  · convert hrr using 1 <;> congr 1 <;> omega

theorem heap_parent_inv__sift_cand_step (c r : Int) :
    0 < c → HeapParent c = r → c = 2*r+1 ∨ c = 2*r+2 := heap_children_char__hpop_sift_left_child r c

theorem sift_state_init__sift_cand_step (t0 b0 : List Int) (size lo : Int)
    (hlen : Zlength b0 = Zlength t0) (ho : HeapOrderedFrom t0 size (lo+1)) :
    SiftState t0 b0 t0 b0 size lo lo := by
  refine ⟨⟨hlen,rfl,hlen,List.Perm.refl _⟩,rfl,rfl,?_,Or.inl rfl⟩
  intro child hc0 hclt hp hne
  exact ho child hc0 hclt (by omega)

theorem sift_state_swap__sift_cand_step (t0 b0 t b : List Int) (size lo r ch : Int)
    (hlo : 0 ≤ lo) (hlr : lo ≤ r) (hrch : r < ch) (hch : ch < size) (hs : size ≤ Zlength t0)
    (hp : HeapParent ch = r) (hle : Znth r t 0 ≤ Znth ch t 0)
    (hselect : ∀ s, 0 < s → s < size → HeapParent s = r → Znth ch t 0 ≥ Znth s t 0)
    (hst : SiftState t0 b0 t b size lo r) :
    SiftState t0 b0
      (replace_Znth ch (Znth r t 0) (replace_Znth r (Znth ch t 0) t))
      (replace_Znth ch (Znth r b 0) (replace_Znth r (Znth ch b 0) b)) size lo ch := by
  obtain ⟨hz,htail,btail,hex,hguard⟩ := hst
  have hb0 := hz.1
  have ht := hz.2.1
  have hb := hz.2.2.1
  let swapped := replace_Znth ch (Znth r t 0) (replace_Znth r (Znth ch t 0) t)
  have hsw := SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.Znth_swap_Znth t r ch 0 (by omega) (by omega) (by omega)
  change Znth r swapped 0 = _ ∧ Znth ch swapped 0 = _ ∧ _ at hsw
  refine ⟨zip_perm_swap__sift_cand_step t0 b0 t b r ch hz (by omega) hrch (by omega),?_,?_,?_,Or.inr ?_⟩
  · rw [sublist_replace_Znth_lo__sift_cand_step _ ch _ size (Zlength t0) (by omega) hs (by rw [Zlength_replace_Znth]; omega),
      sublist_replace_Znth_lo__sift_cand_step t r _ size (Zlength t0) (by omega) hs (by omega)]
    exact htail
  · rw [sublist_replace_Znth_lo__sift_cand_step _ ch _ size (Zlength b0) (by omega) (by omega) (by rw [Zlength_replace_Znth]; omega),
      sublist_replace_Znth_lo__sift_cand_step b r _ size (Zlength b0) (by omega) (by omega) (by omega)]
    exact btail
  · intro child hc0 hclt hplow hpne
    have hpc := heap_parent_range__hpush_sift_up child hc0
    by_cases hcr : child = r
    · subst child
      rw [hsw.1,hsw.2.2 (HeapParent r) (by omega) (by omega) (by omega)]
      rcases hguard with he | hg
      · omega
      · exact hg ch (by omega) hch hp
    · by_cases hcch : child = ch
      · subst child; rw [hp,hsw.1,hsw.2.1]; exact hle
      · rw [hsw.2.2 child (by omega) hcr hcch]
        by_cases hpr : HeapParent child = r
        · rw [hpr,hsw.1]; exact hselect child hc0 hclt hpr
        · rw [hsw.2.2 (HeapParent child) (by omega) hpr hpne]
          exact hex child hc0 hclt hplow hpr
  · intro child hc0 hclt hpar
    have hpc := heap_parent_range__hpush_sift_up child hc0
    rw [hp,hsw.1,hsw.2.2 child (by omega) (by omega) (by omega)]
    have h := hex child hc0 hclt (by omega) (by omega)
    simpa only [hpar] using h

theorem heap_parent_children__sift_cand_exit (child root : Int) (hc : 0 < child)
    (hp : HeapParent child = root) : child = 2*root+1 ∨ child = 2*root+1+1 := by
  have h := heap_children_char__hpop_sift_left_child root child hc hp
  omega

theorem sift_state_exit__sift_cand_exit (t0 b0 t b : List Int) (size lo root : Int)
    (hst : SiftState t0 b0 t b size lo root)
    (hc : ∀ child, 0 < child → child < size → HeapParent child = root → Znth root t 0 ≥ Znth child t 0) :
    HeapOrderedFrom t size lo := by
  intro child hc0 hclt hlow
  by_cases he : HeapParent child = root
  · simpa only [he] using hc child hc0 hclt he
  · exact hst.2.2.2.1 child hc0 hclt hlow he

theorem quot2_bounds__sort_build_phase (n : Int) (hn : 0 ≤ n) :
    0 ≤ Z.quot n 2 ∧ 2*Z.quot n 2 ≤ n ∧ n ≤ 2*Z.quot n 2+1 := by
  change 0 ≤ n.tdiv 2 ∧ 2*n.tdiv 2 ≤ n ∧ n ≤ 2*n.tdiv 2+1
  rw [Int.tdiv_eq_ediv_of_nonneg hn]
  omega

theorem heap_ordered_from_half__sort_build_phase (l : List Int) (n lo : Int)
    (hn : 0 ≤ n) (hlo : Z.quot n 2 ≤ lo) : HeapOrderedFrom l n lo := by
  intro child hc0 hclt hpar
  have h := quot2_bounds__sort_build_phase n hn
  have hp := heap_parent_spec__sift_cand_step child hc0
  omega

theorem zip_perm_trans__sort_build_phase (t0 b0 t b t1 b1 : List Int)
    (h0 : ZipPerm t0 b0 t b) (h1 : ZipPerm t b t1 b1) : ZipPerm t0 b0 t1 b1 :=
  ⟨h0.1,h1.2.1.trans h0.2.1,h1.2.2.1.trans h0.2.1,h0.2.2.2.trans h1.2.2.2⟩

theorem zip_perm_refl__sort_build_phase (t b : List Int) (hl : Zlength b = Zlength t) :
    ZipPerm t b t b := ⟨hl,rfl,hl,List.Perm.refl _⟩

theorem heap_sort_state_full__sort_build_phase (t : List Int) (n : Int) (hn : 0 ≤ n) :
    HeapSortState t n (n-1) := by
  refine ⟨?_,?_⟩
  · rw [show n-1+1=n by omega,Zsublist_nil t n n (by omega)]
    intro i j hi hij hj
    simp only [Zlength_nil] at hj
    omega
  · intro p q hp hpmax hq hnq
    omega


theorem length_replace_nth__sort_extract_phase {A : Type} (l : List A) (n : Nat) (a : A) :
    (replace_nth n l a).length = l.length := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons x l ih => cases n <;> simp_all [replace_nth]

theorem length_replace_Znth__sort_extract_phase {A : Type} (l : List A) (i : Int) (v : A) :
    (replace_Znth i v l).length = l.length := length_replace_nth__sort_extract_phase l i.toNat v

theorem Zlength_replace_Znth__sort_extract_phase {A : Type} (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l) = Zlength l := Zlength_replace_Znth l n v

theorem replace_nth_split__sort_extract_phase {A : Type} (l : List A) (n : Nat) (a : A)
    (hn : n < l.length) : replace_nth n l a = l.take n ++ a :: l.drop (n+1) := by
  induction l generalizing n with
  | nil => simp at hn
  | cons x l ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [replace_nth,List.take_succ_cons,List.drop_succ_cons,List.cons_append]
      rw [ih n (by simpa using hn)]

theorem perm_move__sort_extract_phase {A : Type} (d : A) (l : List A) (x : A) (m : Nat)
    (hm : m < l.length) : List.Perm (x::l) (l.getD m d :: replace_nth m l x) :=
  (perm_cons_replace_nth__sift_cand_step d l x m hm).symm

theorem perm_swap0__sort_extract_phase {A : Type} (d : A) (l : List A) (j : Int)
    (hj : 0 < j ∧ j < Zlength l) :
    List.Perm l (replace_Znth j (Znth 0 l d) (replace_Znth 0 (Znth j l d) l)) :=
  permutation_swap_Znth_lt__hpush_sift_up l 0 j d ⟨by omega,hj.1⟩ hj.2

theorem combine_app__sort_extract_phase {A B : Type} (l1 l2 : List A) (l1' l2' : List B)
    (hlen : l1.length = l1'.length) :
    (l1++l2).zip (l1'++l2') = l1.zip l1' ++ l2.zip l2' := List.zip_append hlen

theorem combine_firstn__sort_extract_phase {A B : Type} (n : Nat) (l1 : List A) (l2 : List B) :
    (l1.zip l2).take n = (l1.take n).zip (l2.take n) := List.take_zipWith

theorem combine_skipn__sort_extract_phase {A B : Type} (n : Nat) (l1 : List A) (l2 : List B) :
    (l1.zip l2).drop n = (l1.drop n).zip (l2.drop n) := List.drop_zipWith

theorem sublist_combine__sort_extract_phase {A B : Type} (lo hi : Int) (l1 : List A) (l2 : List B) :
    sublist lo hi (l1.zip l2) = (sublist lo hi l1).zip (sublist lo hi l2) := by
  simp only [sublist,combine_firstn__sort_extract_phase,combine_skipn__sort_extract_phase]

theorem map_fst_combine__sort_extract_phase {A B : Type} (l1 : List A) (l2 : List B)
    (hlen : l1.length = l2.length) : (l1.zip l2).map Prod.fst = l1 := by
  exact List.map_fst_zip (by omega)

theorem combine_replace_nth__sort_extract_phase {A B : Type} (l1 : List A) (l2 : List B)
    (n : Nat) (x : A) (y : B) (hlen : l1.length = l2.length) :
    (replace_nth n l1 x).zip (replace_nth n l2 y) = replace_nth n (l1.zip l2) (x,y) :=
  combine_replace_nth__sift_cand_step l1 l2 n x y

theorem combine_replace_Znth__sort_extract_phase {A B : Type} (l1 : List A) (l2 : List B)
    (i : Int) (x : A) (y : B) (hlen : l1.length = l2.length) :
    (replace_Znth i x l1).zip (replace_Znth i y l2) = replace_Znth i (x,y) (l1.zip l2) :=
  combine_replace_Znth__sift_cand_step l1 l2 i x y

theorem nth_combine__sort_extract_phase {A B : Type} (d1 : A) (d2 : B) (l1 : List A) (l2 : List B)
    (n : Nat) (hn : n < l1.length) (hlen : l1.length = l2.length) :
    (l1.zip l2).getD n (d1,d2) = (l1.getD n d1,l2.getD n d2) := getD_zip_equal l1 l2 n d1 d2 hlen

theorem Znth_combine__sort_extract_phase {A B : Type} (d1 : A) (d2 : B) (l1 : List A) (l2 : List B)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength l1) (hlen : Zlength l1 = Zlength l2) :
    Znth i (l1.zip l2) (d1,d2) = (Znth i l1 d1,Znth i l2 d2) :=
  getD_zip_equal l1 l2 i.toNat d1 d2 (Int.ofNat_inj.mp hlen)

theorem Zlength_combine__sort_extract_phase {A B : Type} (l1 : List A) (l2 : List B)
    (hlen : Zlength l1 = Zlength l2) : Zlength (l1.zip l2) = Zlength l1 :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.Zlength_combine_eq l1 l2 hlen

theorem heap_parent_range__sort_extract_phase (child : Int) :
    0 < child → 0 ≤ HeapParent child ∧ HeapParent child < child := heap_parent_range__hpush_sift_up child

theorem heap_root_max__sort_extract_phase (l : List Int) (size j : Int)
    (hord : HeapOrderedFrom l size 0) (hj : 0 ≤ j) (hjs : j < size) : Znth j l 0 ≤ Znth 0 l 0 :=
  heap_root_is_max__hpop_sift_left_child l size j hord ⟨hj,hjs⟩

theorem swap_Znth__sort_extract_phase (t : List Int) (i j q : Int)
    (hi : 0 ≤ i ∧ i < Zlength t) (hj : 0 ≤ j ∧ j < Zlength t) (hne : i ≠ j)
    (hq : 0 ≤ q ∧ q < Zlength t) :
    Znth q (replace_Znth j (Znth i t 0) (replace_Znth i (Znth j t 0) t)) 0 =
      if q=j then Znth i t 0 else if q=i then Znth j t 0 else Znth q t 0 := by
  by_cases hqj : q=j
  · subst q; simpa only [if_pos rfl] using Znth_swap_at_j__sift_cand_step t i j hi hj hne
  · by_cases hqi : q=i
    · subst q; simpa only [if_neg hqj,if_pos rfl] using Znth_swap_at_i__sift_cand_step t i j hi hj hne
    · simpa only [if_neg hqj,if_neg hqi] using Znth_swap_other__sift_cand_step t i j q hi hj hq hqi hqj

theorem zip_perm_trans__sort_extract_phase (t0 b0 t b t1 b1 : List Int) :
    ZipPerm t0 b0 t b → ZipPerm t b t1 b1 → ZipPerm t0 b0 t1 b1 :=
  zip_perm_trans__sort_build_phase t0 b0 t b t1 b1

theorem zip_perm_swap0__sort_extract_phase (t0 b0 t b : List Int) (j : Int)
    (hz : ZipPerm t0 b0 t b) (hj : 0 < j ∧ j < Zlength t) :
    ZipPerm t0 b0 (replace_Znth j (Znth 0 t 0) (replace_Znth 0 (Znth j t 0) t))
      (replace_Znth j (Znth 0 b 0) (replace_Znth 0 (Znth j b 0) b)) :=
  zip_perm_swap__sift_cand_step t0 b0 t b 0 j hz (by omega) hj.1 hj.2

theorem Zlength_length__sort_extract_phase (u v : List Int) (hlen : Zlength u = Zlength v) :
    u.length = v.length := Int.ofNat_inj.mp hlen


private theorem slice_length {A : Type} (lo hi : Int) (l : List A)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l hlo hhi

private theorem nondecreasing_slice_iff (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Nondecreasing (sublist lo hi l) ↔
      ∀ i j, lo ≤ i → i ≤ j → j < hi → Znth i l 0 ≤ Znth j l 0 := by
  have hs := slice_length lo hi l hlo hhi
  constructor
  · intro h i j hi' hij hj
    have v := h (i-lo) (j-lo) (by omega) (by omega) (by omega)
    rw [Znth_sublist 0 lo (i-lo) hi l hlo.1 (by omega),Znth_sublist 0 lo (j-lo) hi l hlo.1 (by omega)] at v
    simpa only [Int.sub_add_cancel] using v
  · intro h i j hi' hij hj
    rw [Znth_sublist 0 lo i hi l hlo.1 (by omega),Znth_sublist 0 lo j hi l hlo.1 (by omega)]
    exact h (i+lo) (j+lo) (by omega) (by omega) (by omega)

private theorem znth_mem (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l 0 ∈ l := by
  have hn : i.toNat < l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

private theorem mem_znth (l : List Int) (x : Int) (hx : x ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l 0 = x := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  refine ⟨i,⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩,?_⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using he

theorem heap_sort_state_swap__sort_extract_phase (t : List Int) (n hi : Int)
    (hlen : Zlength t = n) (hhi1 : 1 ≤ hi) (hhi2 : hi ≤ n-1)
    (hheap : HeapOrdered t (hi+1)) (hst : HeapSortState t n hi) :
    HeapSortState (replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t)) n (hi-1) := by
  obtain ⟨hnd,hcross⟩ := hst
  let sw := replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t)
  have hswlen : Zlength sw = n := by simp only [sw,Zlength_replace_Znth,hlen]
  have hread (q : Int) (hq : 0 ≤ q ∧ q < n) :
      Znth q sw 0 = if q=hi then Znth 0 t 0 else if q=0 then Znth hi t 0 else Znth q t 0 :=
    swap_Znth__sort_extract_phase t 0 hi q (by omega) (by omega) (by omega) (by omega)
  have hmax (p : Int) (hp : 0 ≤ p ∧ p ≤ hi) : Znth p t 0 ≤ Znth 0 t 0 :=
    heap_root_is_max__hpop_sift_left_child t (hi+1) p hheap (by omega)
  have htail := (nondecreasing_slice_iff t (hi+1) n (by omega) (by omega)).mp hnd
  refine ⟨?_,?_⟩
  · change Nondecreasing (sublist (hi-1+1) n sw)
    rw [show hi-1+1=hi by omega]
    apply (nondecreasing_slice_iff sw hi n (by omega) (by omega)).mpr
    intro i j hi' hij hj
    rw [hread i (by omega),hread j (by omega)]
    by_cases hie : i=hi
    · subst i
      simp only [if_pos rfl]
      by_cases hje : j=hi
      · subst j; simp
      · simp only [if_neg hje,if_neg (by omega : j ≠ 0)]
        exact hcross 0 j (by omega) (by omega) (by omega) hj
    · simp only [if_neg hie,if_neg (by omega : i ≠ 0),if_neg (by omega : j ≠ hi),if_neg (by omega : j ≠ 0)]
      exact htail i j (by omega) hij hj
  · intro p q hp hphi hqhi hqn
    rw [hread p (by omega),hread q (by omega)]
    simp only [if_neg (by omega : p ≠ hi)]
    by_cases hqe : q=hi
    · simp only [if_pos hqe]
      by_cases hpe : p=0
      · simp only [if_pos hpe]; exact hmax hi (by omega)
      · simp only [if_neg hpe]; exact hmax p (by omega)
    · simp only [if_neg hqe,if_neg (by omega : q ≠ 0)]
      by_cases hpe : p=0
      · simp only [if_pos hpe]; exact hcross hi q (by omega) (by omega) (by omega) hqn
      · simp only [if_neg hpe]; exact hcross p q hp (by omega) (by omega) hqn

theorem zip_prefix_perm__sort_extract_phase (t b t' b' : List Int) (m n : Int)
    (ht : Zlength t = n) (hb : Zlength b = n) (ht' : Zlength t' = n) (hb' : Zlength b' = n)
    (hm : 0 ≤ m ∧ m ≤ n) (hp : List.Perm (t.zip b) (t'.zip b'))
    (hst : sublist m n t' = sublist m n t) (hsb : sublist m n b' = sublist m n b) :
    List.Perm (sublist 0 m t) (sublist 0 m t') := by
  have hz (u : List Int) (hu : Zlength u=n) : Zlength (sublist 0 m u)=m := Zlength_sublist0 m u (by omega)
  have hsplit (u v : List Int) (hu : Zlength u=n) (hv : Zlength v=n) :
      u.zip v = (sublist 0 m u).zip (sublist 0 m v) ++ (sublist m n u).zip (sublist m n v) := by
    have hlen : Zlength (u.zip v)=n := (Zlength_combine__sort_extract_phase u v (by omega)).trans hu
    calc
      u.zip v = sublist 0 n (u.zip v) := (sublist_self _ n hlen.symm).symm
      _ = _ := by rw [sublist_split 0 n m _ (by omega) (by omega),
        sublist_combine__sort_extract_phase,sublist_combine__sort_extract_phase]
  rw [hsplit t b ht hb,hsplit t' b' ht' hb',hst,hsb] at hp
  have hpre := (List.perm_append_right_iff _).mp hp
  have hmap := hpre.map Prod.fst
  rw [map_fst_combine__sort_extract_phase _ _ (Int.ofNat_inj.mp ((hz t ht).trans (hz b hb).symm)),
    map_fst_combine__sort_extract_phase _ _ (Int.ofNat_inj.mp ((hz t' ht').trans (hz b' hb').symm))] at hmap
  exact hmap

theorem heap_sort_state_after_sift__sort_extract_phase (t b t1 b1 : List Int) (n m : Int)
    (ht : Zlength t=n) (hb : Zlength b=n) (ht1 : Zlength t1=n) (hb1 : Zlength b1=n)
    (hm : 0 ≤ m ∧ m ≤ n) (hp : List.Perm (t.zip b) (t1.zip b1))
    (hst : sublist m n t1 = sublist m n t) (hsb : sublist m n b1 = sublist m n b)
    (hstate : HeapSortState t n (m-1)) : HeapSortState t1 n (m-1) := by
  obtain ⟨hnd,hcross⟩ := hstate
  have hpre := zip_prefix_perm__sort_extract_phase t b t1 b1 m n ht hb ht1 hb1 hm hp hst hsb
  have hl0 := Zlength_sublist0 m t (by omega)
  have hl1 := Zlength_sublist0 m t1 (by omega)
  refine ⟨?_,?_⟩
  · simpa only [show m-1+1=m by omega,hst] using hnd
  · intro p q hp0 hpm hqm hqn
    have hq := congrArg (fun xs => Znth (q-m) xs 0) hst
    dsimp only at hq
    rw [Znth_sublist 0 m (q-m) n t1 (by omega) (by omega),
      Znth_sublist 0 m (q-m) n t (by omega) (by omega)] at hq
    simp only [Int.sub_add_cancel] at hq
    rw [hq]
    have hx : Znth p t1 0 ∈ sublist 0 m t := by
      apply hpre.mem_iff.mpr
      rw [← Znth_sublist0 0 p m t1 (by omega)]
      exact znth_mem _ p (by omega)
    obtain ⟨k,hk,he⟩ := mem_znth _ _ hx
    rw [Znth_sublist0 0 k m t (by omega)] at he
    rw [← he]
    exact hcross k q hk.1 (by omega) hqm hqn

theorem heap_sort_done_nondecreasing__sort_extract_phase (t : List Int) (n hi : Int)
    (hlen : Zlength t=n) (hlo : -1 ≤ hi) (hhi : hi ≤ 0) (hst : HeapSortState t n hi) :
    Nondecreasing t := by
  obtain ⟨hnd,hcross⟩ := hst
  by_cases he : hi = -1
  · subst hi
    simpa only [show (-1:Int)+1=0 by omega,sublist_self t n hlen.symm] using hnd
  · have h0 : hi=0 := by omega
    subst hi
    intro i j hi hij hj
    by_cases hi0 : i=0
    · subst i
      by_cases hj0 : j=0
      · subst j; exact le_refl _
      · exact hcross 0 j (by omega) (by omega) (by omega) (by omega)
    · have hnd' := (nondecreasing_slice_iff t 1 n (by omega) (by omega)).mp hnd
      exact hnd' i j (by omega) hij (by omega)

theorem heap_ordered_from_swap__sort_extract_phase (t : List Int) (n hi : Int)
    (hlen : Zlength t=n) (hhi1 : 1 ≤ hi) (hhi2 : hi ≤ n-1) (ho : HeapOrdered t (hi+1)) :
    HeapOrderedFrom (replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t)) hi 1 := by
  intro child hc0 hclt hcp
  have hpc := heap_parent_range__hpush_sift_up child hc0
  rw [Znth_swap_other__sift_cand_step t 0 hi (HeapParent child) (by omega) (by omega) (by omega) (by omega) (by omega),
    Znth_swap_other__sift_cand_step t 0 hi child (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact ho child hc0 (by omega) (by omega)


private theorem mod5_as_emod (x : Int) : Z.modulo x 5 = x % 5 :=
  Int.fmod_eq_emod_of_nonneg x (by decide)

private theorem div5_as_ediv (x : Int) : Z.div x 5 = x / 5 :=
  Int.fdiv_eq_ediv_of_nonneg x (by decide)

theorem rem5_quot5_spec__solver_safety_cand_a (x : Int) :
    x = 5*Z.quot x 5 + Z.rem x 5 ∧ -5 < Z.rem x 5 ∧ Z.rem x 5 < 5 :=
  ⟨Z.quot_rem x 5 (by decide),AUXLib.rem_bounds x 5 (by decide)⟩

theorem rem5_to_mod5__solver_safety_cand_a (x : Int) :
    Z.rem (Z.rem x 5+5) 5 = Z.modulo x 5 ∧ 0 ≤ Z.modulo x 5 ∧ Z.modulo x 5 < 5 := by
  obtain ⟨he,hlo,hhi⟩ := rem5_quot5_spec__solver_safety_cand_a x
  rw [AUXLib.rem_eq_mod (Z.rem x 5+5) 5 (by omega) (by decide),mod5_as_emod,mod5_as_emod]
  omega

theorem rem5_shift_bound__solver_safety_cand_a (x : Int) :
    0 ≤ Z.rem (Z.rem x 5+5) 5 ∧ Z.rem (Z.rem x 5+5) 5 < 5 := by
  obtain ⟨he,hb⟩ := rem5_to_mod5__solver_safety_cand_a x
  rwa [he]

theorem rem5_shift_bounds__solver_safety_cand_b (a : Int) :
    0 ≤ Z.rem (Z.rem a 5+5) 5 ∧ Z.rem (Z.rem a 5+5) 5 < 5 := rem5_shift_bound__solver_safety_cand_a a

theorem quot5_nonneg_bound__solver_safety_cand_b (x m : Int) (hx : 0 ≤ x) (hm : x ≤ 5*m) :
    0 ≤ Z.quot x 5 ∧ Z.quot x 5 ≤ m :=
  ⟨Z.quot_pos x 5 hx (by decide),Z.quot_le_upper_bound x 5 m (by decide) hm⟩

theorem target_quot_bounds__solver_safety_cand_b (s j : Int)
    (hs : 1000000000 ≤ s ∧ s ≤ 3000000000) (hj : 0 ≤ j ∧ j < 5) :
    0 ≤ Z.quot (s+Z.rem (Z.rem (j-s) 5+5) 5-j) 5 ∧
      Z.quot (s+Z.rem (Z.rem (j-s) 5+5) 5-j) 5 ≤ 600000001 := by
  have h := rem5_shift_bound__solver_safety_cand_a (j-s)
  exact quot5_nonneg_bound__solver_safety_cand_b _ _ (by omega) (by omega)

theorem sweep_total_int64_bounds__solver_safety_sweep_a (k W j x : Int)
    (hk0 : 0 ≤ k) (hk : k ≤ 200000) (hw0 : 1 ≤ W) (hw : W ≤ 1000)
    (hj0 : 0 ≤ j) (hj : j < 5) (hx0 : 1000000000 ≤ x) (hx : x ≤ 3000000004) :
    (0 ≤ Z.quot (x-j) 5 ∧ Z.quot (x-j) 5 ≤ 600000001) ∧
    (0 ≤ k*Z.quot (x-j) 5 ∧ k*Z.quot (x-j) 5 ≤ 120000000200000) ∧
    0 ≤ k*Z.quot (x-j) 5*W ∧ k*Z.quot (x-j) 5*W ≤ 120000000200000000 := by
  have hq := quot5_nonneg_bound__solver_safety_cand_b (x-j) 600000001 (by omega) (by omega)
  have hp0 := Int.mul_nonneg hk0 hq.1
  have hp : k*Z.quot (x-j) 5 ≤ 120000000200000 :=
    (Int.mul_le_mul_of_nonneg_right hk hq.1).trans
      (Int.mul_le_mul_of_nonneg_left hq.2 (by decide))
  have htotal : k*Z.quot (x-j) 5*W ≤ 120000000200000000 :=
    (Int.mul_le_mul_of_nonneg_right hp (by omega)).trans
      (Int.mul_le_mul_of_nonneg_left hw (by decide))
  exact ⟨hq,⟨hp0,hp⟩,Int.mul_nonneg hp0 (by omega),htotal⟩

theorem sweep_total_int64_bounds__solver_safety_sweep_b (k W j T hsum : Int)
    (hk0 : 2 ≤ k) (hk : k ≤ 200000) (hw0 : 1 ≤ W) (hw : W ≤ 1000)
    (hj0 : 0 ≤ j) (hj : j < 5) (ht0 : 1000000000 ≤ T) (ht : T ≤ 3000000004)
    (hlo : -300000000000000000 ≤ hsum) (hhi : hsum ≤ 300000000000000000) :
    0 ≤ k*Z.quot (T-j) 5 ∧ k*Z.quot (T-j) 5 ≤ 120000000200000 ∧
    0 ≤ k*Z.quot (T-j) 5*W ∧ k*Z.quot (T-j) 5*W ≤ 120000000200000000 ∧
    -300000000000000000 ≤ hsum+k*Z.quot (T-j) 5*W ∧
      hsum+k*Z.quot (T-j) 5*W ≤ 420000000200000000 := by
  have h := sweep_total_int64_bounds__solver_safety_sweep_a k W j T (by omega) hk hw0 hw hj0 hj ht0 ht
  exact ⟨h.2.1.1,h.2.1.2,h.2.2.1,h.2.2.2,by omega,by omega⟩

theorem replace_znth_length__solver_shift_loop (A : Type) (n : Nat) (l : List A) (a : A) :
    (replace_nth n l a).length = l.length := length_replace_nth__sort_extract_phase l n a

theorem zlength_replace_Znth__solver_shift_loop (A : Type) (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l) = Zlength l := Zlength_replace_Znth l n v

theorem shifted_prefix_step__solver_shift_loop (values sh : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength sh) (hpre : ShiftedPrefix values sh i) :
    ShiftedPrefix values (replace_Znth i (Znth i values 0+2000000000) sh) (i+1) := by
  intro q hq
  by_cases he : q=i
  · subst q; exact Znth_replace_Znth_Same 0 sh i _ hi
  · rw [Znth_replace_Znth_Diff 0 sh i q _ hi (by omega) (Ne.symm he)]
    exact hpre q (by omega)

theorem residue_best_zero__solver_shift_loop (values : List Int) (k b c : Int) :
    ResidueBest values k b c 0 (-1) := by
  refine Or.inl ⟨rfl,?_⟩
  rintro v ⟨j,hj,_⟩
  omega

theorem rem_norm__solver_cand_fill (a : Int) : Z.rem (Z.rem a 5+5) 5 = Z.modulo a 5 :=
  (rem5_to_mod5__solver_safety_cand_a a).1

theorem target_point_normal_form__solver_cand_fill (s j : Int)
    (hj : 0 ≤ j ∧ j < 5) (hs : j ≤ s) :
    s+Z.rem (Z.rem (j-s) 5+5) 5 = TargetPoint s j ∧
      Z.quot (TargetPoint s j-j) 5 = Z.div (TargetPoint s j-j) 5 := by
  refine ⟨by rw [rem_norm__solver_cand_fill]; rfl,?_⟩
  have h : 0 ≤ Z.modulo (j-s) 5 := (rem5_to_mod5__solver_safety_cand_a (j-s)).2.1
  rw [div5_as_ediv]
  exact Int.tdiv_eq_ediv_of_nonneg (by unfold TargetPoint; omega)

theorem cand_prefix_step__solver_cand_fill (sh t b : List Int) (j W c i : Int)
    (hj : 0 ≤ j ∧ j < 5) (hi0 : 0 ≤ i) (hit : i < Zlength t) (hib : i < Zlength b)
    (hjs : j ≤ Znth i sh 0) (hpre : CandPrefix sh j W c i t b) :
    CandPrefix sh j W c (i+1)
      (replace_Znth i (Znth i sh 0+Z.rem (Z.rem (j-Znth i sh 0) 5+5) 5) t)
      (replace_Znth i (Z.rem (Z.rem (j-Znth i sh 0) 5+5) 5*c -
        Z.quot (Znth i sh 0+Z.rem (Z.rem (j-Znth i sh 0) 5+5) 5-j) 5*W) b) := by
  have ht := target_point_normal_form__solver_cand_fill (Znth i sh 0) j hj hjs
  intro q hq
  by_cases he : q=i
  · subst q
    rw [Znth_replace_Znth_Same 0 t i _ (by omega),Znth_replace_Znth_Same 0 b i _ (by omega)]
    refine ⟨ht.1,?_⟩
    rw [ht.1,ht.2,rem_norm__solver_cand_fill]
    rfl
  · rw [Znth_replace_Znth_Diff 0 t i q _ (by omega) (by omega) (Ne.symm he),
      Znth_replace_Znth_Diff 0 b i q _ (by omega) (by omega) (Ne.symm he)]
    exact hpre q (by omega)

theorem sublist_0_0_nil__solver_postsort_sweep_init (l : List Int) : sublist 0 0 l = [] := rfl

theorem heap_ordered_zero__solver_postsort_sweep_init (l : List Int) : HeapOrdered l 0 := by
  intro child hc0 hclt _
  omega

theorem zsum_sublist_0_0__solver_postsort_sweep_init (l : List Int) : ZSum (sublist 0 0 l)=0 := rfl

theorem sub_multiset_nil_inv__solver_postsort_sweep_init (m : List Int) (h : SubMultiset m []) : m=[] := by
  obtain ⟨rest,hp⟩ := h
  have hl := hp.length_eq
  simp only [List.length_nil,List.length_append] at hl
  exact List.length_eq_zero_iff.mp (by omega)

theorem heap_content_empty__solver_postsort_sweep_init (sb hl : List Int) :
    HeapContent sb 0 (sublist 0 0 hl) 0 := by
  change MinSubMultiset [] [] ∧ 0=ZSum []
  refine ⟨⟨⟨[],List.Perm.refl _⟩,?_⟩,rfl⟩
  intro m' hm' _
  rw [sub_multiset_nil_inv__solver_postsort_sweep_init m' hm']

theorem best_state_ext__solver_postsort_sweep_init (P Q : Int → Prop) (best : Int)
    (he : ∀ v, P v ↔ Q v) (hst : BestState P best) : BestState Q best := by
  rcases hst with ⟨hb,hn⟩ | ⟨hb,a,⟨ha,hmin⟩,heq⟩
  · exact Or.inl ⟨hb,fun v hv => hn v ((he v).mpr hv)⟩
  · exact Or.inr ⟨hb,a,⟨(he a).mp ha,fun b hb => hmin b ((he b).mpr hb)⟩,heq⟩

theorem sweep_best_at_zero__solver_postsort_sweep_init (values : List Int) (k b c j : Int)
    (st sb : List Int) (W best : Int) (hk : 2 ≤ k) (hbest : ResidueBest values k b c j best) :
    SweepBest values k b c j st sb W 0 best := by
  apply best_state_ext__solver_postsort_sweep_init _ _ best ?_ hbest
  intro v
  constructor
  · exact Or.inl
  · rintro (h | ⟨i,hi,hlt,_⟩)
    · exact h
    · omega


theorem zsum_cons__solver_heap_maintain (x : Int) (l : List Int) : ZSum (x::l)=x+ZSum l := rfl

theorem zsum_permutation__solver_heap_maintain (l1 l2 : List Int) (hp : List.Perm l1 l2) : ZSum l1=ZSum l2 := by
  induction hp with
  | nil => rfl
  | cons a hp ih => simpa only [zsum_cons__solver_heap_maintain] using congrArg (a+·) ih
  | swap a b l => simp only [zsum_cons__solver_heap_maintain]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem zsum_bounds__solver_heap_maintain (l : List Int) (lo hi : Int)
    (hb : ∀ y, y ∈ l → lo ≤ y ∧ y ≤ hi) :
    Zlength l*lo ≤ ZSum l ∧ ZSum l ≤ Zlength l*hi := by
  induction l with
  | nil => simp [ZSum]
  | cons a l ih =>
    have ha := hb a List.mem_cons_self
    have hh := ih (fun y hy => hb y (List.mem_cons_of_mem a hy))
    rw [Zlength_cons,zsum_cons__solver_heap_maintain]
    constructor <;> nlinarith

theorem Znth_In__solver_heap_maintain (l : List Int) (i : Int) :
    (0 ≤ i ∧ i < Zlength l) → Znth i l 0 ∈ l := znth_mem l i

theorem In_Znth__solver_heap_maintain (l : List Int) (y : Int) :
    y ∈ l → ∃ i, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l 0=y := mem_znth l y

theorem forall_bounds_permutation__solver_heap_maintain (l1 l2 : List Int) (lo hi : Int)
    (hp : List.Perm l1 l2) (hb : ∀ y, y ∈ l1 → lo ≤ y ∧ y ≤ hi)
    (q : Int) (hq : 0 ≤ q ∧ q < Zlength l2) : lo ≤ Znth q l2 0 ∧ Znth q l2 0 ≤ hi :=
  hb _ (hp.mem_iff.mpr (znth_mem l2 q hq))

theorem sublist_In_bounds__solver_heap_maintain (l : List Int) (n lo hi : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength l) (hb : ∀ q, (0 ≤ q ∧ q < n) → lo ≤ Znth q l 0 ∧ Znth q l 0 ≤ hi)
    (y : Int) (hy : y ∈ sublist 0 n l) : lo ≤ y ∧ y ≤ hi := by
  obtain ⟨i,hi',he⟩ := mem_znth _ y hy
  rw [Zlength_sublist0 n l hn] at hi'
  rw [Znth_sublist0 0 i n l hi'] at he
  simpa only [he] using hb i hi'

-- For integers, List.count computes the same equality-based multiplicities as
-- Coq count_occ Z.eq_dec. The source argument order is preserved by each theorem.
theorem perm_count__solver_heap_maintain (l1 l2 : List Int) (hp : List.Perm l1 l2) (z : Int) :
    l1.count z = l2.count z := hp.count_eq z

theorem count_app__solver_heap_maintain (l1 l2 : List Int) (z : Int) :
    (l1++l2).count z = l1.count z+l2.count z := List.count_append

theorem submultiset_count__solver_heap_maintain (m l : List Int) (hs : SubMultiset m l) (z : Int) :
    m.count z ≤ l.count z := by
  obtain ⟨rest,hp⟩ := hs
  have hc := hp.count_eq z
  rw [List.count_append] at hc
  omega

theorem count_submultiset__solver_heap_maintain (m l : List Int)
    (hc : ∀ z, m.count z ≤ l.count z) : SubMultiset m l := by
  obtain ⟨mid,hp,hs⟩ := List.subperm_iff_count.mpr hc
  obtain ⟨rest,hr⟩ := hs.exists_perm_append
  exact ⟨rest,hr.trans (hp.append_right rest)⟩

theorem submultiset_length__solver_heap_maintain (m l : List Int) (hs : SubMultiset m l) :
    Zlength m ≤ Zlength l := by
  obtain ⟨rest,hp⟩ := hs
  have hl := hp.length_eq
  simp only [List.length_append] at hl
  simp only [Zlength,Int.ofNat_eq_coe]
  omega

theorem submultiset_full_perm__solver_heap_maintain (m l : List Int)
    (hs : SubMultiset m l) (hlen : Zlength m=Zlength l) : List.Perm l m := by
  obtain ⟨rest,hp⟩ := hs
  have hl := hp.length_eq
  have hm := Int.ofNat_inj.mp hlen
  have hr : rest=[] := List.length_eq_zero_iff.mp (by simp only [List.length_append] at hl; omega)
  simpa only [hr,List.append_nil] using hp

theorem min_sub_multiset_whole__solver_heap_maintain (l m : List Int) (hp : List.Perm l m) :
    MinSubMultiset l m := by
  refine ⟨⟨[],by simpa only [List.append_nil] using hp⟩,?_⟩
  intro m' hs hm
  have hl : Zlength m'=Zlength l := hm.trans (congrArg Int.ofNat hp.length_eq).symm
  have hperm := hp.symm.trans (submultiset_full_perm__solver_heap_maintain m' l hs hl)
  exact le_of_eq (zsum_permutation__solver_heap_maintain m m' hperm)

theorem submultiset_extend__solver_heap_maintain (L M N : List Int)
    (hm : SubMultiset M L) (hn : SubMultiset N L) (hlen : Zlength N < Zlength M) :
    ∃ y, y ∈ M ∧ SubMultiset (y::N) L := by
  classical
  by_contra hnone
  have hcnt : ∀ z, M.count z ≤ N.count z := by
    intro z
    by_cases hz : z ∈ M
    · have hnot : ¬SubMultiset (z::N) L := fun hs => hnone ⟨z,hz,hs⟩
      have hnotcnt : ¬∀ w, (z::N).count w ≤ L.count w := fun hc =>
        hnot (count_submultiset__solver_heap_maintain (z::N) L hc)
      obtain ⟨w,hw⟩ := not_forall.mp hnotcnt
      have hnw := submultiset_count__solver_heap_maintain N L hn w
      have hmz := submultiset_count__solver_heap_maintain M L hm z
      by_cases he : w=z
      · subst w; simp only [List.count_cons_self] at hw; omega
      · have hcons : (z::N).count w=N.count w := by simp [List.count_cons,Ne.symm he]
        rw [hcons] at hw; omega
    · rw [List.count_eq_zero_of_not_mem hz]
      omega
  have hsub := count_submultiset__solver_heap_maintain M N hcnt
  have h := submultiset_length__solver_heap_maintain M N hsub
  omega


theorem min_sub_multiset_push_pop__solver_heap_maintain (L M M' : List Int) (x m : Int)
    (hmin : MinSubMultiset L M) (hp : List.Perm (x::M) (m::M'))
    (hub : ∀ y, y ∈ x::M → y ≤ m) : MinSubMultiset (L++[x]) M' := by
  obtain ⟨hsub,hmin⟩ := hmin
  obtain ⟨rest,hrest⟩ := hsub
  have hl : Zlength M'=Zlength M := by
    have h := hp.length_eq
    simp only [List.length_cons] at h
    simp only [Zlength,Int.ofNat_eq_coe]
    omega
  have hsum : ZSum M'=x+ZSum M-m := by
    have h := zsum_permutation__solver_heap_maintain _ _ hp
    simp only [zsum_cons__solver_heap_maintain] at h
    omega
  have hxm := hub x List.mem_cons_self
  refine ⟨⟨m::rest,?_⟩,?_⟩
  · exact (hrest.append_right [x]).trans
      ((List.perm_append_singleton x (M++rest)).trans
        ((hp.append_right rest).trans List.perm_middle.symm))
  · intro N hsubN hlenN
    by_cases hnl : SubMultiset N L
    · have h := hmin N hnl (hlenN.trans hl)
      omega
    · have hcnt (z : Int) : N.count z ≤ L.count z + [x].count z := by
        have h := submultiset_count__solver_heap_maintain N (L++[x]) hsubN z
        simpa only [List.count_append] using h
      have hxin : x ∈ N := by
        by_contra hxnot
        apply hnl
        apply count_submultiset__solver_heap_maintain
        intro z
        have h := hcnt z
        by_cases hz : z=x
        · subst z
          rw [List.count_eq_zero_of_not_mem hxnot]
          omega
        · simpa [List.count_singleton,Ne.symm hz] using h
      let N0 := N.erase x
      have hpn : List.Perm N (x::N0) := List.perm_cons_erase hxin
      have hsubN0 : SubMultiset N0 L := by
        apply count_submultiset__solver_heap_maintain
        intro z
        have hc := hcnt z
        have hpc := hpn.count_eq z
        by_cases hz : z=x
        · subst z
          simp only [List.count_cons_self,List.count_nil] at hc hpc
          omega
        · simp [List.count_cons,List.count_singleton,Ne.symm hz] at hc hpc
          omega
      have hn0 : Zlength N0+1=Zlength N := by
        have h := hpn.length_eq
        simp only [List.length_cons] at h
        simp only [Zlength,Int.ofNat_eq_coe]
        omega
      obtain ⟨y,hyM,hsuby⟩ := submultiset_extend__solver_heap_maintain L M N0 ⟨rest,hrest⟩ hsubN0 (by omega)
      have hmy := hmin (y::N0) hsuby (by rw [Zlength_cons]; omega)
      have hym := hub y (List.mem_cons_of_mem x hyM)
      have hnsum : ZSum N=x+ZSum N0 := by
        simpa only [zsum_cons__solver_heap_maintain] using zsum_permutation__solver_heap_maintain _ _ hpn
      rw [zsum_cons__solver_heap_maintain] at hmy
      omega


set_option maxHeartbeats 2000000 in
private theorem perm_nat_index {A : Type} (l l' : List A) (d : A) (hp : List.Perm l l') :
    ∃ f : Nat → Nat,
      (∀ x, x < l'.length → f x < l.length) ∧
      (∀ x y, x < l'.length → y < l'.length → f x=f y → x=y) ∧
      ∀ x, x < l'.length → l'.getD x d = l.getD (f x) d := by
  induction hp with
  | nil => exact ⟨id,by simp,by simp,by simp⟩
  | @cons a l1 l2 hp ih =>
    obtain ⟨f,hb,hinj,hget⟩ := ih
    let g : Nat → Nat | 0 => 0 | n+1 => f n+1
    refine ⟨g,?_,?_,?_⟩
    · intro x hx
      cases x with
      | zero => simp [g]
      | succ x => have h := hb x (by simpa using hx); simp only [g,List.length_cons]; omega
    · intro x y hx hy he
      cases x with
      | zero =>
        cases y with
        | zero => rfl
        | succ y => change 0=f y+1 at he; omega
      | succ x =>
        cases y with
        | zero => change f x+1=0 at he; omega
        | succ y =>
          have h : f x=f y := Nat.add_right_cancel (show f x+1=f y+1 from he)
          have heq := hinj x y (by simpa using hx) (by simpa using hy) h
          omega
    · intro x hx
      cases x with
      | zero => rfl
      | succ x => simpa only [g,List.getD_cons_succ] using hget x (by simpa using hx)
  | @swap a b l =>
    let g : Nat → Nat | 0 => 1 | 1 => 0 | n+2 => n+2
    refine ⟨g,?_,?_,?_⟩
    · intro x hx
      rcases x with _ | (_ | x) <;> simp only [g,List.length_cons] at * <;> omega
    · intro x y hx hy he
      rcases x with _ | (_ | x) <;> rcases y with _ | (_ | y) <;>
        simp only [g] at he ⊢ <;> omega
    · intro x hx
      rcases x with _ | (_ | x) <;> rfl
  | @trans l1 l2 l3 hp1 hp2 ih1 ih2 =>
    obtain ⟨f,hf,hfi,hfg⟩ := ih1
    obtain ⟨g,hg,hgi,hgg⟩ := ih2
    refine ⟨fun x => f (g x),fun x hx => hf (g x) (hg x hx),?_,?_⟩
    · intro x y hx hy he
      exact hgi x y hx hy (hfi (g x) (g y) (hg x hx) (hg y hy) he)
    · intro x hx
      exact (hgg x hx).trans (hfg (g x) (hg x hx))

theorem perm_index__solver_sweep_value (A : Type) (l l' : List A) (d : A) (hp : List.Perm l l') :
    ∃ f : Int → Int,
      (∀ x, (0 ≤ x ∧ x < Zlength l') → 0 ≤ f x ∧ f x < Zlength l) ∧
      (∀ x y, (0 ≤ x ∧ x < Zlength l') → (0 ≤ y ∧ y < Zlength l') → f x=f y → x=y) ∧
      ∀ x, (0 ≤ x ∧ x < Zlength l') → Znth x l' d=Znth (f x) l d := by
  obtain ⟨f,hb,hinj,hget⟩ := perm_nat_index l l' d hp
  refine ⟨fun x => (f x.toNat : Int),?_,?_,?_⟩
  · intro x hx
    have hn : x.toNat < l'.length := by simp only [Zlength,Int.ofNat_eq_coe] at hx; omega
    have h := hb x.toNat hn
    simp only [Zlength,Int.ofNat_eq_coe]
    omega
  · intro x y hx hy he
    have hxn : x.toNat < l'.length := by simp only [Zlength,Int.ofNat_eq_coe] at hx; omega
    have hyn : y.toNat < l'.length := by simp only [Zlength,Int.ofNat_eq_coe] at hy; omega
    have h := hinj x.toNat y.toNat hxn hyn (Int.ofNat_inj.mp he)
    omega
  · intro x hx
    have hn : x.toNat < l'.length := by simp only [Zlength,Int.ofNat_eq_coe] at hx; omega
    simpa only [Znth,Int.toNat_natCast] using hget x.toNat hn

theorem Znth_combine__solver_sweep_value (A B : Type) (l1 : List A) (l2 : List B)
    (d1 : A) (d2 : B) (q : Int) (hlen : Zlength l1=Zlength l2) :
    Znth q (l1.zip l2) (d1,d2)=(Znth q l1 d1,Znth q l2 d2) :=
  getD_zip_equal l1 l2 q.toNat d1 d2 (Int.ofNat_inj.mp hlen)

theorem Zlength_combine__solver_sweep_value (A B : Type) (l1 : List A) (l2 : List B)
    (hlen : Zlength l1=Zlength l2) : Zlength (l1.zip l2)=Zlength l1 :=
  Zlength_combine__sort_extract_phase l1 l2 hlen

theorem nodup_Znth__solver_sweep_value (l : List Int)
    (hinj : ∀ x y, (0 ≤ x ∧ x < Zlength l) → (0 ≤ y ∧ y < Zlength l) →
      Znth x l 0=Znth y l 0 → x=y) : l.Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  have h := hinj i.val j.val (by simp only [Zlength,Int.ofNat_eq_coe]; omega) (by simp only [Zlength,Int.ofNat_eq_coe]; omega)
    (by simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem j.isLt,Option.getD_some] using he)
  omega

theorem zsum_map_add__solver_sweep_value (dd : Int) (l : List Int) :
    ZSum (l.map (fun x => x+dd))=ZSum l+Zlength l*dd := by
  induction l with
  | nil => simp [ZSum]
  | cons a l ih =>
    simp only [List.map_cons,zsum_cons__solver_heap_maintain,Zlength_cons,ih]
    ring

theorem zsum_bounds__solver_sweep_value (lo hi : Int) (l : List Int)
    (hb : Forall (fun x => lo ≤ x ∧ x ≤ hi) l) :
    Zlength l*lo ≤ ZSum l ∧ ZSum l ≤ Zlength l*hi :=
  zsum_bounds__solver_heap_maintain l lo hi (Forall.iff_forall_mem.mp hb)

theorem raise_cost_normal_form__solver_sweep_value (b c «from» target : Int)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (ht : «from» ≤ target) :
    RaiseCost b c «from» target
      (Z.modulo (target-«from») 5*c+Z.div (target-«from») 5*WCost b c) := by
  rw [mod5_as_emod,div5_as_ediv]
  have hr0 := Int.emod_nonneg (target-«from») (by omega : (5:Int)≠0)
  have hr5 := Int.emod_lt_of_pos (target-«from») (by omega : (0:Int)<5)
  have hq0 : 0 ≤ (target-«from»)/5 := Int.ediv_nonneg (by omega) (by omega)
  have he := Int.emod_add_ediv (target-«from») 5
  rcases le_total b (5*c) with hbc | hcb
  · simp only [WCost,min_eq_left hbc]
    refine ⟨_,⟨?_,?_⟩,rfl⟩
    · refine ⟨(target-«from»)/5,(target-«from»)%5,hq0,hr0,by omega,?_⟩
      ring
    · rintro v ⟨blogs,comments,hbl,hco,hdec,rfl⟩
      have hle : blogs ≤ (target-«from»)/5 := by omega
      nlinarith
  · simp only [WCost,min_eq_right hcb]
    refine ⟨_,⟨?_,?_⟩,rfl⟩
    · refine ⟨0,target-«from»,by omega,by omega,by omega,?_⟩
      nlinarith
    · rintro v ⟨blogs,comments,hbl,hco,hdec,rfl⟩
      nlinarith

theorem target_point_mod__solver_sweep_value (s j : Int) (hj : 0 ≤ j ∧ j < 5) :
    Z.modulo (TargetPoint s j) 5=j := by
  simp only [TargetPoint,mod5_as_emod]
  omega

private theorem normalized_cost_eq (s j W c t : Int) (hj : 0 ≤ j ∧ j < 5)
    (ht : Z.modulo t 5=j) :
    NormalizedBase s j W c+Z.div (t-j) 5*W=
      Z.modulo (t-s) 5*c+Z.div (t-s) 5*W := by
  simp only [NormalizedBase,TargetPoint,mod5_as_emod,div5_as_ediv] at *
  have hr : (t-s)%5=(j-s)%5 := by omega
  have hq : (t-s)/5=(t-j)/5-(s+(j-s)%5-j)/5 := by omega
  rw [hr,hq]
  ring

theorem raise_cost_shifted__solver_sweep_value (b c W j s t' : Int)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hw : W=WCost b c) (hj : 0 ≤ j ∧ j < 5)
    (ht : TargetPoint s j ≤ t') (hm : Z.modulo t' 5=j) :
    RaiseCost b c (s-2000000000) (t'-2000000000)
      (NormalizedBase s j W c+Z.div (t'-j) 5*W) := by
  rw [normalized_cost_eq s j W c t' hj hm,hw]
  have hs : s ≤ t' := by
    have h := Int.emod_nonneg (j-s) (by omega : (5:Int)≠0)
    simp only [TargetPoint,mod5_as_emod] at ht
    omega
  have hh := raise_cost_normal_form__solver_sweep_value b c (s-2000000000) (t'-2000000000) hb hc (by omega)
  simpa only [show t'-2000000000-(s-2000000000)=t'-s by omega] using hh

theorem nth_map_len__solver_sweep_value (A B : Type) (f : A → B) (l : List A)
    (n : Nat) (da : A) (db : B) (hn : n < l.length) :
    (l.map f).getD n db=f (l.getD n da) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hn,
    Option.map_some,Option.getD_some]

theorem Forall_Znth__solver_sweep_value (P : Int → Prop) (l : List Int)
    (hp : ∀ m, (0 ≤ m ∧ m < Zlength l) → P (Znth m l 0)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro y hy
  obtain ⟨i,hi,rfl⟩ := mem_znth l y hy
  exact hp i hi

theorem perm_Zlength__solver_sweep_value (A : Type) (l l' : List A) (hp : l.Perm l') :
    Zlength l=Zlength l' := congrArg Int.ofNat hp.length_eq

theorem norm_cost_bounds__solver_sweep_value (b c W j s t' : Int)
    (hb : 1 ≤ b) (hb' : b ≤ 1000) (hc : 1 ≤ c) (hc' : c ≤ 1000)
    (hw : W=WCost b c) (hj : 0 ≤ j ∧ j < 5)
    (ht : TargetPoint s j ≤ t') (hm : Z.modulo t' 5=j)
    (hs : 1000000000 ≤ s) (ht' : t' ≤ 3000000004) :
    0 ≤ NormalizedBase s j W c+Z.div (t'-j) 5*W ∧
      NormalizedBase s j W c+Z.div (t'-j) 5*W ≤ 400000004000 := by
  rw [normalized_cost_eq s j W c t' hj hm,mod5_as_emod,div5_as_ediv]
  have hw0 : 1 ≤ W := by rw [hw,WCost]; exact le_min hb (by omega)
  have hw1 : W ≤ 1000 := by rw [hw,WCost]; exact (min_le_left _ _).trans hb'
  have hr0 := Int.emod_nonneg (t'-s) (by omega : (5:Int)≠0)
  have hr5 := Int.emod_lt_of_pos (t'-s) (by omega : (0:Int)<5)
  have hmod := Int.emod_nonneg (j-s) (by omega : (5:Int)≠0)
  simp only [TargetPoint,mod5_as_emod] at ht
  have hd : 0 ≤ t'-s ∧ t'-s ≤ 2000000004 := by omega
  have hq : 0 ≤ (t'-s)/5 ∧ (t'-s)/5 ≤ 400000000 := by omega
  constructor
  · exact add_nonneg (mul_nonneg hr0 (by omega)) (mul_nonneg hq.1 (by omega))
  · have h1 : (t'-s)%5*c ≤ 4000 := by nlinarith
    have h2 : (t'-s)/5*W ≤ 400000000000 := by nlinarith
    omega

theorem ksmall_sum_unique__solver_best_update (l : List Int) (k s1 s2 : Int)
    (h1 : KSmallSum l k s1) (h2 : KSmallSum l k s2) : s1=s2 := by
  obtain ⟨m1,⟨hsub1,hmin1⟩,hlen1,rfl⟩ := h1
  obtain ⟨m2,⟨hsub2,hmin2⟩,hlen2,rfl⟩ := h2
  exact le_antisymm (hmin1 m2 hsub2 (by omega)) (hmin2 m1 hsub1 (by omega))

theorem sweep_value_unique__solver_best_update (st sb : List Int) (k j W i v1 v2 : Int)
    (h1 : SweepValue st sb k j W i v1) (h2 : SweepValue st sb k j W i v2) : v1=v2 := by
  obtain ⟨s1,hs1,rfl⟩ := h1
  obtain ⟨s2,hs2,rfl⟩ := h2
  rw [ksmall_sum_unique__solver_best_update _ k s1 s2 hs1 hs2]

theorem sweep_set_step__solver_best_update (values : List Int) (k b c j : Int)
    (st sb : List Int) (W i total : Int) (hi : k-1 ≤ i)
    (hs : SweepValue st sb k j W i total) (v : Int) :
    SweepSet values k b c j st sb W (i+1) v ↔
      (SweepSet values k b c j st sb W i v ∨ v=total) := by
  constructor
  · rintro (h | ⟨i',hk,hi',hv⟩)
    · exact Or.inl (Or.inl h)
    · by_cases he : i'=i
      · subst i'; exact Or.inr (sweep_value_unique__solver_best_update st sb k j W i v total hv hs)
      · exact Or.inl (Or.inr ⟨i',hk,by omega,hv⟩)
  · rintro ((h | ⟨i',hk,hi',hv⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨i',hk,by omega,hv⟩
    · exact Or.inr ⟨i,hi,by omega,hs⟩

theorem sweep_set_stall__solver_best_update (values : List Int) (k b c j : Int)
    (st sb : List Int) (W i : Int) (hi : i+1 < k) (v : Int) :
    SweepSet values k b c j st sb W (i+1) v ↔ SweepSet values k b c j st sb W i v := by
  constructor
  · rintro (h | ⟨i',hk,hi',_⟩)
    · exact Or.inl h
    · omega
  · rintro (h | ⟨i',hk,hi',_⟩)
    · exact Or.inl h
    · omega

theorem min_id_intro__solver_best_update (X : Int → Prop) (n : Int)
    (hn : X n) (hmin : ∀ b, X b → n ≤ b) : min_value_of_subset (· ≤ ·) X (fun x => x) n :=
  ⟨n,⟨hn,hmin⟩,rfl⟩

theorem min_id_elim__solver_best_update (X : Int → Prop) (n : Int)
    (hm : min_value_of_subset (· ≤ ·) X (fun x => x) n) : X n ∧ ∀ b, X b → n ≤ b := by
  obtain ⟨a,⟨ha,hmin⟩,rfl⟩ := hm
  exact ⟨ha,hmin⟩

theorem best_state_same__solver_best_update (P Q : Int → Prop) (best : Int)
    (he : ∀ v, Q v ↔ P v) (hb : BestState P best) : BestState Q best :=
  best_state_ext__solver_postsort_sweep_init P Q best (fun v => (he v).symm) hb

theorem best_state_step__solver_best_update (P Q : Int → Prop) (best total : Int)
    (hb : BestState P best) (he : ∀ v, Q v ↔ (P v ∨ v=total))
    (ht : 0 ≤ total) (hless : best < 0 ∨ total < best) : BestState Q total := by
  refine Or.inr ⟨ht,min_id_intro__solver_best_update Q total ((he total).mpr (Or.inr rfl)) ?_⟩
  intro v hv
  rcases (he v).mp hv with hp | rfl
  · rcases hb with ⟨_,hn⟩ | ⟨hb0,hm⟩
    · exact False.elim (hn v hp)
    · have h := (min_id_elim__solver_best_update P best hm).2 v hp; omega
  · exact le_refl _

theorem best_state_keep__solver_best_update (P Q : Int → Prop) (best total : Int)
    (hb : BestState P best) (he : ∀ v, Q v ↔ (P v ∨ v=total))
    (hb0 : 0 ≤ best) (hle : best ≤ total) : BestState Q best := by
  rcases hb with ⟨hn,_⟩ | ⟨_,hm⟩
  · omega
  · obtain ⟨hp,hmin⟩ := min_id_elim__solver_best_update P best hm
    refine Or.inr ⟨hb0,min_id_intro__solver_best_update Q best ((he best).mpr (Or.inl hp)) ?_⟩
    intro v hv
    rcases (he v).mp hv with hv | rfl
    · exact hmin v hv
    · exact hle

theorem zsum_perm__solver_residue_rollup (l1 l2 : List Int) (hp : l1.Perm l2) : ZSum l1=ZSum l2 :=
  zsum_permutation__solver_heap_maintain l1 l2 hp

theorem abssum_app__solver_residue_rollup (l1 l2 : List Int) :
    (l1++l2).foldr (fun x a => |x|+a) 0=l1.foldr (fun x a => |x|+a) 0+l2.foldr (fun x a => |x|+a) 0 := by
  induction l1 with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append,List.foldr_cons,ih]; omega

theorem abssum_perm__solver_residue_rollup (l1 l2 : List Int) (hp : l1.Perm l2) :
    l1.foldr (fun x a => |x|+a) 0=l2.foldr (fun x a => |x|+a) 0 := by
  induction hp with
  | nil => rfl
  | cons a hp ih => simp only [List.foldr_cons,ih]
  | swap a b l => simp only [List.foldr_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem abssum_nonneg__solver_residue_rollup (l : List Int) : 0 ≤ l.foldr (fun x a => |x|+a) 0 := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih => exact add_nonneg (abs_nonneg a) ih

theorem zsum_abs_bound__solver_residue_rollup (l : List Int) :
    -l.foldr (fun x a => |x|+a) 0 ≤ ZSum l ∧ ZSum l ≤ l.foldr (fun x a => |x|+a) 0 := by
  induction l with
  | nil => simp [ZSum]
  | cons a l ih =>
    have h1 := le_abs_self a
    have h2 := neg_abs_le a
    simp only [List.foldr_cons,zsum_cons__solver_heap_maintain]
    omega

theorem submultiset_prefix__solver_residue_rollup (l : List Int) (k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength l) : SubMultiset (sublist 0 k l) l := by
  refine ⟨sublist k (Zlength l) l,?_⟩
  have he := sublist_split 0 (Zlength l) k l ⟨by omega,by omega⟩ ⟨hk.2,le_refl _⟩
  rw [sublist_self l (Zlength l) rfl] at he
  rw [← he]

theorem submultiset_abs__solver_residue_rollup (m l : List Int) (hs : SubMultiset m l) :
    m.foldr (fun x a => |x|+a) 0 ≤ l.foldr (fun x a => |x|+a) 0 := by
  obtain ⟨rest,hp⟩ := hs
  rw [abssum_perm__solver_residue_rollup _ _ hp,abssum_app__solver_residue_rollup]
  have h := abssum_nonneg__solver_residue_rollup rest
  omega

theorem min_submultiset_exists__solver_residue_rollup (l : List Int) (k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength l) : ∃ m, MinSubMultiset l m ∧ Zlength m=k := by
  let B := l.foldr (fun x a => |x|+a) 0
  have hb0 : 0 ≤ B := abssum_nonneg__solver_residue_rollup l
  let Q := fun z => ∃ m, SubMultiset m l ∧ Zlength m=k ∧ z=ZSum m+B
  have hbound : ∀ m, SubMultiset m l → 0 ≤ ZSum m+B ∧ ZSum m+B ≤ 2*B := by
    intro m hm
    have h1 := submultiset_abs__solver_residue_rollup m l hm
    have h2 := zsum_abs_bound__solver_residue_rollup m
    change 0 ≤ ZSum m+l.foldr (fun x a => |x|+a) 0 ∧ _
    dsimp [B]
    omega
  have hpre := submultiset_prefix__solver_residue_rollup l k hk
  obtain ⟨z,⟨m,hsub,hlen,hz⟩,hzr,hmin⟩ := min_n_in_range Q (2*B) (by omega)
    ⟨ZSum (sublist 0 k l)+B,hbound _ hpre,sublist 0 k l,hpre,Zlength_sublist0 k l hk,rfl⟩
  refine ⟨m,⟨hsub,?_⟩,hlen⟩
  intro m' hm' hlen'
  have hh := hmin (ZSum m'+B) (hbound m' hm') ⟨m',hm',hlen'.trans hlen,rfl⟩
  omega

theorem ksmallsum_exists__solver_residue_rollup (l : List Int) (k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength l) : ∃ s, KSmallSum l k s := by
  obtain ⟨m,hm,hlen⟩ := min_submultiset_exists__solver_residue_rollup l k hk
  exact ⟨ZSum m,m,hm,hlen,rfl⟩

theorem Znth_app1__solver_residue_rollup (A : Type) (d : A) (l1 l2 : List A)
    (p : Int) (hp : 0 ≤ p ∧ p < Zlength l1) : Znth p (l1++l2) d=Znth p l1 d := by
  have hn : p.toNat < l1.length := by simp only [Zlength,Int.ofNat_eq_coe] at hp; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

theorem Znth_app2__solver_residue_rollup (A : Type) (d : A) (l1 l2 : List A)
    (p : Int) (hp : Zlength l1 ≤ p) : Znth p (l1++l2) d=Znth (p-Zlength l1) l2 d :=
  app_Znth2 d l1 l2 p hp

theorem NoDup_map_inj__solver_residue_rollup (f : Int → Int) (l : List Int)
    (hi : ∀ x y, x ∈ l → y ∈ l → f x=f y → x=y) (hn : l.Nodup) : (l.map f).Nodup :=
  hn.map_on (fun x hx y hy => hi x y hx hy)

theorem split_at_index__solver_residue_rollup (A : Type) (d : A) (L : List A)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength L) :
    ∃ L1 L2, L=L1++Znth i L d::L2 ∧ Zlength L1=i := by
  have hn : i.toNat < L.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  refine ⟨L.take i.toNat,L.drop (i.toNat+1),?_,?_⟩
  · simpa only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
      using ((List.take_append_drop i.toNat L).symm.trans (congrArg (L.take i.toNat ++ ·) (List.drop_eq_getElem_cons hn)))
  · simp only [Zlength,List.length_take,Int.ofNat_eq_coe,min_eq_left (Nat.le_of_lt hn)]
    omega

theorem sweep_set_inhabited__solver_residue_rollup (contributions st sb : List Int)
    (k b c j W n : Int) (hk : 2 ≤ k) (hkn : k ≤ n) (hlen : Zlength sb=n) :
    ∃ v, SweepSet contributions k b c j st sb W n v := by
  have hslice : Zlength (sublist 0 (n-1+1) sb)=n := by rw [Zlength_sublist0 (n-1+1) sb (by omega)]; omega
  obtain ⟨s,hs⟩ := ksmallsum_exists__solver_residue_rollup (sublist 0 (n-1+1) sb) k (by omega)
  exact ⟨_,Or.inr ⟨n-1,by omega,by omega,s,hs,rfl⟩⟩

theorem raisecost_le__solver_residue_rollup (b c «from» target cost : Int)
    (hr : RaiseCost b c «from» target cost) : «from» ≤ target := by
  obtain ⟨a,⟨⟨blogs,comments,hb,hc,ht,_⟩,_⟩,_⟩ := hr
  omega

theorem raisecost_closed__solver_residue_rollup (b c W «from» target : Int)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hw : W=min b (5*c)) (ht : «from» ≤ target) :
    RaiseCost b c «from» target (Z.modulo (target-«from») 5*c+Z.div (target-«from») 5*W) := by
  rw [hw]
  exact raise_cost_normal_form__solver_sweep_value b c «from» target hb hc ht

theorem raisecost_det__solver_residue_rollup (b c W «from» target cost : Int)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hw : W=min b (5*c)) (hr : RaiseCost b c «from» target cost) :
    cost=Z.modulo (target-«from») 5*c+Z.div (target-«from») 5*W := by
  have ht := raisecost_le__solver_residue_rollup b c «from» target cost hr
  have he := raisecost_closed__solver_residue_rollup b c W «from» target hb hc hw ht
  have h1 := min_id_elim__solver_best_update _ cost hr
  have h2 := min_id_elim__solver_best_update _ _ he
  exact le_antisymm (h1.2 _ h2.1) (h2.2 _ h1.1)

theorem targetpoint_mod__solver_residue_rollup (s j : Int) (hj : 0 ≤ j ∧ j < 5) :
    Z.modulo (TargetPoint s j-j) 5=0 := by
  have h := target_point_mod__solver_sweep_value s j hj
  simp only [mod5_as_emod] at *
  omega

theorem targetpoint_ge__solver_residue_rollup (s j : Int) (hj : 0 ≤ j ∧ j < 5) :
    s ≤ TargetPoint s j ∧ TargetPoint s j < s+5 := by
  simp only [TargetPoint,mod5_as_emod]
  omega

theorem targetpoint_le__solver_residue_rollup (s j t : Int) (hj : 0 ≤ j ∧ j < 5)
    (hm : Z.modulo (t-j) 5=0) (hst : s ≤ t) : TargetPoint s j ≤ t := by
  simp only [TargetPoint,mod5_as_emod] at *
  omega

theorem cost_decomp__solver_residue_rollup (s j t W c : Int) (hj : 0 ≤ j ∧ j < 5)
    (hm : Z.modulo (t-j) 5=0) (hst : s ≤ t) :
    Z.modulo (t-s) 5*c+Z.div (t-s) 5*W=NormalizedBase s j W c+Z.div (t-j) 5*W := by
  apply (normalized_cost_eq s j W c t hj ?_).symm
  simp only [mod5_as_emod] at *
  omega

theorem Zlength_combine__solver_residue_rollup (A B : Type) (l1 : List A) (l2 : List B)
    (hl : Zlength l2=Zlength l1) : Zlength (l1.zip l2)=Zlength l1 :=
  Zlength_combine__solver_sweep_value A B l1 l2 hl.symm

theorem Znth_combine__solver_residue_rollup (A B : Type) (l1 : List A) (l2 : List B)
    (d1 : A) (d2 : B) (p : Int) (hl : Zlength l2=Zlength l1) (hp : 0 ≤ p ∧ p < Zlength l1) :
    Znth p (l1.zip l2) (d1,d2)=(Znth p l1 d1,Znth p l2 d2) :=
  Znth_combine__solver_sweep_value A B l1 l2 d1 d2 p hl.symm

theorem map_fst_combine__solver_residue_rollup (A B : Type) (l1 : List A) (l2 : List B)
    (hl : Zlength l2=Zlength l1) : (l1.zip l2).map Prod.fst=l1 :=
  List.map_fst_zip (by have h := Int.ofNat_inj.mp hl; omega)

theorem map_snd_combine__solver_residue_rollup (A B : Type) (l1 : List A) (l2 : List B)
    (hl : Zlength l2=Zlength l1) : (l1.zip l2).map Prod.snd=l2 :=
  List.map_snd_zip (by have h := Int.ofNat_inj.mp hl; omega)

theorem zsum_add_const__solver_residue_rollup (A : Type) (f : A → Int) (K : Int) (l : List A) :
    ZSum (l.map (fun x => f x+K))=ZSum (l.map f)+Zlength l*K := by
  induction l with
  | nil => simp [ZSum]
  | cons a l ih => simp only [List.map_cons,zsum_cons__solver_heap_maintain,Zlength_cons,ih]; ring

theorem Zlength_map__solver_residue_rollup (A B : Type) (f : A → B) (l : List A) :
    Zlength (l.map f)=Zlength l := by simp only [Zlength,List.length_map]

theorem Znth_map__solver_residue_rollup (A B : Type) (f : A → B) (l : List A)
    (q : Int) (da : A) (db : B) (hq : 0 ≤ q ∧ q < Zlength l) :
    Znth q (l.map f) db=f (Znth q l da) :=
  nth_map_len__solver_sweep_value A B f l q.toNat da db (by simp only [Zlength,Int.ofNat_eq_coe] at hq; omega)

theorem mul3_mono__solver_residue_rollup (k X Y W : Int) (hk : 0 ≤ k) (hw : 0 ≤ W) (hxy : X ≤ Y) :
    k*X*W ≤ k*Y*W := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hk) hw

theorem In_Znth__solver_residue_rollup (l : List Int) (x : Int) (hx : x ∈ l) :
    ∃ q, (0 ≤ q ∧ q < Zlength l) ∧ Znth q l 0=x := mem_znth l x hx

theorem Znth_In__solver_residue_rollup (l : List Int) (q : Int) (hq : 0 ≤ q ∧ q < Zlength l) :
    Znth q l 0 ∈ l := znth_mem l q hq

theorem div5_mono__solver_residue_rollup (x y j : Int) (hx : Z.modulo (x-j) 5=0)
    (hy : Z.modulo (y-j) 5=0) (hxy : x ≤ y) : Z.div (x-j) 5 ≤ Z.div (y-j) 5 := by
  simp only [div5_as_ediv]
  omega

theorem list_eq_Znth__solver_residue_rollup (l1 l2 : List Int) (hl : Zlength l1=Zlength l2)
    (he : ∀ q, (0 ≤ q ∧ q < Zlength l1) → Znth q l1 0=Znth q l2 0) : l1=l2 :=
  (list_eq_ext l1 l2 0).mpr ⟨hl,he⟩

theorem zsum_cons__solver_hpop_call_pre (a : Int) (l : List Int) : ZSum (a::l)=a+ZSum l := rfl

theorem zsum_permutation__solver_hpop_call_pre (l1 l2 : List Int) (hp : l1.Perm l2) : ZSum l1=ZSum l2 :=
  zsum_permutation__solver_heap_maintain l1 l2 hp

theorem zsum_range_from_bounds__solver_hpop_call_pre (l : List Int) (lo hi : Int)
    (hb : Forall (fun x => lo ≤ x ∧ x ≤ hi) l) : Zlength l*lo ≤ ZSum l ∧ ZSum l ≤ Zlength l*hi :=
  zsum_bounds__solver_sweep_value lo hi l hb

theorem zsum_range_from_znth__solver_hpop_call_pre (l : List Int) (n lo hi : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength l) (hb : ∀ q, (0 ≤ q ∧ q < n) → lo ≤ Znth q l 0 ∧ Znth q l 0 ≤ hi) :
    n*lo ≤ ZSum (sublist 0 n l) ∧ ZSum (sublist 0 n l) ≤ n*hi := by
  have hlen := Zlength_sublist0 n l hn
  have hh := zsum_bounds__solver_sweep_value lo hi (sublist 0 n l) (Forall_Znth__solver_sweep_value _ _ (by
    intro q hq
    rw [hlen] at hq
    rw [Znth_sublist0 0 q n l hq]
    exact hb q hq))
  simpa only [hlen] using hh

private theorem read_range {A : Type} (d : A) (L : List A) :
    (List.range L.length).map (fun (i : Nat) => Znth (i : Int) L d)=L := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range,Znth,Int.toNat_natCast,
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]

theorem perm_split_indices__solver_residue_rollup (A : Type) (d : A) (m L rest : List A)
    (hp : L.Perm (m++rest)) :
    ∃ il : List Int, il.Nodup ∧ Forall (fun i => 0 ≤ i ∧ i < Zlength L) il ∧
      il.map (fun i => Znth i L d)=m := by
  obtain ⟨f,hfr,hfi,hfv⟩ := perm_index__solver_sweep_value A L (m++rest) d hp
  have hr : ∀ i : Nat, i < m.length → 0 ≤ (i:Int) ∧ (i:Int) < Zlength (m++rest) := by
    intro i hi
    simp only [Zlength,List.length_append,Int.ofNat_eq_coe]
    omega
  refine ⟨(List.range m.length).map (fun (i : Nat) => f (i:Int)),?_,?_,?_⟩
  · apply List.nodup_range.map_on
    intro x hx y hy he
    have hx := List.mem_range.mp hx
    have hy := List.mem_range.mp hy
    have hh := hfi x y (hr x hx) (hr y hy) he
    omega
  · apply Forall.iff_forall_mem.mpr
    intro y hy
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
    exact hfr i (hr i (List.mem_range.mp hi))
  · apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    have he := hfv i (hr i hj)
    rw [Znth_app1__solver_residue_rollup A d m rest i (by simp only [Zlength,Int.ofNat_eq_coe]; omega)] at he
    simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj,Option.getD_some] using he.symm

theorem indices_submultiset_n__solver_residue_rollup (A : Type) (d : A) (n : Nat)
    (il : List Int) (L : List A) (hlen : il.length=n) (hnd : il.Nodup)
    (hr : Forall (fun i => 0 ≤ i ∧ i < Zlength L) il) :
    ∃ rest, L.Perm (il.map (fun i => Znth i L d)++rest) := by
  let full := (List.range L.length).map Int.ofNat
  have hsub : il.Subperm full := hnd.subperm (by
    intro i hi
    have hh := Forall.iff_forall_mem.mp hr i hi
    refine List.mem_map.mpr ⟨i.toNat,List.mem_range.mpr ?_,?_⟩
    · simp only [Zlength,Int.ofNat_eq_coe] at hh
      omega
    · exact Int.toNat_of_nonneg hh.1)
  obtain ⟨mid,hpm,hsm⟩ := hsub
  obtain ⟨rest,hrest⟩ := hsm.exists_perm_append
  have hp : full.Perm (il++rest) := hrest.trans (hpm.append_right rest)
  have hm := hp.map (fun i => Znth i L d)
  refine ⟨rest.map (fun i => Znth i L d),?_⟩
  simpa only [full,List.map_map,List.map_append,Function.comp_def,Int.ofNat_eq_coe,read_range] using hm

theorem indices_submultiset__solver_residue_rollup (A : Type) (d : A) (il : List Int) (L : List A)
    (hnd : il.Nodup) (hr : Forall (fun i => 0 ≤ i ∧ i < Zlength L) il) :
    ∃ rest, L.Perm (il.map (fun i => Znth i L d)++rest) :=
  indices_submultiset_n__solver_residue_rollup A d il.length il L rfl hnd hr

theorem nodup_range_length__solver_residue_rollup (il : List Int) (M : Int)
    (hm : 0 ≤ M) (hnd : il.Nodup) (hr : Forall (fun p => 0 ≤ p ∧ p < M) il) : Zlength il ≤ M := by
  have hsub : il.Subperm ((List.range M.toNat).map Int.ofNat) := hnd.subperm (by
    intro i hi
    have hh := Forall.iff_forall_mem.mp hr i hi
    exact List.mem_map.mpr ⟨i.toNat,List.mem_range.mpr (by omega),Int.toNat_of_nonneg hh.1⟩)
  have hlen := hsub.length_le
  simp only [List.length_map,List.length_range] at hlen
  simp only [Zlength,Int.ofNat_eq_coe]
  omega

theorem min_value_of_subset_ext__solver_final_spec (X Y : Int → Prop) (n : Int)
    (he : ∀ v, X v ↔ Y v) (hm : min_value_of_subset (· ≤ ·) X (fun x => x) n) :
    min_value_of_subset (· ≤ ·) Y (fun x => x) n := by
  obtain ⟨hx,hmin⟩ := min_id_elim__solver_best_update X n hm
  exact min_id_intro__solver_best_update Y n ((he n).mp hx) (fun v hv => hmin v ((he v).mpr hv))

theorem tie_cost_residue_cover__solver_final_spec (values : List Int) (k b c v : Int) :
    (∃ j', (0 ≤ j' ∧ j' < 5) ∧ TieCostAtResidue values k b c j' v) ↔ TieCost values k b c v := by
  constructor
  · rintro ⟨j',hj,chosen,costs,target,hm,hch,hlen,hcost,hsum⟩
    exact ⟨chosen,costs,target,hch,hlen,hcost,hsum⟩
  · rintro ⟨chosen,costs,target,hch,hlen,hcost,hsum⟩
    refine ⟨Z.modulo target 5,?_,chosen,costs,target,rfl,hch,hlen,hcost,hsum⟩
    simp only [mod5_as_emod]
    omega

theorem fold_max_nonneg__solver_final_spec (l : List Int) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih => exact ih.trans (le_max_right _ _)

theorem nth_le_fold_max__solver_final_spec (l : List Int) (n : Nat) : l.getD n 0 ≤ l.foldr max 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => exact le_max_left _ _
    | succ n => exact (ih n).trans (le_max_right _ _)

theorem Znth_le_fold_max__solver_final_spec (l : List Int) (i : Int) : Znth i l 0 ≤ l.foldr max 0 :=
  nth_le_fold_max__solver_final_spec l i.toNat

theorem z_min_exists_nonneg__solver_final_spec (X : Int → Prop)
    (hex : ∃ v, X v) (h0 : ∀ v, X v → 0 ≤ v) : ∃ n, min_value_of_subset (· ≤ ·) X (fun x => x) n := by
  obtain ⟨v,hv⟩ := hex
  have hv0 := h0 v hv
  obtain ⟨n,hn,hnb,hmin⟩ := min_n_in_range X v hv0 ⟨v,⟨hv0,le_refl _⟩,hv⟩
  refine ⟨n,min_id_intro__solver_best_update X n hn ?_⟩
  intro b hb
  by_cases h : b ≤ v
  · exact hmin b ⟨h0 b hb,h⟩ hb
  · omega

theorem raise_cost_exists__solver_final_spec (b c «from» target : Int)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (ht : «from» ≤ target) : ∃ cost, RaiseCost b c «from» target cost :=
  ⟨_,raise_cost_normal_form__solver_sweep_value b c «from» target hb hc ht⟩

theorem Znth_map__solver_final_spec (f : Int → Int) (l : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i (l.map f) 0=f (Znth i l 0) :=
  Znth_map__solver_residue_rollup Int Int f l i 0 0 hi

theorem nodup_map_of_nat_seq__solver_final_spec (n s : Nat) :
    ((List.range' s n).map Int.ofNat).Nodup :=
  (List.nodup_range' 1).map (fun _ _ h => Int.ofNat_inj.mp h)

theorem Zlength_map_of_nat_seq__solver_final_spec (n s : Nat) :
    Zlength ((List.range' s n).map Int.ofNat)=(n:Int) := by simp only [Zlength,List.length_map,List.length_range']; rfl

theorem tie_cost_inhabited__solver_final_spec (values : List Int) (k b c : Int)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hk : 0 ≤ k) (hklen : k ≤ Zlength values) : ∃ v, TieCost values k b c v := by
  let chosen := (List.range' 0 k.toNat).map Int.ofNat
  let target := values.foldr max 0
  let f := fun i : Int => Z.modulo (target-Znth i values 0) 5*c+Z.div (target-Znth i values 0) 5*WCost b c
  let costs := chosen.map f
  have hlen : Zlength chosen=k := by
    have hh := Zlength_map_of_nat_seq__solver_final_spec k.toNat 0
    simpa only [Int.toNat_of_nonneg hk] using hh
  have hr : Forall (fun i => 0 ≤ i ∧ i < Zlength values) chosen := by
    apply Forall.iff_forall_mem.mpr
    intro i hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
    have hh := List.mem_range'.mp hq
    simp only [Zlength,Int.ofNat_eq_coe] at hklen ⊢
    omega
  refine ⟨ZSum costs,chosen,costs,target,⟨hlen,nodup_map_of_nat_seq__solver_final_spec k.toNat 0,hr⟩,?_,?_,rfl⟩
  · exact (Zlength_map__solver_residue_rollup Int Int f chosen).trans hlen
  · intro i hi
    have him : 0 ≤ i ∧ i < Zlength chosen := by omega
    change RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i (chosen.map f) 0)
    rw [Znth_map__solver_final_spec f chosen i him]
    exact raise_cost_normal_form__solver_sweep_value b c _ target hb hc
      (Znth_le_fold_max__solver_final_spec values (Znth i chosen 0))

private theorem zip_index (t0 b0 t1 b1 : List Int) (n : Int)
    (ht0 : Zlength t0=n) (hb0 : Zlength b0=n) (ht1 : Zlength t1=n) (hb1 : Zlength b1=n)
    (hp : (t0.zip b0).Perm (t1.zip b1)) :
    ∃ f : Int → Int,
      (∀ p, (0 ≤ p ∧ p < n) → 0 ≤ f p ∧ f p < n) ∧
      (∀ p q, (0 ≤ p ∧ p < n) → (0 ≤ q ∧ q < n) → f p=f q → p=q) ∧
      ∀ p, (0 ≤ p ∧ p < n) → Znth p t1 0=Znth (f p) t0 0 ∧ Znth p b1 0=Znth (f p) b0 0 := by
  have h0 : Zlength (t0.zip b0)=n := (Zlength_combine__solver_sweep_value Int Int t0 b0 (by omega)).trans ht0
  have h1 : Zlength (t1.zip b1)=n := (Zlength_combine__solver_sweep_value Int Int t1 b1 (by omega)).trans ht1
  obtain ⟨f,hfr,hfi,hfv⟩ := perm_index__solver_sweep_value (Int×Int) (t0.zip b0) (t1.zip b1) (0,0) hp
  rw [h0,h1] at hfr
  rw [h1] at hfi hfv
  refine ⟨f,hfr,hfi,?_⟩
  intro p hp
  have he := hfv p hp
  rw [Znth_combine__solver_sweep_value Int Int t1 b1 0 0 p (by omega),
    Znth_combine__solver_sweep_value Int Int t0 b0 0 0 (f p) (by omega)] at he
  exact Prod.mk.inj he

theorem st_mod__solver_residue_rollup (sh ct cb st sb : List Int) (n j W c p : Int)
    (hj : 0 ≤ j ∧ j < 5) (hct : Zlength ct=n) (hcb : Zlength cb=n)
    (hst : Zlength st=n) (hsb : Zlength sb=n) (hcand : CandPrefix sh j W c n ct cb)
    (hzip : ZipPerm ct cb st sb) (hp : 0 ≤ p ∧ p < n) : Z.modulo (Znth p st 0-j) 5=0 := by
  obtain ⟨f,hfr,_,hfv⟩ := zip_index ct cb st sb n hct hcb hst hsb hzip.2.2.2
  rw [(hfv p hp).1,(hcand (f p) (hfr p hp)).1]
  exact targetpoint_mod__solver_residue_rollup _ j hj

theorem sweep_value_is_tie__solver_residue_rollup (contributions sh ct cb st sb : List Int)
    (n k b c j W i' v : Int) (hn : n=Zlength contributions) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hw : W=WCost b c) (hj : 0 ≤ j ∧ j < 5)
    (hsh : Zlength sh=n) (hct : Zlength ct=n) (hcb : Zlength cb=n)
    (hst : Zlength st=n) (hsb : Zlength sb=n)
    (hshift : ShiftedPrefix contributions sh n) (hcand : CandPrefix sh j W c n ct cb)
    (hzip : ZipPerm ct cb st sb) (hsort : Nondecreasing st)
    (hki : k-1 ≤ i') (hin : i' < n) (hsv : SweepValue st sb k j W i' v) :
    TieCostAtResidue contributions k b c j v := by
  obtain ⟨s,⟨m,⟨⟨rest,hperm⟩,_⟩,hmlen,hs⟩,hv⟩ := hsv
  have hslice : Zlength (sublist 0 (i'+1) sb)=i'+1 := Zlength_sublist0 (i'+1) sb (by omega)
  obtain ⟨il,hnd,hr,hmap⟩ := perm_split_indices__solver_residue_rollup Int 0 m (sublist 0 (i'+1) sb) rest hperm
  rw [hslice] at hr
  have hilmap : il.map (fun p => Znth p sb 0)=m := by
    rw [← hmap]
    apply List.map_congr_left
    intro p hp
    have hh := Forall.iff_forall_mem.mp hr p hp
    exact (Znth_sublist0 0 p (i'+1) sb hh).symm
  have hillen : Zlength il=k := by
    have he := congrArg Zlength hilmap
    rw [Zlength_map__solver_residue_rollup] at he
    omega
  obtain ⟨f,hfr,hfi,hfv⟩ := zip_index ct cb st sb n hct hcb hst hsb hzip.2.2.2
  have hrn : ∀ p, p ∈ il → 0 ≤ p ∧ p < n := by
    intro p hp
    have hh := Forall.iff_forall_mem.mp hr p hp
    omega
  let chosen := il.map f
  let QW := Z.div (Znth i' st 0-j) 5*W
  let costs := il.map (fun p => Znth p sb 0+QW)
  have hchosen : ChosenBloggers contributions k chosen := by
    refine ⟨(Zlength_map__solver_residue_rollup Int Int f il).trans hillen,?_,?_⟩
    · exact hnd.map_on (fun x hx y hy he => hfi x y (hrn x hx) (hrn y hy) he)
    · apply Forall.iff_forall_mem.mpr
      intro y hy
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hy
      have hh := hfr p (hrn p hp)
      omega
  have hmod := st_mod__solver_residue_rollup sh ct cb st sb n j W c i' hj hct hcb hst hsb hcand hzip (by omega)
  have hmodi : Z.modulo (Znth i' st 0) 5=j := by simp only [mod5_as_emod] at *; omega
  refine ⟨chosen,costs,Znth i' st 0-2000000000,?_,hchosen,?_,?_,?_⟩
  · simp only [mod5_as_emod] at *
    omega
  · exact (Zlength_map__solver_residue_rollup Int Int _ il).trans hillen
  · intro q hq
    have hqil : 0 ≤ q ∧ q < Zlength il := by omega
    have hpMem := znth_mem il q hqil
    have hpr := Forall.iff_forall_mem.mp hr _ hpMem
    have hpn := hrn _ hpMem
    have hfp := hfr _ hpn
    obtain ⟨het,heb⟩ := hfv _ hpn
    obtain ⟨hctf,hcbf⟩ := hcand _ hfp
    have hstle : TargetPoint (Znth (f (Znth q il 0)) sh 0) j ≤ Znth i' st 0 := by
      rw [← hctf,← het]
      exact hsort _ _ hpr.1 (by omega) (by omega)
    have hh := raise_cost_shifted__solver_sweep_value b c W j (Znth (f (Znth q il 0)) sh 0)
      (Znth i' st 0) hb hc hw hj hstle hmodi
    have hshf := hshift _ hfp
    have hefrom : Znth (f (Znth q il 0)) sh 0-2000000000=Znth (f (Znth q il 0)) contributions 0 := by omega
    change RaiseCost b c (Znth (Znth q (il.map f) 0) contributions 0) _ (Znth q (il.map (fun p => Znth p sb 0+QW)) 0)
    rw [Znth_map__solver_final_spec f il q hqil,Znth_map__solver_final_spec _ il q hqil,heb,hcbf]
    rw [hefrom] at hh
    exact hh
  · change v=ZSum (il.map (fun p => Znth p sb 0+QW))
    rw [zsum_add_const__solver_residue_rollup Int (fun p => Znth p sb 0) QW il,hilmap,hillen,hv,hs]
    dsimp [QW]
    ring

theorem tie_ge_sweep__solver_residue_rollup (contributions sh ct cb st sb : List Int)
    (n k b c j W v : Int) (hn : n=Zlength contributions) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hw : W=WCost b c) (hj : 0 ≤ j ∧ j < 5)
    (hsh : Zlength sh=n) (hct : Zlength ct=n) (hcb : Zlength cb=n)
    (hst : Zlength st=n) (hsb : Zlength sb=n)
    (hshift : ShiftedPrefix contributions sh n) (hcand : CandPrefix sh j W c n ct cb)
    (hzip : ZipPerm ct cb st sb) (hsort : Nondecreasing st)
    (htie : TieCostAtResidue contributions k b c j v) :
    ∃ i' w, k-1 ≤ i' ∧ i' < n ∧ SweepValue st sb k j W i' w ∧ w ≤ v := by
  obtain ⟨chosen,costs,tau,htau,⟨hclen,hcnd,hcr⟩,hcostlen,hcost,hv⟩ := htie
  let t := tau+2000000000
  have htmod : Z.modulo (t-j) 5=0 := by
    simp only [mod5_as_emod,t] at *
    omega
  have hcrn : ∀ p, p ∈ chosen → 0 ≤ p ∧ p < n := by
    intro p hp
    have h := Forall.iff_forall_mem.mp hcr p hp
    omega
  obtain ⟨f,hfr,hfi,hfv⟩ := zip_index st sb ct cb n hst hsb hct hcb hzip.2.2.2.symm
  let il := chosen.map f
  have hillen : Zlength il=k := (Zlength_map__solver_residue_rollup Int Int f chosen).trans hclen
  have hind : il.Nodup := hcnd.map_on (fun x hx y hy he => hfi x y (hcrn x hx) (hcrn y hy) he)
  have hir : ∀ p, p ∈ il → 0 ≤ p ∧ p < n := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hfr q (hcrn q hq)
  have hstle : ∀ p, p ∈ il → Znth p st 0 ≤ t := by
    intro p hp
    obtain ⟨idx,hidx,rfl⟩ := List.mem_map.mp hp
    obtain ⟨q,hq,heq⟩ := mem_znth chosen idx hidx
    have hqk : 0 ≤ q ∧ q < k := by omega
    have hval := hcost q hqk
    rw [heq] at hval
    have hle := raisecost_le__solver_residue_rollup b c _ tau _ hval
    have hidxr := hcrn idx hidx
    have hshidx := hshift idx hidxr
    have hctidx := (hcand idx hidxr).1
    have hmap := (hfv idx hidxr).1
    rw [← hmap,hctidx]
    exact targetpoint_le__solver_residue_rollup _ j t hj htmod (by dsimp [t]; omega)
  have hzero : 0 ≤ (0:Int) ∧ (0:Int) < Zlength il := by omega
  have hin0 := znth_mem il 0 hzero
  have hir0 := hir _ hin0
  obtain ⟨imax,himax,himr,hmax⟩ := max_n_in_range (fun p => p ∈ il) (n-1) (by omega)
    ⟨Znth 0 il 0,⟨hir0.1,by omega⟩,hin0⟩
  have hall : ∀ p, p ∈ il → p ≤ imax := by
    intro p hp
    have hr := hir p hp
    exact hmax p ⟨hr.1,by omega⟩ hp
  have hirpre : Forall (fun p => 0 ≤ p ∧ p < imax+1) il := by
    apply Forall.iff_forall_mem.mpr
    intro p hp
    have hr := hir p hp
    have hm := hall p hp
    omega
  have hkmax : k-1 ≤ imax := by
    have hlen := nodup_range_length__solver_residue_rollup il (imax+1) (by omega) hind hirpre
    omega
  have himt := hstle imax himax
  have hslice : Zlength (sublist 0 (imax+1) sb)=imax+1 := Zlength_sublist0 (imax+1) sb (by omega)
  have hrpre : Forall (fun p => 0 ≤ p ∧ p < Zlength (sublist 0 (imax+1) sb)) il := by
    simpa only [hslice] using hirpre
  obtain ⟨rest,hperm⟩ := indices_submultiset__solver_residue_rollup Int 0 il (sublist 0 (imax+1) sb) hind hrpre
  have hmap : il.map (fun p => Znth p (sublist 0 (imax+1) sb) 0)=il.map (fun p => Znth p sb 0) := by
    apply List.map_congr_left
    intro p hp
    exact Znth_sublist0 0 p (imax+1) sb (Forall.iff_forall_mem.mp hirpre p hp)
  rw [hmap] at hperm
  obtain ⟨mm,hmm,hmmlen⟩ := min_submultiset_exists__solver_residue_rollup (sublist 0 (imax+1) sb) k (by omega)
  have hmin : ZSum mm ≤ ZSum (il.map (fun p => Znth p sb 0)) :=
    hmm.2 _ ⟨rest,hperm⟩ (by rw [Zlength_map__solver_residue_rollup]; omega)
  let QW := Z.div (t-j) 5*W
  have hcostseq : costs=il.map (fun p => Znth p sb 0+QW) := by
    apply (list_eq_ext costs _ 0).mpr
    refine ⟨by rw [Zlength_map__solver_residue_rollup]; omega,?_⟩
    intro q hq
    have hqk : 0 ≤ q ∧ q < k := by omega
    have hqch : 0 ≤ q ∧ q < Zlength chosen := by omega
    have hqil : 0 ≤ q ∧ q < Zlength il := by omega
    have hidxmem := znth_mem chosen q hqch
    have hidxr := hcrn _ hidxmem
    have hdet := raisecost_det__solver_residue_rollup b c W _ tau _ hb hc hw (hcost q hqk)
    have hle := raisecost_le__solver_residue_rollup b c _ tau _ (hcost q hqk)
    have hshidx := hshift _ hidxr
    obtain ⟨hctidx,hcbidx⟩ := hcand _ hidxr
    have hmapb := (hfv _ hidxr).2
    rw [Znth_map__solver_final_spec _ il q hqil]
    change Znth q costs 0=Znth (Znth q (chosen.map f) 0) sb 0+QW
    rw [Znth_map__solver_final_spec f chosen q hqch,← hmapb,hcbidx,hdet]
    have hd : tau-Znth (Znth q chosen 0) contributions 0=t-Znth (Znth q chosen 0) sh 0 := by dsimp [t]; omega
    rw [hd]
    exact cost_decomp__solver_residue_rollup _ j t W c hj htmod (by dsimp [t]; omega)
  refine ⟨imax,ZSum mm+k*Z.div (Znth imax st 0-j) 5*W,hkmax,by omega,?_,?_⟩
  · exact ⟨ZSum mm,⟨mm,hmm,hmmlen,rfl⟩,rfl⟩
  · have hdiv : Z.div (Znth imax st 0-j) 5 ≤ Z.div (t-j) 5 := by simp only [div5_as_ediv]; omega
    have hw0 : 0 ≤ W := by rw [hw,WCost]; exact le_min (by omega) (by omega)
    have hmul := mul3_mono__solver_residue_rollup k _ _ W (by omega) hw0 hdiv
    rw [hv,hcostseq]
    change _ ≤ ZSum (il.map (fun p => Znth p sb 0+QW))
    rw [zsum_add_const__solver_residue_rollup Int _ QW il,hillen]
    dsimp [QW]
    nlinarith

theorem residue_best_of_sweep_best__solver_residue_rollup (contributions sh ct cb st sb : List Int)
    (n k b c j W best : Int) (hn : n=Zlength contributions) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hw : W=WCost b c) (hj : 0 ≤ j ∧ j < 5) (hbest : 0 ≤ best)
    (hsh : Zlength sh=n) (hct : Zlength ct=n) (hcb : Zlength cb=n)
    (hst : Zlength st=n) (hsb : Zlength sb=n)
    (hshift : ShiftedPrefix contributions sh n) (hcand : CandPrefix sh j W c n ct cb)
    (hzip : ZipPerm ct cb st sb) (hsort : Nondecreasing st)
    (hsweep : SweepBest contributions k b c j st sb W n best) : ResidueBest contributions k b c (j+1) best := by
  rcases hsweep with ⟨hnone,_⟩ | ⟨_,hmin⟩
  · omega
  · obtain ⟨hmem,hlower⟩ := min_id_elim__solver_best_update _ best hmin
    refine Or.inr ⟨hbest,min_id_intro__solver_best_update _ best ?_ ?_⟩
    · rcases hmem with ⟨j',hj',htie⟩ | ⟨i',hi',hin,hsv⟩
      · exact ⟨j',⟨hj'.1,by omega⟩,htie⟩
      · exact ⟨j,⟨hj.1,by omega⟩,sweep_value_is_tie__solver_residue_rollup contributions sh ct cb st sb
          n k b c j W i' best hn hk hkn hb hc hw hj hsh hct hcb hst hsb hshift hcand hzip hsort hi' hin hsv⟩
    · rintro v ⟨j',hj',htie⟩
      by_cases hlt : j' < j
      · exact hlower v (Or.inl ⟨j',⟨hj'.1,hlt⟩,htie⟩)
      · have he : j'=j := by omega
        subst j'
        obtain ⟨i',w,hi',hin,hsv,hwv⟩ := tie_ge_sweep__solver_residue_rollup contributions sh ct cb st sb
          n k b c j W v hn hk hkn hb hc hw hj hsh hct hcb hst hsb hshift hcand hzip hsort htie
        exact (hlower w (Or.inr ⟨i',hi',hin,hsv⟩)).trans hwv

private theorem tie_cost_nonneg (values : List Int) (k b c j v : Int)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (htie : TieCostAtResidue values k b c j v) : 0 ≤ v := by
  obtain ⟨chosen,costs,target,_,_,hlen,hcost,rfl⟩ := htie
  have hbnd : ∀ x, x ∈ costs → 0 ≤ x := by
    intro x hx
    obtain ⟨q,hq,he⟩ := mem_znth costs x hx
    have hr := hcost q (by omega)
    obtain ⟨blogs,comments,hbl,hco,_,hval⟩ := (min_id_elim__solver_best_update _ _ hr).1
    have hnon := add_nonneg (mul_nonneg hbl (by omega : 0 ≤ b)) (mul_nonneg hco (by omega : 0 ≤ c))
    omega
  have hsum : ∀ l : List Int, (∀ x, x ∈ l → 0 ≤ x) → 0 ≤ l.foldr (· + ·) 0 := by
    intro l
    induction l with
    | nil => intros; exact le_refl _
    | cons a l ih =>
      intro hh
      exact add_nonneg (hh a List.mem_cons_self)
        (ih (fun x hx => hh x (List.mem_cons_of_mem a hx)))
  exact hsum costs hbnd

theorem tie_cost_from_sweep__solver_sweep_value (contributions sh ct cb st sb hl : List Int)
    (n k b c W j i hsum : Int) (hk : 2 ≤ k) (hkn : k ≤ n) (hnmax : n ≤ 200000)
    (hn : n=Zlength contributions) (hb : 1 ≤ b) (hbmax : b ≤ 1000)
    (hc : 1 ≤ c) (hcmax : c ≤ 1000) (hw : W=WCost b c) (hj0 : 0 ≤ j) (hj5 : j < 5)
    (hi0 : 0 ≤ i) (hin : i < n) (hsh : Zlength sh=n) (hct : Zlength ct=n)
    (hcb : Zlength cb=n) (hhl : Zlength hl=n) (hst : Zlength st=n) (hsb : Zlength sb=n)
    (hshift : ShiftedPrefix contributions sh n)
    (hshb : ∀ q, (0 ≤ q ∧ q < n) → 1000000000 ≤ Znth q sh 0 ∧ Znth q sh 0 ≤ 3000000000)
    (hcand : CandPrefix sh j W c n ct cb) (hzip : ZipPerm ct cb st sb) (hsort : Nondecreasing st)
    (hstb : ∀ q, (0 ≤ q ∧ q < n) →
      ((1000000000 ≤ Znth q st 0 ∧ Znth q st 0 ≤ 3000000004) ∧ -600000000000 ≤ Znth q sb 0) ∧ Znth q sb 0 ≤ 4000)
    (hhc : HeapContent sb (i+1) (sublist 0 k hl) hsum) :
    KSmallSum (sublist 0 (i+1) sb) k hsum ∧
    SweepValue st sb k j W i (hsum+(k*Z.quot (Znth i st 0-j) 5)*W) ∧
    TieCostAtResidue contributions k b c j (hsum+(k*Z.quot (Znth i st 0-j) 5)*W) ∧
    0 ≤ hsum+(k*Z.quot (Znth i st 0-j) 5)*W ∧ hsum+(k*Z.quot (Znth i st 0-j) 5)*W ≤ 300000000000000000 := by
  obtain ⟨hmin,hsumEq⟩ := hhc
  have hlenH : Zlength (sublist 0 k hl)=k := Zlength_sublist0 k hl (by omega)
  have hlenP : Zlength (sublist 0 (i+1) sb)=i+1 := Zlength_sublist0 (i+1) sb (by omega)
  have hkpre : k ≤ i+1 := by
    have h := submultiset_length__solver_heap_maintain _ _ hmin.1
    omega
  have hsti := (hstb i ⟨hi0,hin⟩).1.1
  have hquot : Z.quot (Znth i st 0-j) 5=Z.div (Znth i st 0-j) 5 := by
    rw [div5_as_ediv]
    exact Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hks : KSmallSum (sublist 0 (i+1) sb) k hsum := ⟨sublist 0 k hl,hmin,hlenH,hsumEq⟩
  have hsv : SweepValue st sb k j W i (hsum+(k*Z.quot (Znth i st 0-j) 5)*W) := by
    refine ⟨hsum,hks,?_⟩
    rw [hquot]
  have htie := sweep_value_is_tie__solver_residue_rollup contributions sh ct cb st sb n k b c j W i _
    hn hk hkn hb hc hw ⟨hj0,hj5⟩ hsh hct hcb hst hsb hshift hcand hzip hsort (by omega) hin hsv
  refine ⟨hks,hsv,htie,tie_cost_nonneg contributions k b c j _ hb hc htie,?_⟩
  have hsumBounds : Zlength (sublist 0 k hl)*(-600000000000) ≤ ZSum (sublist 0 k hl) ∧
      ZSum (sublist 0 k hl) ≤ Zlength (sublist 0 k hl)*4000 := by
    apply zsum_bounds__solver_heap_maintain
    intro y hy
    obtain ⟨rest,hperm⟩ := hmin.1
    have hymem : y ∈ sublist 0 (i+1) sb := hperm.mem_iff.mpr (List.mem_append_left rest hy)
    apply sublist_In_bounds__solver_heap_maintain sb (i+1) (-600000000000) 4000 (by omega) ?_ y hymem
    intro q hq
    have h := hstb q (by omega)
    exact ⟨h.1.2,h.2⟩
  have hw0 : 1 ≤ W := by rw [hw,WCost]; exact le_min hb (by omega)
  have hwmax : W ≤ 1000 := by rw [hw,WCost]; exact (min_le_left _ _).trans hbmax
  have hprod := sweep_total_int64_bounds__solver_safety_sweep_a k W j (Znth i st 0)
    (by omega) (by omega) hw0 hwmax hj0 hj5 hsti.1 hsti.2
  rw [hlenH,← hsumEq] at hsumBounds
  omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_lib
