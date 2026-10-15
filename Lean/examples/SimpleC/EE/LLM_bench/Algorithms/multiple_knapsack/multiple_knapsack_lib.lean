import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib
open AUXLib

open MaxMinLib

def PairwiseWeightValue (xs : List (Int × Int)) : Int :=
  sum (List.map (fun wp => Prod.fst wp * Prod.snd wp) xs)

def PickWeight (weights picks : List Int) : Int :=
  PairwiseWeightValue (List.zip weights picks)

def PickValue (values picks : List Int) : Int :=
  PairwiseWeightValue (List.zip values picks)

def BoundedPickList
    (weights values counts : List Int) (capacity : Int) (picks : List Int) : Prop :=
  Zlength weights = Zlength values ∧
  Zlength weights = Zlength counts ∧
  Zlength picks = Zlength weights ∧
  0 ≤ capacity ∧
  List.Forall₂ (fun pick cnt => (0 ≤ pick ∧ pick ≤ cnt) ) picks counts ∧
  0 ≤ PickWeight weights picks ∧
  PickWeight weights picks ≤ capacity

def MultipleKnapsackAnswer
    (weights values counts : List Int) (capacity answer : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun picks => BoundedPickList weights values counts capacity picks)
    (fun picks => PickValue values picks)
    answer

def MultipleKnapsackPrefixAnswer
    (weights values counts : List Int) (i capacity answer : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun picks =>
       BoundedPickList
         (sublist 0 i weights)
         (sublist 0 i values)
         (sublist 0 i counts)
         capacity
         picks)
    (fun picks => PickValue (sublist 0 i values) picks)
    answer

def MKDPValueBound (dp : List Int) (capacity : Int) : Prop :=
  Zlength dp = capacity + 1 ∧
  forall cap,
    (0 ≤ cap ∧ cap ≤ capacity) →
    (0 ≤ Znth cap dp 0 ∧ Znth cap dp 0 ≤ 1000000) 

def MKScratchArraysSafety
    (old q_idx q_val : List Int) (capacity : Int) : Prop :=
  Zlength old = capacity + 1 ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1

def MKDPTable
    (weights values counts : List Int) (i capacity : Int) (dp : List Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength weights) ∧
  0 ≤ capacity ∧
  Zlength dp = capacity + 1 ∧
  forall cap,
    (0 ≤ cap ∧ cap ≤ capacity) →
    MultipleKnapsackPrefixAnswer weights values counts i cap (Znth cap dp 0)

def MKZeroPrefix (dp : List Int) (hi : Int) : Prop :=
  0 ≤ hi ∧
  Zlength dp = hi ∧
  forall cap, (0 ≤ cap ∧ cap < hi) → Znth cap dp 0 = 0

def MKCopyPrefix (src dst : List Int) (j capacity : Int) : Prop :=
  (0 ≤ j ∧ j ≤ capacity + 1) ∧
  Zlength src = capacity + 1 ∧
  Zlength dst = capacity + 1 ∧
  forall cap, (0 ≤ cap ∧ cap < j) → Znth cap dst 0 = Znth cap src 0

def MKTransitionValue
    (old : List Int) (w v cnt capacity pos ans : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  (0 ≤ pos ∧ pos ≤ capacity) ∧
  Zlength old = capacity + 1 ∧
  max_value_of_subset (· ≤ ·)
    (fun take =>
       (0 ≤ take ∧ take ≤ cnt) ∧
       take * w ≤ pos ∧
       (0 ≤ pos - take * w ∧ pos - take * w ≤ capacity) )
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans

def MKTransitionValueBound
    (old : List Int) (w v cnt capacity : Int) : Prop :=
  forall pos ans,
    (0 ≤ pos ∧ pos ≤ capacity) →
    MKTransitionValue old w v cnt capacity pos ans →
    (0 ≤ ans ∧ ans ≤ 1000000) 

def MKItemResidueProgress
    (old dp : List Int) (r w v cnt capacity : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  0 ≤ r ∧
  r ≤ w ∧
  r ≤ capacity + 1 ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1 ∧
  (forall rem k pos,
     pos = rem + k * w →
     (0 ≤ rem ∧ rem < r) →
     0 ≤ k →
     (0 ≤ pos ∧ pos ≤ capacity) →
     MKTransitionValue old w v cnt capacity pos (Znth pos dp 0)) ∧
  (forall rem k pos,
     pos = rem + k * w →
     (r ≤ rem ∧ rem < w) →
     0 ≤ k →
     (0 ≤ pos ∧ pos ≤ capacity) →
     Znth pos dp 0 = Znth pos old 0)

def MKResiduePrefix
    (old dp : List Int) (r w v cnt k capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1 ∧
  forall t,
    (0 ≤ t ∧ t < k) →
    r + t * w ≤ capacity →
    MKTransitionValue old w v cnt capacity (r + t * w)
      (Znth (r + t * w) dp 0)

def MKItemResiduePrefixProgress
    (old dp : List Int) (r w v cnt k capacity : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  r ≤ capacity ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1 ∧
  MKResiduePrefix old dp r w v cnt k capacity ∧
  forall pos,
    (0 ≤ pos ∧ pos ≤ capacity) →
    (forall rem t,
       pos = rem + t * w →
       (0 ≤ rem ∧ rem < r) →
       0 ≤ t →
       MKTransitionValue old w v cnt capacity pos (Znth pos dp 0)) ∧
    (forall rem t,
       pos = rem + t * w →
       (0 ≤ rem ∧ rem < w) →
       0 ≤ t →
       (r < rem ∨ (rem = r ∧ k ≤ t)) →
       Znth pos dp 0 = Znth pos old 0)

def MKQueueEntryValue
    (old q_idx q_val : List Int) (r w v pos : Int) : Prop :=
  0 ≤ Znth pos q_idx 0 ∧
  r + Znth pos q_idx 0 * w < Zlength old ∧
  Znth pos q_val 0 =
    Znth (r + Znth pos q_idx 0 * w) old 0 - Znth pos q_idx 0 * v

def MKQueueEntriesValid
    (old q_idx q_val : List Int) (head tail r w v k cnt : Int) : Prop :=
  forall pos,
    (head ≤ pos ∧ pos < tail) →
    k - cnt ≤ Znth pos q_idx 0 ∧
    Znth pos q_idx 0 < k ∧
    MKQueueEntryValue old q_idx q_val r w v pos

def MKQueueEntriesValidAfterDrop
    (old q_idx q_val : List Int) (head tail r w v k cnt : Int) : Prop :=
  forall pos,
    (head ≤ pos ∧ pos < tail) →
    k - cnt ≤ Znth pos q_idx 0 ∧
    Znth pos q_idx 0 < k ∧
    MKQueueEntryValue old q_idx q_val r w v pos

def MKQueueIndexIncreasing (q_idx : List Int) (head tail : Int) : Prop :=
  forall p q,
    head ≤ p ∧ p < q ∧ q < tail →
    Znth p q_idx 0 < Znth q q_idx 0

def MKQueueValueDecreasing (q_val : List Int) (head tail : Int) : Prop :=
  forall p q,
    head ≤ p ∧ p < q ∧ q < tail →
    Znth p q_val 0 > Znth q q_val 0

def MKQueueResultValueBound
    (q_val : List Int) (head tail v k : Int) : Prop :=
  forall pos,
    (head ≤ pos ∧ pos < tail) →
    (0 ≤ Znth pos q_val 0 + k * v ∧ Znth pos q_val 0 + k * v ≤ 1000000) 

def MKQueueCoversWindow
    (old q_idx q_val : List Int) (head tail r w v k cnt : Int) : Prop :=
  forall cand,
    0 ≤ cand →
    cand < k →
    k - cnt ≤ cand →
    r + cand * w < Zlength old →
    exists pos,
      (head ≤ pos ∧ pos < tail) ∧
      cand ≤ Znth pos q_idx 0 ∧
      Znth pos q_idx 0 < k ∧
      Znth (r + cand * w) old 0 - cand * v ≤ Znth pos q_val 0

def MKQueueCoversWithPending
    (old q_idx q_val : List Int) (head tail r w v k cnt current : Int) : Prop :=
  forall cand,
    0 ≤ cand →
    cand < k →
    k - cnt ≤ cand →
    r + cand * w < Zlength old →
    (exists pos,
      (head ≤ pos ∧ pos < tail) ∧
      cand ≤ Znth pos q_idx 0 ∧
      Znth pos q_idx 0 < k ∧
      Znth (r + cand * w) old 0 - cand * v ≤ Znth pos q_val 0) ∨
    Znth (r + cand * w) old 0 - cand * v ≤ current

def MKQueueEntriesValidForResult
    (old q_idx q_val : List Int) (head tail r w v processed cnt : Int) : Prop :=
  forall pos,
    (head ≤ pos ∧ pos < tail) →
    processed - 1 - cnt ≤ Znth pos q_idx 0 ∧
    Znth pos q_idx 0 < processed ∧
    MKQueueEntryValue old q_idx q_val r w v pos

def MKQueueCoversResultWindow
    (old q_idx q_val : List Int) (head tail r w v processed cnt : Int) : Prop :=
  forall cand,
    0 ≤ cand →
    cand < processed →
    processed - 1 - cnt ≤ cand →
    r + cand * w < Zlength old →
    exists pos,
      (head ≤ pos ∧ pos < tail) ∧
      cand ≤ Znth pos q_idx 0 ∧
      Znth pos q_idx 0 < processed ∧
      Znth (r + cand * w) old 0 - cand * v ≤ Znth pos q_val 0

def MKQueueDropLoopState
    (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ k ∧
  tail ≤ Zlength q_idx ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1 ∧
  Zlength old = capacity + 1 ∧
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt ∧
  MKQueueResultValueBound q_val head tail v (k - 1)

def MKQueueAfterDrop
    (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ k ∧
  tail ≤ Zlength q_idx ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1 ∧
  Zlength old = capacity + 1 ∧
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt ∧
  MKQueueResultValueBound q_val head tail v k

def MKQueuePendingState
    (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity current : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ k ∧
  tail ≤ Zlength q_idx ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1 ∧
  Zlength old = capacity + 1 ∧
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWithPending old q_idx q_val head tail r w v k cnt current ∧
  MKQueueResultValueBound q_val head tail v k ∧
  (0 ≤ current + k * v ∧ current + k * v ≤ 1000000) 

def MKQueueState
    (old q_idx q_val : List Int)
    (head tail r w v cnt processed capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ processed ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ processed ∧
  tail ≤ Zlength q_idx ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1 ∧
  Zlength old = capacity + 1 ∧
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v processed cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversResultWindow old q_idx q_val head tail r w v processed cnt ∧
  MKQueueResultValueBound q_val head tail v (processed - 1) ∧
  (head < tail →
     MKTransitionValue old w v cnt capacity (r + (processed - 1) * w)
       (Znth head q_val 0 + (processed - 1) * v))

def MKResidueLoopState
    (old dp q_idx q_val : List Int)
    (r w v cnt k head tail capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ k ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1 ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1 ∧
  MKResiduePrefix old dp r w v cnt k capacity ∧
  MKQueueState old q_idx q_val head tail r w v cnt k capacity

def MKDPTableSafety
    (weights : List Int) (i capacity : Int) (dp : List Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength weights) ∧
  0 ≤ capacity ∧
  Zlength dp = capacity + 1

def MKDPTableSemantics
    (weights values counts : List Int) (i capacity : Int) (dp : List Int) : Prop :=
  forall cap,
    (0 ≤ cap ∧ cap ≤ capacity) →
    MultipleKnapsackPrefixAnswer weights values counts i cap (Znth cap dp 0)

def MKZeroPrefixSafety (dp : List Int) (hi : Int) : Prop :=
  0 ≤ hi ∧ Zlength dp = hi

def MKZeroPrefixSemantics (dp : List Int) (hi : Int) : Prop :=
  forall cap, (0 ≤ cap ∧ cap < hi) → Znth cap dp 0 = 0

def MKCopyPrefixSafety
    (src dst : List Int) (j capacity : Int) : Prop :=
  (0 ≤ j ∧ j ≤ capacity + 1) ∧
  Zlength src = capacity + 1 ∧
  Zlength dst = capacity + 1

def MKCopyPrefixSemantics
    (src dst : List Int) (j : Int) : Prop :=
  forall cap, (0 ≤ cap ∧ cap < j) → Znth cap dst 0 = Znth cap src 0

def MKTransitionSafety
    (old : List Int) (w cnt capacity pos : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  (0 ≤ pos ∧ pos ≤ capacity) ∧
  Zlength old = capacity + 1

def MKTransitionSemantics
    (old : List Int) (w v cnt capacity pos ans : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun take =>
       (0 ≤ take ∧ take ≤ cnt) ∧
       take * w ≤ pos ∧
       (0 ≤ pos - take * w ∧ pos - take * w ≤ capacity) )
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans

def MKItemResidueProgressSafety
    (old dp : List Int) (r w cnt capacity : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  0 ≤ r ∧
  r ≤ w ∧
  r ≤ capacity + 1 ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1

def MKItemResidueProgressSemantics
    (old dp : List Int) (r w v cnt capacity : Int) : Prop :=
  (forall rem k pos,
     pos = rem + k * w →
     (0 ≤ rem ∧ rem < r) →
     0 ≤ k →
     (0 ≤ pos ∧ pos ≤ capacity) →
     MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) ∧
  (forall rem k pos,
     pos = rem + k * w →
     (r ≤ rem ∧ rem < w) →
     0 ≤ k →
     (0 ≤ pos ∧ pos ≤ capacity) →
     Znth pos dp 0 = Znth pos old 0)

def MKItemResiduePrefixSafety
    (old dp : List Int) (r w cnt k capacity : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  r ≤ capacity ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1

def MKItemResiduePrefixSemantics
    (old dp : List Int) (r w v cnt k capacity : Int) : Prop :=
  (forall t,
     (0 ≤ t ∧ t < k) →
     r + t * w ≤ capacity →
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) ∧
  forall pos,
    (0 ≤ pos ∧ pos ≤ capacity) →
    (forall rem t,
       pos = rem + t * w →
       (0 ≤ rem ∧ rem < r) →
       0 ≤ t →
       MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) ∧
    (forall rem t,
       pos = rem + t * w →
       (0 ≤ rem ∧ rem < w) →
       0 ≤ t →
       (r < rem ∨ (rem = r ∧ k ≤ t)) →
       Znth pos dp 0 = Znth pos old 0)

def MKQueueStorageSafety
    (old q_idx q_val : List Int) (head tail limit capacity : Int) : Prop :=
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ limit ∧
  tail ≤ Zlength q_idx ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1 ∧
  Zlength old = capacity + 1

def MKQueueDropSafety
    (old q_idx q_val : List Int)
    (head tail r w k capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  MKQueueStorageSafety old q_idx q_val head tail k capacity

def MKQueueDropSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt k : Int) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt ∧
  MKQueueResultValueBound q_val head tail v (k - 1)

def MKQueueAfterDropSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt k : Int) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt ∧
  MKQueueResultValueBound q_val head tail v k

def MKQueuePendingSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt k current : Int) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWithPending old q_idx q_val head tail r w v k cnt current ∧
  MKQueueResultValueBound q_val head tail v k ∧
  (0 ≤ current + k * v ∧ current + k * v ≤ 1000000) 

def MKQueueResultSafety
    (old q_idx q_val : List Int)
    (head tail r w processed capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ processed ∧
  MKQueueStorageSafety old q_idx q_val head tail processed capacity

def MKQueueResultSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt processed capacity : Int) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v processed cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversResultWindow old q_idx q_val head tail r w v processed cnt ∧
  MKQueueResultValueBound q_val head tail v (processed - 1) ∧
  (head < tail →
     MKTransitionSemantics old w v cnt capacity (r + (processed - 1) * w)
       (Znth head q_val 0 + (processed - 1) * v))

def MKResidueLoopSafety
    (old dp q_idx q_val : List Int)
    (r w k head tail capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ k ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1 ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1

def MKResidueLoopSemantics
    (old dp q_idx q_val : List Int)
    (r w v cnt k head tail capacity : Int) : Prop :=
  (forall t,
     (0 ≤ t ∧ t < k) →
     r + t * w ≤ capacity →
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) ∧
  MKQueueResultSemantics old q_idx q_val head tail r w v cnt k capacity


private theorem nil_of_length {A : Type} (l : List A) (hl : Zlength l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l => rw [Zlength_cons] at hl; have := Zlength_nonneg l; omega

private theorem nth_app_left {A : Type} (l r : List A) (d : A) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    Znth i (l++r) d = Znth i l d := ListLib.app_Znth1 d l r i hi

private theorem prefix_length {A : Type} (l : List A) (i : Int) (hi : 0 ≤ i ∧ i ≤ Zlength l) :
    Zlength (sublist 0 i l) = i := by
  have hh := ListLib.Zlength_sublist 0 i l ⟨le_refl _,hi.1⟩ hi.2
  simpa only [Int.sub_zero] using hh

private theorem prefix_nth {A : Type} (l : List A) (d : A) (i k : Int) (hk : 0 ≤ k ∧ k < i) :
    Znth k (sublist 0 i l) d = Znth k l d := by
  simpa only [Int.add_zero] using Znth_sublist d 0 k i l (le_refl _) (by simpa using hk)

theorem MKZeroPrefix_extend_by_zero (dp : List Int) (hi : Int) (hz : MKZeroPrefix dp hi) :
    MKZeroPrefix (dp++[0]) (hi+1) := by
  obtain ⟨hn,hl,hzero⟩ := hz
  refine ⟨by omega, by rw [Zlength_app,Zlength_cons,Zlength_nil]; omega, ?_⟩
  intro cap hc
  by_cases he : cap = hi
  · rw [he, app_Znth2 0 dp [0] hi (by omega), hl, Int.sub_self, Znth0_cons]
  · rw [nth_app_left dp [0] 0 cap ⟨hc.1, by omega⟩]
    exact hzero cap ⟨hc.1, by omega⟩

theorem MKCopyPrefix_zero (src dst : List Int) (capacity : Int) (hc : 0 ≤ capacity)
    (hs : Zlength src = capacity+1) (hd : Zlength dst = capacity+1) : MKCopyPrefix src dst 0 capacity :=
  ⟨⟨le_refl _,by omega⟩,hs,hd,fun _ hk => by omega⟩

theorem MKCopyPrefix_extend_by_replace_Znth (src dst : List Int) (j capacity : Int)
    (hp : MKCopyPrefix src dst j capacity) (hj : 0 ≤ j ∧ j ≤ capacity) :
    MKCopyPrefix src (replace_Znth j (Znth j src 0) dst) (j+1) capacity := by
  obtain ⟨hr,hs,hd,hcopy⟩ := hp
  refine ⟨⟨by omega,by omega⟩,hs,by rw [Zlength_replace_Znth]; exact hd,?_⟩
  intro cap hc
  by_cases he : cap = j
  · rw [he,Znth_replace_Znth_Same 0 dst j _ ⟨hj.1,by omega⟩]
  · rw [Znth_replace_Znth_Diff 0 dst j cap _ ⟨hj.1,by omega⟩ ⟨hc.1,by omega⟩ (Ne.symm he)]
    exact hcopy cap ⟨hc.1,by omega⟩

theorem MKDPTable_copy_full (weights values counts : List Int) (i capacity : Int) (src dst : List Int)
    (hd : MKDPTable weights values counts i capacity src) (hc : MKCopyPrefix src dst (capacity+1) capacity) :
    MKDPTable weights values counts i capacity dst := by
  obtain ⟨hi,hcap,hs,ha⟩ := hd
  obtain ⟨_,_,hl,hcopy⟩ := hc
  refine ⟨hi,hcap,hl,?_⟩
  intro cap hc; rw [hcopy cap ⟨hc.1,by omega⟩]; exact ha cap hc

theorem MKItemResiduePrefixProgress_init (old dp : List Int) (r w v cnt capacity : Int)
    (hr : 0 ≤ r ∧ r < w) (hc : r ≤ capacity) (hs : MKItemResidueProgress old dp r w v cnt capacity) :
    MKItemResiduePrefixProgress old dp r w v cnt 0 capacity := by
  obtain ⟨hw,hcnt,hr0,hrw,hrcap,hold,hdp,hdone,hfuture⟩ := hs
  refine ⟨hw,hcnt,hr,le_refl _,hc,hold,hdp,⟨hr,le_refl _,hold,hdp,fun _ ht _ => by omega⟩,?_⟩
  intro pos hp
  refine ⟨fun rem t he hr ht => hdone rem t pos he hr ht hp,?_⟩
  intro rem t he hrem ht hlater
  exact hfuture rem t pos he ⟨by omega,hrem.2⟩ ht hp

theorem MKResidueLoopState_empty_queue_init (old dp q_idx q_val : List Int) (r w v cnt capacity : Int)
    (hr : 0 ≤ r ∧ r < w) (hc : r ≤ capacity) (hqi : Zlength q_idx = capacity+1) (hqv : Zlength q_val = capacity+1)
    (hs : MKItemResidueProgress old dp r w v cnt capacity) : MKResidueLoopState old dp q_idx q_val r w v cnt 0 0 0 capacity := by
  obtain ⟨hw,hcnt,hr0,hrw,hrcap,hold,hdp,hdone,hfuture⟩ := hs
  refine ⟨hr,le_refl _,⟨le_refl _,le_refl _⟩,le_refl _,hold,hdp,hqi,hqv,
    ⟨hr,le_refl _,hold,hdp,fun _ ht _ => by omega⟩,?_⟩
  refine ⟨hr,le_refl _,⟨le_refl _,le_refl _⟩,le_refl _,by omega,hqi,hqv,hold,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [MKQueueEntriesValidForResult,MKQueueIndexIncreasing,MKQueueValueDecreasing,MKQueueCoversResultWindow,MKQueueResultValueBound]
  all_goals intros <;> omega

theorem MKForall2_pick_nonneg_Znth (picks counts : List Int) (idx : Int)
    (hf : List.Forall₂ (fun pick cnt => 0 ≤ pick ∧ pick ≤ cnt) picks counts)
    (hi : 0 ≤ idx ∧ idx < Zlength picks) : 0 ≤ Znth idx picks 0 := by
  induction hf generalizing idx with
  | nil => simp [Zlength] at hi; omega
  | @cons pick cnt picks counts hp ht ih =>
    by_cases he : idx = 0
    · rw [he,Znth0_cons]; exact hp.1
    · rw [Znth_cons 0 idx pick picks (by omega)]
      exact ih (idx-1) (by rw [Zlength_cons] at hi; omega)

private theorem pick_cons (a b : Int) (xs ys : List Int) : PickWeight (a::xs) (b::ys) = a*b+PickWeight xs ys := rfl

private theorem bounds_tail (weights values : List Int) (w v : Int)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength (w::weights)) →
      1 ≤ Znth idx (w::weights) 0 ∧ 0 ≤ Znth idx (v::values) 0 ∧ Znth idx (v::values) 0 ≤ 1000) :
    ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000 := by
  intro idx hi
  have hh := hb (idx+1) ⟨by omega,by rw [Zlength_cons]; omega⟩
  simpa only [Znth_cons 0 (idx+1) w weights (by omega),Znth_cons 0 (idx+1) v values (by omega),Int.add_sub_cancel] using hh

theorem MKPickValue_le_weight_times_1000 (weights values picks : List Int)
    (hv : Zlength values = Zlength weights) (hp : Zlength picks = Zlength weights)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000)
    (hpn : ∀ idx, (0 ≤ idx ∧ idx < Zlength picks) → 0 ≤ Znth idx picks 0) :
    0 ≤ PickValue values picks ∧ PickValue values picks ≤ PickWeight weights picks*1000 := by
  induction weights generalizing values picks with
  | nil =>
    have ve := nil_of_length values hv; have pe := nil_of_length picks hp
    subst values; subst picks; exact ⟨le_refl _,le_refl _⟩
  | cons w weights ih =>
    cases values with
    | nil => rw [Zlength_cons] at hv; have := Zlength_nonneg weights; change 0 = _ at hv; omega
    | cons v values =>
      cases picks with
      | nil => rw [Zlength_cons] at hp; have := Zlength_nonneg weights; change 0 = _ at hp; omega
      | cons p picks =>
        have hh := hb 0 ⟨le_refl _,by rw [Zlength_cons]; have := Zlength_nonneg weights; omega⟩
        have hn := hpn 0 ⟨le_refl _,by rw [Zlength_cons]; have := Zlength_nonneg picks; omega⟩
        simp only [Znth0_cons] at hh hn
        have ht := ih values picks (by rw [Zlength_cons,Zlength_cons] at hv; omega)
          (by rw [Zlength_cons,Zlength_cons] at hp; omega) (bounds_tail weights values w v hb) (by
            intro idx hi
            have hh := hpn (idx+1) ⟨by omega,by rw [Zlength_cons]; omega⟩
            simpa only [Znth_cons 0 (idx+1) p picks (by omega),Int.add_sub_cancel] using hh)
        change 0 ≤ v*p+PickValue values picks ∧ v*p+PickValue values picks ≤ (w*p+PickWeight weights picks)*1000
        have h1 := mul_nonneg hh.2.1 hn
        have h2 := mul_le_mul_of_nonneg_right hh.2.2 hn
        have h3 := mul_le_mul_of_nonneg_right hh.1 hn
        constructor <;> nlinarith

theorem MKBoundedPickList_value_bound (weights values counts : List Int) (capacity : Int) (picks : List Int)
    (hc : 0 ≤ capacity)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000)
    (hp : BoundedPickList weights values counts capacity picks) : 0 ≤ PickValue values picks ∧ PickValue values picks ≤ capacity*1000 := by
  obtain ⟨hwv,hwc,hp,hcap,hfor,hn,hweight⟩ := hp
  have := MKPickValue_le_weight_times_1000 weights values picks hwv.symm hp hb (fun idx hi => MKForall2_pick_nonneg_Znth picks counts idx hfor hi)
  omega

theorem MultipleKnapsackPrefixAnswer_zero_items (weights values counts : List Int) (capacity : Int) (hc : 0 ≤ capacity) :
    MultipleKnapsackPrefixAnswer weights values counts 0 capacity 0 := by
  refine ⟨[],⟨?_,?_⟩,rfl⟩
  · exact ⟨rfl,rfl,rfl,hc,List.Forall₂.nil,le_refl _,hc⟩
  · intro picks hp
    have he := nil_of_length picks hp.2.2.1
    subst picks; exact le_refl _

theorem MKZeroPrefix_implies_MKDPTable_zero_items (weights values counts : List Int) (capacity : Int) (dp : List Int)
    (hc : 0 ≤ capacity) (hz : MKZeroPrefix dp (capacity+1)) : MKDPTable weights values counts 0 capacity dp := by
  refine ⟨⟨le_refl _,Zlength_nonneg _⟩,hc,hz.2.1,?_⟩
  intro cap hcap
  rw [hz.2.2 cap ⟨hcap.1,by omega⟩]
  exact MultipleKnapsackPrefixAnswer_zero_items weights values counts cap hcap.1

theorem MultipleKnapsackPrefixAnswer_value_bound_by_capacity (weights values counts : List Int) (i capacity ans : Int)
    (hi : 0 ≤ i ∧ i ≤ Zlength weights) (hc : 0 ≤ capacity)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000)
    (ha : MultipleKnapsackPrefixAnswer weights values counts i capacity ans) : 0 ≤ ans ∧ ans ≤ capacity*1000 := by
  obtain ⟨picks,⟨hp,hm⟩,he⟩ := ha
  rw [← he]
  apply MKBoundedPickList_value_bound _ _ _ capacity picks hc _ hp
  intro idx hidx
  rw [prefix_length weights i hi] at hidx
  rw [prefix_nth weights 0 i idx hidx,prefix_nth values 0 i idx hidx]
  exact hb idx ⟨hidx.1,by omega⟩

theorem MKDPTable_value_bound_by_capacity (weights values counts : List Int) (i capacity : Int) (dp : List Int) (pos : Int)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000)
    (hd : MKDPTable weights values counts i capacity dp) (hp : 0 ≤ pos ∧ pos ≤ capacity) :
    0 ≤ Znth pos dp 0 ∧ Znth pos dp 0 ≤ pos*1000 :=
  MultipleKnapsackPrefixAnswer_value_bound_by_capacity weights values counts i pos _ hd.1 hp.1 hb (hd.2.2.2 pos hp)

theorem MKDPTable_implies_MKDPValueBound_under_global_item_bounds (weights values counts : List Int) (i capacity : Int) (dp : List Int)
    (hc : 0 ≤ capacity ∧ capacity ≤ 1000)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000)
    (hd : MKDPTable weights values counts i capacity dp) : MKDPValueBound dp capacity := by
  refine ⟨hd.2.2.1,?_⟩
  intro cap hp
  have := MKDPTable_value_bound_by_capacity weights values counts i capacity dp cap hb hd hp
  omega

theorem MKCopyPrefix_full_preserves_Znth (src dst : List Int) (capacity pos : Int)
    (hc : MKCopyPrefix src dst (capacity+1) capacity) (hp : 0 ≤ pos ∧ pos ≤ capacity) : Znth pos dst 0 = Znth pos src 0 :=
  hc.2.2.2 pos ⟨hp.1,by omega⟩

theorem MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds (weights values counts : List Int) (i capacity : Int) (dp old : List Int)
    (hc : 0 ≤ capacity ∧ capacity ≤ 1000)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000)
    (hd : MKDPTable weights values counts i capacity dp) (hcopy : MKCopyPrefix dp old (capacity+1) capacity) : MKDPValueBound old capacity :=
  MKDPTable_implies_MKDPValueBound_under_global_item_bounds weights values counts i capacity old hc hb (MKDPTable_copy_full weights values counts i capacity dp old hd hcopy)

theorem MKDPTable_implies_MKTransitionValueBound_for_current_item (weights values counts : List Int) (i capacity : Int) (dp old : List Int) (w v cnt : Int)
    (hc : 0 ≤ capacity ∧ capacity ≤ 1000) (hw : 1 ≤ w) (hv : 0 ≤ v ∧ v ≤ 1000)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0 ∧ 0 ≤ Znth idx values 0 ∧ Znth idx values 0 ≤ 1000)
    (hd : MKDPTable weights values counts i capacity dp) (hcopy : MKCopyPrefix dp old (capacity+1) capacity) :
    MKTransitionValueBound old w v cnt capacity := by
  intro pos ans hp ht
  obtain ⟨_,_,_,_,take,⟨⟨htake,htw,hrem⟩,hm⟩,he⟩ := ht
  dsimp at he
  rw [← he,MKCopyPrefix_full_preserves_Znth dp old capacity _ hcopy hrem]
  have hh := MKDPTable_value_bound_by_capacity weights values counts i capacity dp (pos-take*w) hb hd hrem
  have hvp := mul_nonneg htake.1 hv.1
  have hvt := mul_le_mul_of_nonneg_left hv.2 htake.1
  have hwt := mul_le_mul_of_nonneg_left hw htake.1
  constructor <;> nlinarith

theorem MKCopyPrefix_full_implies_MKItemResidueProgress_zero (old dp : List Int) (w v cnt capacity : Int)
    (hw : 1 ≤ w) (hcnt : 0 ≤ cnt) (hc : MKCopyPrefix dp old (capacity+1) capacity) :
    MKItemResidueProgress old dp 0 w v cnt capacity := by
  obtain ⟨hr,hd,ho,hcopy⟩ := hc
  refine ⟨by omega,hcnt,le_refl _,by omega,by omega,ho,hd,?_,?_⟩
  · intro rem k pos he hr hk hp; omega
  · intro rem k pos he hr hk hp; exact (hcopy pos ⟨hp.1,by omega⟩).symm

theorem MKResidueLoopState_to_MKQueueDropLoopState_predrop (old dp q_idx q_val : List Int) (r w v cnt k head tail capacity : Int)
    (hs : MKResidueLoopState old dp q_idx q_val r w v cnt k head tail capacity) :
    MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound,_⟩ := hs
  refine ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,?_,hbound⟩
  intro cand hc hck hcl hco
  exact hcover cand hc hck (by omega) hco

theorem MKQueueDropLoopState_pop_expired_preserves_predrop (old q_idx q_val : List Int) (head tail r w v cnt k capacity : Int)
    (he : Znth head q_idx 0 < k-cnt) (hn : head < tail)
    (hs : MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity) :
    MKQueueDropLoopState old q_idx q_val (head+1) tail r w v cnt k capacity := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound⟩ := hs
  refine ⟨hr,hk,⟨by omega,by omega⟩,ht,htl,hqi,hqv,ho,?_,?_,?_,?_,?_⟩
  · intro p hp; exact hvalid p ⟨by omega,hp.2⟩
  · intro p q hpq; exact hinc p q ⟨by omega,hpq.2⟩
  · intro p q hpq; exact hdec p q ⟨by omega,hpq.2⟩
  · intro cand hc hck hcl hco
    obtain ⟨pos,hpos,hcp,hpk,hv⟩ := hcover cand hc hck hcl hco
    have hne : pos ≠ head := by intro heq; rw [heq] at hcp; omega
    exact ⟨pos,⟨by omega,hpos.2⟩,hcp,hpk,hv⟩
  · intro p hp; exact hbound p ⟨by omega,hp.2⟩

theorem MKQueueDropLoopState_empty_exit_to_MKQueueAfterDrop (old q_idx q_val : List Int) (head tail r w v cnt k capacity : Int)
    (he : head ≥ tail) (hs : MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity) :
    MKQueueAfterDrop old q_idx q_val head tail r w v cnt k capacity := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound⟩ := hs
  exact ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,fun _ hp => by omega,hinc,hdec,hcover,fun _ hp => by omega⟩

private theorem candidate_nonnegative (r w k take : Int) (hr : 0 ≤ r ∧ r < w) (ht : take*w ≤ r+k*w) : 0 ≤ k-take := by
  by_contra hn
  have : k+1 ≤ take := by omega
  have hw : 0 < w := by omega
  nlinarith

private theorem transition_by_candidates (old : List Int) (r w v cnt capacity k idx ans : Int)
    (hr : 0 ≤ r ∧ r < w) (hk : 0 ≤ k) (hc : 0 ≤ cnt) (hp : 0 ≤ r+k*w ∧ r+k*w ≤ capacity)
    (hl : Zlength old = capacity+1) (hi : 0 ≤ idx ∧ idx ≤ k) (hci : k-cnt ≤ idx)
    (hpos : r+idx*w ≤ capacity) (he : Znth (r+idx*w) old 0+(k-idx)*v = ans)
    (hm : ∀ cand, (0 ≤ cand ∧ cand ≤ k) → k-cnt ≤ cand → r+cand*w ≤ capacity →
      Znth (r+cand*w) old 0+(k-cand)*v ≤ ans) : MKTransitionValue old w v cnt capacity (r+k*w) ans := by
  have hw : 0 < w := by omega
  have hprod := mul_nonneg hi.1 (le_of_lt hw)
  have hprod2 := mul_nonneg (show 0 ≤ k-idx by omega) (le_of_lt hw)
  have hs : r+k*w-(k-idx)*w = r+idx*w := by ring
  refine ⟨hw,hc,hp,hl,k-idx,⟨?_,?_⟩,?_⟩
  · exact ⟨⟨by omega,by omega⟩,by nlinarith,by rw [hs]; constructor <;> nlinarith⟩
  · intro take ht
    obtain ⟨htr,htfit,htpos⟩ := ht
    have hn := candidate_nonnegative r w k take hr htfit
    have hcan : r+(k-take)*w = r+k*w-take*w := by ring
    have hh := hm (k-take) ⟨hn,by omega⟩ (by omega) (by rw [hcan]; exact htpos.2)
    dsimp
    rw [hs,he,← hcan]
    simpa only [show k-(k-take) = take by omega] using hh
  · dsimp; rw [hs]; exact he

private theorem decreasing_head_upper (q : List Int) (head tail : Int) (hd : MKQueueValueDecreasing q head tail)
    (pos : Int) (hp : head ≤ pos ∧ pos < tail) : Znth pos q 0 ≤ Znth head q 0 := by
  by_cases he : pos = head
  · rw [he]
  · have := hd head pos ⟨le_refl _,by omega,hp.2⟩; omega

theorem MKQueueDropLoopState_nonempty_exit_to_MKQueueAfterDrop (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity current curpos : Int) (hg : Znth head q_idx 0 ≥ k-cnt)
    (hn : head < tail) (hv : 0 ≤ v) (hr0 : 0 ≤ r) (hrw : r < w) (hw : 1 ≤ w)
    (hpos : curpos = r+k*w) (hp : 0 ≤ curpos ∧ curpos ≤ capacity)
    (hcurrent : current = Znth curpos old 0-k*v) (hcupper : current+k*v ≤ 1000000)
    (htrans : MKTransitionValueBound old w v cnt capacity)
    (hs : MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity) :
    MKQueueAfterDrop old q_idx q_val head tail r w v cnt k capacity := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound⟩ := hs
  obtain ⟨hheadold,hheadlt,hhead0,hheadpos,hheadval⟩ := hvalid head ⟨le_refl _,hn⟩
  have hheadupper : Znth head q_val 0+k*v ≤ 1000000 := by
    by_cases hle : Znth head q_val 0+k*v ≤ current+k*v
    · omega
    · have hcnt : 0 ≤ cnt := by omega
      have he : Znth (r+Znth head q_idx 0*w) old 0+(k-Znth head q_idx 0)*v = Znth head q_val 0+k*v := by
        rw [hheadval]; ring
      have htransition := transition_by_candidates old r w v cnt capacity k (Znth head q_idx 0) _ hr hk hcnt
        (by rw [← hpos]; exact hp) ho ⟨hhead0,by omega⟩ hg (by omega) he (by
          intro cand hcan hcl hcp
          by_cases hck : cand = k
          · rw [hck,Int.sub_self,Int.zero_mul,Int.add_zero,← hpos]
            omega
          · obtain ⟨pos,hpr,hci,hik,hvc⟩ := hcover cand hcan.1 (by omega) hcl (by omega)
            have hupper := decreasing_head_upper q_val head tail hdec pos hpr
            nlinarith)
      have hh := htrans (r+k*w) _ (by rw [← hpos]; exact hp) htransition
      exact hh.2
  refine ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,?_,hinc,hdec,hcover,?_⟩
  · intro pos hpr
    obtain ⟨hlo,hlt,hentry⟩ := hvalid pos hpr
    have hidx : k-cnt ≤ Znth pos q_idx 0 := by
      by_cases he : pos = head
      · rw [he]; exact hg
      · have hh := hinc head pos ⟨le_refl _,by omega,hpr.2⟩; omega
    exact ⟨hidx,hlt,hentry⟩
  · intro pos hp
    have hprev := hbound pos hp
    have hhead := decreasing_head_upper q_val head tail hdec pos hp
    constructor <;> nlinarith

theorem MKQueueAfterDrop_to_MKQueuePendingState_current (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity current : Int)
    (hs : MKQueueAfterDrop old q_idx q_val head tail r w v cnt k capacity) (hc : 0 ≤ current+k*v ∧ current+k*v ≤ 1000000) :
    MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound⟩ := hs
  exact ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,fun cand hc hck hcl hco => Or.inl (hcover cand hc hck hcl hco),hbound,hc⟩

theorem MKQueuePendingState_pop_dominated_tail_preserves (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity current : Int)
    (hs : MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current)
    (hn : head < tail) (hd : Znth (tail-1) q_val 0 ≤ current) :
    MKQueuePendingState old q_idx q_val head (tail-1) r w v cnt k capacity current := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound,hcurrent⟩ := hs
  refine ⟨hr,hk,⟨hh.1,by omega⟩,by omega,by omega,hqi,hqv,ho,?_,?_,?_,?_,?_,hcurrent⟩
  · intro p hp; exact hvalid p ⟨hp.1,by omega⟩
  · intro p q hpq; exact hinc p q ⟨hpq.1,hpq.2.1,by omega⟩
  · intro p q hpq; exact hdec p q ⟨hpq.1,hpq.2.1,by omega⟩
  · intro cand hc hck hcl hco
    rcases hcover cand hc hck hcl hco with ⟨pos,hpr,hci,hik,hvc⟩ | hvc
    · by_cases ht : pos < tail-1
      · exact Or.inl ⟨pos,⟨hpr.1,ht⟩,hci,hik,hvc⟩
      · have he : pos = tail-1 := by omega
        rw [he] at hvc; exact Or.inr (le_trans hvc hd)
    · exact Or.inr hvc
  · intro p hp; exact hbound p ⟨hp.1,by omega⟩

private theorem updated_nth (l : List Int) (idx value pos : Int)
    (hi : 0 ≤ idx ∧ idx < Zlength l) (hp : 0 ≤ pos ∧ pos < Zlength l) :
    Znth pos (replace_Znth idx value l) 0 = if pos = idx then value else Znth pos l 0 := by
  by_cases he : pos = idx
  · subst pos; rw [Znth_replace_Znth_Same 0 l idx value hi,if_pos rfl]
  · rw [Znth_replace_Znth_Diff 0 l idx pos value hi hp (Ne.symm he),if_neg he]

theorem MKQueuePendingState_push_to_MKQueueState (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity current : Int)
    (hs : MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current)
    (hc : current = Znth (r+k*w) old 0-k*v) (hp : 0 ≤ r+k*w ∧ r+k*w ≤ capacity)
    (hcnt : 0 ≤ cnt) (hkc : k ≤ capacity) (hdom : head < tail → Znth (tail-1) q_val 0 > current) :
    MKQueueState old (replace_Znth tail k q_idx) (replace_Znth tail current q_val) head (tail+1) r w v cnt (k+1) capacity := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound,hcurrent⟩ := hs
  let qi := replace_Znth tail k q_idx
  let qv := replace_Znth tail current q_val
  have hti : 0 ≤ tail ∧ tail < Zlength q_idx := ⟨by omega,by omega⟩
  have htv : 0 ≤ tail ∧ tail < Zlength q_val := ⟨by omega,by omega⟩
  have ni (pos : Int) (hp : head ≤ pos ∧ pos < tail+1) : Znth pos qi 0 = if pos = tail then k else Znth pos q_idx 0 :=
    updated_nth q_idx tail k pos hti ⟨by omega,by omega⟩
  have nv (pos : Int) (hp : head ≤ pos ∧ pos < tail+1) : Znth pos qv 0 = if pos = tail then current else Znth pos q_val 0 :=
    updated_nth q_val tail current pos htv ⟨by omega,by omega⟩
  have vf : MKQueueEntriesValidForResult old qi qv head (tail+1) r w v (k+1) cnt := by
    intro pos hp'
    unfold MKQueueEntryValue
    rw [ni pos hp',nv pos hp']
    by_cases he : pos = tail
    · simp only [if_pos he]
      exact ⟨by omega,by omega,hk,by omega,hc⟩
    · simp only [if_neg he]
      obtain ⟨hlo,hlt,hentry⟩ := hvalid pos ⟨hp'.1,by omega⟩
      exact ⟨by omega,by omega,hentry⟩
  have inf : MKQueueIndexIncreasing qi head (tail+1) := by
    intro p q hpq
    rw [ni p ⟨hpq.1,by omega⟩,ni q ⟨by omega,hpq.2.2⟩,if_neg (by omega : p ≠ tail)]
    by_cases he : q = tail
    · rw [if_pos he]
      exact (hvalid p ⟨hpq.1,by omega⟩).2.1
    · rw [if_neg he]; exact hinc p q ⟨hpq.1,hpq.2.1,by omega⟩
  have df : MKQueueValueDecreasing qv head (tail+1) := by
    intro p q hpq
    rw [nv p ⟨hpq.1,by omega⟩,nv q ⟨by omega,hpq.2.2⟩,if_neg (by omega : p ≠ tail)]
    by_cases he : q = tail
    · rw [if_pos he]
      have hlast := hdom (by omega)
      by_cases hep : p = tail-1
      · rw [hep]; exact hlast
      · have := hdec p (tail-1) ⟨hpq.1,by omega,by omega⟩; omega
    · rw [if_neg he]; exact hdec p q ⟨hpq.1,hpq.2.1,by omega⟩
  have cf : MKQueueCoversResultWindow old qi qv head (tail+1) r w v (k+1) cnt := by
    intro cand hcn hck hcc hco
    by_cases hlt : cand < k
    · rcases hcover cand hcn hlt (by omega) hco with ⟨pos,hpr,hci,hik,hvc⟩ | hvc
      · refine ⟨pos,⟨hpr.1,by omega⟩,?_,?_,?_⟩
        · rw [ni pos ⟨hpr.1,by omega⟩,if_neg (by omega)]; exact hci
        · rw [ni pos ⟨hpr.1,by omega⟩,if_neg (by omega)]; omega
        · rw [nv pos ⟨hpr.1,by omega⟩,if_neg (by omega)]; exact hvc
      · refine ⟨tail,⟨hh.2,by omega⟩,?_,?_,?_⟩
        · rw [ni tail ⟨hh.2,by omega⟩,if_pos rfl]; omega
        · rw [ni tail ⟨hh.2,by omega⟩,if_pos rfl]; omega
        · rw [nv tail ⟨hh.2,by omega⟩,if_pos rfl]; exact hvc
    · have he : cand = k := by omega
      subst cand
      refine ⟨tail,⟨hh.2,by omega⟩,?_,?_,?_⟩
      · rw [ni tail ⟨hh.2,by omega⟩,if_pos rfl]
      · rw [ni tail ⟨hh.2,by omega⟩,if_pos rfl]; omega
      · rw [nv tail ⟨hh.2,by omega⟩,if_pos rfl,← hc]
  have bf : MKQueueResultValueBound qv head (tail+1) v k := by
    intro pos hp'
    rw [nv pos hp']
    by_cases he : pos = tail
    · rw [if_pos he]; exact hcurrent
    · rw [if_neg he]; exact hbound pos ⟨hp'.1,by omega⟩
  refine ⟨hr,by omega,⟨hh.1,by omega⟩,by omega,by change tail+1 ≤ Zlength (replace_Znth tail k q_idx); rw [Zlength_replace_Znth]; omega,
    by change Zlength (replace_Znth tail k q_idx) = capacity+1; rw [Zlength_replace_Znth]; exact hqi,
    by change Zlength (replace_Znth tail current q_val) = capacity+1; rw [Zlength_replace_Znth]; exact hqv,ho,vf,inf,df,cf,?_,?_⟩
  · simpa only [show k+1-1 = k by omega] using bf
  · intro hn
    simp only [show k+1-1 = k by omega]
    obtain ⟨hlo,hlt,hidx,hidxpos,hval⟩ := vf head ⟨le_refl _,hn⟩
    apply transition_by_candidates old r w v cnt capacity k (Znth head qi 0) _ hr hk hcnt hp ho
      ⟨hidx,by omega⟩ (by omega) (by omega) (by rw [hval]; ring)
    intro cand hcan hcc hcp
    obtain ⟨pos,hpr,hci,hik,hvc⟩ := cf cand hcan.1 (by omega) (by omega) (by omega)
    have hupper := decreasing_head_upper qv head (tail+1) df pos hpr
    nlinarith

theorem MKQueueState_head_transition (old q_idx q_val : List Int) (head tail r w v cnt processed capacity : Int)
    (hs : MKQueueState old q_idx q_val head tail r w v cnt processed capacity) (hn : head < tail) :
    MKTransitionValue old w v cnt capacity (r+(processed-1)*w) (Znth head q_val 0+(processed-1)*v) :=
  hs.2.2.2.2.2.2.2.2.2.2.2.2.2 hn

theorem MKQueueState_head_result_bound (q_val : List Int) (head tail v processed : Int)
    (hb : MKQueueResultValueBound q_val head tail v (processed-1)) (hn : head < tail) :
    0 ≤ Znth head q_val 0+(processed-1)*v ∧ Znth head q_val 0+(processed-1)*v ≤ 1000000 := hb head ⟨le_refl _,hn⟩

theorem MKQueueState_head_bound (old q_idx q_val : List Int) (head tail r w v cnt processed capacity : Int)
    (hs : MKQueueState old q_idx q_val head tail r w v cnt processed capacity) (hn : head < tail) :
    0 ≤ Znth head q_val 0+(processed-1)*v ∧ Znth head q_val 0+(processed-1)*v ≤ 1000000 :=
  hs.2.2.2.2.2.2.2.2.2.2.2.2.1 head ⟨le_refl _,hn⟩

theorem residue_repr_unique (rem1 rem2 t1 t2 w : Int) (hw : 0 < w)
    (h1 : 0 ≤ rem1 ∧ rem1 < w) (h2 : 0 ≤ rem2 ∧ rem2 < w)
    (he : rem1+t1*w = rem2+t2*w) : rem1 = rem2 := by
  have hmod := congrArg (fun z : Int => z % w) he
  simpa only [Int.add_mul_emod_self_right,Int.emod_eq_of_lt h1.1 h1.2,Int.emod_eq_of_lt h2.1 h2.2] using hmod

theorem MKItemResiduePrefixProgress_extend_after_dp_write (old dp : List Int) (r w v cnt k capacity pos ans : Int)
    (he : pos = r+k*w) (hp : 0 ≤ pos ∧ pos ≤ capacity)
    (hs : MKItemResiduePrefixProgress old dp r w v cnt k capacity)
    (ht : MKTransitionValue old w v cnt capacity pos ans) :
    MKItemResiduePrefixProgress old (replace_Znth pos ans dp) r w v cnt (k+1) capacity := by
  obtain ⟨hw,hcnt,hr,hk,hrc,ho,hd,hpref,hrest⟩ := hs
  have hpidx : 0 ≤ pos ∧ pos < Zlength dp := ⟨hp.1,by omega⟩
  refine ⟨hw,hcnt,hr,by omega,hrc,ho,by rw [Zlength_replace_Znth]; exact hd,?_,?_⟩
  · refine ⟨hr,by omega,ho,by rw [Zlength_replace_Znth]; exact hd,?_⟩
    intro t htr hcap
    have hprod := mul_nonneg htr.1 (le_of_lt hw)
    by_cases htk : t < k
    · rw [Znth_replace_Znth_Diff 0 dp pos (r+t*w) ans hpidx ⟨by nlinarith,by omega⟩ (by nlinarith)]
      exact hpref.2.2.2.2 t ⟨htr.1,htk⟩ hcap
    · have htk : t = k := by omega
      rw [htk,← he,Znth_replace_Znth_Same 0 dp pos ans hpidx]; exact ht
  · intro p hpr
    obtain ⟨hdone,hsame⟩ := hrest p hpr
    refine ⟨?_,?_⟩
    · intro rem t hrep hrem ht0
      have hne : pos ≠ p := by
        intro heq
        have hre := residue_repr_unique rem r t k w hw ⟨hrem.1,by omega⟩ hr (by omega)
        omega
      rw [Znth_replace_Znth_Diff 0 dp pos p ans hpidx ⟨hpr.1,by omega⟩ hne]
      exact hdone rem t hrep hrem ht0
    · intro rem t hrep hrem ht0 hcase
      have hne : pos ≠ p := by
        intro heq
        have hre := residue_repr_unique rem r t k w hw hrem hr (by omega)
        rcases hcase with hlater | ⟨hrr,htt⟩
        · omega
        · nlinarith
      rw [Znth_replace_Znth_Diff 0 dp pos p ans hpidx ⟨hpr.1,by omega⟩ hne]
      exact hsame rem t hrep hrem ht0 (by omega)

theorem MKResidueLoopState_after_dp_write (old dp qidx qval : List Int) (r w v cnt k head tail capacity : Int)
    (hp : MKItemResiduePrefixProgress old dp r w v cnt k capacity)
    (hq : MKQueueState old qidx qval head tail r w v cnt k capacity) :
    MKResidueLoopState old dp qidx qval r w v cnt k head tail capacity := by
  obtain ⟨hw,hcnt,hr,hk,hrc,ho,hd,hpref,hrest⟩ := hp
  exact ⟨hr,hk,hq.2.2.1,hq.2.2.2.1,ho,hd,hq.2.2.2.2.2.1,hq.2.2.2.2.2.2.1,hpref,hq⟩

theorem MKResidueLoopState_to_MKItemResidueProgress_next_residue (old dp qidx qval : List Int) (r w v cnt k head tail capacity pos : Int)
    (he : pos = r+k*w) (hpos : pos > capacity)
    (hp : MKItemResiduePrefixProgress old dp r w v cnt k capacity)
    (hloop : MKResidueLoopState old dp qidx qval r w v cnt k head tail capacity) :
    MKItemResidueProgress old dp (r+1) w v cnt capacity := by
  obtain ⟨hw,hcnt,hr,hk,hrc,ho,hd,hpref,hrest⟩ := hp
  refine ⟨hw,hcnt,by omega,by omega,by omega,ho,hd,?_,?_⟩
  · intro rem t p hrep hrem ht hpr
    by_cases hrlt : rem < r
    · exact (hrest p hpr).1 rem t hrep ⟨hrem.1,hrlt⟩ ht
    · have hre : rem = r := by omega
      have htk : t < k := by nlinarith
      rw [hrep,hre]
      exact hpref.2.2.2.2 t ⟨ht,htk⟩ (by rw [← hre,← hrep]; exact hpr.2)
  · intro rem t p hrep hrem ht hpr
    exact (hrest p hpr).2 rem t hrep ⟨by omega,hrem.2⟩ ht (Or.inl (by omega))

theorem worker_Zlength_eq_length (A B : Type) (xs : List A) (ys : List B)
    (h : Zlength xs = Zlength ys) : xs.length = ys.length := by
  change (xs.length : Int) = (ys.length : Int) at h
  omega

theorem worker_sublist_0_succ {A : Type} (d : A) (xs : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength xs) : sublist 0 (i+1) xs = sublist 0 i xs ++ [Znth i xs d] := by
  rw [sublist_split 0 (i+1) i xs ⟨by omega,by omega⟩ ⟨by omega,by omega⟩,sublist_single d i xs hi]

theorem worker_PickWeight_app_single (weights picks : List Int) (w take : Int)
    (hl : Zlength picks = Zlength weights) :
    PickWeight (weights++[w]) (picks++[take]) = PickWeight weights picks+w*take := by
  induction weights generalizing picks with
  | nil =>
    have he : picks = [] := nil_of_length picks (by simpa using hl)
    subst picks; change w*take+0 = 0+w*take; omega
  | cons x xs ih =>
    cases picks with
    | nil => simp only [Zlength_nil,Zlength_cons] at hl; have := Zlength_nonneg xs; omega
    | cons p ps =>
      simp only [Zlength_cons] at hl
      change x*p+PickWeight (xs++[w]) (ps++[take]) = (x*p+PickWeight xs ps)+w*take
      rw [ih ps (by omega)]; ring

theorem worker_PickValue_app_single (values picks : List Int) (v take : Int)
    (hl : Zlength picks = Zlength values) :
    PickValue (values++[v]) (picks++[take]) = PickValue values picks+v*take :=
  worker_PickWeight_app_single values picks v take hl

theorem worker_BoundedPickList_extend (pweights pvalues pcounts picks : List Int) (rem capacity w v cnt take : Int)
    (hb : BoundedPickList pweights pvalues pcounts rem picks) (hw : 0 < w)
    (ht : 0 ≤ take ∧ take ≤ cnt) (hc : capacity = rem+take*w) :
    BoundedPickList (pweights++[w]) (pvalues++[v]) (pcounts++[cnt]) capacity (picks++[take]) := by
  obtain ⟨hwv,hwc,hp,hr,hall,hn,hle⟩ := hb
  refine ⟨?_,?_,?_,by nlinarith,?_,?_,?_⟩
  · simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  · simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  · simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  · exact List.rel_append hall (.cons ht .nil)
  · rw [worker_PickWeight_app_single pweights picks w take hp]; nlinarith
  · rw [worker_PickWeight_app_single pweights picks w take hp]; nlinarith

theorem worker_PickWeight_nonneg (weights picks counts : List Int)
    (hl : Zlength weights = Zlength picks)
    (hf : List.Forall₂ (fun pick cnt : Int => 0 ≤ pick ∧ pick ≤ cnt) picks counts)
    (hw : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 0 ≤ Znth idx weights 0) :
    0 ≤ PickWeight weights picks := by
  induction weights generalizing picks counts with
  | nil => change 0 ≤ 0; omega
  | cons w ws ih =>
    cases picks with
    | nil => change 0 ≤ 0; omega
    | cons p ps =>
      cases hf with
      | cons hp hf =>
        have hw0 := hw 0 ⟨by omega,by rw [Zlength_cons]; have := Zlength_nonneg ws; omega⟩
        rw [Znth0_cons] at hw0
        have ht := ih ps _ (by simp only [Zlength_cons] at hl; omega) hf (by
          intro idx hidx
          have ht := hw (idx+1) ⟨by omega,by rw [Zlength_cons]; omega⟩
          rw [Znth_cons 0 (idx+1) w ws (by omega)] at ht
          simpa only [show idx+1-1 = idx by omega] using ht)
        change 0 ≤ w*p+PickWeight ws ps
        nlinarith [hp.1]

private theorem forall2_split_single {R : Int → Int → Prop} (counts : List Int) (cnt : Int) (picks : List Int)
    (h : List.Forall₂ R picks (counts++[cnt])) :
    ∃ pre take, picks = pre++[take] ∧ List.Forall₂ R pre counts ∧ R take cnt := by
  induction counts generalizing picks with
  | nil =>
    cases h with
    | cons hr ht =>
      cases ht
      exact ⟨[],_,rfl,.nil,hr⟩
  | cons c cs ih =>
    cases h with
    | cons hr ht =>
      obtain ⟨pre,t,he,hpre,hrt⟩ := ih _ ht
      exact ⟨_::pre,t,by simp only [he,List.cons_append],.cons hr hpre,hrt⟩

theorem MKTransitionValue_matches_bounded_pick_extension
    (weights values counts : List Int) (i capacity : Int) (old : List Int) (w v cnt pos ans : Int)
    (hi : 0 ≤ i ∧ i < Zlength weights) (hvlen : Zlength values = Zlength weights)
    (hclen : Zlength counts = Zlength weights) (hw : w = Znth i weights 0)
    (hv : v = Znth i values 0) (hc : cnt = Znth i counts 0)
    (hwpos : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0)
    (hdp : MKDPTable weights values counts i capacity old)
    (ht : MKTransitionValue old w v cnt capacity pos ans) :
    MultipleKnapsackPrefixAnswer weights values counts (i+1) pos ans := by
  obtain ⟨hwp,hcn,hpos,hol,bt,⟨hbset,hbmax⟩,hbval⟩ := ht
  obtain ⟨_,hcap,_,htable⟩ := hdp
  obtain ⟨bp,⟨hpb,hpm⟩,hpv⟩ := htable (pos-bt*w) hbset.2.2
  dsimp only at hpv hbval
  have hpbl : Zlength bp = Zlength (sublist 0 i values) := hpb.2.2.1.trans hpb.1
  have heval : PickValue (sublist 0 i values++[v]) (bp++[bt]) = ans := by
    rw [worker_PickValue_app_single _ _ v bt hpbl,hpv]
    nlinarith
  unfold MultipleKnapsackPrefixAnswer
  rw [worker_sublist_0_succ 0 weights i hi,
    worker_sublist_0_succ 0 values i ⟨hi.1,by omega⟩,
    worker_sublist_0_succ 0 counts i ⟨hi.1,by omega⟩,← hw,← hv,← hc]
  refine ⟨bp++[bt],⟨worker_BoundedPickList_extend _ _ _ bp _ pos w v cnt bt hpb hwp hbset.1 (by ring),?_⟩,heval⟩
  intro picks hpicks
  obtain ⟨hwv,hwc,hplen,hpn,hforall,hweightn,hweightle⟩ := hpicks
  obtain ⟨pre,t,hpick,hpre,htbounds⟩ := forall2_split_single (sublist 0 i counts) cnt picks hforall
  subst picks
  have hwpl := prefix_length weights i ⟨hi.1,by omega⟩
  have hvpl := prefix_length values i ⟨hi.1,by omega⟩
  have hcpl := prefix_length counts i ⟨hi.1,by omega⟩
  have hprelen : Zlength pre = Zlength (sublist 0 i counts) := by
    change (pre.length : Int) = ((sublist 0 i counts).length : Int)
    exact congrArg (fun n : Nat => (n : Int)) hpre.length_eq
  have hprew : Zlength pre = Zlength (sublist 0 i weights) := by omega
  have hprev : Zlength pre = Zlength (sublist 0 i values) := by omega
  rw [worker_PickWeight_app_single _ pre w t hprew] at hweightn hweightle
  have hn := worker_PickWeight_nonneg (sublist 0 i weights) pre (sublist 0 i counts) hprew.symm hpre (by
    intro idx hidx
    have hir : 0 ≤ idx ∧ idx < i := ⟨hidx.1,by omega⟩
    rw [prefix_nth weights 0 i idx hir]
    have hh := hwpos idx ⟨hidx.1,by omega⟩
    omega)
  have hrange : 0 ≤ pos-t*w ∧ pos-t*w ≤ capacity := by constructor <;> nlinarith [htbounds.1]
  have htset : (0 ≤ t ∧ t ≤ cnt) ∧ t*w ≤ pos ∧ (0 ≤ pos-t*w ∧ pos-t*w ≤ capacity) :=
    ⟨htbounds,by nlinarith,hrange⟩
  have htmax := hbmax t htset
  obtain ⟨best,⟨_,hbestmax⟩,hbestval⟩ := htable (pos-t*w) hrange
  have hpreb : BoundedPickList (sublist 0 i weights) (sublist 0 i values) (sublist 0 i counts) (pos-t*w) pre :=
    ⟨by omega,by omega,hprew,hrange.1,hpre,hn,by nlinarith⟩
  have hpremax := hbestmax pre hpreb
  dsimp only at hpremax hbestval htmax
  rw [hbestval] at hpremax
  dsimp only
  rw [worker_PickValue_app_single _ pre v t hprev,heval]
  nlinarith

theorem MKItemResidueProgress_complete_implies_MKDPTable_next_item
    (weights values counts : List Int) (i capacity : Int) (old dp : List Int) (r w v cnt : Int)
    (hi : 0 ≤ i ∧ i < Zlength weights) (hvlen : Zlength values = Zlength weights)
    (hclen : Zlength counts = Zlength weights) (hw : w = Znth i weights 0)
    (hv : v = Znth i values 0) (hc : cnt = Znth i counts 0)
    (hwpos : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0)
    (hrge : r ≥ w) (hdp : MKDPTable weights values counts i capacity old)
    (hprog : MKItemResidueProgress old dp r w v cnt capacity) :
    MKDPTable weights values counts (i+1) capacity dp := by
  obtain ⟨hwp,hcn,hr0,hrw,hrcap,hol,hdl,hdone,hsame⟩ := hprog
  refine ⟨⟨by omega,by omega⟩,hdp.2.1,hdl,?_⟩
  intro cap hcap
  have hmod : 0 ≤ cap % w ∧ cap % w < r :=
    ⟨Int.emod_nonneg _ (by omega),by have := Int.emod_lt_of_pos cap hwp; omega⟩
  have hdiv : 0 ≤ cap / w := Int.ediv_nonneg hcap.1 (le_of_lt hwp)
  have he : cap = cap%w+(cap/w)*w := by have := Int.emod_add_ediv_mul cap w; omega
  exact MKTransitionValue_matches_bounded_pick_extension weights values counts i capacity old w v cnt cap _
    hi hvlen hclen hw hv hc hwpos hdp (hdone (cap%w) (cap/w) cap he hmod hdiv hcap)

theorem MKDPTable_final_capacity_implies_MultipleKnapsackAnswer (weights values counts : List Int)
    (capacity : Int) (dp : List Int) (n : Int) (hw : Zlength weights = n)
    (hv : Zlength values = n) (hc : Zlength counts = n) (hcap : 0 ≤ capacity)
    (hdp : MKDPTable weights values counts n capacity dp) :
    MultipleKnapsackAnswer weights values counts capacity (Znth capacity dp 0) := by
  have h := hdp.2.2.2 capacity ⟨hcap,le_refl _⟩
  unfold MultipleKnapsackPrefixAnswer at h
  rw [sublist_self weights n hw.symm,sublist_self values n hv.symm,sublist_self counts n hc.symm] at h
  exact h

theorem MKQueuePending_layers_push__g08 (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity current : Int)
    (hs : MKQueueDropSafety old q_idx q_val head tail r w k capacity)
    (hm : MKQueuePendingSemantics old q_idx q_val head tail r w v cnt k current)
    (hc : current = Znth (r+k*w) old 0-k*v) (hp : 0 ≤ r+k*w ∧ r+k*w ≤ capacity)
    (hcnt : 0 ≤ cnt) (hkc : k ≤ capacity) (hdom : head < tail → Znth (tail-1) q_val 0 > current) :
    MKQueueResultSafety old (replace_Znth tail k q_idx) (replace_Znth tail current q_val) head (tail+1) r w (k+1) capacity ∧
    MKQueueResultSemantics old (replace_Znth tail k q_idx) (replace_Znth tail current q_val) head (tail+1) r w v cnt (k+1) capacity := by
  have hstate : MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current := by
    dsimp only [MKQueueDropSafety,MKQueueStorageSafety] at hs
    dsimp only [MKQueuePendingSemantics] at hm
    exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2,hm⟩
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hvalid,hinc,hdec,hcover,hbound,htrans⟩ :=
    MKQueuePendingState_push_to_MKQueueState old q_idx q_val head tail r w v cnt k capacity current hstate hc hp hcnt hkc hdom
  exact ⟨⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩,hvalid,hinc,hdec,hcover,hbound,fun hn => (htrans hn).2.2.2.2⟩

private theorem prefix_sem_write (old dp : List Int) (r w v cnt k capacity pos ans : Int)
    (hr : 0 ≤ r) (hw : 0 < w) (he : pos = r+k*w) (hp : 0 ≤ pos ∧ pos ≤ capacity)
    (hl : Zlength dp = capacity+1)
    (hpre : ∀ t, (0 ≤ t ∧ t < k) → r+t*w ≤ capacity → MKTransitionSemantics old w v cnt capacity (r+t*w) (Znth (r+t*w) dp 0))
    (ht : MKTransitionSemantics old w v cnt capacity pos ans) :
    ∀ t, (0 ≤ t ∧ t < k+1) → r+t*w ≤ capacity → MKTransitionSemantics old w v cnt capacity (r+t*w) (Znth (r+t*w) (replace_Znth pos ans dp) 0) := by
  intro t htr hcap
  have hpidx : 0 ≤ pos ∧ pos < Zlength dp := ⟨hp.1,by omega⟩
  by_cases htk : t < k
  · rw [Znth_replace_Znth_Diff 0 dp pos (r+t*w) ans hpidx ⟨by nlinarith [htr.1],by omega⟩ (by nlinarith)]
    exact hpre t ⟨htr.1,htk⟩ hcap
  · have htk : t = k := by omega
    rw [htk,← he,Znth_replace_Znth_Same 0 dp pos ans hpidx]; exact ht

theorem MKResidueLoopSemantics_after_dp_write__g09 (old dp qidx qval : List Int)
    (r w v cnt k head tail capacity pos ans : Int) (hr : 0 ≤ r) (hw : 0 < w)
    (he : pos = r+k*w) (hp : 0 ≤ pos ∧ pos ≤ capacity) (hl : Zlength dp = capacity+1)
    (hpre : MKItemResiduePrefixSemantics old dp r w v cnt k capacity)
    (hq : MKQueueResultSemantics old qidx qval head tail r w v cnt (k+1) capacity)
    (ht : MKTransitionSemantics old w v cnt capacity pos ans) :
    MKResidueLoopSemantics old (replace_Znth pos ans dp) qidx qval r w v cnt (k+1) head tail capacity :=
  ⟨prefix_sem_write old dp r w v cnt k capacity pos ans hr hw he hp hl hpre.1 ht,hq⟩

theorem MKResidueLoopSafety_after_dp_write__g09 (old dp qidx qval : List Int)
    (r w k head tail capacity pos ans : Int) (hl : Zlength dp = capacity+1)
    (hq : MKQueueResultSafety old qidx qval head tail r w (k+1) capacity) :
    MKResidueLoopSafety old (replace_Znth pos ans dp) qidx qval r w (k+1) head tail capacity := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩ := hq
  exact ⟨hr,hk,hh,ht,ho,by rw [Zlength_replace_Znth]; exact hl,hqi,hqv⟩

theorem MKItemResiduePrefixSemantics_after_dp_write__g09 (old dp : List Int)
    (r w v cnt k capacity pos ans : Int) (hw : 0 < w) (hr : 0 ≤ r) (hrw : r < w)
    (he : pos = r+k*w) (hp : 0 ≤ pos ∧ pos ≤ capacity) (hl : Zlength dp = capacity+1)
    (hpre : MKItemResiduePrefixSemantics old dp r w v cnt k capacity)
    (ht : MKTransitionSemantics old w v cnt capacity pos ans) :
    MKItemResiduePrefixSemantics old (replace_Znth pos ans dp) r w v cnt (k+1) capacity := by
  refine ⟨prefix_sem_write old dp r w v cnt k capacity pos ans hr hw he hp hl hpre.1 ht,?_⟩
  have hpidx : 0 ≤ pos ∧ pos < Zlength dp := ⟨hp.1,by omega⟩
  intro p hpr
  obtain ⟨hdone,hsame⟩ := hpre.2 p hpr
  refine ⟨?_,?_⟩
  · intro rem t hrep hrem ht0
    have hne : pos ≠ p := by
      intro heq
      have hre := residue_repr_unique rem r t k w hw ⟨hrem.1,by omega⟩ ⟨hr,hrw⟩ (by omega)
      omega
    rw [Znth_replace_Znth_Diff 0 dp pos p ans hpidx ⟨hpr.1,by omega⟩ hne]
    exact hdone rem t hrep hrem ht0
  · intro rem t hrep hrem ht0 hcase
    have hne : pos ≠ p := by
      intro heq
      have hre := residue_repr_unique rem r t k w hw hrem ⟨hr,hrw⟩ (by omega)
      rcases hcase with hlater | ⟨hrr,htt⟩
      · omega
      · nlinarith
    rw [Znth_replace_Znth_Diff 0 dp pos p ans hpidx ⟨hpr.1,by omega⟩ hne]
    exact hsame rem t hrep hrem ht0 (by omega)

theorem MKItemResiduePrefixSafety_after_dp_write__g09 (old dp : List Int)
    (r w cnt k capacity pos ans : Int) (hl : Zlength dp = capacity+1)
    (hs : MKItemResiduePrefixSafety old dp r w cnt k capacity) :
    MKItemResiduePrefixSafety old (replace_Znth pos ans dp) r w cnt (k+1) capacity := by
  obtain ⟨hw,hcnt,hr,hk,hrc,ho,hd⟩ := hs
  exact ⟨hw,hcnt,hr,by omega,hrc,ho,by rw [Zlength_replace_Znth]; exact hl⟩

theorem MKItemResidueProgressSemantics_next_residue__g09 (old dp : List Int)
    (r w v cnt k capacity pos : Int) (hw : 0 < w) (hr : 0 ≤ r)
    (he : pos = r+k*w) (hp : pos > capacity)
    (hpre : MKItemResiduePrefixSemantics old dp r w v cnt k capacity) :
    MKItemResidueProgressSemantics old dp (r+1) w v cnt capacity := by
  refine ⟨?_,?_⟩
  · intro rem t p hrep hrem ht hpr
    by_cases hrlt : rem < r
    · exact (hpre.2 p hpr).1 rem t hrep ⟨hrem.1,hrlt⟩ ht
    · have hre : rem = r := by omega
      have htk : t < k := by nlinarith
      rw [hrep,hre]
      exact hpre.1 t ⟨ht,htk⟩ (by rw [← hre,← hrep]; exact hpr.2)
  · intro rem t p hrep hrem ht hpr
    exact (hpre.2 p hpr).2 rem t hrep ⟨by omega,hrem.2⟩ ht (Or.inl (by omega))

theorem MKItemResidueProgressSafety_next_residue__g09 (old dp : List Int)
    (r w cnt k capacity pos : Int) (hp : pos > capacity)
    (hs : MKItemResiduePrefixSafety old dp r w cnt k capacity) :
    MKItemResidueProgressSafety old dp (r+1) w cnt capacity := by
  obtain ⟨hw,hcnt,hr,hk,hrc,ho,hd⟩ := hs
  exact ⟨hw,hcnt,by omega,by omega,by omega,ho,hd⟩

theorem MKDPTable_from_safety_semantics__g10 (weights values counts : List Int) (i capacity : Int) (dp : List Int)
    (hs : MKDPTableSafety weights i capacity dp) (hm : MKDPTableSemantics weights values counts i capacity dp) :
    MKDPTable weights values counts i capacity dp := ⟨hs.1,hs.2.1,hs.2.2,hm⟩

theorem MKItemResidueProgress_from_safety_semantics__g10 (old dp : List Int) (r w v cnt capacity : Int)
    (hs : MKItemResidueProgressSafety old dp r w cnt capacity)
    (hm : MKItemResidueProgressSemantics old dp r w v cnt capacity) :
    MKItemResidueProgress old dp r w v cnt capacity := by
  obtain ⟨hw,hcnt,hr,hrw,hrc,ho,hd⟩ := hs
  exact ⟨hw,hcnt,hr,hrw,hrc,ho,hd,
    fun rem k pos he hrem hk hp => ⟨hw,hcnt,hp,ho,hm.1 rem k pos he hrem hk hp⟩,hm.2⟩

theorem MKQueuePending_push_complete_outcome__g06 (old q_idx q_val : List Int)
    (head tail r w v cnt k capacity current pos : Int) (he : pos = r+k*w)
    (hs : MKQueueDropSafety old q_idx q_val head tail r w k capacity)
    (hm : MKQueuePendingSemantics old q_idx q_val head tail r w v cnt k current)
    (hc : current = Znth pos old 0-k*v) (hp : 0 ≤ pos ∧ pos ≤ capacity)
    (hcnt : 0 ≤ cnt) (hkc : k ≤ capacity) (hdom : head < tail → Znth (tail-1) q_val 0 > current) :
    MKQueueResultSafety old (replace_Znth tail k q_idx) (replace_Znth tail current q_val) head (tail+1) r w (k+1) capacity ∧
    MKQueueResultSemantics old (replace_Znth tail k q_idx) (replace_Znth tail current q_val) head (tail+1) r w v cnt (k+1) capacity ∧
    (0 ≤ Znth head (replace_Znth tail current q_val) 0+k*v ∧ Znth head (replace_Znth tail current q_val) 0+k*v ≤ 1000000) ∧
    MKTransitionSafety old w cnt capacity pos ∧
    MKTransitionSemantics old w v cnt capacity pos (Znth head (replace_Znth tail current q_val) 0+k*v) := by
  obtain ⟨hrs,hrm⟩ := MKQueuePending_layers_push__g08 old q_idx q_val head tail r w v cnt k capacity current hs hm
    (by rw [← he]; exact hc) (by rw [← he]; exact hp) hcnt hkc hdom
  have hn : head < tail+1 := by have := hs.2.2.1.2; omega
  have hb := hrm.2.2.2.2.1 head ⟨le_refl _,hn⟩
  have ht := hrm.2.2.2.2.2 hn
  simp only [show k+1-1 = k by omega] at hb ht
  rw [← he] at ht
  exact ⟨hrs,hrm,hb,⟨by have := hs.1; omega,hcnt,hp,hs.2.2.2.2.2.2.2⟩,ht⟩

theorem MKItemResidue_complete_table__g09 (weights values counts : List Int) (i capacity : Int)
    (old dp : List Int) (r w v cnt : Int) (hi : 0 ≤ i ∧ i < Zlength weights)
    (hvlen : Zlength values = Zlength weights) (hclen : Zlength counts = Zlength weights)
    (hw : w = Znth i weights 0) (hv : v = Znth i values 0) (hc : cnt = Znth i counts 0)
    (hwpos : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights) → 1 ≤ Znth idx weights 0) (hrge : r ≥ w)
    (hts : MKDPTableSafety weights i capacity old) (htm : MKDPTableSemantics weights values counts i capacity old)
    (hps : MKItemResidueProgressSafety old dp r w cnt capacity) (hpm : MKItemResidueProgressSemantics old dp r w v cnt capacity) :
    MKDPTableSafety weights (i+1) capacity dp ∧ MKDPTableSemantics weights values counts (i+1) capacity dp := by
  have h := MKItemResidueProgress_complete_implies_MKDPTable_next_item weights values counts i capacity old dp r w v cnt
    hi hvlen hclen hw hv hc hwpos hrge
    (MKDPTable_from_safety_semantics__g10 weights values counts i capacity old hts htm)
    (MKItemResidueProgress_from_safety_semantics__g10 old dp r w v cnt capacity hps hpm)
  exact ⟨⟨h.1,h.2.1,h.2.2.1⟩,h.2.2.2⟩

end SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib
