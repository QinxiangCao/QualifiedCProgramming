import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
namespace SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib
open AUXLib

def SWMInputSafe (l : List Int) (n k : Int) : Prop :=
  1 ≤ k ∧ k ≤ n ∧ n ≤ 100000 ∧ Zlength l = n ∧
  ∀ idx, (0 ≤ idx ∧ idx < n) → -10000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 10000

def SWMOutputPrefixShape (l : List Int) (k out_idx : Int) (out : List Int) : Prop :=
  1 ≤ k ∧ k ≤ Zlength l ∧ (0 ≤ out_idx ∧ out_idx ≤ Zlength l-k+1) ∧ Zlength out = out_idx

def SWMQueueStorageSafe (l q_l : List Int) (head tail processed : Int) : Prop :=
  Zlength q_l = Zlength l ∧ (0 ≤ processed ∧ processed ≤ Zlength l) ∧
  (0 ≤ head ∧ head ≤ tail) ∧ tail ≤ processed ∧
  ∀ pos, (head ≤ pos ∧ pos < tail) → 0 ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < Zlength l

def WindowMaxValue (l : List Int) (lo hi ans : Int) : Prop :=
  ∃ pos, (lo ≤ pos ∧ pos < hi) ∧ ans = Znth pos l 0 ∧
    ∀ idx, (lo ≤ idx ∧ idx < hi) → Znth idx l 0 ≤ ans

def SlidingWindowMaximum (l : List Int) (k : Int) (out : List Int) : Prop :=
  Zlength out = Zlength l-k+1 ∧
    ∀ idx, (0 ≤ idx ∧ idx < Zlength out) → WindowMaxValue l idx (idx+k) (Znth idx out 0)

def SWMOutputPrefix (l : List Int) (k out_idx : Int) (out : List Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < out_idx) → WindowMaxValue l idx (idx+k) (Znth idx out 0)

def SWMQueueEntriesInWindow (q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ pos, (head ≤ pos ∧ pos < tail) → lo ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < hi

def SWMQueueEntriesInOpenWindow (q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ pos, (head ≤ pos ∧ pos < tail) → lo < Znth pos q_l 0 ∧ Znth pos q_l 0 < hi

def SWMQueueIndexIncreasing (q_l : List Int) (head tail : Int) : Prop :=
  ∀ p q, (head ≤ p ∧ p < q ∧ q < tail) → Znth p q_l 0 < Znth q q_l 0

def SWMQueueValueDecreasing (l q_l : List Int) (head tail : Int) : Prop :=
  ∀ p q, (head ≤ p ∧ p < q ∧ q < tail) → Znth (Znth p q_l 0) l 0 > Znth (Znth q q_l 0) l 0

def SWMQueueCoversWindow (l q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < Zlength l) → (lo ≤ idx ∧ idx < hi) →
    ∃ pos, (head ≤ pos ∧ pos < tail) ∧ (idx ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < hi) ∧
      Znth idx l 0 ≤ Znth (Znth pos q_l 0) l 0

def SWMQueueCoversOpenWindow (l q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < Zlength l) → (lo < idx ∧ idx < hi) →
    ∃ pos, (head ≤ pos ∧ pos < tail) ∧ (idx ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < hi) ∧
      Znth idx l 0 ≤ Znth (Znth pos q_l 0) l 0

def SWMQueueCoversWithPending (l q_l : List Int) (head tail lo i : Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < Zlength l) → (lo < idx ∧ idx < i) →
    (∃ pos, (head ≤ pos ∧ pos < tail) ∧ (idx ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < i) ∧
      Znth idx l 0 ≤ Znth (Znth pos q_l 0) l 0) ∨ Znth idx l 0 ≤ Znth i l 0

def SWMQueueDropLoopState (l q_l : List Int) (head tail i k : Int) : Prop :=
  SWMQueueEntriesInWindow q_l head tail (i-k) i ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversOpenWindow l q_l head tail (i-k) i

def SWMQueueAfterDrop (l q_l : List Int) (head tail i k : Int) : Prop :=
  SWMQueueEntriesInOpenWindow q_l head tail (i-k) i ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversOpenWindow l q_l head tail (i-k) i

def SWMQueuePendingState (l q_l : List Int) (head tail i k : Int) : Prop :=
  SWMQueueEntriesInOpenWindow q_l head tail (i-k) i ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversWithPending l q_l head tail (i-k) i

def SWMQueueState (l q_l : List Int) (head tail processed k : Int) : Prop :=
  SWMQueueEntriesInWindow q_l head tail (processed-k) processed ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversWindow l q_l head tail (processed-k) processed ∧
  ((head < tail ∧ k ≤ processed) → WindowMaxValue l (processed-k) processed (Znth (Znth head q_l 0) l 0))

theorem replace_Znth_append_bounds__value_loop_exit_and_append
    (q_l : List Int) (head tail i n : Int) (hlen : Zlength q_l = n)
    (hht : 0 ≤ head ∧ head ≤ tail) (hit : tail ≤ i ∧ i < n)
    (hold : ∀ pos, (head ≤ pos ∧ pos < tail) → 0 ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < n)
    (pos : Int) (hpos : head ≤ pos ∧ pos < tail+1) :
    0 ≤ Znth pos (replace_Znth tail i q_l) 0 ∧ Znth pos (replace_Znth tail i q_l) 0 < n := by
  by_cases heq : pos = tail
  · subst pos
    rw [Znth_replace_Znth_Same 0 q_l tail i (by omega)]
    omega
  · rw [Znth_replace_Znth_Diff 0 q_l tail pos i (by omega) (by omega) (by omega)]
    exact hold pos (by omega)

theorem queue_append_state__value_loop_exit_and_append
    (l q_l : List Int) (head tail i k : Int) (hlen : Zlength l = Zlength q_l)
    (hk : 1 ≤ k) (hi : 0 ≤ i ∧ i < Zlength l) (hht : 0 ≤ head ∧ head ≤ tail) (hti : tail ≤ i)
    (hstate : SWMQueuePendingState l q_l head tail i k)
    (hlast : head < tail → Znth (Znth (tail-1) q_l 0) l 0 > Znth i l 0) :
    SWMQueueState l (replace_Znth tail i q_l) head (tail+1) (i+1) k := by
  rcases hstate with ⟨he, hinc, hdec, hcov⟩
  have hs := Znth_replace_Znth_Same 0 q_l tail i (by omega)
  have hd (p : Int) (hp : head ≤ p ∧ p < tail) :
      Znth p (replace_Znth tail i q_l) 0 = Znth p q_l 0 :=
    Znth_replace_Znth_Diff 0 q_l tail p i (by omega) (by omega) (by omega)
  have hnewEntries : SWMQueueEntriesInWindow (replace_Znth tail i q_l) head (tail+1) (i+1-k) (i+1) := by
    intro p hp
    by_cases hpt : p = tail
    · subst p; rw [hs] <;> omega
    · rw [hd p (by omega)]
      have := he p (by omega)
      omega
  have hnewDec : SWMQueueValueDecreasing l (replace_Znth tail i q_l) head (tail+1) := by
    intro p q hpq
    by_cases hqt : q = tail
    · subst q
      rw [hs, hd p (by omega)]
      by_cases hpt : p = tail-1
      · subst p; exact hlast (by omega)
      · have := hdec p (tail-1) (by omega)
        have := hlast (by omega)
        omega
    · rw [hd p (by omega), hd q (by omega)]
      exact hdec p q (by omega)
  have hnewCov : SWMQueueCoversWindow l (replace_Znth tail i q_l) head (tail+1) (i+1-k) (i+1) := by
    intro idx hidx hwin
    by_cases heq : idx = i
    · subst idx
      exact ⟨tail, by omega, by rw [hs] <;> omega, by rw [hs] <;> omega⟩
    · rcases hcov idx hidx (by omega) with ⟨p, hp, hip, hv⟩ | hv
      · exact ⟨p, by omega, by rw [hd p hp] <;> omega, by rw [hd p hp]; exact hv⟩
      · exact ⟨tail, by omega, by rw [hs] <;> omega, by rw [hs]; exact hv⟩
  refine ⟨hnewEntries, ?_, hnewDec, hnewCov, ?_⟩
  · intro p q hpq
    by_cases hqt : q = tail
    · subst q
      rw [hs, hd p (by omega)]
      exact (he p (by omega)).2
    · rw [hd p (by omega), hd q (by omega)]
      exact hinc p q (by omega)
  · intro hnonempty
    refine ⟨Znth head (replace_Znth tail i q_l) 0, hnewEntries head (by omega), rfl, ?_⟩
    intro idx hidx
    rcases hnewCov idx (by omega) hidx with ⟨p, hp, hip, hv⟩
    by_cases heq : p = head
    · subst p; exact hv
    · have := hnewDec head p (by omega)
      omega

theorem queue_append_storage__value_loop_exit_and_append
    (l q_l : List Int) (head tail i : Int) (hlen : Zlength q_l = Zlength l)
    (hi : 0 ≤ i ∧ i < Zlength l) (hht : 0 ≤ head ∧ head ≤ tail) (hti : tail ≤ i)
    (hb : ∀ pos, (head ≤ pos ∧ pos < tail) → 0 ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < Zlength l) :
    SWMQueueStorageSafe l (replace_Znth tail i q_l) head (tail+1) (i+1) := by
  refine ⟨?_, by omega, by omega, by omega, ?_⟩
  · rw [Zlength_replace_Znth]; exact hlen
  · exact replace_Znth_append_bounds__value_loop_exit_and_append q_l head tail i (Zlength l) hlen hht (by omega) hb

private theorem getD_append_left (l1 l2 : List Int) (d : Int) (n : Nat) (hn : n < l1.length) :
    (l1 ++ l2).getD n d = l1.getD n d := by
  induction l1 generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n (by simpa using hn)

theorem Znth_app_left__window_output_append (l1 l2 : List Int) (d i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1++l2) d = Znth i l1 d := by
  unfold Znth
  exact getD_append_left l1 l2 d i.toNat (by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega)

theorem Znth_app_last__window_output_append (l : List Int) (d x : Int) :
    Znth (Zlength l) (l++[x]) d = x := by
  rw [app_Znth2 d l [x] (Zlength l) (by omega)]
  simp [Znth]

theorem SWMOutputPrefix_app_single__window_output_append
    (l : List Int) (k out_idx : Int) (out : List Int) (value : Int)
    (hshape : SWMOutputPrefixShape l k out_idx out) (hp : SWMOutputPrefix l k out_idx out)
    (hv : WindowMaxValue l out_idx (out_idx+k) value) :
    SWMOutputPrefix l k (out_idx+1) (out++[value]) := by
  intro idx hi
  by_cases hlt : idx < out_idx
  · rw [Znth_app_left__window_output_append out [value] 0 idx (by have := hshape.2.2.2; omega)]
    exact hp idx (by omega)
  · have heq : idx = out_idx := by omega
    subst idx
    have hz : Znth out_idx (out++[value]) 0 = value := by
      rw [← hshape.2.2.2]; exact Znth_app_last__window_output_append out 0 value
    rw [hz]; exact hv

theorem SWMOutputPrefixShape_app_single__window_output_append
    (l : List Int) (k out_idx : Int) (out : List Int) (value : Int)
    (hshape : SWMOutputPrefixShape l k out_idx out) (hr : out_idx < Zlength l-k+1) :
    SWMOutputPrefixShape l k (out_idx+1) (out++[value]) := by
  rcases hshape with ⟨hk, hkl, hi, hlen⟩
  refine ⟨hk, hkl, by omega, ?_⟩
  simpa [Zlength, List.length_append, Int.natCast_add] using congrArg (fun x : Int => x+1) hlen

theorem drop_loop_remove_expired_head__head_drop_transitions
    (l q_l : List Int) (head tail i k : Int) (hn : head < tail) (hex : Znth head q_l 0 ≤ i-k)
    (hstate : SWMQueueDropLoopState l q_l head tail i k) :
    SWMQueueDropLoopState l q_l (head+1) tail i k := by
  rcases hstate with ⟨he, hi, hv, hc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pos hp; exact he pos (by omega)
  · intro p q hpq; exact hi p q (by omega)
  · intro p q hpq; exact hv p q (by omega)
  · intro idx hidx hw
    rcases hc idx hidx hw with ⟨p, hp, hip, hval⟩
    by_cases heq : p = head
    · subst p; omega
    · exact ⟨p, by omega, hip, hval⟩

theorem drop_loop_exit_nonexpired__head_drop_transitions
    (l q_l : List Int) (head tail i k : Int) (hn : head < tail) (hh : i-k < Znth head q_l 0)
    (hstate : SWMQueueDropLoopState l q_l head tail i k) :
    SWMQueueAfterDrop l q_l head tail i k := by
  rcases hstate with ⟨he, hi, hv, hc⟩
  refine ⟨?_, hi, hv, hc⟩
  intro pos hp
  have hep := he pos hp
  by_cases heq : pos = head
  · subst pos; omega
  · have := hi head pos (by omega)
    omega

theorem SWMQueuePendingState_drop_tail__pending_and_tail_drop
    (l q_l : List Int) (head tail i k : Int) (hn : head < tail)
    (hd : Znth (Znth (tail-1) q_l 0) l 0 ≤ Znth i l 0)
    (hstate : SWMQueuePendingState l q_l head tail i k) :
    SWMQueuePendingState l q_l head (tail-1) i k := by
  rcases hstate with ⟨he, hi, hv, hc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pos hp; exact he pos (by omega)
  · intro p q hpq; exact hi p q (by omega)
  · intro p q hpq; exact hv p q (by omega)
  · intro idx hidx hw
    rcases hc idx hidx hw with ⟨p, hp, hip, hval⟩ | hpend
    · by_cases hlt : p < tail-1
      · exact Or.inl ⟨p, by omega, hip, hval⟩
      · have heq : p = tail-1 := by omega
        subst p
        exact Or.inr (by omega)
    · exact Or.inr hpend

end SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib
namespace SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum
export sliding_window_maximum_lib (SWMInputSafe SWMOutputPrefixShape SWMQueueStorageSafe WindowMaxValue
  SlidingWindowMaximum SWMOutputPrefix SWMQueueEntriesInWindow SWMQueueEntriesInOpenWindow
  SWMQueueIndexIncreasing SWMQueueValueDecreasing SWMQueueCoversWindow SWMQueueCoversOpenWindow
  SWMQueueCoversWithPending SWMQueueDropLoopState SWMQueueAfterDrop SWMQueuePendingState SWMQueueState)
end SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum
