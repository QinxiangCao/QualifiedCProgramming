import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib
open AUXLib


abbrev Some {A : Type} (x : A) : Option A := .some x
abbrev None {A : Type} : Option A := .none
abbrev _Prod_Z_Z := Int × Int
abbrev fst {A B : Type} (p : A × B) : A := p.1
abbrev snd {A B : Type} (p : A × B) : B := p.2

def CrossSwap (st st' : List Int × List Int) (op : Int × Int) : Prop :=
  let (s,t) := st
  let (s',t') := st'
  let (i,j) := op
  (0 ≤ i ∧ i < Zlength s) ∧ (0 ≤ j ∧ j < Zlength t) ∧
    s' = replace_Znth i (Znth j t 0) s ∧ t' = replace_Znth j (Znth i s 0) t

def SwapsWork (s t : List Int) (ops : List (Int × Int)) : Prop :=
  (1 ≤ Zlength ops ∧ Zlength ops ≤ 2 * Zlength s) ∧ ∃ st : List (List Int × List Int),
    Zlength st = Zlength ops + 1 ∧ Znth 0 st ([],[]) = (s,t) ∧
    (∀ q, (0 ≤ q ∧ q < Zlength ops) → CrossSwap (Znth q st ([],[])) (Znth (q+1) st ([],[])) (Znth q ops (0,0))) ∧
    (Znth (Zlength ops) st ([],[])).1 = (Znth (Zlength ops) st ([],[])).2

def Pre (s t : List Int) : Prop := s ≠ t

def Spec (s t : List Int) (out : Option (List (Int × Int))) : Prop :=
  (out = none ∧ ¬ ∃ ops, SwapsWork s t ops) ∨ (∃ ops, out = some ops ∧ SwapsWork s t ops)

def CountedPrefix (s t : List Int) (i : Int) (counts : List Int) : Prop :=
  Zlength counts = 26 ∧ ∀ c, (0 ≤ c ∧ c < 26) →
    Znth c counts 0 = ((sublist 0 i s ++ sublist 0 i t).count (97+c) : Int)

def CountsEvenBefore (counts : List Int) (bound : Int) : Prop :=
  ∀ c, (0 ≤ c ∧ c < bound) → Z.modulo (Znth c counts 0) 2 = 0

def CombinedEven (s t : List Int) : Prop :=
  ∀ c, (0 ≤ c ∧ c < 26) → Z.modulo ((s ++ t).count (97+c)) 2 = 0

def CombinedOddAt (s t : List Int) (c : Int) : Prop :=
  (0 ≤ c ∧ c < 26) ∧ Z.modulo ((s ++ t).count (97+c)) 2 = 1

def SwapTrace (s0 t0 s t : List Int) (ops : List (Int × Int)) : Prop :=
  ∃ states : List (List Int × List Int), Zlength states = Zlength ops + 1 ∧ Znth 0 states ([],[]) = (s0,t0) ∧
    (∀ q, (0 ≤ q ∧ q < Zlength ops) → CrossSwap (Znth q states ([],[])) (Znth (q+1) states ([],[])) (Znth q ops (0,0))) ∧
    Znth (Zlength ops) states ([],[]) = (s,t)

def PrefixEqual (s t : List Int) (i : Int) : Prop :=
  ∀ k, (0 ≤ k ∧ k < i) → Znth k s 0 = Znth k t 0

def NoValueInRange (l : List Int) (value lo hi : Int) : Prop :=
  ∀ k, (lo ≤ k ∧ k < hi) → Znth k l 0 ≠ value

def OperationLists (ops : List (Int × Int)) (is js : List Int) : Prop :=
  Zlength is = Zlength ops ∧ Zlength js = Zlength ops ∧
    (∀ q, (0 ≤ q ∧ q < Zlength ops) → Znth q is 0 = (Znth q ops (0,0)).1 + 1 ∧ Znth q js 0 = (Znth q ops (0,0)).2 + 1)

def RepairState (source target s t : List Int) (i : Int) (ops : List (Int × Int)) : Prop :=
  Zlength s = Zlength source ∧ Zlength t = Zlength target ∧ PrefixEqual s t i ∧
    List.Perm (source ++ target) (s ++ t) ∧ CombinedEven s t ∧ SwapTrace source target s t ops ∧
    (0 ≤ Zlength ops ∧ Zlength ops ≤ 2 * i)

theorem zlength_replace_znth__count_invariants {A : Type} (l : List A) (n : Int) (v : A) : Zlength (replace_Znth n v l)=Zlength l := AUXLib.Zlength_replace_Znth l n v

theorem Zlength_replace_Znth__repair_transitions {A : Type} (l : List A) (n : Int) (v : A) : Zlength (replace_Znth n v l)=Zlength l := AUXLib.Zlength_replace_Znth l n v

private theorem replace_eq_set {A : Type} (l : List A) (n : Nat) (v : A) : replace_nth n l v=l.set n v := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a l ih => cases n <;> simp only [replace_nth,List.set_cons_zero,List.set_cons_succ,ih]

theorem replace_Znth_decomp__repair_transitions {A : Type} (i : Int) (l : List A) (v : A) (hi : 0≤i ∧ i<Zlength l) :
    replace_Znth i v l=l.take i.toNat++v::l.drop (i.toNat+1) := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  rw [replace_Znth,replace_eq_set,List.set_eq_take_append_cons_drop,if_pos hn]

private theorem list_decomp {A : Type} (d : A) (l : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) :
    l=l.take i.toNat++Znth i l d::l.drop (i.toNat+1) := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  rw [List.getElem_cons_drop_succ_eq_drop,List.take_append_drop]

theorem replace_Znth_decompose__final_results (l : List Int) (i v d : Int) (hi : 0≤i ∧ i<Zlength l) :
    ∃ pre suf, l=pre++Znth i l d::suf ∧ replace_Znth i v l=pre++v::suf :=
  ⟨l.take i.toNat,l.drop (i.toNat+1),list_decomp d l i hi,replace_Znth_decomp__repair_transitions i l v hi⟩

private theorem replace_count_balance (l : List Int) (i v x : Int) (hi : 0≤i ∧ i<Zlength l) :
    (replace_Znth i v l).count x+(if Znth i l 0=x then 1 else 0)=l.count x+(if v=x then 1 else 0) := by
  rcases replace_Znth_decompose__final_results l i v 0 hi with ⟨pre,suf,hl,hr⟩
  rw [hr]
  conv_rhs => rw [hl]
  simp only [List.count_append,List.count_cons,beq_iff_eq]
  split <;> split <;> omega

theorem cross_swap_combined_permutation__repair_transitions (s t : List Int) (a b : Int)
    (ha : 0≤a ∧ a<Zlength s) (hb : 0≤b ∧ b<Zlength t) :
    List.Perm (s++t) (replace_Znth a (Znth b t 0) s++replace_Znth b (Znth a s 0) t) := by
  apply List.perm_iff_count.mpr
  intro x
  have h1 := replace_count_balance s a (Znth b t 0) x ha
  have h2 := replace_count_balance t b (Znth a s 0) x hb
  simp only [List.count_append]
  omega

theorem combined_even_permutation__repair_transitions (s t s' t' : List Int) (h : CombinedEven s t)
    (hp : List.Perm (s++t) (s'++t')) : CombinedEven s' t' := by
  intro c hc
  rw [←hp.count_eq (97+c)]
  exact h c hc

theorem cross_swap_preserves_count__final_results (st st' : List Int×List Int) (op : Int×Int) (x : Int) (h : CrossSwap st st' op) :
    (st.1++st.2).count x=(st'.1++st'.2).count x := by
  rcases st with ⟨s,t⟩
  rcases st' with ⟨s',t'⟩
  rcases op with ⟨a,b⟩
  rcases h with ⟨ha,hb,rfl,rfl⟩
  exact (cross_swap_combined_permutation__repair_transitions s t a b ha hb).count_eq x

private theorem zlength_snoc {A : Type} (l : List A) (a : A) : Zlength (l++[a])=Zlength l+1 := by
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

private theorem znth_app_left {A : Type} (d : A) (l l' : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) : Znth i (l++l') d=Znth i l d := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

private theorem znth_snoc {A : Type} (d : A) (l : List A) (a : A) : Znth (Zlength l) (l++[a]) d=a := by
  rw [app_Znth2 d l [a] (Zlength l) (le_refl _),sub_self]
  rfl

theorem repair_state_initial__repair_control (source target : List Int) (he : CombinedEven source target) : RepairState source target source target 0 [] := by
  refine ⟨rfl,rfl,by intro k hk; omega,List.Perm.refl _,he,?_,by simp only [Zlength_nil]; omega⟩
  exact ⟨[(source,target)],rfl,rfl,by intro q hq; simp only [Zlength_nil] at hq; omega,rfl⟩

theorem no_value_range_empty__repair_control (l : List Int) (value lo : Int) : NoValueInRange l value lo lo := by intro k hk; omega

theorem no_value_range_extend__repair_control (l : List Int) (value lo hi : Int) (h : NoValueInRange l value lo hi)
    (hv : Znth hi l 0≠value) : NoValueInRange l value lo (hi+1) := by
  intro k hk
  by_cases he : k=hi
  · rw [he]; exact hv
  · exact h k (by omega)

theorem operation_lists_empty__repair_control : OperationLists [] [] [] := ⟨rfl,rfl,by intro q hq; simp only [Zlength_nil] at hq; omega⟩

theorem repair_state_advance_equal__repair_transitions (source target s t : List Int) (i : Int) (ops : List (Int×Int))
    (h : RepairState source target s t i ops) (hi : 0≤i ∧ i<Zlength s) (he : Znth i s 0=Znth i t 0) :
    RepairState source target s t (i+1) ops := by
  rcases h with ⟨hs,ht,hp,hperm,heven,htrace,hops⟩
  refine ⟨hs,ht,?_,hperm,heven,htrace,by omega⟩
  intro k hk
  by_cases hki : k=i
  · rw [hki]; exact he
  · exact hp k (by omega)

theorem replace_znth_preserves_char_bounds__repair_transitions (xs : List Int) (i v k : Int)
    (hl : Zlength xs=k) (hi : 0≤i ∧ i<k) (hv : 97≤v ∧ v≤122)
    (hb : ∀ q, (0≤q ∧ q<k) → 97≤Znth q xs 0 ∧ Znth q xs 0≤122) :
    ∀ q, (0≤q ∧ q<k) → 97≤Znth q (replace_Znth i v xs) 0 ∧ Znth q (replace_Znth i v xs) 0≤122 := by
  intro q hq
  by_cases he : i=q
  · subst q
    rw [Znth_replace_Znth_Same 0 xs i v (by omega)]
    exact hv
  · rw [Znth_replace_Znth_Diff 0 xs i q v (by omega) (by omega) he]
    exact hb q hq

theorem swap_trace_append__repair_transitions (source target s t : List Int) (ops : List (Int×Int)) (s' t' : List Int) (op : Int×Int)
    (h : SwapTrace source target s t ops) (hstep : CrossSwap (s,t) (s',t') op) : SwapTrace source target s' t' (ops++[op]) := by
  rcases h with ⟨states,hl,h0,hsteps,hfinal⟩
  have ho := Zlength_nonneg ops
  refine ⟨states++[(s',t')],?_,?_,?_,?_⟩
  · rw [zlength_snoc,zlength_snoc,hl]
  · rw [znth_app_left ([],[]) states _ 0 (by omega)]
    exact h0
  · intro q hq
    rw [zlength_snoc] at hq
    by_cases hqo : q<Zlength ops
    · rw [znth_app_left ([],[]) states _ q (by omega),znth_app_left ([],[]) states _ (q+1) (by omega),znth_app_left (0,0) ops _ q ⟨hq.1,hqo⟩]
      exact hsteps q ⟨hq.1,hqo⟩
    · have hqe : q=Zlength ops := by omega
      subst q
      rw [znth_app_left ([],[]) states _ (Zlength ops) (by omega),hfinal,znth_snoc,←hl,znth_snoc]
      exact hstep
  · rw [zlength_snoc,←hl,znth_snoc]

theorem operation_lists_append__repair_transitions (ops : List (Int×Int)) (is js : List Int) (a b : Int)
    (h : OperationLists ops is js) : OperationLists (ops++[(a,b)]) (is++[a+1]) (js++[b+1]) := by
  rcases h with ⟨hi,hj,hpoint⟩
  refine ⟨by rw [zlength_snoc,zlength_snoc,hi],by rw [zlength_snoc,zlength_snoc,hj],?_⟩
  intro q hq
  rw [zlength_snoc] at hq
  by_cases hqo : q<Zlength ops
  · rw [znth_app_left 0 is _ q (by omega),znth_app_left 0 js _ q (by omega),znth_app_left (0,0) ops _ q ⟨hq.1,hqo⟩]
    exact hpoint q ⟨hq.1,hqo⟩
  · have hqe : q=Zlength ops := by omega
    subst q
    rw [znth_snoc,←hi,znth_snoc,hi,←hj,znth_snoc]
    exact ⟨rfl,rfl⟩

theorem counted_prefix_counter_bound__count_invariants (s t counts : List Int) (i c : Int)
    (hi : 0≤i) (his : i≤Zlength s) (hit : i≤Zlength t) (hc : 0≤c ∧ c<26) (h : CountedPrefix s t i counts) :
    0≤Znth c counts 0 ∧ Znth c counts 0≤2*i := by
  rw [h.2 c hc]
  have hb := List.count_le_length (a:=97+c) (l:=sublist 0 i s++sublist 0 i t)
  have hs := sublist_length 0 i s ⟨by omega,hi⟩ his
  have ht := sublist_length 0 i t ⟨by omega,hi⟩ hit
  simp only [List.length_append] at hb
  rw [hs,ht] at hb
  simp only [sub_zero] at hb
  omega

theorem counted_prefix_full_count__parity_scan (source target : List Int) (n : Int) (counts : List Int) (c : Int)
    (hs : n=Zlength source) (ht : Zlength target=n) (h : CountedPrefix source target n counts) (hc : 0≤c ∧ c<26) :
    Znth c counts 0=((source++target).count (97+c):Int) := by
  have hh := h.2 c hc
  rw [sublist_self source n hs,sublist_self target n ht.symm] at hh
  exact hh

theorem counts_even_before_succ__parity_scan (counts : List Int) (c : Int) (hc : 0≤c) (hn : 0≤Znth c counts 0)
    (h : CountsEvenBefore counts c) (he : Z.rem (Znth c counts 0) 2=0) : CountsEvenBefore counts (c+1) := by
  rw [AUXLib.rem_eq_mod _ 2 hn (by omega)] at he
  intro k hk
  by_cases hkc : k=c
  · rw [hkc]; exact he
  · exact h k (by omega)

theorem combined_parity_from_full_counts__parity_scan (source target : List Int) (n : Int) (counts : List Int)
    (hs : n=Zlength source) (ht : Zlength target=n) (h : CountedPrefix source target n counts) :
    (CountsEvenBefore counts 26 → CombinedEven source target) ∧
    (∀ c, (0≤c ∧ c<26) → Z.rem (Znth c counts 0) 2≠0 → CombinedOddAt source target c) := by
  constructor
  · intro he c hc
    have hh := he c hc
    rw [counted_prefix_full_count__parity_scan source target n counts c hs ht h hc] at hh
    exact hh
  · intro c hc hn
    have hf := counted_prefix_full_count__parity_scan source target n counts c hs ht h hc
    have hz : 0≤Znth c counts 0 := by rw [hf]; omega
    rw [AUXLib.rem_eq_mod _ 2 hz (by omega)] at hn
    refine ⟨hc,?_⟩
    rw [←hf]
    change Int.fmod (Znth c counts 0) 2=1
    change Int.fmod (Znth c counts 0) 2≠0 at hn
    rw [Int.fmod_eq_emod_of_nonneg _ (by omega : (0:Int)≤2)] at hn ⊢
    omega

theorem repair_state_cross_swap__repair_transitions (source target s t : List Int) (i : Int) (ops : List (Int×Int)) (s' t' : List Int) (a b : Int)
    (h : RepairState source target s t i ops) (hc : CrossSwap (s,t) (s',t') (a,b))
    (hp : PrefixEqual s' t' (i+1)) (hb : Zlength ops+1≤2*(i+1)) : RepairState source target s' t' (i+1) (ops++[(a,b)]) := by
  rcases hc with ⟨hai,hbi,rfl,rfl⟩
  rcases h with ⟨hs,ht,hpold,hperm,heven,htrace,hop⟩
  have hperm' := cross_swap_combined_permutation__repair_transitions s t a b hai hbi
  refine ⟨?_,?_,hp,hperm.trans hperm',combined_even_permutation__repair_transitions s t _ _ heven hperm',?_,?_⟩
  · rw [AUXLib.Zlength_replace_Znth,hs]
  · rw [AUXLib.Zlength_replace_Znth,ht]
  · exact swap_trace_append__repair_transitions source target s t ops _ _ (a,b) htrace ⟨hai,hbi,rfl,rfl⟩
  · rw [zlength_snoc]
    omega

theorem repair_state_one_cross_swap__repair_transitions (source target s t : List Int) (i : Int) (ops : List (Int×Int)) (j : Int)
    (h : RepairState source target s t i ops) (hl : Zlength s=Zlength t) (hi : 0≤i ∧ i<Zlength s)
    (hj : i<j ∧ j<Zlength s) (hm : Znth j s 0=Znth i s 0) :
    RepairState source target (replace_Znth j (Znth i t 0) s) (replace_Znth i (Znth j s 0) t) (i+1) (ops++[(j,i)]) := by
  apply repair_state_cross_swap__repair_transitions source target s t i ops _ _ j i h ⟨by omega,by omega,rfl,rfl⟩
  · intro k hk
    rw [Znth_replace_Znth_Diff 0 s j k _ (by omega) (by omega) (by omega)]
    by_cases he : k=i
    · subst k
      rw [Znth_replace_Znth_Same 0 t i _ (by omega)]
      exact hm.symm
    · rw [Znth_replace_Znth_Diff 0 t i k _ (by omega) (by omega) (by omega)]
      exact h.2.2.1 k (by omega)
  · have := h.2.2.2.2.2.2
    omega

theorem repair_state_two_cross_swaps__repair_transitions (source target s t : List Int) (i : Int) (ops : List (Int×Int)) (j : Int)
    (h : RepairState source target s t i ops) (hl : Zlength s=Zlength t) (hi : 0≤i ∧ i<Zlength s)
    (hj : i<j ∧ j<Zlength s) (hm : Znth j t 0=Znth i s 0) :
    RepairState source target
      (replace_Znth j (Znth i (replace_Znth j (Znth j s 0) t) 0) (replace_Znth j (Znth j t 0) s))
      (replace_Znth i (Znth j (replace_Znth j (Znth j t 0) s) 0) (replace_Znth j (Znth j s 0) t))
      (i+1) ((ops++[(j,j)])++[(j,i)]) := by
  let s1 := replace_Znth j (Znth j t 0) s
  let t1 := replace_Znth j (Znth j s 0) t
  let s2 := replace_Znth j (Znth i t1 0) s1
  let t2 := replace_Znth i (Znth j s1 0) t1
  have hs1 : Zlength s1=Zlength s := AUXLib.Zlength_replace_Znth s j _
  have ht1 : Zlength t1=Zlength t := AUXLib.Zlength_replace_Znth t j _
  have hs2 : Zlength s2=Zlength s1 := AUXLib.Zlength_replace_Znth s1 j _
  have ht2 : Zlength t2=Zlength t1 := AUXLib.Zlength_replace_Znth t1 i _
  have hc1 : CrossSwap (s,t) (s1,t1) (j,j) := ⟨by omega,by omega,rfl,rfl⟩
  have hc2 : CrossSwap (s1,t1) (s2,t2) (j,i) := ⟨by omega,by omega,rfl,rfl⟩
  have hp1 : List.Perm (s++t) (s1++t1) := cross_swap_combined_permutation__repair_transitions s t j j (by omega) (by omega)
  have hp2 : List.Perm (s1++t1) (s2++t2) := cross_swap_combined_permutation__repair_transitions s1 t1 j i (by omega) (by omega)
  have hprefix : PrefixEqual s2 t2 (i+1) := by
    intro k hk
    change Znth k (replace_Znth j (Znth i t1 0) s1) 0=Znth k (replace_Znth i (Znth j s1 0) t1) 0
    rw [Znth_replace_Znth_Diff 0 s1 j k _ (by omega) (by omega) (by omega)]
    change Znth k (replace_Znth j (Znth j t 0) s) 0=_
    rw [Znth_replace_Znth_Diff 0 s j k _ (by omega) (by omega) (by omega)]
    by_cases he : k=i
    · subst k
      rw [Znth_replace_Znth_Same 0 t1 i _ (by omega)]
      change Znth i s 0=Znth j (replace_Znth j (Znth j t 0) s) 0
      rw [Znth_replace_Znth_Same 0 s j _ (by omega)]
      exact hm.symm
    · rw [Znth_replace_Znth_Diff 0 t1 i k _ (by omega) (by omega) (by omega)]
      change Znth k s 0=Znth k (replace_Znth j (Znth j s 0) t) 0
      rw [Znth_replace_Znth_Diff 0 t j k _ (by omega) (by omega) (by omega)]
      exact h.2.2.1 k (by omega)
  rcases h with ⟨hs,ht,hp,hperm,heven,htrace,hops⟩
  change RepairState source target s2 t2 (i+1) ((ops++[(j,j)])++[(j,i)])
  refine ⟨hs2.trans (hs1.trans hs),ht2.trans (ht1.trans ht),hprefix,hperm.trans (hp1.trans hp2),?_,?_,?_⟩
  · exact combined_even_permutation__repair_transitions s t s2 t2 heven (hp1.trans hp2)
  · exact swap_trace_append__repair_transitions source target s1 t1 (ops++[(j,j)]) s2 t2 (j,i)
      (swap_trace_append__repair_transitions source target s t ops s1 t1 (j,j) htrace hc1) hc2
  · rw [zlength_snoc,zlength_snoc]
    omega

theorem trace_prefix_preserves_count__final_results (states : List (List Int×List Int)) (ops : List (Int×Int)) (q x : Int)
    (h : ∀ k, (0≤k ∧ k<Zlength ops) → CrossSwap (Znth k states ([],[])) (Znth (k+1) states ([],[])) (Znth k ops (0,0)))
    (hq : 0≤q ∧ q≤Zlength ops) :
    ((Znth 0 states ([],[])).1++(Znth 0 states ([],[])).2).count x=((Znth q states ([],[])).1++(Znth q states ([],[])).2).count x := by
  have inv : ∀ n:Nat, (n:Int)≤Zlength ops →
      ((Znth 0 states ([],[])).1++(Znth 0 states ([],[])).2).count x=((Znth (n:Int) states ([],[])).1++(Znth (n:Int) states ([],[])).2).count x := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      rw [hi,Int.natCast_succ]
      exact cross_swap_preserves_count__final_results _ _ _ x (h (n:Int) (by omega))
  simpa only [Int.toNat_of_nonneg hq.1] using inv q.toNat (by omega)

theorem swap_trace_preserves_count__final_results (s0 t0 s t : List Int) (ops : List (Int×Int)) (x : Int)
    (h : SwapTrace s0 t0 s t ops) : (s0++t0).count x=(s++t).count x := by
  rcases h with ⟨states,hl,h0,hsteps,hfinal⟩
  have hh := trace_prefix_preserves_count__final_results states ops (Zlength ops) x hsteps ⟨Zlength_nonneg ops,le_refl _⟩
  rw [h0,hfinal] at hh
  exact hh

theorem combined_odd_forbids_swaps_work__final_results (s t : List Int) (c : Int) (ops : List (Int×Int)) (hodd : CombinedOddAt s t c) : ¬SwapsWork s t ops := by
  rintro ⟨hops,states,hl,h0,hsteps,he⟩
  have hh := trace_prefix_preserves_count__final_results states ops (Zlength ops) (97+c) hsteps ⟨Zlength_nonneg ops,le_refl _⟩
  rw [h0,he] at hh
  change (s++t).count (97+c)=_ at hh
  have hp := hodd.2
  rw [hh,List.count_append,Int.natCast_add] at hp
  change Int.fmod _ 2=1 at hp
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega : (0:Int)≤2)] at hp
  omega

theorem prefix_equal_full__final_results (s t : List Int) (i : Int) (hl : Zlength s=Zlength t) (hi : Zlength s≤i)
    (hp : PrefixEqual s t i) : s=t := by
  have hlen : s.length=t.length := by simp only [Zlength,Int.ofNat_eq_coe] at hl; omega
  apply List.ext_getElem hlen
  intro n hn ht
  have hh := hp (n:Int) (by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega)
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,List.getElem?_eq_getElem ht,Option.getD_some] using hh

theorem repair_state_success_swaps_work__final_results (source target s t : List Int) (i : Int) (ops : List (Int×Int))
    (hne : source≠target) (hlen : Zlength source=Zlength target) (hi : i=Zlength source)
    (h : RepairState source target s t i ops) : SwapsWork source target ops := by
  rcases h with ⟨hs,ht,hp,hperm,heven,htrace,hops⟩
  rcases htrace with ⟨states,hsl,h0,hsteps,hfinal⟩
  have hst := prefix_equal_full__final_results s t i (by omega) (by omega) hp
  have hopne : Zlength ops≠0 := by
    intro hz
    rw [hz,h0] at hfinal
    have hp1 := congrArg Prod.fst hfinal
    have hp2 := congrArg Prod.snd hfinal
    exact hne (hp1.trans (hst.trans hp2.symm))
  refine ⟨by omega,states,hsl,h0,hsteps,?_⟩
  rw [hfinal]
  exact hst

theorem no_value_full_count_zero__final_results (l : List Int) (v : Int) (h : NoValueInRange l v 0 (Zlength l)) : l.count v=0 := by
  apply List.count_eq_zero_of_not_mem
  intro hv
  rcases List.mem_iff_getElem.mp hv with ⟨n,hn,he⟩
  apply h (n:Int) (by simp only [Zlength,Int.ofNat_eq_coe]; omega)
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some] using he

private theorem counter_increment (counts : List Int) (a c : Int) (ha : 0≤a ∧ a<Zlength counts) (hc : 0≤c ∧ c<Zlength counts) :
    Znth c (replace_Znth a (Znth a counts 0+1) counts) 0=Znth c counts 0+(if c=a then 1 else 0) := by
  by_cases he : c=a
  · subst c
    rw [Znth_replace_Znth_Same 0 counts a _ ha,if_pos rfl]
  · rw [Znth_replace_Znth_Diff 0 counts a c _ ha hc (Ne.symm he),if_neg he,add_zero]

private theorem sublist_extend (l : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength l) :
    sublist 0 (i+1) l=sublist 0 i l++[Znth i l 0] := by
  rw [sublist_split 0 (i+1) i l (by omega) (by omega),sublist_single 0 i l hi]

theorem counted_prefix_step__count_invariants (s t counts : List Int) (i : Int)
    (hs : 0≤i ∧ i<Zlength s) (ht : 0≤i ∧ i<Zlength t)
    (hsv : 97≤Znth i s 0 ∧ Znth i s 0≤122) (htv : 97≤Znth i t 0 ∧ Znth i t 0≤122)
    (h : CountedPrefix s t i counts) :
    CountedPrefix s t (i+1)
      (replace_Znth (Znth i t 0-97) (Znth (Znth i t 0-97)
        (replace_Znth (Znth i s 0-97) (Znth (Znth i s 0-97) counts 0+1) counts) 0+1)
        (replace_Znth (Znth i s 0-97) (Znth (Znth i s 0-97) counts 0+1) counts)) := by
  refine ⟨by rw [AUXLib.Zlength_replace_Znth,AUXLib.Zlength_replace_Znth]; exact h.1,?_⟩
  intro c hc
  have hlen := h.1
  rw [counter_increment _ (Znth i t 0-97) c (by rw [AUXLib.Zlength_replace_Znth]; omega) (by rw [AUXLib.Zlength_replace_Znth]; omega),
    counter_increment counts (Znth i s 0-97) c (by omega) (by omega),h.2 c hc,
    sublist_extend s i hs,sublist_extend t i ht]
  simp only [List.count_append,List.count_cons,List.count_nil,beq_iff_eq]
  by_cases hsx : Znth i s 0=97+c <;> by_cases htx : Znth i t 0=97+c
  all_goals simp only [hsx,htx,if_true,if_false]
  all_goals (repeat' split) <;> simp only [Int.natCast_add,Int.natCast_one,Int.natCast_zero] <;> omega

private theorem znth_cons_shift {A : Type} (d : A) (a : A) (l : List A) (i : Int) (hi : 0≤i) : Znth (i+1) (a::l) d=Znth i l d := by
  rw [Znth_cons d (i+1) a l (by omega),add_sub_cancel_right]

theorem paired_prefix_unmatched_count_odd__final_results (s t : List Int) (i v : Int)
    (hlen : Zlength s=Zlength t) (hi : 0≤i ∧ i<Zlength s) (hp : PrefixEqual s t i)
    (hsi : Znth i s 0=v) (hti : Znth i t 0≠v)
    (hsuf : NoValueInRange s v (i+1) (Zlength s)) (htuf : NoValueInRange t v (i+1) (Zlength t)) :
    ∃ k:Nat, (s++t).count v=2*k+1 := by
  induction s generalizing t i with
  | nil => simp only [Zlength_nil] at hi; omega
  | cons a s ih =>
    cases t with
    | nil => simp only [Zlength_cons,Zlength_nil] at hlen; have := Zlength_nonneg s; omega
    | cons b t =>
      have hslen := Zlength_nonneg s
      have htlen := Zlength_nonneg t
      have htl : Zlength s=Zlength t := by simp only [Zlength_cons] at hlen; omega
      by_cases hz : i=0
      · subst i
        change a=v at hsi
        change b≠v at hti
        have hsn : NoValueInRange s v 0 (Zlength s) := by
          intro k hk
          have hh := hsuf (k+1) (by rw [Zlength_cons]; omega)
          rw [znth_cons_shift 0 a s k hk.1] at hh
          exact hh
        have htn : NoValueInRange t v 0 (Zlength t) := by
          intro k hk
          have hh := htuf (k+1) (by rw [Zlength_cons]; omega)
          rw [znth_cons_shift 0 b t k hk.1] at hh
          exact hh
        have hsc := no_value_full_count_zero__final_results s v hsn
        have htc := no_value_full_count_zero__final_results t v htn
        refine ⟨0,?_⟩
        simp only [List.count_append,List.count_cons,beq_iff_eq,hsi,hti,if_true,if_false,hsc,htc]
      · have hin : 0<i := by omega
        have hab : a=b := hp 0 (by omega)
        subst b
        have hp' : PrefixEqual s t (i-1) := by
          intro k hk
          have hh := hp (k+1) (by omega)
          rw [znth_cons_shift 0 a s k hk.1,znth_cons_shift 0 a t k hk.1] at hh
          exact hh
        have hsuf' : NoValueInRange s v ((i-1)+1) (Zlength s) := by
          intro k hk
          have hh := hsuf (k+1) (by rw [Zlength_cons]; omega)
          rw [znth_cons_shift 0 a s k (by omega)] at hh
          exact hh
        have htuf' : NoValueInRange t v ((i-1)+1) (Zlength t) := by
          intro k hk
          have hh := htuf (k+1) (by rw [Zlength_cons]; omega)
          rw [znth_cons_shift 0 a t k (by omega)] at hh
          exact hh
        rw [Znth_cons 0 i a s hin] at hsi
        rw [Znth_cons 0 i a t hin] at hti
        have hitail : 0≤i-1 ∧ i-1<Zlength s := by rw [Zlength_cons] at hi; omega
        rcases ih t (i-1) htl hitail hp' hsi hti hsuf' htuf' with ⟨k,hk⟩
        rw [List.count_append] at hk
        by_cases he : a=v
        · refine ⟨k+1,?_⟩
          simp only [List.count_append,List.count_cons,beq_iff_eq,he,if_true]
          omega
        · refine ⟨k,?_⟩
          simp only [List.count_append,List.count_cons,beq_iff_eq,he,if_false]
          omega

theorem no_match_contradicts_combined_even__final_results (s t : List Int) (i v : Int)
    (hlen : Zlength s=Zlength t) (hi : 0≤i ∧ i<Zlength s) (hv : 97≤v ∧ v≤122) (hp : PrefixEqual s t i)
    (hsi : Znth i s 0=v) (hti : Znth i t 0≠v)
    (hsuf : NoValueInRange s v (i+1) (Zlength s)) (htuf : NoValueInRange t v (i+1) (Zlength t)) : ¬CombinedEven s t := by
  intro he
  rcases paired_prefix_unmatched_count_odd__final_results s t i v hlen hi hp hsi hti hsuf htuf with ⟨k,hk⟩
  have hh := he (v-97) (by omega)
  rw [show 97+(v-97)=v by omega,hk] at hh
  change Int.fmod ((2*k+1:Nat):Int) 2=0 at hh
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega : (0:Int)≤2)] at hh
  simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one] at hh
  omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib
