import MaxMinLib.Interface
import SimpleC.EE.LLM_bench.Algorithms.decimal_digits.decimal_digits_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 6000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib
open AUXLib

def number_item : Type := List Int × Int

def item_digits (x : number_item) : List Int :=
  sublist 0 (Prod.snd x) (Prod.fst x)

def paired_items (rows : List (List Int)) (lengths : List Int) :
  List number_item :=
  List.zip rows lengths

def concatenate_items (items : List number_item) : List Int :=
  List.flatten (List.map item_digits items)

def concatenate_rows (rows : List (List Int)) (lengths : List Int) :
  List Int :=
  concatenate_items (paired_items rows lengths)

def digit_lex_ge (xs ys : List Int) : Prop :=
  Zlength xs = Zlength ys ∧
  (xs = ys ∨
   ∃ k, (0 ≤ k ∧ k < Zlength xs) ∧
     (∀ j, (0 ≤ j ∧ j < k) → Znth j xs 0 = Znth j ys 0) ∧
     Znth k ys 0 < Znth k xs 0)

def digit_lex_gt (xs ys : List Int) : Prop :=
  Zlength xs = Zlength ys ∧
  ∃ k, (0 ≤ k ∧ k < Zlength xs) ∧
    (∀ j, (0 ≤ j ∧ j < k) → Znth j xs 0 = Znth j ys 0) ∧
    Znth k ys 0 < Znth k xs 0

def item_at (rows : List (List Int)) (lengths : List Int) (i : Int) :
  number_item :=
  (Znth i rows [], Znth i lengths 0)

def item_before
    (rows : List (List Int)) (lengths : List Int) (i j : Int) : Prop :=
  digit_lex_gt
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i))

def item_before_or_equal
    (rows : List (List Int)) (lengths : List Int) (i j : Int) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i))

def ConcatLeftDigit
    (rows : List (List Int)) (lens : List Int) (i j position : Int) : Int :=
  Znth position
    (item_digits (item_at rows lens i) ++
     item_digits (item_at rows lens j)) 0

def ConcatRightDigit
    (rows : List (List Int)) (lens : List Int) (i j position : Int) : Int :=
  Znth position
    (item_digits (item_at rows lens j) ++
     item_digits (item_at rows lens i)) 0

def RowsWellFormed
    (rows : List (List Int)) (lengths : List Int)
    (count width : Int) : Prop :=
  Zlength rows = count ∧
  Zlength lengths = count ∧
  (∀ i, (0 ≤ i ∧ i < count) →
     Zlength (Znth i rows []) = width ∧ (1 ≤ Znth i lengths 0 ∧ Znth i lengths 0 ≤ width) ∧ (1 ≤ Znth 0 (Znth i rows []) 0 ∧ Znth 0 (Znth i rows []) 0 ≤ 9) ∧
     (∀ j, (0 ≤ j ∧ j < Znth i lengths 0) → (0 ≤ Znth j (Znth i rows []) 0 ∧ Znth j (Znth i rows []) 0 ≤ 9) ))

def FlatRows
    (flat : List Int) (rows : List (List Int)) (count width : Int) : Prop :=
  Zlength flat = count * width ∧
  Zlength rows = count ∧
  ∀ i, (0 ≤ i ∧ i < count) →
    Znth i rows [] = sublist (i * width) ((i + 1) * width) flat

def PairedPermutation
    (rows lengths_rows : List (List Int))
    (lens lengths_lens : List Int) : Prop :=
  Zlength rows = Zlength lens ∧
  Zlength lengths_rows = Zlength lengths_lens ∧
  Permutation (paired_items rows lens)
              (paired_items lengths_rows lengths_lens)

def SameOutsidePairedRange
    (rows0 rows1 : List (List Int)) (lens0 lens1 : List Int)
    (left right : Int) : Prop :=
  Zlength rows0 = Zlength rows1 ∧
  Zlength lens0 = Zlength lens1 ∧
  ∀ k, (0 ≤ k ∧ k < Zlength rows0) →
    (k < left ∨ right < k) →
    item_at rows1 lens1 k = item_at rows0 lens0 k

def ConcatComparePrefix
    (rows : List (List Int)) (lens : List Int)
    (i j position : Int) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j);
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i);
  (0 ≤ position ∧ position ≤ Zlength lhs) ∧
  Zlength lhs = Zlength rhs ∧
  ∀ k, (0 ≤ k ∧ k < position) → Znth k lhs 0 = Znth k rhs 0

def ConcatCompareOutcome
    (rows : List (List Int)) (lens : List Int)
    (i j comparison : Int) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j);
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i);
  (comparison = 0 ∧ lhs = rhs) ∨
  (∃ k, (0 ≤ k ∧ k < Zlength lhs) ∧
     Zlength lhs = Zlength rhs ∧
     (∀ p, (0 ≤ p ∧ p < k) → Znth p lhs 0 = Znth p rhs 0) ∧
     Znth k lhs 0 ≠ Znth k rhs 0 ∧
     comparison = Znth k lhs 0 - Znth k rhs 0)

def swap_Znth {A : Type} (default : A) (i j : Int) (xs : List A) :
  List A :=
  replace_Znth j (Znth i xs default)
    (replace_Znth i (Znth j xs default) xs)

def SwapRowsPrefix
    (before after : List (List Int)) (first second progress width : Int) : Prop :=
  let first_row := Znth first before [];
  let second_row := Znth second before [];
  let first_now := sublist 0 progress second_row ++
                   sublist progress width first_row;
  let second_now := sublist 0 progress first_row ++
                    sublist progress width second_row;
  after = replace_Znth second second_now
            (replace_Znth first first_now before)

def PartitionScanState
    (rows0 rows1 : List (List Int)) (lens0 lens1 : List Int)
    (low high boundary scan : Int) : Prop :=
  PairedPermutation rows0 rows1 lens0 lens1 ∧
  SameOutsidePairedRange rows0 rows1 lens0 lens1 low high ∧
  item_at rows1 lens1 high = item_at rows0 lens0 high ∧
  (∀ k, (low ≤ k ∧ k ≤ boundary) → item_before rows1 lens1 k high) ∧
  (∀ k, (boundary < k ∧ k < scan) → ¬ item_before rows1 lens1 k high)

def GreedyPartitionedAt
    (rows : List (List Int)) (lens : List Int)
    (low high pivot : Int) : Prop := (low ≤ pivot ∧ pivot ≤ high) ∧
  (∀ k, (low ≤ k ∧ k < pivot) → item_before rows lens k pivot) ∧
  (∀ k, (pivot < k ∧ k ≤ high) → ¬ item_before rows lens k pivot)

def GreedySortedRange
    (rows : List (List Int)) (lens : List Int) (left right : Int) : Prop :=
  ∀ i j,
    left ≤ i ∧ i ≤ j ∧ j ≤ right →
    item_before_or_equal rows lens i j

def GreedySorted
    (rows : List (List Int)) (lens : List Int) : Prop :=
  ∀ i j,
    0 ≤ i ∧ i ≤ j ∧ j < Zlength rows →
    item_before_or_equal rows lens i j

def ConcatenatedPrefix
    (rows : List (List Int)) (lens : List Int) (row_count : Int) : List Int :=
  concatenate_rows (sublist 0 row_count rows) (sublist 0 row_count lens)

def ConcatenatedOutputPrefix
    (rows : List (List Int)) (lens : List Int)
    (row_count digit_count : Int) : List Int :=
  ConcatenatedPrefix rows lens row_count ++
  sublist 0 digit_count (Znth row_count rows [])

def LargestConcatenationLegacy
    (original_rows arranged_rows : List (List Int))
    (original_lens arranged_lens output : List Int) : Prop :=
  PairedPermutation original_rows arranged_rows
                    original_lens arranged_lens ∧
  output = concatenate_rows arranged_rows arranged_lens ∧
  ∀ alternative_rows alternative_lens,
    PairedPermutation original_rows alternative_rows
                      original_lens alternative_lens →
    digit_lex_ge output
      (concatenate_rows alternative_rows alternative_lens)

private abbrev decimalFold (xs : List Int) (acc : Int) : Int := xs.foldl (fun value digit=>10*value+digit) acc

private theorem zlist_ext {A : Type} (l1 l2 : List A) (d : A) (hl : Zlength l1=Zlength l2)
    (he : ∀i, (0≤i ∧ i<Zlength l1) → Znth i l1 d=Znth i l2 d) : l1=l2 := by
  have hl' : l1.length=l2.length := by simp only [Zlength,Int.ofNat_eq_coe] at hl; omega
  apply List.ext_getElem hl'
  intro i hi1 hi2
  have h := he i ⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi1,
    List.getElem?_eq_getElem hi2,Option.getD_some] using h

private theorem app_Znth1 {A : Type} (d : A) (l1 l2 : List A) (i : Int)
    (h : 0≤i ∧ i<Zlength l1) : Znth i (l1++l2) d=Znth i l1 d := by
  have hn : i.toNat<l1.length := by simp only [Zlength,Int.ofNat_eq_coe] at h; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

private theorem sub_len {A : Type} (l : List A) (lo hi : Int) (hlo : 0≤lo ∧ lo≤hi)
    (hhi : hi≤Zlength l) : Zlength (sublist lo hi l)=hi-lo := by
  unfold Zlength
  rw [sublist_length lo hi l hlo hhi]
  simp only [Int.ofNat_eq_coe]
  omega

private theorem prefix_len {A : Type} (l : List A) (n : Int) (hn : 0≤n ∧ n≤Zlength l) :
    Zlength (sublist 0 n l)=n := by simpa using sub_len l 0 n (by omega) hn.2

private theorem Znth_prefix {A : Type} (l : List A) (d : A) (n i : Int) (hi : 0≤i ∧ i<n) :
    Znth i (sublist 0 n l) d=Znth i l d := by
  simpa only [Int.add_zero] using Znth_sublist d 0 i n l (by omega) (by omega)

private theorem replace_nth_eq_set {A : Type} (l : List A) (n : Nat) (x : A) :
    replace_nth n l x=l.set n x := by
  induction l generalizing n with
  | nil => simp [replace_nth]
  | cons a l ih => cases n <;> simp [replace_nth,ih]

private theorem nth_set_comm {A : Type} (ni nj : Nat) (l : List A) (a b : A) (h : ni≠nj) :
    replace_nth nj (replace_nth ni l a) b=replace_nth ni (replace_nth nj l b) a := by
  induction l generalizing ni nj with
  | nil => simp [replace_nth]
  | cons x l ih => cases ni <;> cases nj <;> simp_all [replace_nth]

private theorem nth_set_twice {A : Type} (n : Nat) (l : List A) (a b : A) :
    replace_nth n (replace_nth n l a) b=replace_nth n l b := by
  induction l generalizing n with
  | nil => simp [replace_nth]
  | cons x l ih => cases n <;> simp_all [replace_nth]

private theorem perm_replace_head {A : Type} (l : List A) (k : Nat) (x d : A) (hk : k < l.length) :
    Permutation (x :: l) (l.getD k d :: replace_nth k l x) := by
  induction l generalizing k x with
  | nil => simp at hk
  | cons y l ih =>
    cases k with
    | zero => exact List.Perm.swap y x l
    | succ k =>
      simp only [List.getD_cons_succ, replace_nth]
      exact (List.Perm.swap y x l).trans
        ((ih k x (by simpa using hk)).cons y |>.trans (List.Perm.swap _ _ _))


private theorem permutation_swap_nat {A : Type} (l : List A) (i j : Nat) (d : A)
    (hij : i < j) (hj : j < l.length) :
    Permutation l (replace_nth j (replace_nth i l (l.getD j d)) (l.getD i d)) := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_zero, List.getD_cons_succ] using
          perm_replace_head l j x d (by simpa using hj)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_succ] using
          (ih i j (by omega) (by simpa using hj)).cons x


private theorem swap_complete_core (before after : List (List Int)) (first second width : Int)
    (hf : Zlength (Znth first before [])=width) (hs : Zlength (Znth second before [])=width)
    (hc : SwapRowsPrefix before after first second width width) : after=swap_Znth [] first second before := by
  dsimp only [SwapRowsPrefix] at hc
  rw [sublist_self _ width hf.symm,sublist_self _ width hs.symm,
    Zsublist_nil _ width width (by omega),Zsublist_nil _ width width (by omega),List.append_nil,List.append_nil] at hc
  exact hc

private theorem read_set {A : Type} (d : A) (l : List A) (i k : Int) (v : A)
    (hi : 0≤i ∧ i<Zlength l) (hk : 0≤k ∧ k<Zlength l) :
    Znth k (replace_Znth i v l) d=if k=i then v else Znth k l d := by
  by_cases he : k=i
  · subst k
    rw [if_pos rfl,Znth_replace_Znth_Same d l i v hi]
  · rw [if_neg he,Znth_replace_Znth_Diff d l i k v hi hk (Ne.symm he)]

private theorem sub_replace_inside {A : Type} (d : A) (l : List A) (lo hi i : Int) (v : A)
    (hlo : 0≤lo ∧ lo≤hi) (hhi : hi≤Zlength l) (hir : lo≤i ∧ i<hi) :
    sublist lo hi (replace_Znth i v l)=replace_Znth (i-lo) v (sublist lo hi l) := by
  have hsub := sub_len l lo hi hlo hhi
  have hsub' := sub_len (replace_Znth i v l) lo hi hlo (by simpa only [Zlength_replace_Znth] using hhi)
  apply zlist_ext _ _ d (by simpa only [Zlength_replace_Znth] using hsub'.trans hsub.symm)
  intro k hk
  have hk' : 0≤k ∧ k<hi-lo := by omega
  rw [Znth_sublist d lo k hi _ hlo.1 hk',read_set d l i (k+lo) v (by omega) (by omega),
    read_set d (sublist lo hi l) (i-lo) k v (by omega) (by omega)]
  by_cases he : k+lo=i
  · rw [if_pos he,if_pos (by omega)]
  · rw [if_neg he,if_neg (by omega),Znth_sublist d lo k hi l hlo.1 hk']

private theorem sub_replace_outside {A : Type} (d : A) (l : List A) (lo hi i : Int) (v : A)
    (hlo : 0≤lo ∧ lo≤hi) (hhi : hi≤Zlength l) (hir : 0≤i ∧ i<Zlength l)
    (hout : i<lo ∨ hi≤i) : sublist lo hi (replace_Znth i v l)=sublist lo hi l := by
  have hsub := sub_len l lo hi hlo hhi
  have hsub' := sub_len (replace_Znth i v l) lo hi hlo (by simpa only [Zlength_replace_Znth] using hhi)
  apply zlist_ext _ _ d (hsub'.trans hsub.symm)
  intro k hk
  have hk' : 0≤k ∧ k<hi-lo := by omega
  rw [Znth_sublist d lo k hi _ hlo.1 hk',read_set d l i (k+lo) v hir (by omega),if_neg (by omega),
    Znth_sublist d lo k hi l hlo.1 hk']

private theorem flat_index_bounds (count width row column : Int) (hw : 0<width)
    (hr : 0≤row ∧ row<count) (hc : 0≤column ∧ column<width) :
    0≤row*width+column ∧ row*width+column<count*width := by
  have h0 := Int.mul_nonneg hr.1 (Int.le_of_lt hw)
  have h1 := Int.mul_le_mul_of_nonneg_right (by omega : row+1≤count) (Int.le_of_lt hw)
  rw [Int.add_mul,Int.one_mul] at h1
  omega

private theorem forall_append {A : Type} {P : A → Prop} {xs ys : List A}
    (hx : Forall P xs) (hy : Forall P ys) : Forall P (xs ++ ys) := by
  apply Forall.iff_forall_mem.mpr
  intro x hm
  rcases List.mem_append.mp hm with hm|hm
  · exact hx.mem hm
  · exact hy.mem hm

private theorem forall_znth {A : Type} (P : A → Prop) (l : List A) (d : A) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have h := hp.mem (List.getElem_mem (l := l) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using h

private theorem forall_of_znth {A : Type} (P : A → Prop) (l : List A) (d : A)
    (h : ∀ i, (0 ≤ i ∧ i < Zlength l) → P (Znth i l d)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hp := h i (by simp only [Zlength, Int.ofNat_eq_coe]; omega)
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some] using hp

private theorem forall_sub_znth {A : Type} (P : A → Prop) (l : List A) (d : A) (lo hi : Int)
    (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l)
    (h : ∀ k, lo ≤ k ∧ k < hi → P (Znth k l d)) : Forall P (sublist lo hi l) := by
  apply forall_of_znth P _ d
  intro i hi'
  rw [sub_len l lo hi hl hh] at hi'
  rw [Znth_sublist d lo i hi l hl.1 hi']
  exact h _ (by omega)

theorem concat_left_digit_bounds__safety_arithmetic :
  ∀ rows lens count width i j position,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) → ((0 : Int) ≤ position ∧ position < Znth i lens (0 : Int) + Znth j lens (0 : Int)) → ((0 : Int) ≤ ConcatLeftDigit rows lens i j position ∧ ConcatLeftDigit rows lens i j position ≤ (9 : Int)) := by
  intro rows lens count width i j position hw hi hj hpos
  have hiw := hw.2.2 i hi
  have hjw := hw.2.2 j hj
  have hlen := prefix_len (Znth i rows []) (Znth i lens 0) (by omega)
  unfold ConcatLeftDigit item_digits item_at
  simp only [Prod.fst,Prod.snd]
  by_cases hl : position<Znth i lens 0
  · rw [app_Znth1 0 _ _ position (by omega),Znth_prefix _ 0 _ position (by omega)]
    exact hiw.2.2.2 position (by omega)
  · rw [app_Znth2 0 _ _ position (by omega),hlen,Znth_prefix _ 0 _ (position-Znth i lens 0) (by omega)]
    exact hjw.2.2.2 _ (by omega)

theorem concat_right_digit_bounds__safety_arithmetic :
  ∀ rows lens count width i j position,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) → ((0 : Int) ≤ position ∧ position < Znth i lens (0 : Int) + Znth j lens (0 : Int)) → ((0 : Int) ≤ ConcatRightDigit rows lens i j position ∧ ConcatRightDigit rows lens i j position ≤ (9 : Int)) := by
  intro rows lens count width i j position hw hi hj hpos
  have hiw := hw.2.2 j hj
  have hjw := hw.2.2 i hi
  have hlen := prefix_len (Znth j rows []) (Znth j lens 0) (by omega)
  unfold ConcatRightDigit item_digits item_at
  simp only [Prod.fst,Prod.snd]
  by_cases hl : position<Znth j lens 0
  · rw [app_Znth1 0 _ _ position (by omega),Znth_prefix _ 0 _ position (by omega)]
    exact hiw.2.2.2 position (by omega)
  · rw [app_Znth2 0 _ _ position (by omega),hlen,Znth_prefix _ 0 _ (position-Znth j lens 0) (by omega)]
    exact hjw.2.2.2 _ (by omega)

theorem PartitionScanState_identity__partition_and_compare_init :
  ∀ rows lens low high,
    Zlength rows = Zlength lens →
    PartitionScanState rows rows lens lens low high (low - (1 : Int)) low := by
  intro rows lens low high hl
  refine ⟨⟨hl,hl,List.Perm.refl _⟩,⟨rfl,rfl,by intros; rfl⟩,rfl,?_,?_⟩ <;> intro k hk <;> omega

theorem ConcatComparePrefix_zero__partition_and_compare_init :
  ∀ rows lens i j,
    ConcatComparePrefix rows lens i j (0 : Int) := by
  intros
  unfold ConcatComparePrefix
  refine ⟨⟨by omega,Zlength_nonneg _⟩,?_,?_⟩
  · rw [Zlength_app,Zlength_app]; omega
  · intro k hk; omega

theorem FlatRows_Znth__compare_left_digit :
  ∀ flat rows count width i j,
    FlatRows flat rows count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < width) →
    Znth (i * width + j) flat (0 : Int) = Znth j (Znth i rows []) (0 : Int) := by
  intro flat rows count width i j hf hi hj
  have hd : (i+1)*width-i*width=width := by grind
  rw [hf.2.2 i hi,Znth_sublist 0 (i*width) j ((i+1)*width) flat (Int.mul_nonneg hi.1 (by omega)) (by rw [hd]; exact hj)]
  congr 1
  omega

theorem ConcatLeftDigit_first__compare_left_digit :
  ∀ rows lens count width i j position,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ position ∧ position < Znth i lens (0 : Int)) →
    ConcatLeftDigit rows lens i j position =
      Znth position (Znth i rows []) (0 : Int) := by
  intro rows lens count width i j position hw hi hp
  have hr := hw.2.2 i hi
  have hlen := prefix_len (Znth i rows []) (Znth i lens 0) (by omega)
  unfold ConcatLeftDigit item_digits item_at
  simp only [Prod.fst,Prod.snd]
  rw [app_Znth1 0 _ _ position (by omega),Znth_prefix _ 0 _ position hp]

theorem ConcatLeftDigit_second__compare_left_digit :
  ∀ rows lens count width i j position,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) → (Znth i lens (0 : Int) ≤ position ∧ position < Znth i lens (0 : Int) + Znth j lens (0 : Int)) →
    ConcatLeftDigit rows lens i j position =
      Znth (position - Znth i lens (0 : Int)) (Znth j rows []) (0 : Int) := by
  intro rows lens count width i j position hw hi hj hp
  have hir := hw.2.2 i hi
  have hjr := hw.2.2 j hj
  have hlen := prefix_len (Znth i rows []) (Znth i lens 0) (by omega)
  unfold ConcatLeftDigit item_digits item_at
  simp only [Prod.fst,Prod.snd]
  rw [app_Znth2 0 _ _ position (by omega),hlen,Znth_prefix _ 0 _ (position-Znth i lens 0) (by omega)]

theorem ConcatRightDigit_first_flat__compare_right_digit :
  ∀ flat rows lens count width scan high position,
    FlatRows flat rows count width →
    RowsWellFormed rows lens count width → ((0 : Int) ≤ high ∧ high < count) → ((0 : Int) ≤ position ∧ position < Znth high lens (0 : Int)) →
    Znth (high * width + position) flat (0 : Int) =
      ConcatRightDigit rows lens scan high position := by
  intro flat rows lens count width scan high position hf hw hh hp
  have hr := hw.2.2 high hh
  change Znth (high*width+position) flat 0=ConcatLeftDigit rows lens high scan position
  rw [ConcatLeftDigit_first__compare_left_digit rows lens count width high scan position hw hh hp]
  exact FlatRows_Znth__compare_left_digit flat rows count width high position hf hh (by omega)

theorem ConcatRightDigit_second_flat__compare_right_digit :
  ∀ flat rows lens count width scan high position,
    FlatRows flat rows count width →
    RowsWellFormed rows lens count width → ((0 : Int) ≤ scan ∧ scan < count) → ((0 : Int) ≤ high ∧ high < count) →
    Znth high lens (0 : Int) ≤ position →
    position < Znth high lens (0 : Int) + Znth scan lens (0 : Int) →
    Znth (scan * width + (position - Znth high lens (0 : Int))) flat (0 : Int) =
      ConcatRightDigit rows lens scan high position := by
  intro flat rows lens count width scan high position hf hw hs hh hp hpos
  have hr := hw.2.2 scan hs
  change Znth (scan*width+(position-Znth high lens 0)) flat 0=ConcatLeftDigit rows lens high scan position
  rw [ConcatLeftDigit_second__compare_left_digit rows lens count width high scan position hw hh hs ⟨hp,hpos⟩]
  exact FlatRows_Znth__compare_left_digit flat rows count width scan _ hf hs (by omega)

theorem concat_item_digits_Zlength__compare_outcome :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) →
    Zlength
      (item_digits (item_at rows lens i) ++
       item_digits (item_at rows lens j)) =
    Znth i lens (0 : Int) + Znth j lens (0 : Int) := by
  intro rows lens count width i j hw hi hj
  have hir := hw.2.2 i hi
  have hjr := hw.2.2 j hj
  unfold item_digits item_at
  simp only [Prod.fst,Prod.snd,Zlength_app]
  rw [prefix_len _ _ (by omega),prefix_len _ _ (by omega)]

theorem ConcatComparePrefix_step__compare_outcome :
  ∀ rows lens i j position,
    ConcatComparePrefix rows lens i j position →
    ConcatLeftDigit rows lens i j position =
      ConcatRightDigit rows lens i j position →
    position <
      Zlength
        (item_digits (item_at rows lens i) ++
         item_digits (item_at rows lens j)) →
    ConcatComparePrefix rows lens i j (position + (1 : Int)) := by
  intro rows lens i j position hp he hlt
  rcases hp with ⟨hr,hlen,hpre⟩
  refine ⟨⟨by omega,by omega⟩,hlen,?_⟩
  intro k hk
  by_cases h : k=position
  · subst k; exact he
  · exact hpre k (by omega)

theorem ConcatCompareOutcome_difference__compare_outcome :
  ∀ rows lens i j position,
    ConcatComparePrefix rows lens i j position →
    position <
      Zlength
        (item_digits (item_at rows lens i) ++
         item_digits (item_at rows lens j)) →
    ConcatLeftDigit rows lens i j position ≠
      ConcatRightDigit rows lens i j position →
    ConcatCompareOutcome rows lens i j
      (ConcatLeftDigit rows lens i j position -
       ConcatRightDigit rows lens i j position) := by
  intro rows lens i j position hp hlt hne
  exact Or.inr ⟨position,⟨hp.1.1,hlt⟩,hp.2.1,hp.2.2,hne,rfl⟩

theorem ConcatCompareOutcome_zero__compare_outcome :
  ∀ rows lens i j position,
    ConcatComparePrefix rows lens i j position →
    Zlength
      (item_digits (item_at rows lens i) ++
       item_digits (item_at rows lens j)) ≤ position →
    ConcatCompareOutcome rows lens i j (0 : Int) := by
  intro rows lens i j position hp hle
  apply Or.inl
  refine ⟨rfl,?_⟩
  apply zlist_ext _ _ 0 hp.2.1
  intro k hk
  exact hp.2.2 k (by omega)

theorem SwapRowsPrefix_zero__scan_row_swap :
  ∀ before lens count width first second,
    RowsWellFormed before lens count width → ((0 : Int) ≤ first ∧ first < count) → ((0 : Int) ≤ second ∧ second < count) →
    SwapRowsPrefix before before first second (0 : Int) width := by
  intro before lens count width first second hw hf hs
  have hfw := (hw.2.2 first hf).1
  have hsw := (hw.2.2 second hs).1
  dsimp only [SwapRowsPrefix]
  simp only [sublist,Int.toNat_zero,List.take_zero,List.drop_nil,List.nil_append,List.drop_zero]
  have hf' : width.toNat=(Znth first before []).length := by simp only [Zlength,Int.ofNat_eq_coe] at hfw; omega
  have hs' : width.toNat=(Znth second before []).length := by simp only [Zlength,Int.ofNat_eq_coe] at hsw; omega
  rw [hf',List.take_length,←hf',hs',List.take_length]
  simp only [replace_Znth_Znth]

theorem advance_prefix_row__scan_row_swap :
  ∀ (first_row second_row : List Int) progress width,
    Zlength first_row = width →
    Zlength second_row = width → ((0 : Int) ≤ progress ∧ progress < width) →
    replace_Znth progress (Znth progress second_row (0 : Int))
      (sublist (0 : Int) progress second_row ++
       sublist progress width first_row) =
    sublist (0 : Int) (progress + (1 : Int)) second_row ++
    sublist (progress + (1 : Int)) width first_row := by
  intro first_row second_row progress width hf hs hp
  let old := sublist 0 progress second_row++sublist progress width first_row
  let new := sublist 0 (progress+1) second_row++sublist (progress+1) width first_row
  have hpre := prefix_len second_row progress (by omega)
  have hpre' := prefix_len second_row (progress+1) (by omega)
  have htail := sub_len first_row progress width (by omega) (by omega)
  have htail' := sub_len first_row (progress+1) width (by omega) (by omega)
  have hold : Zlength old=width := by change Zlength (sublist 0 progress second_row++sublist progress width first_row)=width; rw [Zlength_app,hpre,htail]; omega
  have hnew : Zlength new=width := by change Zlength (sublist 0 (progress+1) second_row++sublist (progress+1) width first_row)=width; rw [Zlength_app,hpre',htail']; omega
  apply zlist_ext _ _ 0 (by simpa only [Zlength_replace_Znth] using hold.trans hnew.symm)
  intro k hk
  have hkr : 0≤k ∧ k<width := by simp only [Zlength_replace_Znth] at hk; change 0≤k ∧ k<Zlength old at hk; omega
  rw [read_set 0 old progress k _ (by omega) (by omega)]
  by_cases he : k=progress
  · subst k
    rw [if_pos rfl]
    try dsimp only [new]
    rw [app_Znth1 0 _ _ progress (by omega),Znth_prefix _ 0 _ progress (by omega)]
  · rw [if_neg he]
    by_cases hl : k<progress
    · try dsimp only [old,new]
      rw [app_Znth1 0 _ _ k (by omega),app_Znth1 0 _ _ k (by omega),
        Znth_prefix _ 0 _ k (by omega),Znth_prefix _ 0 _ k (by omega)]
    · try dsimp only [old,new]
      rw [app_Znth2 0 _ _ k (by omega),app_Znth2 0 _ _ k (by omega),hpre,hpre',
        Znth_sublist 0 progress (k-progress) width first_row (by omega) (by omega),
        Znth_sublist 0 (progress+1) (k-(progress+1)) width first_row (by omega) (by omega)]
      congr 1
      omega

theorem sublist_replace_flat_cell__scan_row_swap :
  ∀ (flat : List Int) count width row column i value,
    Zlength flat = count * width →
    (0 : Int) < width → ((0 : Int) ≤ row ∧ row < count) → ((0 : Int) ≤ column ∧ column < width) → ((0 : Int) ≤ i ∧ i < count) →
    sublist (i * width) ((i + (1 : Int)) * width)
      (replace_Znth (row * width + column) value flat) =
    if i = row then
      replace_Znth column value
        (sublist (i * width) ((i + (1 : Int)) * width) flat)
    else
      sublist (i * width) ((i + (1 : Int)) * width) flat := by
  intro flat count width row column i value hlen hw hr hc hi
  have hib := flat_index_bounds count width row column hw hr hc
  have hil0 := Int.mul_nonneg hi.1 (Int.le_of_lt hw)
  have hil1 := Int.mul_le_mul_of_nonneg_right (by omega : i+1≤count) (Int.le_of_lt hw)
  have hstep : (i+1)*width=i*width+width := by grind
  by_cases he : i=row
  · rw [if_pos he]
    subst row
    rw [sub_replace_inside 0 flat (i*width) ((i+1)*width) (i*width+column) value (by omega) (by omega) (by omega)]
    congr 1
    omega
  · rw [if_neg he]
    apply sub_replace_outside 0 flat (i*width) ((i+1)*width) (row*width+column) value (by omega) (by omega) (by omega)
    by_cases hl : row<i
    · have hm := Int.mul_le_mul_of_nonneg_right (by omega : row+1≤i) (Int.le_of_lt hw)
      rw [Int.add_mul,Int.one_mul] at hm
      exact Or.inl (by omega)
    · have hm := Int.mul_le_mul_of_nonneg_right (by omega : i+1≤row) (Int.le_of_lt hw)
      exact Or.inr (by omega)

theorem FlatRows_replace_cell__scan_row_swap :
  ∀ flat rows count width row column value,
    FlatRows flat rows count width →
    (0 : Int) < width → ((0 : Int) ≤ row ∧ row < count) → ((0 : Int) ≤ column ∧ column < width) →
    FlatRows
      (replace_Znth (row * width + column) value flat)
      (replace_Znth row
        (replace_Znth column value (Znth row rows [])) rows)
      count width := by
  intro flat rows count width row column value hf hw hr hc
  refine ⟨by simpa only [Zlength_replace_Znth] using hf.1,
    by simpa only [Zlength_replace_Znth] using hf.2.1,?_⟩
  intro i hi
  rw [read_set [] rows row i _ (by have := hf.2.1; omega) (by have := hf.2.1; omega),
    sublist_replace_flat_cell__scan_row_swap flat count width row column i value hf.1 hw hr hc hi]
  by_cases he : i=row
  · rw [if_pos he,if_pos he,he,hf.2.2 row hr]
  · rw [if_neg he,if_neg he,hf.2.2 i hi]

theorem FlatRows_Znth_cell__scan_row_swap :
  ∀ flat rows count width row column,
    FlatRows flat rows count width → ((0 : Int) ≤ row ∧ row < count) → ((0 : Int) ≤ column ∧ column < width) →
    Znth (row * width + column) flat (0 : Int) =
    Znth column (Znth row rows []) (0 : Int) := by
  exact FlatRows_Znth__compare_left_digit

theorem prefix_row_at_progress__scan_row_swap :
  ∀ (first_row second_row : List Int) progress width,
    Zlength first_row = width →
    Zlength second_row = width → ((0 : Int) ≤ progress ∧ progress < width) →
    Znth progress
      (sublist (0 : Int) progress second_row ++
       sublist progress width first_row) (0 : Int) =
    Znth progress first_row (0 : Int) := by
  intro first_row second_row progress width hf hs hp
  have hlen := prefix_len second_row progress (by omega)
  rw [app_Znth2 0 _ _ progress (by omega),hlen,Int.sub_self,Znth_sublist 0 progress 0 width first_row hp.1 (by omega)]
  simp

theorem replace_Znth_comm__scan_row_swap :
  ∀ {A : Type} (xs : List A) i j (a b : A),
    (0 : Int) ≤ i →
    (0 : Int) ≤ j →
    i ≠ j →
    replace_Znth j b (replace_Znth i a xs) =
    replace_Znth i a (replace_Znth j b xs) := by
  intro A xs i j a b hi hj hne
  apply nth_set_comm
  omega

theorem replace_Znth_overwrite__scan_row_swap :
  ∀ {A : Type} (xs : List A) i (a b : A),
    replace_Znth i b (replace_Znth i a xs) =
    replace_Znth i b xs := by
  intro A xs i a b
  exact nth_set_twice i.toNat xs a b

theorem SwapRowsPrefix_step__scan_row_swap :
  ∀ before now first second progress width count,
    Zlength before = count → ((0 : Int) ≤ first ∧ first < count) → ((0 : Int) ≤ second ∧ second < count) →
    first ≠ second →
    Zlength (Znth first before []) = width →
    Zlength (Znth second before []) = width → ((0 : Int) ≤ progress ∧ progress < width) →
    SwapRowsPrefix before now first second progress width →
    SwapRowsPrefix before
      (replace_Znth second
        (replace_Znth progress (Znth progress (Znth first now []) (0 : Int))
          (Znth second now []))
        (replace_Znth first
          (replace_Znth progress (Znth progress (Znth second now []) (0 : Int))
            (Znth first now []))
          now))
      first second (progress + (1 : Int)) width := by
  intro before now first second progress width count hlen hf hs hne hfw hsw hp hc
  let fr := Znth first before []
  let sr := Znth second before []
  let fm := sublist 0 progress sr++sublist progress width fr
  let sm := sublist 0 progress fr++sublist progress width sr
  have hn : now=replace_Znth second sm (replace_Znth first fm before) := hc
  have hfr : 0≤first ∧ first<Zlength before := by omega
  have hsr : 0≤second ∧ second<Zlength before := by omega
  have hfn : Znth first now []=fm := by
    rw [hn,Znth_replace_Znth_Diff [] (replace_Znth first fm before) second first sm
      (by simpa only [Zlength_replace_Znth] using hsr) (by simpa only [Zlength_replace_Znth] using hfr) hne.symm,
      Znth_replace_Znth_Same [] before first fm hfr]
  have hsn : Znth second now []=sm := by
    rw [hn,Znth_replace_Znth_Same [] (replace_Znth first fm before) second sm (by simpa only [Zlength_replace_Znth] using hsr)]
  have hfp : Znth progress fm 0=Znth progress fr 0 := prefix_row_at_progress__scan_row_swap fr sr progress width hfw hsw hp
  have hsp : Znth progress sm 0=Znth progress sr 0 := prefix_row_at_progress__scan_row_swap sr fr progress width hsw hfw hp
  have hfa := advance_prefix_row__scan_row_swap fr sr progress width hfw hsw hp
  have hsa := advance_prefix_row__scan_row_swap sr fr progress width hsw hfw hp
  change replace_Znth progress (Znth progress sr 0) fm = _ at hfa
  change replace_Znth progress (Znth progress fr 0) sm = _ at hsa
  dsimp only [SwapRowsPrefix]
  rw [hfn,hsn,hfp,hsp,hfa,hsa,hn]
  rw [replace_Znth_comm__scan_row_swap (replace_Znth first fm before) second first sm
    (sublist 0 (progress+1) sr++sublist (progress+1) width fr) hs.1 hf.1 hne.symm]
  simp only [replace_Znth_overwrite__scan_row_swap]
  rfl

theorem SwapRowsPrefix_same__scan_row_swap :
  ∀ before index progress width,
    Zlength (Znth index before []) = width → ((0 : Int) ≤ progress ∧ progress ≤ width) →
    SwapRowsPrefix before before index index progress width := by
  intro before index progress width hw hp
  have he : sublist 0 progress (Znth index before [])++sublist progress width (Znth index before [])=Znth index before [] := by
    rw [←sublist_split 0 width progress _ (by omega) (by omega),sublist_self _ width hw.symm]
  dsimp only [SwapRowsPrefix]
  rw [he]
  simp only [replace_Znth_Znth]

theorem FlatRows_swap_progress_step__scan_row_swap :
  ∀ flat before now count width first second progress,
    FlatRows flat now count width →
    Zlength before = count → ((0 : Int) ≤ first ∧ first < count) → ((0 : Int) ≤ second ∧ second < count) →
    Zlength (Znth first before []) = width →
    Zlength (Znth second before []) = width → ((0 : Int) ≤ progress ∧ progress < width) →
    SwapRowsPrefix before now first second progress width →
    ∃ next,
      FlatRows
        (replace_Znth (second * width + progress)
          (Znth (first * width + progress) flat (0 : Int))
          (replace_Znth (first * width + progress)
            (Znth (second * width + progress) flat (0 : Int)) flat))
        next count width ∧
      SwapRowsPrefix before next first second (progress + (1 : Int)) width := by
  intro flat before now count width first second progress hf hlen hfirst hsecond hfw hsw hp hc
  by_cases he : first=second
  · subst second
    have hmix : sublist 0 progress (Znth first before [])++sublist progress width (Znth first before [])=Znth first before [] := by
      rw [←sublist_split 0 width progress _ (by omega) (by omega),sublist_self _ width hfw.symm]
    dsimp only [SwapRowsPrefix] at hc
    rw [hmix] at hc
    simp only [replace_Znth_Znth] at hc
    subst now
    refine ⟨before,?_,SwapRowsPrefix_same__scan_row_swap before first (progress+1) width hfw (by omega)⟩
    simpa only [replace_Znth_Znth] using hf
  · let firstValue := Znth (first*width+progress) flat 0
    let secondValue := Znth (second*width+progress) flat 0
    let once := replace_Znth first (replace_Znth progress secondValue (Znth first now [])) now
    let next := replace_Znth second (replace_Znth progress firstValue (Znth second now [])) once
    have hn := hf.2.1
    have hone := FlatRows_replace_cell__scan_row_swap flat now count width first progress secondValue hf (by omega) hfirst hp
    have hsame : Znth second once []=Znth second now [] := by
      exact Znth_replace_Znth_Diff [] now first second _ (by omega) (by omega) he
    have htwo := FlatRows_replace_cell__scan_row_swap
      (replace_Znth (first*width+progress) secondValue flat) once count width second progress firstValue hone (by omega) hsecond hp
    rw [hsame] at htwo
    refine ⟨next,htwo,?_⟩
    have hfv : firstValue=Znth progress (Znth first now []) 0 := FlatRows_Znth__compare_left_digit flat now count width first progress hf hfirst hp
    have hsv : secondValue=Znth progress (Znth second now []) 0 := FlatRows_Znth__compare_left_digit flat now count width second progress hf hsecond hp
    dsimp only [next,once]
    rw [hfv,hsv]
    exact SwapRowsPrefix_step__scan_row_swap before now first second progress width count hlen hfirst hsecond he hfw hsw hp hc

theorem ConcatCompareOutcome_nonpositive_not_item_before__scan_advance :
  ∀ rows lens i j comparison,
    ConcatCompareOutcome rows lens i j comparison →
    comparison ≤ (0 : Int) →
    ¬ item_before rows lens i j := by
  intro rows lens i j comparison hc hnon hg
  rcases hg with ⟨hlen,t,ht,hpre,hgt⟩
  rcases hc with ⟨heq,he⟩|⟨k,hk,hlen',hprek,hne,hcmp⟩
  · rw [he] at hgt
    omega
  · by_cases hkt : k<t
    · exact hne (hpre k ⟨hk.1,hkt⟩)
    · by_cases htk : t<k
      · have he := hprek t ⟨ht.1,htk⟩
        omega
      · have he : t=k := by omega
        subst t
        omega

theorem PartitionScanState_advance_nonbefore__scan_advance :
  ∀ rows0 rows1 lens0 lens1 low high boundary scan,
    PartitionScanState rows0 rows1 lens0 lens1 low high boundary scan →
    ¬ item_before rows1 lens1 scan high →
    PartitionScanState rows0 rows1 lens0 lens1 low high boundary (scan + (1 : Int)) := by
  intro rows0 rows1 lens0 lens1 low high boundary scan hs hn
  refine ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
  intro k hk
  by_cases he : k=scan
  · subst k; exact hn
  · exact hs.2.2.2.2 k (by omega)

theorem ConcatCompareOutcome_positive_item_before__scan_advance :
  ∀ rows lens i j comparison,
    ConcatCompareOutcome rows lens i j comparison →
    comparison > (0 : Int) →
    item_before rows lens i j := by
  intro rows lens i j comparison hc hpos
  rcases hc with ⟨heq,he⟩|⟨k,hk,hlen,hpre,hne,hcmp⟩
  · omega
  · exact ⟨hlen,k,hk,hpre,by omega⟩

theorem Zlength_swap_Znth__scan_advance :
  ∀ (A : Type) (d : A) i j (xs : List A),
    Zlength (swap_Znth d i j xs) = Zlength xs := by
  intros
  simp only [swap_Znth,Zlength_replace_Znth]

theorem Znth_swap_Znth_left__scan_advance :
  ∀ (A : Type) (d : A) i j (xs : List A), ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) →
    Znth i (swap_Znth d i j xs) d = Znth j xs d := by
  intro A d i j xs hi hj
  by_cases he : i=j
  · subst j
    simp only [swap_Znth,replace_Znth_Znth]
  · unfold swap_Znth
    rw [Znth_replace_Znth_Diff d _ j i _ (by simpa only [Zlength_replace_Znth] using hj)
      (by simpa only [Zlength_replace_Znth] using hi) (Ne.symm he),Znth_replace_Znth_Same d xs i _ hi]

theorem Znth_swap_Znth_right__scan_advance :
  ∀ (A : Type) (d : A) i j (xs : List A), ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) →
    Znth j (swap_Znth d i j xs) d = Znth i xs d := by
  intro A d i j xs hi hj
  exact Znth_replace_Znth_Same d _ j _ (by simpa only [Zlength_replace_Znth] using hj)

theorem Znth_swap_Znth_diff__scan_advance :
  ∀ (A : Type) (d : A) i j k (xs : List A), ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) → ((0 : Int) ≤ k ∧ k < Zlength xs) →
    k ≠ i →
    k ≠ j →
    Znth k (swap_Znth d i j xs) d = Znth k xs d := by
  intro A d i j k xs hi hj hk hki hkj
  unfold swap_Znth
  rw [Znth_replace_Znth_Diff d _ j k _ (by simpa only [Zlength_replace_Znth] using hj)
    (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm hkj),
    Znth_replace_Znth_Diff d xs i k _ hi hk (Ne.symm hki)]

theorem item_at_swap_left__scan_advance :
  ∀ rows lens i j, ((0 : Int) ≤ i ∧ i < Zlength rows) → ((0 : Int) ≤ j ∧ j < Zlength rows) →
    Zlength rows = Zlength lens →
    item_at (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens) i =
    item_at rows lens j := by
  intro rows lens i j hi hj hlen
  unfold item_at
  rw [Znth_swap_Znth_left__scan_advance _ [] i j rows hi hj,Znth_swap_Znth_left__scan_advance _ 0 i j lens (by omega) (by omega)]

theorem item_at_swap_right__scan_advance :
  ∀ rows lens i j, ((0 : Int) ≤ i ∧ i < Zlength rows) → ((0 : Int) ≤ j ∧ j < Zlength rows) →
    Zlength rows = Zlength lens →
    item_at (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens) j =
    item_at rows lens i := by
  intro rows lens i j hi hj hlen
  unfold item_at
  rw [Znth_swap_Znth_right__scan_advance _ [] i j rows hi hj,Znth_swap_Znth_right__scan_advance _ 0 i j lens (by omega) (by omega)]

theorem item_at_swap_diff__scan_advance :
  ∀ rows lens i j k, ((0 : Int) ≤ i ∧ i < Zlength rows) → ((0 : Int) ≤ j ∧ j < Zlength rows) → ((0 : Int) ≤ k ∧ k < Zlength rows) →
    Zlength rows = Zlength lens →
    k ≠ i →
    k ≠ j →
    item_at (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens) k =
    item_at rows lens k := by
  intro rows lens i j k hi hj hk hlen hki hkj
  unfold item_at
  rw [Znth_swap_Znth_diff__scan_advance _ [] i j k rows hi hj hk hki hkj,Znth_swap_Znth_diff__scan_advance _ 0 i j k lens (by omega) (by omega) (by omega) hki hkj]

theorem RowsWellFormed_swap_Znth__scan_advance :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) →
    RowsWellFormed
      (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens) count width := by
  intro rows lens count width i j hw hi hj
  refine ⟨by simpa only [Zlength_swap_Znth__scan_advance] using hw.1,
    by simpa only [Zlength_swap_Znth__scan_advance] using hw.2.1,?_⟩
  have hir : 0≤i ∧ i<Zlength rows := by have := hw.1; omega
  have hjr : 0≤j ∧ j<Zlength rows := by have := hw.1; omega
  have hil : 0≤i ∧ i<Zlength lens := by have := hw.2.1; omega
  have hjl : 0≤j ∧ j<Zlength lens := by have := hw.2.1; omega
  intro k hk
  by_cases hki : k=i
  · subst k
    rw [Znth_swap_Znth_left__scan_advance _ [] i j rows hir hjr,Znth_swap_Znth_left__scan_advance _ 0 i j lens hil hjl]
    exact hw.2.2 j hj
  · by_cases hkj : k=j
    · subst k
      rw [Znth_swap_Znth_right__scan_advance _ [] i j rows hir hjr,Znth_swap_Znth_right__scan_advance _ 0 i j lens hil hjl]
      exact hw.2.2 i hi
    · rw [Znth_swap_Znth_diff__scan_advance _ [] i j k rows hir hjr (by have := hw.1; omega) hki hkj,
        Znth_swap_Znth_diff__scan_advance _ 0 i j k lens hil hjl (by have := hw.2.1; omega) hki hkj]
      exact hw.2.2 k hk

theorem SwapRowsPrefix_complete__scan_advance :
  ∀ before after lens count width first second progress,
    RowsWellFormed before lens count width → ((0 : Int) ≤ first ∧ first < count) → ((0 : Int) ≤ second ∧ second < count) →
    progress = width →
    SwapRowsPrefix before after first second progress width →
    after = swap_Znth [] first second before := by
  intro before after lens count width first second progress hw hf hs he hc
  subst progress
  exact swap_complete_core before after first second width (hw.2.2 first hf).1 (hw.2.2 second hs).1 hc

theorem sum_permutation__scan_advance :
  ∀ xs ys, Permutation xs ys → sum xs = sum ys := by
  intro xs ys hp
  induction hp with
  | nil => rfl
  | cons a hp ih => change a+sum _=a+sum _; rw [ih]
  | swap a b l => simp only [sum,List.foldr_cons]; omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem replace_Znth_swap_form__scan_advance :
  ∀ (A : Type) (l1 l2 l3 : List A) (xi xj : A),
    replace_Znth (Zlength l1 + (1 : Int) + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3 := by
  intro A l1 l2 l3 xi xj
  have hidx : (Zlength l1+1+Zlength l2).toNat=l1.length+1+l2.length := by simp only [Zlength,Int.ofNat_eq_coe]; omega
  unfold replace_Znth
  rw [hidx]
  simp only [replace_nth_eq_set]
  change ((l1++xi::l2++xj::l3).set l1.length xj).set (l1.length+1+l2.length) xi = _
  simp only [List.append_assoc,List.cons_append]
  rw [List.set_append_right l1.length xj (by omega)]
  simp only [Nat.sub_self,List.set_cons_zero]
  rw [List.set_append_right (l1.length+1+l2.length) xi (by omega)]
  have hi : l1.length+1+l2.length-l1.length=l2.length+1 := by omega
  rw [hi]
  simp only [List.set_cons_succ]
  rw [List.set_append_right l2.length xi (by omega)]
  simp only [Nat.sub_self,List.set_cons_zero]

theorem permutation_swap_Znth_lt__scan_advance :
  ∀ (A : Type) (l : List A) i j (d : A),
    (0 : Int) ≤ i ∧ i < j ∧ j < Zlength l →
    Permutation l (swap_Znth d i j l) := by
  intro A l i j d h
  apply permutation_swap_nat
  · omega
  · simp only [Zlength,Int.ofNat_eq_coe] at h; omega

theorem replace_nth_comm__scan_advance :
  ∀ (A : Type) ni nj (l : List A) a b,
    ni ≠ nj →
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a := by
  exact fun _ => nth_set_comm

theorem replace_Znth_comm__scan_advance :
  ∀ (A : Type) (l : List A) i j a b,
    (0 : Int) ≤ i →
    (0 : Int) ≤ j →
    i ≠ j →
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l) := by
  intro A l i j a b hi hj hne
  apply nth_set_comm
  omega

theorem permutation_swap_Znth__scan_advance :
  ∀ (A : Type) (l : List A) i j (d : A), ((0 : Int) ≤ i ∧ i < Zlength l) → ((0 : Int) ≤ j ∧ j < Zlength l) →
    Permutation l (swap_Znth d i j l) := by
  intro A l i j d hi hj
  by_cases he : i=j
  · subst j
    simp only [swap_Znth,replace_Znth_Znth]
    exact List.Perm.refl _
  · by_cases hlt : i<j
    · exact permutation_swap_Znth_lt__scan_advance A l i j d ⟨hi.1,hlt,hj.2⟩
    · unfold swap_Znth
      rw [replace_Znth_comm__scan_advance A l i j _ _ hi.1 hj.1 he]
      exact permutation_swap_Znth_lt__scan_advance A l j i d ⟨hj.1,by omega,hi.2⟩

theorem map_replace_Znth__scan_advance :
  ∀ (A B : Type) (f : A → B) n x (xs : List A),
    List.map f (replace_Znth n x xs) =
    replace_Znth n (f x) (List.map f xs) := by
  intro A B f n x xs
  unfold replace_Znth
  generalize n.toNat=k
  induction xs generalizing k with
  | nil => simp [replace_nth]
  | cons a xs ih => cases k <;> simp_all [replace_nth]

theorem map_swap_Znth__scan_advance :
  ∀ (A B : Type) (f : A → B) d i j (xs : List A),
    List.map f (swap_Znth d i j xs) =
    swap_Znth (f d) i j (List.map f xs) := by
  intro A B f d i j xs
  have hm (k : Int) : f (Znth k xs d)=Znth k (xs.map f) (f d) := by
    unfold Znth
    generalize k.toNat=n
    induction xs generalizing n with
    | nil => simp
    | cons a xs ih => cases n <;> simp_all
  unfold swap_Znth
  rw [map_replace_Znth__scan_advance,map_replace_Znth__scan_advance,hm,hm]

theorem map_fst_combine__scan_advance :
  ∀ (A B : Type) (xs : List A) (ys : List B),
    List.length xs = List.length ys →
    List.map Prod.fst (List.zip xs ys) = xs := by
  intro A B xs ys he
  exact List.map_fst_zip (by omega)

theorem map_snd_combine__scan_advance :
  ∀ (A B : Type) (xs : List A) (ys : List B),
    List.length xs = List.length ys →
    List.map Prod.snd (List.zip xs ys) = ys := by
  intro A B xs ys he
  exact List.map_snd_zip (by omega)

theorem combine_map_fst_snd__scan_advance :
  ∀ (A B : Type) (ps : List (A × B)),
    List.zip (List.map Prod.fst ps) (List.map Prod.snd ps) = ps := by
  intro A B ps
  induction ps with
  | nil => rfl
  | cons a ps ih => cases a; simp only [List.map_cons,List.zip_cons_cons,ih]

theorem paired_items_swap_eq__scan_advance :
  ∀ rows lens i j,
    Zlength rows = Zlength lens →
    paired_items (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens) =
    swap_Znth ([], (0 : Int)) i j (paired_items rows lens) := by
  intro rows lens i j he
  have hlen : rows.length=lens.length := by simp only [Zlength,Int.ofNat_eq_coe] at he; omega
  have hf := map_fst_combine__scan_advance (List Int) Int rows lens hlen
  have hs := map_snd_combine__scan_advance (List Int) Int rows lens hlen
  let ps := paired_items rows lens
  have hmapf := map_swap_Znth__scan_advance number_item (List Int) Prod.fst ([],0) i j ps
  have hmaps := map_swap_Znth__scan_advance number_item Int Prod.snd ([],0) i j ps
  unfold paired_items at *
  dsimp [ps,paired_items,number_item] at hmapf hmaps
  rw [hf] at hmapf
  rw [hs] at hmaps
  rw [←hmapf,←hmaps]
  exact combine_map_fst_snd__scan_advance (List Int) Int _

theorem paired_items_swap_permutation__scan_advance :
  ∀ rows lens i j,
    Zlength rows = Zlength lens → ((0 : Int) ≤ i ∧ i < Zlength rows) → ((0 : Int) ≤ j ∧ j < Zlength rows) →
    Permutation (paired_items rows lens)
      (paired_items (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens)) := by
  intro rows lens i j he hi hj
  rw [paired_items_swap_eq__scan_advance rows lens i j he]
  have hlen : Zlength (paired_items rows lens)=Zlength rows := by
    unfold paired_items Zlength number_item at *
    simp only [List.length_zip,Int.ofNat_eq_coe] at *
    omega
  exact permutation_swap_Znth__scan_advance _ _ i j ([],0) (by omega) (by omega)

theorem PartitionScanState_swap_advance__scan_advance :
  ∀ original_rows before original_lens lens
         count width low high boundary scan comparison,
    RowsWellFormed before lens count width →
    PartitionScanState original_rows before original_lens lens
      low high (boundary - (1 : Int)) scan →
    ConcatCompareOutcome before lens scan high comparison →
    comparison > (0 : Int) →
    (0 : Int) ≤ low →
    low ≤ boundary →
    boundary ≤ scan →
    scan < high →
    high < count →
    PartitionScanState original_rows
      (swap_Znth [] boundary scan before)
      original_lens (swap_Znth (0 : Int) boundary scan lens)
      low high boundary (scan + (1 : Int)) := by
  intro orows rows olens lens count width low high boundary scan cmp hw hs hc hcmp hlo hlb hbs hsh hhc
  have hr := hw.1
  have hl := hw.2.1
  have he : Zlength rows=Zlength lens := by omega
  have hb : 0≤boundary ∧ boundary<Zlength rows := by omega
  have hscan : 0≤scan ∧ scan<Zlength rows := by omega
  have hhigh := item_at_swap_diff__scan_advance rows lens boundary scan high hb hscan (by omega) he (by omega) (by omega)
  have hleft := item_at_swap_left__scan_advance rows lens boundary scan hb hscan he
  have hright := item_at_swap_right__scan_advance rows lens boundary scan hb hscan he
  have hpos := ConcatCompareOutcome_positive_item_before__scan_advance rows lens scan high cmp hc hcmp
  refine ⟨⟨hs.1.1,by simpa only [Zlength_swap_Znth__scan_advance] using he,
      hs.1.2.2.trans (paired_items_swap_permutation__scan_advance rows lens boundary scan he hb hscan)⟩,?_,?_,?_,?_⟩
  · refine ⟨by rw [Zlength_swap_Znth__scan_advance]; exact hs.2.1.1,
      by rw [Zlength_swap_Znth__scan_advance]; exact hs.2.1.2.1,?_⟩
    intro k hk hout
    have horig := hs.2.1.1
    rw [item_at_swap_diff__scan_advance rows lens boundary scan k hb hscan (by omega) he
      (by rcases hout with h|h <;> omega) (by rcases hout with h|h <;> omega)]
    exact hs.2.1.2.2 k hk hout
  · exact hhigh.trans hs.2.2.1
  · intro k hk
    unfold item_before
    rw [hhigh]
    by_cases hkb : k=boundary
    · subst k
      rw [hleft]
      exact hpos
    · rw [item_at_swap_diff__scan_advance rows lens boundary scan k hb hscan (by omega) he hkb (by omega)]
      exact hs.2.2.2.1 k (by omega)
  · intro k hk
    unfold item_before
    rw [hhigh]
    by_cases hks : k=scan
    · subst k
      rw [hright]
      exact hs.2.2.2.2 boundary (by omega)
    · rw [item_at_swap_diff__scan_advance rows lens boundary scan k hb hscan (by omega) he (by omega) hks]
      exact hs.2.2.2.2 k (by omega)

theorem SwapRowsPrefix_zero__scan_advance :
  ∀ rows lens count width first second,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ first ∧ first < count) → ((0 : Int) ≤ second ∧ second < count) →
    SwapRowsPrefix rows rows first second (0 : Int) width := by
  exact SwapRowsPrefix_zero__scan_row_swap

theorem FlatRows_replace_cell__pivot_finalization :
  ∀ flat rows count width row column value,
    FlatRows flat rows count width → ((0 : Int) ≤ row ∧ row < count) → ((0 : Int) ≤ column ∧ column < width) →
    FlatRows
      (replace_Znth (row * width + column) value flat)
      (replace_Znth row
        (replace_Znth column value (Znth row rows [])) rows)
      count width := by
  intro flat rows count width row column value hf hr hc
  exact FlatRows_replace_cell__scan_row_swap flat rows count width row column value hf (by omega) hr hc

theorem FlatRows_Znth_cell__pivot_finalization :
  ∀ flat rows count width row column,
    FlatRows flat rows count width → ((0 : Int) ≤ row ∧ row < count) → ((0 : Int) ≤ column ∧ column < width) →
    Znth (row * width + column) flat (0 : Int) =
    Znth column (Znth row rows []) (0 : Int) := by
  exact FlatRows_Znth__compare_left_digit

theorem row_prefix_replace_advance__pivot_finalization :
  ∀ first_row second_row progress width,
    Zlength first_row = width →
    Zlength second_row = width → ((0 : Int) ≤ progress ∧ progress < width) →
    replace_Znth progress (Znth progress second_row (0 : Int))
      (sublist (0 : Int) progress second_row ++
       sublist progress width first_row) =
    sublist (0 : Int) (progress + (1 : Int)) second_row ++
    sublist (progress + (1 : Int)) width first_row := by
  exact advance_prefix_row__scan_row_swap

theorem Znth_prefix_mix_boundary__pivot_finalization :
  ∀ first_row second_row progress width,
    Zlength first_row = width →
    Zlength second_row = width → ((0 : Int) ≤ progress ∧ progress < width) →
    Znth progress
      (sublist (0 : Int) progress second_row ++
       sublist progress width first_row) (0 : Int) =
    Znth progress first_row (0 : Int) := by
  exact prefix_row_at_progress__scan_row_swap

theorem replace_nth_comm__pivot_finalization :
  ∀ {A : Type} ni nj (l : List A) a b,
    ni ≠ nj →
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a := by
  intros
  apply nth_set_comm
  assumption

theorem replace_Znth_comm__pivot_finalization :
  ∀ {A : Type} (l : List A) i j a b,
    (0 : Int) ≤ i →
    (0 : Int) ≤ j →
    i ≠ j →
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l) := by
  intro A l i j a b hi hj hne
  apply nth_set_comm
  omega

theorem replace_nth_twice__pivot_finalization :
  ∀ {A : Type} n (l : List A) a b,
    replace_nth n (replace_nth n l a) b =
    replace_nth n l b := by
  intros
  apply nth_set_twice

theorem replace_Znth_twice__pivot_finalization :
  ∀ {A : Type} (l : List A) i a b,
    replace_Znth i b (replace_Znth i a l) =
    replace_Znth i b l := by
  exact replace_Znth_overwrite__scan_row_swap

theorem SwapRowsPrefix_advance_distinct__pivot_finalization :
  ∀ before current first second progress width, ((0 : Int) ≤ first ∧ first < second) →
    second < Zlength before →
    Zlength (Znth first before []) = width →
    Zlength (Znth second before []) = width → ((0 : Int) ≤ progress ∧ progress < width) →
    SwapRowsPrefix before current first second progress width →
    SwapRowsPrefix before
      (replace_Znth second
        (replace_Znth progress
          (Znth progress (Znth first current []) (0 : Int))
          (Znth second current []))
        (replace_Znth first
          (replace_Znth progress
            (Znth progress (Znth second current []) (0 : Int))
            (Znth first current []))
          current))
      first second (progress + (1 : Int)) width := by
  intro before current first second progress width hf hs hfw hsw hp hcur
  exact SwapRowsPrefix_step__scan_row_swap before current first second progress width (Zlength before)
    rfl (by omega) (by omega) (by omega) hfw hsw hp hcur

theorem SwapRowsPrefix_same_current__pivot_finalization :
  ∀ before current index progress width,
    Zlength (Znth index before []) = width → ((0 : Int) ≤ progress ∧ progress ≤ width) →
    SwapRowsPrefix before current index index progress width →
    current = before := by
  intro before current index progress width hw hp hc
  have hrefl := SwapRowsPrefix_same__scan_row_swap before index progress width hw hp
  exact hc.trans hrefl.symm

theorem SwapRowsPrefix_same_refl__pivot_finalization :
  ∀ before index progress width,
    Zlength (Znth index before []) = width → ((0 : Int) ≤ progress ∧ progress ≤ width) →
    SwapRowsPrefix before before index index progress width := by
  exact SwapRowsPrefix_same__scan_row_swap

theorem swap_Znth_length__pivot_finalization :
  ∀ {A : Type} (d : A) i j xs,
    Zlength (swap_Znth d i j xs) = Zlength xs := by
  exact Zlength_swap_Znth__scan_advance _

theorem swap_Znth_left__pivot_finalization :
  ∀ {A : Type} (d : A) i j xs, ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) →
    Znth i (swap_Znth d i j xs) d = Znth j xs d := by
  exact Znth_swap_Znth_left__scan_advance _

theorem swap_Znth_right__pivot_finalization :
  ∀ {A : Type} (d : A) i j xs, ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) →
    Znth j (swap_Znth d i j xs) d = Znth i xs d := by
  exact Znth_swap_Znth_right__scan_advance _

theorem swap_Znth_other__pivot_finalization :
  ∀ {A : Type} (d : A) i j k xs, ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) → ((0 : Int) ≤ k ∧ k < Zlength xs) →
    k ≠ i → k ≠ j →
    Znth k (swap_Znth d i j xs) d = Znth k xs d := by
  exact Znth_swap_Znth_diff__scan_advance _

theorem swap_Znth_reverse__pivot_finalization :
  ∀ {A : Type} (d : A) i j xs,
    (0 : Int) ≤ i → (0 : Int) ≤ j →
    replace_Znth i (Znth j xs d)
      (replace_Znth j (Znth i xs d) xs) =
    swap_Znth d i j xs := by
  intro A d i j xs hi hj
  by_cases he : i=j
  · subst j; rfl
  · exact (replace_Znth_comm__scan_advance A xs i j _ _ hi hj he).symm

theorem SwapRowsPrefix_complete__pivot_finalization :
  ∀ before after first second width,
    Zlength (Znth first before []) = width →
    Zlength (Znth second before []) = width →
    SwapRowsPrefix before after first second width width →
    after = swap_Znth [] first second before := by
  exact swap_complete_core

theorem paired_items_length__pivot_finalization :
  ∀ rows lens,
    Zlength rows = Zlength lens →
    Zlength (paired_items rows lens) = Zlength rows := by
  intro rows lens he
  unfold paired_items Zlength number_item at *
  simp only [List.length_zip,Int.ofNat_eq_coe] at *
  omega

theorem Znth_paired_items__pivot_finalization :
  ∀ rows lens i,
    Zlength rows = Zlength lens → ((0 : Int) ≤ i ∧ i < Zlength rows) →
    Znth i (paired_items rows lens) ([], (0 : Int)) = item_at rows lens i := by
  intro rows lens i he hi
  have h1 : i.toNat<rows.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  have h2 : i.toNat<lens.length := by simp only [Zlength,Int.ofNat_eq_coe] at he hi; omega
  simp only [paired_items,item_at,Znth,List.getD_eq_getElem?_getD,List.zip_eq_zipWith,List.getElem?_zipWith,
    List.getElem?_eq_getElem h1,List.getElem?_eq_getElem h2,Option.bind_some,Option.map_some,Option.getD_some]

theorem paired_items_swap__pivot_finalization :
  ∀ rows lens i j,
    Zlength rows = Zlength lens → ((0 : Int) ≤ i ∧ i < Zlength rows) → ((0 : Int) ≤ j ∧ j < Zlength rows) →
    paired_items (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens) =
    swap_Znth ([], (0 : Int)) i j (paired_items rows lens) := by
  intro rows lens i j he _ _
  exact paired_items_swap_eq__scan_advance rows lens i j he

theorem replace_Znth_swap_form__pivot_finalization :
  ∀ {A : Type} (l1 l2 l3 : List A) xi xj,
    replace_Znth (Zlength l1 + (1 : Int) + Zlength l2) xi
      (replace_Znth (Zlength l1) xj
        (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3 := by
  intro A
  exact replace_Znth_swap_form__scan_advance A

theorem permutation_swap_Znth_lt__pivot_finalization :
  ∀ {A : Type} (xs : List A) i j d, ((0 : Int) ≤ i ∧ i < j) →
    j < Zlength xs →
    Permutation xs (swap_Znth d i j xs) := by
  intro A xs i j d hi hj
  exact permutation_swap_Znth_lt__scan_advance A xs i j d ⟨hi.1,hi.2,hj⟩

theorem permutation_swap_Znth__pivot_finalization :
  ∀ {A : Type} (xs : List A) i j d, ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) →
    Permutation xs (swap_Znth d i j xs) := by
  exact permutation_swap_Znth__scan_advance _

theorem RowsWellFormed_swap__pivot_finalization :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) →
    RowsWellFormed (swap_Znth [] i j rows) (swap_Znth (0 : Int) i j lens)
      count width := by
  exact RowsWellFormed_swap_Znth__scan_advance

theorem PairedPermutation_swap__pivot_finalization :
  ∀ original_rows rows original_lens lens i j,
    PairedPermutation original_rows rows original_lens lens →
    Zlength rows = Zlength lens → ((0 : Int) ≤ i ∧ i < Zlength rows) → ((0 : Int) ≤ j ∧ j < Zlength rows) →
    PairedPermutation original_rows (swap_Znth [] i j rows)
      original_lens (swap_Znth (0 : Int) i j lens) := by
  intro original_rows rows original_lens lens i j hp he hi hj
  refine ⟨hp.1,?_,hp.2.2.trans (paired_items_swap_permutation__scan_advance rows lens i j he hi hj)⟩
  simpa only [Zlength_swap_Znth__scan_advance] using he

theorem SameOutsidePairedRange_swap_inside__pivot_finalization :
  ∀ original_rows rows original_lens lens low high i j,
    SameOutsidePairedRange original_rows rows original_lens lens low high →
    Zlength rows = Zlength lens → ((0 : Int) ≤ i ∧ i < Zlength rows) → ((0 : Int) ≤ j ∧ j < Zlength rows) → (low ≤ i ∧ i ≤ high) → (low ≤ j ∧ j ≤ high) →
    SameOutsidePairedRange original_rows (swap_Znth [] i j rows)
      original_lens (swap_Znth (0 : Int) i j lens) low high := by
  intro orows rows olens lens low high i j hs he hi hj hli hlj
  refine ⟨by rw [Zlength_swap_Znth__scan_advance]; exact hs.1,
    by rw [Zlength_swap_Znth__scan_advance]; exact hs.2.1,?_⟩
  intro k hk hout
  have hr := hs.1
  rw [item_at_swap_diff__scan_advance rows lens i j k hi hj (by omega) he (by rcases hout with h|h <;> omega) (by rcases hout with h|h <;> omega)]
  exact hs.2.2 k hk hout

theorem PartitionScanState_finalize__pivot_finalization :
  ∀ original_rows rows original_lens lens count width low high pivot,
    RowsWellFormed rows lens count width →
    PartitionScanState original_rows rows original_lens lens
      low high (pivot - (1 : Int)) high →
    (0 : Int) ≤ low → low < high → high < count → (low ≤ pivot ∧ pivot ≤ high) →
    GreedyPartitionedAt
      (swap_Znth [] pivot high rows)
      (swap_Znth (0 : Int) pivot high lens) low high pivot := by
  intro orows rows olens lens count width low high pivot hw hs hlo hlh hhi hpb
  have hr := hw.1
  have hl := hw.2.1
  have hi : 0≤pivot ∧ pivot<Zlength rows := by omega
  have hj : 0≤high ∧ high<Zlength rows := by omega
  have he : Zlength rows=Zlength lens := by omega
  have hp := item_at_swap_left__scan_advance rows lens pivot high hi hj he
  refine ⟨hpb,?_,?_⟩
  · intro k hk
    unfold item_before
    rw [hp,item_at_swap_diff__scan_advance rows lens pivot high k hi hj (by omega) he (by omega) (by omega)]
    exact hs.2.2.2.1 k (by omega)
  · intro k hk
    unfold item_before
    rw [hp]
    by_cases hkh : k=high
    · subst k
      rw [item_at_swap_right__scan_advance rows lens pivot high hi hj he]
      exact hs.2.2.2.2 pivot (by omega)
    · rw [item_at_swap_diff__scan_advance rows lens pivot high k hi hj (by omega) he (by omega) hkh]
      exact hs.2.2.2.2 k (by omega)

theorem sum_swap_Znth__pivot_finalization :
  ∀ xs i j, ((0 : Int) ≤ i ∧ i < Zlength xs) → ((0 : Int) ≤ j ∧ j < Zlength xs) →
    sum (swap_Znth (0 : Int) i j xs) = sum xs := by
  intro xs i j hi hj
  exact (sum_permutation__scan_advance _ _ (permutation_swap_Znth__scan_advance _ xs i j 0 hi hj)).symm

theorem paired_permutation_refl__quicksort_range_composition :
  ∀ rows lens,
    Zlength rows = Zlength lens →
    PairedPermutation rows rows lens lens := by
  intro rows lens he
  exact ⟨he,he,List.Perm.refl _⟩

theorem paired_permutation_trans__quicksort_range_composition :
  ∀ rows0 rows1 rows2 lens0 lens1 lens2,
    PairedPermutation rows0 rows1 lens0 lens1 →
    PairedPermutation rows1 rows2 lens1 lens2 →
    PairedPermutation rows0 rows2 lens0 lens2 := by
  intro rows0 rows1 rows2 lens0 lens1 lens2 h01 h12
  exact ⟨h01.1,h12.2.1,h01.2.2.trans h12.2.2⟩

theorem same_outside_paired_range_refl__quicksort_range_composition :
  ∀ rows lens left right,
    SameOutsidePairedRange rows rows lens lens left right := by
  intros
  exact ⟨rfl,rfl,by intros; rfl⟩

theorem same_outside_paired_range_trans__quicksort_range_composition :
  ∀ rows0 rows1 rows2 lens0 lens1 lens2 left right,
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left right →
    SameOutsidePairedRange rows1 rows2 lens1 lens2 left right →
    SameOutsidePairedRange rows0 rows2 lens0 lens2 left right := by
  intro rows0 rows1 rows2 lens0 lens1 lens2 left right h01 h12
  refine ⟨h01.1.trans h12.1,h01.2.1.trans h12.2.1,?_⟩
  intro k hk hout
  exact (h12.2.2 k (by rw [←h01.1]; exact hk) hout).trans (h01.2.2 k hk hout)

theorem same_outside_paired_range_weaken__quicksort_range_composition :
  ∀ rows0 rows1 lens0 lens1 left1 right1 left2 right2,
    left2 ≤ left1 →
    right1 ≤ right2 →
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left1 right1 →
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left2 right2 := by
  intro rows0 rows1 lens0 lens1 left1 right1 left2 right2 hl hr h
  refine ⟨h.1,h.2.1,?_⟩
  intro k hk ho
  apply h.2.2 k hk
  rcases ho with ho|ho
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem digit_lex_ge_refl__quicksort_range_composition :
  ∀ xs, digit_lex_ge xs xs := by
  intro xs
  exact ⟨rfl,Or.inl rfl⟩

theorem item_before_or_equal_refl__quicksort_range_composition :
  ∀ rows lens i,
    item_before_or_equal rows lens i i := by
  intros
  exact digit_lex_ge_refl__quicksort_range_composition _

theorem greedy_sorted_range_base__quicksort_range_composition :
  ∀ rows lens left right,
    left ≥ right →
    GreedySortedRange rows lens left right := by
  intro rows lens left right h i j hij
  have he : i=j := by omega
  subst j
  exact item_before_or_equal_refl__quicksort_range_composition rows lens i

theorem decimal_fold_acc__quicksort_range_composition :
  ∀ xs acc,
    (List.foldl (fun value digit : Int => 10*value+digit) acc xs) =
    acc * Z.pow (10 : Int) (Zlength xs) +
    (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) xs) := by
  change ∀ xs acc,
      decimalFold xs acc =
      acc * Z.pow (10 : Int) (Zlength xs) +
      decimalFold xs (0 : Int)
  intro xs
  induction xs with
  | nil => intro acc; simp [decimalFold,Zlength,Z.pow]
  | cons x xs ih =>
    intro acc
    change decimalFold xs (10*acc+x) = acc * (10^(xs.length+1)) + decimalFold xs (10*0+x)
    simp only [Int.mul_zero,Int.zero_add]
    rw [ih (10*acc+x),ih x]
    change (10*acc+x)*10^xs.length+decimalFold xs 0 = acc * (10^(xs.length+1)) + (x*10^xs.length+decimalFold xs 0)
    simp only [Int.pow_succ]
    grind

theorem decimal_fold_app__quicksort_range_composition :
  ∀ xs ys,
    (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) (xs ++ ys)) =
    (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) xs) *
      Z.pow (10 : Int) (Zlength ys) +
    (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) ys) := by
  intro xs ys
  change (xs++ys).foldl _ 0 = _
  rw [List.foldl_append]
  exact decimal_fold_acc__quicksort_range_composition ys (decimalFold xs 0)

private theorem tenpow_pos (n : Nat) : (0 : Int) < 10^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ]; omega

private theorem tenpow_gt_one (xs : List Int) (h : 0 < Zlength xs) :
    1 < Z.pow 10 (Zlength xs) := by
  cases xs with
  | nil => simp only [Zlength_nil] at h; omega
  | cons x xs =>
    change 1 < (10 : Int)^(xs.length+1)
    rw [Int.pow_succ]
    have := tenpow_pos xs.length
    omega

private theorem decimal_cons (x : Int) (xs : List Int) :
    decimalFold (x::xs) 0 = x * Z.pow 10 (Zlength xs) + decimalFold xs 0 := by
  change decimalFold xs (10*0+x) = _
  simpa only [Int.mul_zero,Int.zero_add] using decimal_fold_acc__quicksort_range_composition xs x

private theorem decimal_compare (x y p a b : Int) (hp : 0<p)
    (ha : 0≤a ∧ a<p) (hb : 0≤b ∧ b<p) :
    (y < x ∨ (x=y ∧ b≤a)) ↔ y*p+b ≤ x*p+a := by
  constructor
  · rintro (hlt|⟨rfl,hle⟩)
    · have hm := Int.mul_le_mul_of_nonneg_right (show y+1≤x by omega) (show 0≤p by omega)
      have he : (y+1)*p=y*p+p := by grind
      rw [he] at hm
      omega
    · omega
  · intro h
    by_cases hlt : y<x
    · exact Or.inl hlt
    · have he : x=y := by
        by_cases he : x=y
        · exact he
        have hn := he
        exfalso
        have hm := Int.mul_le_mul_of_nonneg_right (show x+1≤y by omega) (show 0≤p by omega)
        have he : (x+1)*p=x*p+p := by grind
        rw [he] at hm
        omega
      exact Or.inr ⟨he,by rw [he] at h; omega⟩

theorem decimal_fold_bounds__quicksort_range_composition :
  ∀ xs,
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs → ((0 : Int) ≤ (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) xs) ∧ (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) xs) < Z.pow (10 : Int) (Zlength xs)) := by
  change ∀ xs,
      Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs → ((0 : Int) ≤ decimalFold xs (0 : Int) ∧ decimalFold xs (0 : Int) < Z.pow (10 : Int) (Zlength xs))
  intro xs h
  induction h with
  | nil => change 0≤0 ∧ (0:Int)<1; omega
  | @cons x xs hx ht ih =>
    rw [decimal_cons]
    have hp := tenpow_pos xs.length
    change 0≤x*10^xs.length+decimalFold xs 0 ∧ x*10^xs.length+decimalFold xs 0 < 10^(xs.length+1)
    change 0≤decimalFold xs 0 ∧ decimalFold xs 0 < 10^xs.length at ih
    have hm := Int.mul_nonneg hx.1 (show 0≤(10:Int)^xs.length by omega)
    have hle := Int.mul_le_mul_of_nonneg_right (show x≤9 by omega) (show 0≤(10:Int)^xs.length by omega)
    rw [Int.pow_succ]
    omega

theorem digit_lex_ge_cons_iff__quicksort_range_composition :
  ∀ x y xs ys,
    Zlength xs = Zlength ys →
    (digit_lex_ge (x :: xs) (y :: ys) ↔
     y < x ∨ (x = y ∧ digit_lex_ge xs ys)) := by
  intro x y xs ys he
  constructor
  · rintro ⟨_,heq|⟨k,hk,hpre,hgt⟩⟩
    · cases heq
      exact Or.inr ⟨rfl,digit_lex_ge_refl__quicksort_range_composition xs⟩
    · by_cases hk0 : k = 0
      · subst k
        exact Or.inl (by simpa only [Znth0_cons] using hgt)
      · have hxy := hpre 0 (by omega)
        simp only [Znth0_cons] at hxy
        refine Or.inr ⟨hxy,he,Or.inr ⟨k-1,?_,?_,?_⟩⟩
        · simp only [Zlength_cons] at hk
          omega
        · intro j hj
          have h := hpre (j+1) (by omega)
          simpa only [Znth_cons 0 (j+1) x xs (by omega),
            Znth_cons 0 (j+1) y ys (by omega),Int.add_sub_cancel] using h
        · simpa only [Znth_cons 0 k y ys (by omega),Znth_cons 0 k x xs (by omega)] using hgt
  · intro h
    refine ⟨by simpa only [Zlength_cons] using congrArg (· + 1) he,?_⟩
    rcases h with hlt|⟨hxy,_,htail⟩
    · exact Or.inr ⟨0,by have := Zlength_nonneg xs; simp only [Zlength_cons]; omega,
        by intro j hj; omega,by simpa only [Znth0_cons] using hlt⟩
    · rcases htail with heq|⟨k,hk,hpre,hgt⟩
      · exact Or.inl (by rw [hxy,heq])
      · refine Or.inr ⟨k+1,by simp only [Zlength_cons]; omega,?_,?_⟩
        · intro j hj
          by_cases hj0 : j=0
          · subst j
            simpa only [Znth0_cons] using hxy
          · rw [Znth_cons 0 j x xs (by omega),Znth_cons 0 j y ys (by omega)]
            exact hpre _ (by omega)
        · simpa only [Znth_cons 0 (k+1) y ys (by omega),Znth_cons 0 (k+1) x xs (by omega),Int.add_sub_cancel] using hgt

theorem digit_lex_ge_decimal_iff__quicksort_range_composition :
  ∀ xs ys,
    Zlength xs = Zlength ys →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
    (digit_lex_ge xs ys ↔
     (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) xs) ≥
     (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) ys)) := by
  change ∀ xs ys,
      Zlength xs = Zlength ys →
      Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
      Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
      (digit_lex_ge xs ys ↔
       decimalFold xs (0 : Int) ≥
       decimalFold ys (0 : Int))
  intro xs
  induction xs with
  | nil =>
    intro ys hl hx hy
    have he : ys=[] := by simp only [Zlength,List.length_nil,Int.ofNat_eq_coe] at hl; exact List.length_eq_zero_iff.mp (by omega)
    subst ys
    exact ⟨by intro h; omega,by intro h; exact digit_lex_ge_refl__quicksort_range_composition []⟩
  | cons x xs ih =>
    intro ys hl hx hy
    cases ys with
    | nil => have := Zlength_nonneg xs; simp only [Zlength_cons,Zlength_nil] at hl; omega
    | cons y ys =>
      cases hx with
      | cons hx hxs =>
        cases hy with
        | cons hy hys =>
          have hlen : Zlength xs=Zlength ys := by simp only [Zlength_cons] at hl; omega
          have hxb := decimal_fold_bounds__quicksort_range_composition xs hxs
          have hyb := decimal_fold_bounds__quicksort_range_composition ys hys
          have hiff := ih ys hlen hxs hys
          rw [digit_lex_ge_cons_iff__quicksort_range_composition x y xs ys hlen,
            decimal_cons x xs,decimal_cons y ys,←hlen] 
          rw [hiff]
          rw [←hlen] at hyb
          exact decimal_compare x y _ _ _ (tenpow_pos xs.length) hxb hyb

theorem concat_digit_order_cross_iff__quicksort_range_composition :
  ∀ xs ys,
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
    (digit_lex_ge (xs ++ ys) (ys ++ xs) ↔
     (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) xs) *
       (Z.pow (10 : Int) (Zlength ys) - (1 : Int)) ≥
     (List.foldl (fun value digit : Int => 10*value+digit) (0 : Int) ys) *
       (Z.pow (10 : Int) (Zlength xs) - (1 : Int))) := by
  intro xs ys hx hy
  rw [digit_lex_ge_decimal_iff__quicksort_range_composition _ _
    (by simp only [Zlength_app]; omega) (forall_append hx hy) (forall_append hy hx),
    decimal_fold_app__quicksort_range_composition xs ys,
    decimal_fold_app__quicksort_range_composition ys xs]
  constructor <;> intro h <;> grind

theorem concat_digit_order_trans__quicksort_range_composition :
  ∀ xs ys zs,
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) zs →
    (0 : Int) < Zlength xs →
    (0 : Int) < Zlength ys →
    (0 : Int) < Zlength zs →
    digit_lex_ge (xs ++ ys) (ys ++ xs) →
    digit_lex_ge (ys ++ zs) (zs ++ ys) →
    digit_lex_ge (xs ++ zs) (zs ++ xs) := by
  intro xs ys zs hx hy hz hxl hyl hzl hxy hyz
  rw [concat_digit_order_cross_iff__quicksort_range_composition xs ys hx hy] at hxy
  rw [concat_digit_order_cross_iff__quicksort_range_composition ys zs hy hz] at hyz
  rw [concat_digit_order_cross_iff__quicksort_range_composition xs zs hx hz]
  have px := tenpow_gt_one xs hxl
  have py := tenpow_gt_one ys hyl
  have pz := tenpow_gt_one zs hzl
  have h1 := Int.mul_le_mul_of_nonneg_right hxy (show 0 ≤ Z.pow 10 (Zlength zs)-1 by omega)
  have h2 := Int.mul_le_mul_of_nonneg_right hyz (show 0 ≤ Z.pow 10 (Zlength xs)-1 by omega)
  have he1 : decimalFold ys 0*(Z.pow 10 (Zlength xs)-1)*(Z.pow 10 (Zlength zs)-1) =
    decimalFold ys 0*(Z.pow 10 (Zlength zs)-1)*(Z.pow 10 (Zlength xs)-1) := by grind
  have he2 : decimalFold zs 0*(Z.pow 10 (Zlength ys)-1)*(Z.pow 10 (Zlength xs)-1) =
    (decimalFold zs 0*(Z.pow 10 (Zlength xs)-1))*(Z.pow 10 (Zlength ys)-1) := by grind
  have he3 : decimalFold xs 0*(Z.pow 10 (Zlength ys)-1)*(Z.pow 10 (Zlength zs)-1) =
    (decimalFold xs 0*(Z.pow 10 (Zlength zs)-1))*(Z.pow 10 (Zlength ys)-1) := by grind
  rw [he1,he3] at h1
  rw [he2] at h2
  exact (Int.mul_le_mul_right (show 0 < Z.pow 10 (Zlength ys)-1 by omega)).mp (Int.le_trans h2 h1)

private theorem lex_total (xs ys : List Int) (hl : Zlength xs=Zlength ys) :
    digit_lex_ge xs ys ∨ digit_lex_ge ys xs := by
  induction xs generalizing ys with
  | nil =>
    have he : ys=[] := by simp only [Zlength,List.length_nil,Int.ofNat_eq_coe] at hl; exact List.length_eq_zero_iff.mp (by omega)
    subst ys
    exact Or.inl (digit_lex_ge_refl__quicksort_range_composition [])
  | cons x xs ih =>
    cases ys with
    | nil => have := Zlength_nonneg xs; simp only [Zlength_cons,Zlength_nil] at hl; omega
    | cons y ys =>
      have ht : Zlength xs=Zlength ys := by simp only [Zlength_cons] at hl; omega
      rw [digit_lex_ge_cons_iff__quicksort_range_composition x y xs ys ht,
        digit_lex_ge_cons_iff__quicksort_range_composition y x ys xs ht.symm]
      by_cases hxy : y<x
      · exact Or.inl (Or.inl hxy)
      by_cases hyx : x<y
      · exact Or.inr (Or.inl hyx)
      have he : x=y := by omega
      rcases ih ys ht with h|h
      · exact Or.inl (Or.inr ⟨he,h⟩)
      · exact Or.inr (Or.inr ⟨he.symm,h⟩)

theorem digit_lex_not_gt_flip__quicksort_range_composition :
  ∀ xs ys,
    Zlength xs = Zlength ys →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
    ¬ digit_lex_gt xs ys →
    digit_lex_ge ys xs := by
  intro xs ys hl hx hy hn
  rcases lex_total xs ys hl with h|h
  · rcases h.2 with he|hgt
    · subst ys
      exact digit_lex_ge_refl__quicksort_range_composition xs
    · exact False.elim (hn ⟨hl,hgt⟩)
  · exact h

theorem Forall_sublist_by_Znth__quicksort_range_composition :
  ∀ (P : Int → Prop) (l : List Int) lo hi, ((0 : Int) ≤ lo ∧ lo ≤ hi) →
    hi ≤ Zlength l →
    (∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l (0 : Int))) →
    Forall P (sublist lo hi l) := by
  intro P l lo hi hl hh hp
  exact forall_sub_znth P l 0 lo hi hl hh hp

theorem item_digits_properties__quicksort_range_composition :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    (0 : Int) < Zlength (item_digits (item_at rows lens i)) ∧
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) )
      (item_digits (item_at rows lens i)) := by
  intro rows lens count width i hw hi
  have h := hw.2.2 i hi
  change 0 < Zlength (sublist 0 (Znth i lens 0) (Znth i rows [])) ∧ _
  constructor
  · rw [prefix_len _ _ (by omega)]
    omega
  · change Forall (fun digit : Int => 0 ≤ digit ∧ digit < 10) (sublist 0 (Znth i lens 0) (Znth i rows []))
    apply forall_sub_znth _ _ 0
    · omega
    · omega
    · intro k hk
      have hd := h.2.2.2 k hk
      exact ⟨hd.1,by omega⟩

theorem item_before_or_equal_trans__quicksort_range_composition :
  ∀ rows lens count width i j k,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) → ((0 : Int) ≤ k ∧ k < count) →
    item_before_or_equal rows lens i j →
    item_before_or_equal rows lens j k →
    item_before_or_equal rows lens i k := by
  intro rows lens count width i j k hw hi hj hk hij hjk
  have hI := item_digits_properties__quicksort_range_composition rows lens count width i hw hi
  have hJ := item_digits_properties__quicksort_range_composition rows lens count width j hw hj
  have hK := item_digits_properties__quicksort_range_composition rows lens count width k hw hk
  exact concat_digit_order_trans__quicksort_range_composition _ _ _ hI.2 hJ.2 hK.2 hI.1 hJ.1 hK.1 hij hjk

theorem item_before_implies_or_equal__quicksort_range_composition :
  ∀ rows lens i j,
    item_before rows lens i j →
    item_before_or_equal rows lens i j := by
  intro rows lens i j h
  exact ⟨h.1,Or.inr h.2⟩

theorem item_not_before_flip__quicksort_range_composition :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) →
    ¬ item_before rows lens i j →
    item_before_or_equal rows lens j i := by
  intro rows lens count width i j hw hi hj hn
  have hI := item_digits_properties__quicksort_range_composition rows lens count width i hw hi
  have hJ := item_digits_properties__quicksort_range_composition rows lens count width j hw hj
  apply digit_lex_not_gt_flip__quicksort_range_composition _ _ _ (forall_append hI.2 hJ.2) (forall_append hJ.2 hI.2) hn
  simp only [Zlength_app]
  omega

theorem Znth_combine__quicksort_range_composition :
  ∀ {A B : Type} i (xs : List A) (ys : List B) dx dy, ((0 : Int) ≤ i ∧ i < Zlength xs) →
    Zlength xs = Zlength ys →
    Znth i (List.zip xs ys) (dx, dy) = (Znth i xs dx, Znth i ys dy) := by
  intro A B i xs ys dx dy hi he
  have h1 : i.toNat<xs.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  have h2 : i.toNat<ys.length := by simp only [Zlength,Int.ofNat_eq_coe] at he hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.zip_eq_zipWith,List.getElem?_zipWith,
    List.getElem?_eq_getElem h1,List.getElem?_eq_getElem h2,Option.bind_some,Option.map_some,Option.getD_some]

theorem Zlength_paired_items_eq__quicksort_range_composition :
  ∀ rows lens,
    Zlength rows = Zlength lens →
    Zlength (paired_items rows lens) = Zlength rows := by
  exact paired_items_length__pivot_finalization

theorem paired_items_Znth__quicksort_range_composition :
  ∀ rows lens i,
    Zlength rows = Zlength lens → ((0 : Int) ≤ i ∧ i < Zlength rows) →
    Znth i (paired_items rows lens) ([], (0 : Int)) = item_at rows lens i := by
  exact Znth_paired_items__pivot_finalization

theorem sublist_eq_from_Znth__quicksort_range_composition :
  ∀ {A : Type} (d : A) (xs ys : List A) lo hi,
    Zlength xs = Zlength ys → ((0 : Int) ≤ lo ∧ lo ≤ hi) →
    hi ≤ Zlength xs →
    (∀ k, (lo ≤ k ∧ k < hi) → Znth k xs d = Znth k ys d) →
    sublist lo hi xs = sublist lo hi ys := by
  intro A d xs ys lo hi he hl hh hn
  have hy : hi ≤ Zlength ys := by omega
  apply zlist_ext _ _ d
  · rw [sub_len xs lo hi hl hh,sub_len ys lo hi hl hy]
  · intro i hi'
    rw [sub_len xs lo hi hl hh] at hi'
    rw [Znth_sublist d lo i hi xs hl.1 hi',Znth_sublist d lo i hi ys hl.1 hi']
    exact hn _ (by omega)

theorem list_decompose_sublist__quicksort_range_composition :
  ∀ {A : Type} (xs : List A) lo hi, ((0 : Int) ≤ lo ∧ lo ≤ hi) →
    hi ≤ Zlength xs →
    xs = sublist (0 : Int) lo xs ++ sublist lo hi xs ++
         sublist hi (Zlength xs) xs := by
  intro A xs lo hi hl hh
  calc
    xs = sublist 0 (Zlength xs) xs := (sublist_self xs _ rfl).symm
    _ = _ := by
      rw [sublist_split 0 (Zlength xs) hi xs (by omega) (by omega),
        sublist_split 0 hi lo xs (by omega) (by omega)]

theorem paired_items_outside_sublist_eq__quicksort_range_composition :
  ∀ rows0 rows1 lens0 lens1 lo hi left right,
    Zlength rows0 = Zlength lens0 →
    Zlength rows1 = Zlength lens1 →
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left right → ((0 : Int) ≤ lo ∧ lo ≤ hi) →
    hi ≤ Zlength rows0 →
    (∀ k, (lo ≤ k ∧ k < hi) → k < left ∨ right < k) →
    sublist lo hi (paired_items rows1 lens1) =
    sublist lo hi (paired_items rows0 lens0) := by
  intro r0 r1 l0 l1 lo hi left right h0 h1 hs hlo hhi hout
  have hr := hs.1
  have hp0 := paired_items_length__pivot_finalization r0 l0 h0
  have hp1 := paired_items_length__pivot_finalization r1 l1 h1
  apply sublist_eq_from_Znth__quicksort_range_composition ([],0)
  · omega
  · exact hlo
  · omega
  · intro k hk
    rw [Znth_paired_items__pivot_finalization r1 l1 k h1 (by omega),
      Znth_paired_items__pivot_finalization r0 l0 k h0 (by omega)]
    exact hs.2.2 k (by omega) (hout k hk)

theorem paired_middle_permutation__quicksort_range_composition :
  ∀ rows0 rows1 lens0 lens1 left right,
    PairedPermutation rows0 rows1 lens0 lens1 →
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left right → ((0 : Int) ≤ left ∧ left ≤ right + (1 : Int)) →
    right + (1 : Int) ≤ Zlength rows0 →
    Permutation
      (sublist left (right + (1 : Int)) (paired_items rows0 lens0))
      (sublist left (right + (1 : Int)) (paired_items rows1 lens1)) := by
  intro r0 r1 l0 l1 left right hp hs hb hh
  have h0 := hp.1
  have h1 := hp.2.1
  have hr := hs.1
  have hn0 := paired_items_length__pivot_finalization r0 l0 h0
  have hn1 := paired_items_length__pivot_finalization r1 l1 h1
  have hepre := paired_items_outside_sublist_eq__quicksort_range_composition r0 r1 l0 l1 0 left left right
    h0 h1 hs (by omega) (by omega) (by intro k hk; exact Or.inl (by omega))
  have hesuf := paired_items_outside_sublist_eq__quicksort_range_composition r0 r1 l0 l1 (right+1) (Zlength r0) left right
    h0 h1 hs (by omega) (by omega) (by intro k hk; exact Or.inr (by omega))
  have hperm := hp.2.2
  have hd0 := list_decompose_sublist__quicksort_range_composition (paired_items r0 l0) left (right+1) hb (by omega)
  have hd1 := list_decompose_sublist__quicksort_range_composition (paired_items r1 l1) left (right+1) hb (by omega)
  conv at hperm => lhs; rw [hd0]
  conv at hperm => rhs; rw [hd1]
  rw [hn0,hn1,←hr,hepre,hesuf] at hperm
  simp only [List.append_assoc,List.perm_append_left_iff,List.perm_append_right_iff] at hperm
  exact hperm

theorem Forall_sublist_by_Znth_pair__quicksort_range_composition :
  ∀ (P : number_item → Prop) xs lo hi, ((0 : Int) ≤ lo ∧ lo ≤ hi) →
    hi ≤ Zlength xs →
    (∀ k, (lo ≤ k ∧ k < hi) → P (Znth k xs ([], (0 : Int)))) →
    Forall P (sublist lo hi xs) := by
  intro P l lo hi hl hh hp
  exact forall_sub_znth P l ([],0) lo hi hl hh hp

theorem Forall_permutation_pair__quicksort_range_composition :
  ∀ (P : number_item → Prop) xs ys,
    Permutation xs ys →
    Forall P xs →
    Forall P ys := by
  intro P xs ys hp h
  exact h.perm hp

theorem Forall_sublist_Znth_pair__quicksort_range_composition :
  ∀ (P : number_item → Prop) xs lo hi k, ((0 : Int) ≤ lo ∧ lo ≤ hi) →
    hi ≤ Zlength xs →
    Forall P (sublist lo hi xs) → (lo ≤ k ∧ k < hi) →
    P (Znth k xs ([], (0 : Int))) := by
  intro P xs lo hi k hl hh hp hk
  have h := forall_znth P (sublist lo hi xs) ([],0) (k-lo) hp
    (by rw [sub_len xs lo hi hl hh]; omega)
  rw [Znth_sublist ([],0) lo (k-lo) hi xs hl.1 (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

private theorem range_transfer (r0 r1 : List (List Int)) (l0 l1 : List Int) (left right : Int)
    (hp : PairedPermutation r0 r1 l0 l1) (hs : SameOutsidePairedRange r0 r1 l0 l1 left right)
    (hb : 0≤left ∧ left≤right+1) (hh : right+1≤Zlength r0)
    (P : number_item → Prop) (h : ∀ k, left≤k ∧ k≤right → P (item_at r0 l0 k)) :
    ∀ k, left≤k ∧ k≤right → P (item_at r1 l1 k) := by
  have hn0 := paired_items_length__pivot_finalization r0 l0 hp.1
  have hn1 := paired_items_length__pivot_finalization r1 l1 hp.2.1
  have hr := hs.1
  have hperm := paired_middle_permutation__quicksort_range_composition r0 r1 l0 l1 left right hp hs hb hh
  have hsrc : Forall P (sublist left (right+1) (paired_items r0 l0)) := by
    apply Forall_sublist_by_Znth_pair__quicksort_range_composition P _ left (right+1) hb (by omega)
    intro k hk
    rw [Znth_paired_items__pivot_finalization r0 l0 k hp.1 (by omega)]
    exact h k (by omega)
  have hdst := hsrc.perm hperm
  intro k hk
  have hval := Forall_sublist_Znth_pair__quicksort_range_composition P _ left (right+1) k hb (by omega) hdst (by omega)
  rw [Znth_paired_items__pivot_finalization r1 l1 k hp.2.1 (by omega)] at hval
  exact hval

theorem greedy_partitioned_preserved_left__quicksort_range_composition :
  ∀ rows0 rows1 lens0 lens1 count width low high pivot,
    RowsWellFormed rows1 lens1 count width →
    PairedPermutation rows0 rows1 lens0 lens1 →
    SameOutsidePairedRange rows0 rows1 lens0 lens1 low (pivot - (1 : Int)) →
    (0 : Int) ≤ low →
    high < count →
    GreedyPartitionedAt rows0 lens0 low high pivot →
    GreedyPartitionedAt rows1 lens1 low high pivot := by
  intro r0 r1 l0 l1 count width low high pivot hw hp hs hlo hhi hpart
  have hr := hs.1
  have hn := hw.1
  have hb := hpart.1
  have heP := hs.2.2 pivot (by omega) (Or.inr (by omega))
  refine ⟨hb,?_,?_⟩
  · have ht := range_transfer r0 r1 l0 l1 low (pivot-1) hp hs (by omega) (by omega)
      (fun item => digit_lex_gt (item_digits item++item_digits (item_at r0 l0 pivot))
        (item_digits (item_at r0 l0 pivot)++item_digits item))
      (by intro k hk; exact hpart.2.1 k (by omega))
    intro k hk
    unfold item_before
    rw [heP]
    exact ht k (by omega)
  · intro k hk
    have hek := hs.2.2 k (by omega) (Or.inr (by omega))
    unfold item_before
    rw [hek,heP]
    exact hpart.2.2 k hk

theorem greedy_partitioned_preserved_right__quicksort_range_composition :
  ∀ rows0 rows1 lens0 lens1 count width low high pivot,
    RowsWellFormed rows1 lens1 count width →
    PairedPermutation rows0 rows1 lens0 lens1 →
    SameOutsidePairedRange rows0 rows1 lens0 lens1 (pivot + (1 : Int)) high →
    (0 : Int) ≤ low →
    high < count →
    GreedyPartitionedAt rows0 lens0 low high pivot →
    GreedyPartitionedAt rows1 lens1 low high pivot := by
  intro r0 r1 l0 l1 count width low high pivot hw hp hs hlo hhi hpart
  have hr := hs.1
  have hn := hw.1
  have hb := hpart.1
  have heP := hs.2.2 pivot (by omega) (Or.inl (by omega))
  refine ⟨hb,?_,?_⟩
  · intro k hk
    have hek := hs.2.2 k (by omega) (Or.inl (by omega))
    unfold item_before
    rw [hek,heP]
    exact hpart.2.1 k hk
  · have ht := range_transfer r0 r1 l0 l1 (pivot+1) high hp hs (by omega) (by omega)
      (fun item => ¬digit_lex_gt (item_digits item++item_digits (item_at r0 l0 pivot))
        (item_digits (item_at r0 l0 pivot)++item_digits item))
      (by intro k hk; exact hpart.2.2 k (by omega))
    intro k hk
    unfold item_before
    rw [heP]
    exact ht k (by omega)

theorem greedy_sorted_range_preserved_outside__quicksort_range_composition :
  ∀ rows0 rows1 lens0 lens1 change_left change_right left right,
    SameOutsidePairedRange
      rows0 rows1 lens0 lens1 change_left change_right →
    (0 : Int) ≤ left →
    right < Zlength rows0 →
    (∀ k, (left ≤ k ∧ k ≤ right) →
       k < change_left ∨ change_right < k) →
    GreedySortedRange rows0 lens0 left right →
    GreedySortedRange rows1 lens1 left right := by
  intro r0 r1 l0 l1 cl cr left right hs hl hr hout hsorted i j hij
  have hi := hs.2.2 i (by omega) (hout i (by omega))
  have hj := hs.2.2 j (by omega) (hout j (by omega))
  unfold item_before_or_equal
  rw [hi,hj]
  exact hsorted i j hij

theorem greedy_sorted_range_combine__quicksort_range_composition :
  ∀ rows lens count width low high pivot,
    RowsWellFormed rows lens count width →
    (0 : Int) ≤ low →
    high < count →
    GreedyPartitionedAt rows lens low high pivot →
    GreedySortedRange rows lens low (pivot - (1 : Int)) →
    GreedySortedRange rows lens (pivot + (1 : Int)) high →
    GreedySortedRange rows lens low high := by
  intro rows lens count width low high pivot hw hlo hhi hp hsleft hsright i j hij
  have hb := hp.1
  have hPi : ∀ k, low≤k ∧ k≤pivot → item_before_or_equal rows lens k pivot := by
    intro k hk
    by_cases he : k=pivot
    · subst k
      exact item_before_or_equal_refl__quicksort_range_composition rows lens pivot
    · exact item_before_implies_or_equal__quicksort_range_composition rows lens k pivot (hp.2.1 k (by omega))
  have hPj : ∀ k, pivot≤k ∧ k≤high → item_before_or_equal rows lens pivot k := by
    intro k hk
    by_cases he : k=pivot
    · subst k
      exact item_before_or_equal_refl__quicksort_range_composition rows lens pivot
    · exact item_not_before_flip__quicksort_range_composition rows lens count width k pivot hw
        (by omega) (by omega) (hp.2.2 k (by omega))
  by_cases hj : j<pivot
  · exact hsleft i j (by omega)
  by_cases hi : pivot<i
  · exact hsright i j (by omega)
  exact item_before_or_equal_trans__quicksort_range_composition rows lens count width i pivot j hw
    (by omega) (by omega) (by omega) (hPi i (by omega)) (hPj j (by omega))

theorem ConcatenatedPrefix_zero__output_setup :
  ∀ rows lens, ConcatenatedPrefix rows lens (0 : Int) = [] := by
  intros
  rfl

theorem ConcatenatedOutputPrefix_zero__output_setup :
  ∀ rows lens row_count,
    ConcatenatedOutputPrefix rows lens row_count (0 : Int) =
    ConcatenatedPrefix rows lens row_count := by
  intros
  simp [ConcatenatedOutputPrefix,sublist]

theorem sublist_snoc__output_inner_loop :
  ∀ {A : Type} (d : A) (xs : List A) i, ((0 : Int) ≤ i ∧ i < Zlength xs) →
    sublist (0 : Int) (i + (1 : Int)) xs = sublist (0 : Int) i xs ++ Znth i xs d :: [] := by
  intro A d xs i hi
  rw [sublist_split 0 (i+1) i xs (by omega) (by omega),sublist_single d i xs hi]

theorem FlatRows_Znth__output_inner_loop :
  ∀ flat rows count width i j,
    FlatRows flat rows count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < width) →
    Znth (i * width + j) flat (0 : Int) = Znth j (Znth i rows []) (0 : Int) := by
  exact FlatRows_Znth__compare_left_digit

private theorem concat_length (rows : List (List Int)) (lens : List Int)
    (he : Zlength rows=Zlength lens)
    (hp : ∀ i, 0≤i ∧ i<Zlength rows → Zlength (item_digits (item_at rows lens i))=Znth i lens 0) :
    Zlength (concatenate_rows rows lens)=sum lens := by
  induction rows generalizing lens with
  | nil =>
    have hn : lens=[] := by simp only [Zlength,List.length_nil,Int.ofNat_eq_coe] at he; exact List.length_eq_zero_iff.mp (by omega)
    subst lens
    rfl
  | cons row rows ih =>
    cases lens with
    | nil => have := Zlength_nonneg rows; simp only [Zlength_cons,Zlength_nil] at he; omega
    | cons n lens =>
      have hlen : Zlength rows=Zlength lens := by simp only [Zlength_cons] at he; omega
      have hzero := hp 0 (by have := Zlength_nonneg rows; simp only [Zlength_cons]; omega)
      simp only [item_at,Znth0_cons] at hzero
      have ht : ∀ i, 0≤i ∧ i<Zlength rows → Zlength (item_digits (item_at rows lens i))=Znth i lens 0 := by
        intro i hi
        have h := hp (i+1) (by simp only [Zlength_cons]; omega)
        simpa only [item_at,Znth_cons [] (i+1) row rows (by omega),
          Znth_cons 0 (i+1) n lens (by omega),Int.add_sub_cancel] using h
      change Zlength (item_digits (row,n)++concatenate_rows rows lens)=n+sum lens
      rw [Zlength_app,hzero,ih lens hlen ht]

theorem Zlength_concatenate_rows_pointwise__output_inner_loop :
  ∀ rows lens,
    Zlength rows = Zlength lens →
    (∀ k, ((0 : Int) ≤ k ∧ k < Zlength rows) → ((0 : Int) ≤ Znth k lens (0 : Int) ∧ Znth k lens (0 : Int) ≤ Zlength (Znth k rows [])) ) →
    Zlength (concatenate_rows rows lens) = sum lens := by
  intro rows lens he hp
  apply concat_length rows lens he
  intro i hi
  change Zlength (sublist 0 (Znth i lens 0) (Znth i rows [])) = _
  exact prefix_len _ _ (hp i hi)

theorem Zlength_ConcatenatedPrefix__output_inner_loop :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i ≤ count) →
    Zlength (ConcatenatedPrefix rows lens i) = sum (sublist (0 : Int) i lens) := by
  intro rows lens count width i hw hi
  have hr := hw.1
  have hl := hw.2.1
  apply Zlength_concatenate_rows_pointwise__output_inner_loop
  · rw [prefix_len rows i (by omega),prefix_len lens i (by omega)]
  · intro k hk
    rw [prefix_len rows i (by omega)] at hk
    rw [Znth_prefix lens 0 i k hk,Znth_prefix rows [] i k hk]
    have h := hw.2.2 k (by omega)
    exact ⟨by omega,by omega⟩

theorem sum_nonnegative_pointwise__output_inner_loop :
  ∀ xs,
    (∀ k, ((0 : Int) ≤ k ∧ k < Zlength xs) → (0 : Int) ≤ Znth k xs (0 : Int)) →
    (0 : Int) ≤ sum xs := by
  intro xs hp
  induction xs with
  | nil => change (0:Int)≤0; omega
  | cons x xs ih =>
    have h0 := hp 0 (by have := Zlength_nonneg xs; simp only [Zlength_cons]; omega)
    simp only [Znth0_cons] at h0
    have ht := ih (by
      intro k hk
      have h := hp (k+1) (by simp only [Zlength_cons]; omega)
      simpa only [Znth_cons 0 (k+1) x xs (by omega),Int.add_sub_cancel] using h)
    change 0≤x+sum xs
    omega

theorem sum_prefix_plus_digit_lt_total__output_inner_loop :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < Znth i lens (0 : Int)) →
    sum (sublist (0 : Int) i lens) + j < sum lens := by
  intro rows lens count width i j hw hi hj
  have hl := hw.2.1
  have hdecomp : lens=sublist 0 i lens++Znth i lens 0::sublist (i+1) (Zlength lens) lens := by
    calc
      lens = sublist 0 (Zlength lens) lens := (sublist_self lens _ rfl).symm
      _ = _ := by
        rw [sublist_split 0 (Zlength lens) i lens (by omega) (by omega),
          sublist_split i (Zlength lens) (i+1) lens (by omega) (by omega),sublist_single 0 i lens (by omega)]
        rfl
  have hnon : 0≤sum (sublist (i+1) (Zlength lens) lens) := by
    apply sum_nonnegative_pointwise__output_inner_loop
    intro k hk
    rw [sub_len lens (i+1) (Zlength lens) (by omega) (by omega)] at hk
    rw [Znth_sublist 0 (i+1) k (Zlength lens) lens (by omega) hk]
    have h := hw.2.2 (k+(i+1)) (by omega)
    omega
  have heq : sum lens=sum (sublist 0 i lens)+Znth i lens 0+sum (sublist (i+1) (Zlength lens) lens) := by
    conv => lhs; rw [hdecomp,sum_app]
    change _ = _
    simp only [sum,List.foldr_cons]
    omega
  omega

theorem Zlength_ConcatenatedOutputPrefix__output_inner_loop :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j ≤ Znth i lens (0 : Int)) →
    Zlength (ConcatenatedOutputPrefix rows lens i j) =
      sum (sublist (0 : Int) i lens) + j := by
  intro rows lens count width i j hw hi hj
  have h := hw.2.2 i hi
  unfold ConcatenatedOutputPrefix
  rw [Zlength_app,Zlength_ConcatenatedPrefix__output_inner_loop rows lens count width i hw (by omega),
    prefix_len (Znth i rows []) j (by omega)]

theorem ConcatenatedOutputPrefix_lt_sum__output_inner_loop :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < Znth i lens (0 : Int)) →
    Zlength (ConcatenatedOutputPrefix rows lens i j) < sum lens := by
  intro rows lens count width i j hw hi hj
  rw [Zlength_ConcatenatedOutputPrefix__output_inner_loop rows lens count width i j hw hi (by omega)]
  exact sum_prefix_plus_digit_lt_total__output_inner_loop rows lens count width i j hw hi hj

theorem ConcatenatedPrefix_succ__output_inner_loop :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    ConcatenatedPrefix rows lens (i + (1 : Int)) =
      ConcatenatedPrefix rows lens i ++ item_digits (item_at rows lens i) := by
  intro rows lens count width i hw hi
  have hr := hw.1
  have hl := hw.2.1
  unfold ConcatenatedPrefix concatenate_rows paired_items
  rw [sublist_snoc__output_inner_loop [] rows i (by omega),sublist_snoc__output_inner_loop 0 lens i (by omega)]
  have he : (sublist 0 i rows).length=(sublist 0 i lens).length := by
    have h1 := prefix_len rows i (by omega)
    have h2 := prefix_len lens i (by omega)
    simp only [Zlength,Int.ofNat_eq_coe] at h1 h2
    omega
  rw [List.zip_append he]
  simp only [concatenate_items,List.map_append,List.flatten_append,List.zip_cons_cons,List.zip_nil_left,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,item_at]

theorem ConcatenatedOutputPrefix_append__output_inner_loop :
  ∀ flat rows lens count width i j,
    FlatRows flat rows count width →
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < Znth i lens (0 : Int)) →
    ConcatenatedOutputPrefix rows lens i j ++
      Znth (i * width + j) flat (0 : Int) :: [] =
    ConcatenatedOutputPrefix rows lens i (j + (1 : Int)) := by
  intro flat rows lens count width i j hf hw hi hj
  have h := hw.2.2 i hi
  unfold ConcatenatedOutputPrefix
  rw [FlatRows_Znth__compare_left_digit flat rows count width i j hf hi (by omega)]
  rw [sublist_snoc__output_inner_loop 0 (Znth i rows []) j (by omega),List.append_assoc]

theorem ConcatenatedOutputPrefix_full_row__output_inner_loop :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    ConcatenatedOutputPrefix rows lens i (Znth i lens (0 : Int)) =
      ConcatenatedPrefix rows lens (i + (1 : Int)) := by
  intro rows lens count width i hw hi
  rw [ConcatenatedPrefix_succ__output_inner_loop rows lens count width i hw hi]
  rfl

theorem digit_lex_ge_refl__largest_concatenation_final :
  ∀ xs, digit_lex_ge xs xs := by
  exact digit_lex_ge_refl__quicksort_range_composition

theorem digit_lex_ge_cons_strict__largest_concatenation_final :
  ∀ x y xs ys,
    Zlength xs = Zlength ys →
    y < x →
    digit_lex_ge (x :: xs) (y :: ys) := by
  intro x y xs ys hl hxy
  exact (digit_lex_ge_cons_iff__quicksort_range_composition x y xs ys hl).mpr (Or.inl hxy)

theorem digit_lex_ge_cons_same__largest_concatenation_final :
  ∀ x xs ys,
    digit_lex_ge xs ys →
    digit_lex_ge (x :: xs) (x :: ys) := by
  intro x xs ys h
  exact (digit_lex_ge_cons_iff__quicksort_range_composition x x xs ys h.1).mpr (Or.inr ⟨rfl,h⟩)

theorem digit_lex_ge_cons_inv__largest_concatenation_final :
  ∀ x y xs ys,
    digit_lex_ge (x :: xs) (y :: ys) →
    Zlength xs = Zlength ys ∧
    (y < x ∨ (x = y ∧ digit_lex_ge xs ys)) := by
  intro x y xs ys h
  have hl : Zlength xs = Zlength ys := by have := h.1; simp only [Zlength_cons] at this; omega
  exact ⟨hl,(digit_lex_ge_cons_iff__quicksort_range_composition x y xs ys hl).mp h⟩

theorem digit_lex_ge_trans__largest_concatenation_final :
  ∀ xs ys zs,
    digit_lex_ge xs ys →
    digit_lex_ge ys zs →
    digit_lex_ge xs zs := by
  intro xs
  induction xs with
  | nil =>
    intro ys zs hxy hyz
    have hlen := hxy.1
    have hy : ys=[] := by
      simp only [Zlength,List.length_nil,Int.ofNat_eq_coe] at hlen
      exact List.length_eq_zero_iff.mp (by omega)
    subst ys
    exact hyz
  | cons x xs ih =>
    intro ys zs hxy hyz
    cases ys with
    | nil => have := hxy.1; have := Zlength_nonneg xs; simp only [Zlength_nil,Zlength_cons] at *; omega
    | cons y ys =>
      cases zs with
      | nil => have := hyz.1; have := Zlength_nonneg ys; simp only [Zlength_nil,Zlength_cons] at *; omega
      | cons z zs =>
        obtain ⟨h1,htxy⟩ := digit_lex_ge_cons_inv__largest_concatenation_final x y xs ys hxy
        obtain ⟨h2,htyz⟩ := digit_lex_ge_cons_inv__largest_concatenation_final y z ys zs hyz
        apply (digit_lex_ge_cons_iff__quicksort_range_composition x z xs zs (h1.trans h2)).mpr
        rcases htxy with hltxy|⟨hexy,htxy⟩ <;> rcases htyz with hltyz|⟨heyz,htyz⟩
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr ⟨hexy.trans heyz,ih _ _ htxy htyz⟩

theorem digit_lex_ge_prefix__largest_concatenation_final :
  ∀ «prefix» xs ys,
    digit_lex_ge xs ys →
    digit_lex_ge («prefix» ++ xs) («prefix» ++ ys) := by
  intro pre xs ys h
  induction pre with
  | nil => exact h
  | cons x pre ih => exact digit_lex_ge_cons_same__largest_concatenation_final x _ _ ih

theorem digit_lex_ge_suffix__largest_concatenation_final :
  ∀ xs ys suffix,
    digit_lex_ge xs ys →
    digit_lex_ge (xs ++ suffix) (ys ++ suffix) := by
  intro xs ys suf h
  refine ⟨by simp only [Zlength_app]; rw [h.1],?_⟩
  rcases h.2 with he|⟨k,hk,hpre,hgt⟩
  · exact Or.inl (by rw [he])
  · refine Or.inr ⟨k,by have := Zlength_nonneg suf; simp only [Zlength_app]; omega,?_,?_⟩
    · intro j hj
      rw [app_Znth1 0 xs suf j (by omega),app_Znth1 0 ys suf j (by have := h.1; omega)]
      exact hpre j hj
    · rw [app_Znth1 0 ys suf k (by have := h.1; omega),app_Znth1 0 xs suf k hk]
      exact hgt

theorem concatenate_items_nil__largest_concatenation_final :
  concatenate_items [] = [] := by
  rfl

theorem concatenate_items_cons__largest_concatenation_final :
  ∀ x xs,
    concatenate_items (x :: xs) =
    item_digits x ++ concatenate_items xs := by
  intros
  rfl

theorem concatenate_items_app__largest_concatenation_final :
  ∀ xs ys,
    concatenate_items (xs ++ ys) =
    concatenate_items xs ++ concatenate_items ys := by
  intros
  simp [concatenate_items,List.map_append,List.flatten_append]

theorem item_moves_after_list__largest_concatenation_final :
  ∀ x items,
    (∀ y,
       In y items →
       digit_lex_ge
         (item_digits x ++ item_digits y)
         (item_digits y ++ item_digits x)) →
    digit_lex_ge
      (item_digits x ++ concatenate_items items)
      (concatenate_items items ++ item_digits x) := by
  intro x items
  induction items with
  | nil => intro h; simpa only [concatenate_items,List.map_nil,List.flatten_nil,List.append_nil,List.nil_append] using digit_lex_ge_refl__largest_concatenation_final (item_digits x)
  | cons y ys ih =>
    intro h
    have hxy := h y (List.mem_cons_self ..)
    have ht := ih (fun z hz => h z (List.mem_cons_of_mem y hz))
    have hs := digit_lex_ge_suffix__largest_concatenation_final _ _ (concatenate_items ys) hxy
    have hm := digit_lex_ge_prefix__largest_concatenation_final (item_digits y) _ _ ht
    simpa only [concatenate_items_cons__largest_concatenation_final,List.append_assoc] using
      digit_lex_ge_trans__largest_concatenation_final _ _ _ hs (by simpa only [List.append_assoc] using hm)

theorem ordered_items_maximize_concatenation__largest_concatenation_final :
  ∀ items alternative,
    (∀ «prefix» x middle y suffix,
       items = «prefix» ++ x :: middle ++ y :: suffix →
       digit_lex_ge
         (item_digits x ++ item_digits y)
         (item_digits y ++ item_digits x)) →
    Permutation items alternative →
    digit_lex_ge
      (concatenate_items items)
      (concatenate_items alternative) := by
  intro items
  induction items with
  | nil =>
    intro alternative ho hp
    have he : alternative=[] := List.length_eq_zero_iff.mp (by have := hp.length_eq; simp only [List.length_nil] at this; omega)
    subst alternative
    exact digit_lex_ge_refl__largest_concatenation_final _
  | cons x xs ih =>
    intro alternative ho hp
    have hin : x ∈ alternative := hp.mem_iff.mp (List.mem_cons_self ..)
    obtain ⟨pre,suf,he⟩ := List.mem_iff_append.mp hin
    subst alternative
    have ht : List.Perm xs (pre++suf) := (hp.trans List.perm_middle).cons_inv
    have hot : ∀ pre a mid b suf, xs=pre++a::mid++b::suf →
        digit_lex_ge (item_digits a++item_digits b) (item_digits b++item_digits a) := by
      intro pre a mid b suf he
      apply ho (x::pre) a mid b suf
      simp only [List.cons_append,←he]
    have htge := ih (pre++suf) hot ht
    have hhead := digit_lex_ge_prefix__largest_concatenation_final (item_digits x) _ _ htge
    have hcross : ∀ y, In y pre → digit_lex_ge (item_digits x++item_digits y) (item_digits y++item_digits x) := by
      intro y hy
      have hym : y∈xs := ht.mem_iff.mpr (List.mem_append_left suf hy)
      obtain ⟨before,after,he⟩ := List.mem_iff_append.mp hym
      apply ho [] x before y after
      simp only [List.nil_append,List.cons_append,←he]
    have hb := item_moves_after_list__largest_concatenation_final x pre hcross
    have hbs := digit_lex_ge_suffix__largest_concatenation_final _ _ (concatenate_items suf) hb
    apply digit_lex_ge_trans__largest_concatenation_final _ _ _
      (by simpa only [concatenate_items_cons__largest_concatenation_final,
        concatenate_items_app__largest_concatenation_final,List.append_assoc] using hhead)
    simpa only [concatenate_items_app__largest_concatenation_final,
      concatenate_items_cons__largest_concatenation_final,List.append_assoc] using hbs

theorem Zlength_paired_items__largest_concatenation_final :
  ∀ rows lens,
    Zlength rows = Zlength lens →
    Zlength (paired_items rows lens) = Zlength rows := by
  exact paired_items_length__pivot_finalization

theorem Znth_paired_items__largest_concatenation_final :
  ∀ rows lens i,
    Zlength rows = Zlength lens → ((0 : Int) ≤ i ∧ i < Zlength rows) →
    Znth i (paired_items rows lens) ([], (0 : Int)) =
    item_at rows lens i := by
  exact Znth_paired_items__pivot_finalization

theorem Znth_at_app_cons__largest_concatenation_final :
  ∀ (A : Type) (default x : A) «prefix» suffix,
    Znth (Zlength «prefix») («prefix» ++ x :: suffix) default = x := by
  intro A d x pre suf
  rw [app_Znth2 d pre (x::suf) (Zlength pre) (by omega)]
  simp only [Int.sub_self,Znth0_cons]

theorem greedy_sorted_orders_paired_items__largest_concatenation_final :
  ∀ rows lens,
    Zlength rows = Zlength lens →
    GreedySorted rows lens →
    ∀ «prefix» x middle y suffix,
      paired_items rows lens = «prefix» ++ x :: middle ++ y :: suffix →
      digit_lex_ge
        (item_digits x ++ item_digits y)
        (item_digits y ++ item_digits x) := by
  intro rows lens he hs pre x mid y suf hp
  let i := Zlength pre
  let j := Zlength (pre++x::mid)
  have hlen := paired_items_length__pivot_finalization rows lens he
  have hb : 0≤i ∧ i≤j ∧ j<Zlength rows := by
    rw [hp] at hlen
    dsimp only [i,j]
    simp only [Zlength_app,Zlength_cons] at *
    have := Zlength_nonneg pre
    have := Zlength_nonneg mid
    have := Zlength_nonneg suf
    omega
  have hi : item_at rows lens i=x := by
    rw [←Znth_paired_items__pivot_finalization rows lens i he (by omega),hp]
    simp only [List.append_assoc,List.cons_append]
    change Znth (Zlength pre) (pre++x::(mid++y::suf)) ([],0)=x
    exact Znth_at_app_cons__largest_concatenation_final _ _ _ _ _
  have hj : item_at rows lens j=y := by
    rw [←Znth_paired_items__pivot_finalization rows lens j he (by omega),hp]
    have heq : pre++x::mid++y::suf = (pre++x::mid)++y::suf := by simp only [List.append_assoc,List.cons_append]
    rw [heq]
    exact Znth_at_app_cons__largest_concatenation_final _ _ _ _ _
  have ho := hs i j hb
  change digit_lex_ge (item_digits (item_at rows lens i)++item_digits (item_at rows lens j)) _ at ho
  simpa only [hi,hj] using ho

theorem greedy_sorted_maximizes_concatenate_rows__largest_concatenation_final :
  ∀ rows lens alternative_rows alternative_lens,
    Zlength rows = Zlength lens →
    GreedySorted rows lens →
    Permutation (paired_items rows lens)
                (paired_items alternative_rows alternative_lens) →
    digit_lex_ge
      (concatenate_rows rows lens)
      (concatenate_rows alternative_rows alternative_lens) := by
  intro rows lens arows alens he hs hp
  exact ordered_items_maximize_concatenation__largest_concatenation_final _ _
    (greedy_sorted_orders_paired_items__largest_concatenation_final rows lens he hs) hp

theorem RowsWellFormed_item_digits_length__largest_concatenation_final :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    Zlength (item_digits (item_at rows lens i)) = Znth i lens (0 : Int) := by
  intro rows lens count width i hw hi
  have h := hw.2.2 i hi
  change Zlength (sublist 0 (Znth i lens 0) (Znth i rows [])) = _
  exact prefix_len _ _ (by omega)

theorem concatenate_rows_length_from_items__largest_concatenation_final :
  ∀ rows lens,
    Zlength rows = Zlength lens →
    (∀ i, ((0 : Int) ≤ i ∧ i < Zlength rows) →
       Zlength (item_digits (item_at rows lens i)) = Znth i lens (0 : Int)) →
    Zlength (concatenate_rows rows lens) = sum lens := by
  exact concat_length

theorem RowsWellFormed_concatenate_rows_length__largest_concatenation_final :
  ∀ rows lens count width,
    RowsWellFormed rows lens count width →
    Zlength (concatenate_rows rows lens) = sum lens := by
  intro rows lens count width hw
  apply Zlength_concatenate_rows_pointwise__output_inner_loop rows lens (hw.1.trans hw.2.1.symm)
  have hr := hw.1
  intro i hi
  have h := hw.2.2 i (by omega)
  exact ⟨by omega,by omega⟩

theorem ConcatenatedPrefix_full__largest_concatenation_final :
  ∀ rows lens count width,
    RowsWellFormed rows lens count width →
    ConcatenatedPrefix rows lens count = concatenate_rows rows lens := by
  intro rows lens count width hw
  unfold ConcatenatedPrefix
  rw [sublist_self rows count hw.1.symm,sublist_self lens count hw.2.1.symm]

theorem GreedySorted_LargestConcatenation__largest_concatenation_final :
  ∀ original_rows arranged_rows original_lens arranged_lens count width,
    RowsWellFormed arranged_rows arranged_lens count width →
    PairedPermutation original_rows arranged_rows
                      original_lens arranged_lens →
    GreedySorted arranged_rows arranged_lens →
    LargestConcatenationLegacy
      original_rows arranged_rows original_lens arranged_lens
      (concatenate_rows arranged_rows arranged_lens) := by
  intro orows rows olens lens count width hw hp hs
  refine ⟨hp,rfl,?_⟩
  intro arows alens ha
  exact greedy_sorted_maximizes_concatenate_rows__largest_concatenation_final rows lens arows alens
    hp.2.1 hs (hp.2.2.symm.trans ha.2.2)

end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib
namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers
export concatenating_numbers_lib (number_item item_digits paired_items concatenate_items concatenate_rows digit_lex_ge digit_lex_gt item_at item_before item_before_or_equal ConcatLeftDigit ConcatRightDigit RowsWellFormed FlatRows PairedPermutation SameOutsidePairedRange ConcatComparePrefix ConcatCompareOutcome swap_Znth SwapRowsPrefix PartitionScanState GreedyPartitionedAt GreedySortedRange GreedySorted ConcatenatedPrefix ConcatenatedOutputPrefix LargestConcatenationLegacy)
end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib
open AUXLib

export SimpleC.EE.LLM_bench.Algorithms.decimal_digits (DecimalRowValues)
def LargestConcatenation (rows : List (List Int)) (lens output : List Int) : Prop :=
  MaxMinLib.max_value_of_subset (fun xs ys => digit_lex_ge ys xs)
    (Permutation (paired_items rows lens)) concatenate_items output

end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib
namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers
export concatenating_numbers_lib (DecimalRowValues LargestConcatenation)
end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers
