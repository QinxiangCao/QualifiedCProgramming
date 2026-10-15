import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import Mathlib.Data.List.Induction
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib
open AUXLib

abbrev _App_option_Z := Option Int
abbrev _List_Z := List Int
abbrev Some {A : Type} (x : A) : Option A := .some x
abbrev None {A : Type} : Option A := .none


abbrev concat {A : Type} (xs : List (List A)) : List A := xs.flatten

def NextNestedItem (previous next : List Int) : Prop :=
  next = previous ++ [1] ∨ ∃ «prefix» last suffix,
    previous = «prefix» ++ last :: suffix ∧ next = «prefix» ++ [last+1] ∧ Forall (fun x => x ≠ last) suffix

def Pre (last_numbers : List Int) : Prop :=
  (1 ≤ Zlength last_numbers ∧ Zlength last_numbers ≤ 1000) ∧
  Forall (fun x => 1 ≤ x ∧ x ≤ Zlength last_numbers) last_numbers ∧
  ∃ items, Zlength items = Zlength last_numbers ∧ Znth 0 items [] = [1] ∧
    (∀ i, (0 ≤ i ∧ i < Zlength items-1) → NextNestedItem (Znth i items []) (Znth (i+1) items [])) ∧
    List.Forall₂ (fun item last_number => Znth (Zlength item - 1) item 0 = last_number) items last_numbers

def Spec (last_numbers : List Int) (out : List (List Int)) : Prop :=
  Zlength out = Zlength last_numbers ∧ Znth 0 out [] = [1] ∧
    (∀ i, (0 ≤ i ∧ i < Zlength out-1) → NextNestedItem (Znth i out []) (Znth (i+1) out [])) ∧
    List.Forall₂ (fun item last_number => Znth (Zlength item - 1) item 0 = last_number) out last_numbers

def CurrentItem (items : List (List Int)) (count : Int) (active : List Int) : Prop :=
  (count = 0 ∧ active = []) ∨ (0 < count ∧ active = Znth (count - 1) items [])

def PopTarget (active target : List Int) (x : Int) : Prop :=
  ∃ «prefix» last suffix, active = «prefix» ++ last :: suffix ∧ target = «prefix» ++ [last+1] ∧
    x = last + 1 ∧ Forall (fun y => y ≠ last) suffix

def FlatPrefix (items : List (List Int)) (count : Int) (flat_data : List Int) : Prop :=
  flat_data = (sublist 0 count items).flatten

def LengthsPrefix (items : List (List Int)) (count : Int) (lengths_data : List Int) : Prop :=
  Zlength lengths_data = count ∧ ∀ i, (0 ≤ i ∧ i < count) → Znth i lengths_data 0 = Zlength (Znth i items [])

def BoundedItem (bound : Int) (item : List Int) : Prop := Forall (fun value => 1 ≤ value ∧ value ≤ bound) item

private theorem zlength_snoc {A : Type} (l : List A) (a : A) : Zlength (l++[a])=Zlength l+1 := by
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

private theorem znth_snoc {A : Type} (d : A) (l : List A) (a : A) : Znth (Zlength l) (l++[a]) d=a := by
  rw [app_Znth2 d l [a] (Zlength l) (le_refl _),sub_self]
  rfl

private theorem znth_app_left {A : Type} (d : A) (l l' : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) : Znth i (l++l') d=Znth i l d := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

private theorem forall_snoc {A : Type} (P : A→Prop) (l : List A) (a : A) (h : Forall P l) (ha : P a) : Forall P (l++[a]) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h.mem hx
  · simpa only [List.mem_singleton.mp hx] using ha

theorem Forall_Znth__semantic_transitions (A : Type) (P : A→Prop) (values : List A) (default : A) (i : Int)
    (h : Forall P values) (hi : 0≤i ∧ i<Zlength values) : P (Znth i values default) := by
  apply h.mem
  have hn : i.toNat<values.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

theorem BoundedItem_nil (bound : Int) : BoundedItem bound [] := Forall.nil

theorem BoundedItem_Znth (bound : Int) (item : List Int) (i : Int) (h : BoundedItem bound item) (hi : 0≤i ∧ i<Zlength item) :
    1≤Znth i item 0 ∧ Znth i item 0≤bound := Forall_Znth__semantic_transitions Int _ item 0 i h hi

theorem BoundedItem_append_one (bound : Int) (item : List Int) (hb : 1≤bound) (h : BoundedItem bound item) : BoundedItem bound (item++[1]) :=
  forall_snoc _ item 1 h ⟨le_refl _,hb⟩

theorem BoundedItem_prefix (bound : Int) (pre suf : List Int) (h : BoundedItem bound (pre++suf)) : BoundedItem bound pre :=
  Forall.iff_forall_mem.mpr (fun x hx=>h.mem (List.mem_append_left suf hx))

theorem PopTarget_preserves_bounds (bound : Int) (active target : List Int) (x : Int) (h : BoundedItem bound active)
    (hx : 1≤x ∧ x≤bound) (hp : PopTarget active target x) : BoundedItem bound target := by
  rcases hp with ⟨pre,last,suf,rfl,rfl,rfl,hf⟩
  exact forall_snoc _ pre (last+1) (BoundedItem_prefix bound pre (last::suf) h) hx

theorem Forall2_Znth__semantic_transitions (A B : Type) (R : A→B→Prop) (left : List A) (right : List B) (ld : A) (rd : B) (i : Int)
    (h : List.Forall₂ R left right) (hi : 0≤i ∧ i<Zlength left) : R (Znth i left ld) (Znth i right rd) := by
  induction h generalizing i with
  | nil => simp only [Zlength_nil] at hi; omega
  | @cons a b left right hab h ih =>
    by_cases hz : i=0
    · subst i
      exact hab
    · rw [Znth_cons ld i a left (by omega),Znth_cons rd i b right (by omega)]
      apply ih
      rw [Zlength_cons] at hi
      omega

theorem Forall_removelast__semantic_transitions (A : Type) (P : A→Prop) (values : List A) (h : Forall P values) : Forall P values.dropLast :=
  Forall.iff_forall_mem.mpr (fun x hx=>h.mem ((List.dropLast_sublist values).subset hx))

theorem Zlength_removelast_nonempty__semantic_transitions (A : Type) (values : List A) (hne : values≠[]) :
    Zlength values.dropLast=Zlength values-1 := by
  have hn : 0<values.length := List.length_pos_iff.mpr hne
  simp only [Zlength,List.length_dropLast,Int.ofNat_eq_coe]
  omega

theorem Spec_step_and_last__semantic_transitions (last_numbers : List Int) (items : List (List Int)) (active : List Int) (line : Int)
    (h : Spec last_numbers items) (hc : CurrentItem items line active) (hi : 0<line ∧ line<Zlength items) :
    NextNestedItem active (Znth line items []) ∧ Znth (Zlength (Znth line items [])-1) (Znth line items []) 0=Znth line last_numbers 0 := by
  have ht := h.2.2.1 (line-1) (by omega)
  rw [show line-1+1=line by omega] at ht
  have ha : active=Znth (line-1) items [] := by rcases hc with ⟨h1,h2⟩ | ⟨h1,h2⟩; omega; exact h2
  rw [←ha] at ht
  exact ⟨ht,Forall2_Znth__semantic_transitions (List Int) Int _ items last_numbers [] 0 line h.2.2.2 (by omega)⟩

theorem Znth_last_snoc__semantic_transitions (A : Type) (pre : List A) (value default : A) :
    Znth (Zlength (pre++[value])-1) (pre++[value]) default=value := by
  rw [zlength_snoc,add_sub_cancel_right,znth_snoc]

theorem Spec_nonone_pop__semantic_transitions (last_numbers : List Int) (items : List (List Int)) (active : List Int) (line : Int)
    (h : Spec last_numbers items) (hc : CurrentItem items line active) (hi : 0≤line ∧ line<Zlength items) (hne : Znth line last_numbers 0≠1) :
    0<line ∧ PopTarget active (Znth line items []) (Znth line last_numbers 0) := by
  have hp : 0<line := by
    by_contra hn
    have he : line=0 := by omega
    have hx := Forall2_Znth__semantic_transitions (List Int) Int _ items last_numbers [] 0 line h.2.2.2 hi
    rw [he,h.2.1] at hx
    change (1:Int)=Znth 0 last_numbers 0 at hx
    exact hne (he ▸ hx.symm)
  have ht := Spec_step_and_last__semantic_transitions last_numbers items active line h hc ⟨hp,hi.2⟩
  refine ⟨hp,?_⟩
  rcases ht.1 with happ | ⟨pre,last,suf,ha,hitem,hf⟩
  · have hh := ht.2
    rw [happ,Znth_last_snoc__semantic_transitions] at hh
    exact False.elim (hne hh.symm)
  · refine ⟨pre,last,suf,ha,hitem,?_,hf⟩
    have hh := ht.2
    rw [hitem,Znth_last_snoc__semantic_transitions] at hh
    exact hh.symm

theorem Spec_one_append__semantic_transitions (bound : Int) (last_numbers : List Int) (items : List (List Int)) (active : List Int) (line : Int)
    (h : Spec last_numbers items) (hc : CurrentItem items line active) (hi : 0≤line ∧ line<Zlength items)
    (hb : BoundedItem bound active) (hbound : 1≤bound) (hone : Znth line last_numbers 0=1) : Znth line items []=active++[1] := by
  by_cases hz : line=0
  · subst line
    have ha : active=[] := by rcases hc with ⟨h1,h2⟩ | ⟨h1,h2⟩; exact h2; omega
    rw [ha,h.2.1]
    rfl
  · have ht := Spec_step_and_last__semantic_transitions last_numbers items active line h hc ⟨by omega,hi.2⟩
    rcases ht.1 with happ | ⟨pre,last,suf,ha,hitem,hf⟩
    · exact happ
    · have hh := ht.2
      rw [hitem,Znth_last_snoc__semantic_transitions,hone] at hh
      rw [ha] at hb
      have hl := hb.mem (List.mem_append_right pre List.mem_cons_self)
      omega

theorem stack_append_one_invariant__semantic_transitions (cells : List (Option Int)) (active : List Int) (depth : Int) (default : Option Int)
    (hd : depth=Zlength active) (hi : 0≤depth ∧ depth<Zlength cells)
    (h : ∀ k, (0≤k ∧ k<depth) → Znth k cells default=Some (Znth k active 0)) :
    Zlength (replace_Znth depth (Some 1) cells)=Zlength cells ∧
      ∀ k, (0≤k ∧ k<depth+1) → Znth k (replace_Znth depth (Some 1) cells) default=Some (Znth k (active++[1]) 0) := by
  refine ⟨AUXLib.Zlength_replace_Znth cells depth _,?_⟩
  intro k hk
  by_cases he : k=depth
  · subst k
    rw [Znth_replace_Znth_Same default cells depth _ hi,hd,znth_snoc]
  · rw [Znth_replace_Znth_Diff default cells depth k _ hi (by omega) (Ne.symm he),znth_app_left 0 active [1] k (by omega)]
    exact h k (by omega)

theorem sublist_snoc_Znth__flattening_and_completion (A : Type) (d : A) (i : Int) (xs : List A) (hi : 0≤i ∧ i<Zlength xs) :
    sublist 0 (i+1) xs=sublist 0 i xs++[Znth i xs d] := by
  rw [sublist_split 0 (i+1) i xs (by omega) (by omega),sublist_single d i xs hi]

theorem FlatPrefix_snoc__flattening_and_completion (items : List (List Int)) (line : Int) (flat : List Int)
    (h : FlatPrefix items line flat) (hi : 0≤line ∧ line<Zlength items) : FlatPrefix items (line+1) (flat++Znth line items []) := by
  unfold FlatPrefix at h ⊢
  rw [sublist_snoc_Znth__flattening_and_completion (List Int) [] line items hi,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,h]

theorem FlatPrefix_full__flattening_and_completion (items : List (List Int)) (count : Int) (flat : List Int)
    (h : FlatPrefix items count flat) (hc : count=Zlength items) : flat=concat items := by
  unfold FlatPrefix at h
  rw [sublist_self items count hc] at h
  exact h

theorem LengthsPrefix_snoc__flattening_and_completion (items : List (List Int)) (line : Int) (lengths : List Int)
    (h : LengthsPrefix items line lengths) (hi : 0≤line ∧ line<Zlength items) :
    LengthsPrefix items (line+1) (lengths++[Zlength (Znth line items [])]) := by
  have hl := h.1
  refine ⟨by rw [zlength_snoc,hl],?_⟩
  intro i hir
  by_cases he : i=line
  · subst i
    rw [←hl,znth_snoc,hl]
  · rw [znth_app_left 0 lengths _ i (by omega)]
    exact h.2 i (by omega)

theorem LengthsPrefix_full__flattening_and_completion (items : List (List Int)) (count : Int) (lengths : List Int)
    (hc : count=Zlength items) (h : LengthsPrefix items count lengths) :
    Zlength lengths=count ∧ ∀ i, (0≤i ∧ i<count) → Znth i lengths 0=Zlength (Znth i items []) := h

private theorem znth_dropLast {A : Type} (l : List A) (d : A) (i : Int) (hi : 0≤i ∧ i<Zlength l.dropLast) :
    Znth i l.dropLast d=Znth i l d := by
  have hn : i.toNat<l.length-1 := by simp only [Zlength,List.length_dropLast,Int.ofNat_eq_coe] at hi; omega
  rw [List.dropLast_eq_take]
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_take_of_lt hn]

theorem PopTarget_remove_last__semantic_transitions (bound : Int) (active target : List Int) (x : Int)
    (hb : BoundedItem bound active) (hp : PopTarget active target x) (hne : Znth (Zlength active-1) active 0+1≠x) :
    2≤Zlength active ∧ Zlength active.dropLast=Zlength active-1 ∧ PopTarget active.dropLast target x ∧
      BoundedItem bound active.dropLast ∧ (∀ i, (0≤i ∧ i<Zlength active.dropLast) → Znth i active.dropLast 0=Znth i active 0) := by
  rcases hp with ⟨pre,last,suf,ha,ht,hx,hf⟩
  cases suf using List.reverseRecOn with
  | nil =>
    rw [ha,Znth_last_snoc__semantic_transitions] at hne
    omega
  | append_singleton suf value =>
    have has : active=(pre++last::suf)++[value] := by rw [ha,List.append_assoc]; rfl
    have hdr : active.dropLast=pre++last::suf := by rw [has,List.dropLast_concat]
    have hnpre := Zlength_nonneg pre
    have hnsuf := Zlength_nonneg suf
    have hlen : Zlength active=Zlength pre+(Zlength suf+1)+1 := by rw [has,zlength_snoc,Zlength_app,Zlength_cons]
    have hnonempty : active≠[] := by intro he; rw [he,Zlength_nil] at hlen; omega
    refine ⟨by omega,Zlength_removelast_nonempty__semantic_transitions Int active hnonempty,?_,Forall_removelast__semantic_transitions Int _ active hb,?_⟩
    · exact ⟨pre,last,suf,hdr,ht,hx,Forall.iff_forall_mem.mpr (fun v hv=>hf.mem (List.mem_append_left [value] hv))⟩
    · intro i hi
      exact znth_dropLast active 0 i hi

private theorem replace_last_snoc (pre : List Int) (last x : Int) :
    replace_Znth (Zlength (pre++[last])-1) x (pre++[last])=pre++[x] := by
  rw [zlength_snoc,add_sub_cancel_right,replace_Znth_app_r (Zlength pre) x pre [last] (le_refl _),
    replace_Znth_nothing (Zlength pre) pre x (le_refl _),sub_self]
  rfl

theorem PopTarget_last_match__semantic_transitions (bound : Int) (active target : List Int) (x : Int)
    (hb : BoundedItem bound active) (hxbound : 1≤x ∧ x≤bound) (hp : PopTarget active target x)
    (hmatch : Znth (Zlength active-1) active 0+1=x) :
    target=replace_Znth (Zlength active-1) x active ∧ BoundedItem bound target := by
  refine ⟨?_,PopTarget_preserves_bounds bound active target x hb hxbound hp⟩
  rcases hp with ⟨pre,last,suf,ha,ht,hx,hf⟩
  cases suf using List.reverseRecOn with
  | nil =>
    rw [ha,replace_last_snoc,ht,hx]
  | append_singleton suf value =>
    have has : active=(pre++last::suf)++[value] := by rw [ha,List.append_assoc]; rfl
    rw [has,Znth_last_snoc__semantic_transitions] at hmatch
    have hne := hf.mem (List.mem_append_right suf (List.mem_singleton_self value))
    omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib
