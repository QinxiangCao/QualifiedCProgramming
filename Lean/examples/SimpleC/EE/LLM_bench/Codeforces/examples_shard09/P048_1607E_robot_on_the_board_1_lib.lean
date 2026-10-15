import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib
open AUXLib


open MaxMinLib
abbrev fst {A B : Type} (p : A × B) : A := p.1
abbrev snd {A B : Type} (p : A × B) : B := p.2

def Delta (c : Int) : Int × Int :=
  if c = 76 then (0,-1) else if c = 82 then (0,1) else if c = 85 then (-1,0) else (1,0)

def Executes (n m : Int) (s : List Int) (start : Int × Int) (q : Int) : Prop :=
  (0 ≤ q ∧ q ≤ Zlength s) ∧ ∀ p, (0 ≤ p ∧ p ≤ q) →
    let ds := (sublist 0 p s).map Delta
    (1 ≤ start.1 + (ds.map Prod.fst).foldr (· + ·) 0 ∧ start.1 + (ds.map Prod.fst).foldr (· + ·) 0 ≤ n) ∧
    (1 ≤ start.2 + (ds.map Prod.snd).foldr (· + ·) 0 ∧ start.2 + (ds.map Prod.snd).foldr (· + ·) 0 ≤ m)

def Pre (n m : Int) (s : List Int) : Prop := True

def Spec (n m : Int) (s : List Int) (out : Int × Int) : Prop :=
  (1 ≤ out.1 ∧ out.1 ≤ n) ∧ (1 ≤ out.2 ∧ out.2 ≤ m) ∧ ∃ q, Executes n m s out q ∧
    max_value_of_subset (· ≤ ·) (fun q' => ∃ st : Int × Int,
      (1 ≤ st.1 ∧ st.1 ≤ n) ∧ (1 ≤ st.2 ∧ st.2 ≤ m) ∧ Executes n m s st q') (fun x => x) q

def RowOffset (s : List Int) (q : Int) : Int :=
  (((sublist 0 q s).map Delta).map Prod.fst).foldr (· + ·) 0

def ColOffset (s : List Int) (q : Int) : Int :=
  (((sublist 0 q s).map Delta).map Prod.snd).foldr (· + ·) 0

def PrefixWindow (s : List Int) (q r c minr maxr minc maxc : Int) : Prop :=
  (0 ≤ q ∧ q ≤ Zlength s) ∧ r = RowOffset s q ∧ c = ColOffset s q ∧
  (minr ≤ 0 ∧ 0 ≤ maxr) ∧ (minc ≤ 0 ∧ 0 ≤ maxc) ∧
  (∀ p, (0 ≤ p ∧ p ≤ q) → (minr ≤ RowOffset s p ∧ RowOffset s p ≤ maxr) ∧
    (minc ≤ ColOffset s p ∧ ColOffset s p ≤ maxc)) ∧
  (∃ p, (0 ≤ p ∧ p ≤ q) ∧ RowOffset s p = minr) ∧
  (∃ p, (0 ≤ p ∧ p ≤ q) ∧ RowOffset s p = maxr) ∧
  (∃ p, (0 ≤ p ∧ p ≤ q) ∧ ColOffset s p = minc) ∧
  (∃ p, (0 ≤ p ∧ p ≤ q) ∧ ColOffset s p = maxc)

def WindowFits (n m minr maxr minc maxc : Int) : Prop := maxr - minr < n ∧ maxc - minc < m

def OptimalPrefixWindow (n m : Int) (s : List Int) (minr maxr minc maxc : Int) : Prop :=
  ∃ q r c, PrefixWindow s q r c minr maxr minc maxc ∧ WindowFits n m minr maxr minc maxc ∧
    max_value_of_subset (· ≤ ·) (fun q' => ∃ st : Int × Int,
      (1 ≤ st.1 ∧ st.1 ≤ n) ∧ (1 ≤ st.2 ∧ st.2 ≤ m) ∧ Executes n m s st q') (fun x => x) q

private theorem fold_snoc (l : List Int) (x : Int) : (l++[x]).foldr (·+·) 0=l.foldr (·+·) 0+x := by
  induction l with
  | nil => simp only [List.nil_append,List.foldr_cons,List.foldr_nil,zero_add,add_zero]
  | cons a l ih => simp only [List.cons_append,List.foldr_cons,ih,add_assoc]

private theorem offset_step (s : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength s) :
    RowOffset s (i+1)=RowOffset s i+(Delta (Znth i s 0)).1 ∧
    ColOffset s (i+1)=ColOffset s i+(Delta (Znth i s 0)).2 := by
  have hs : sublist 0 (i+1) s=sublist 0 i s++[Znth i s 0] := by
    rw [sublist_split 0 (i+1) i s (by omega) (by omega),sublist_single 0 i s hi]
  unfold RowOffset ColOffset
  rw [hs]
  simp only [List.map_append,List.map_cons,List.map_nil,fold_snoc]
  trivial

private theorem window_extend (s : List Int) (i r c minr maxr minc maxc nr nc nminr nmaxr nminc nmaxc : Int)
    (hi : 0≤i ∧ i<Zlength s) (h : PrefixWindow s i r c minr maxr minc maxc)
    (hr : nr=RowOffset s (i+1)) (hc : nc=ColOffset s (i+1))
    (hgrow : nminr≤minr ∧ maxr≤nmaxr ∧ nminc≤minc ∧ maxc≤nmaxc)
    (hnew : (nminr≤nr ∧ nr≤nmaxr) ∧ (nminc≤nc ∧ nc≤nmaxc))
    (hatt : (nminr=minr ∨ nminr=nr) ∧ (nmaxr=maxr ∨ nmaxr=nr) ∧
      (nminc=minc ∨ nminc=nc) ∧ (nmaxc=maxc ∨ nmaxc=nc)) :
    PrefixWindow s (i+1) nr nc nminr nmaxr nminc nmaxc := by
  rcases h with ⟨hqi,hri,hci,hzr,hzc,hall,hminr,hmaxr,hminc,hmaxc⟩
  refine ⟨by omega,hr,hc,by omega,by omega,?_,?_,?_,?_,?_⟩
  · intro p hp
    by_cases hpi : p≤i
    · have hh := hall p ⟨hp.1,hpi⟩
      omega
    · have he : p=i+1 := by omega
      rw [he,←hr,←hc]
      exact hnew
  · rcases hatt.1 with he | he
    · rcases hminr with ⟨p,hp,hv⟩
      exact ⟨p,by omega,hv.trans he.symm⟩
    · exact ⟨i+1,by omega,hr.symm.trans he.symm⟩
  · rcases hatt.2.1 with he | he
    · rcases hmaxr with ⟨p,hp,hv⟩
      exact ⟨p,by omega,hv.trans he.symm⟩
    · exact ⟨i+1,by omega,hr.symm.trans he.symm⟩
  · rcases hatt.2.2.1 with he | he
    · rcases hminc with ⟨p,hp,hv⟩
      exact ⟨p,by omega,hv.trans he.symm⟩
    · exact ⟨i+1,by omega,hc.symm.trans he.symm⟩
  · rcases hatt.2.2.2 with he | he
    · rcases hmaxc with ⟨p,hp,hv⟩
      exact ⟨p,by omega,hv.trans he.symm⟩
    · exact ⟨i+1,by omega,hc.symm.trans he.symm⟩

private theorem current_bounds (s : List Int) (i r c minr maxr minc maxc : Int)
    (h : PrefixWindow s i r c minr maxr minc maxc) : (minr≤r ∧ r≤maxr) ∧ (minc≤c ∧ c≤maxc) := by
  have hh := h.2.2.2.2.2.1 i ⟨h.1.1,le_refl _⟩
  rw [←h.2.1,←h.2.2.1] at hh
  exact hh

theorem prefix_window_zero__initialization (s : List Int) : PrefixWindow s 0 0 0 0 0 0 0 := by
  have hlen := Zlength_nonneg s
  have hr : RowOffset s 0=0 := by simp only [RowOffset,sublist,Int.toNat_zero,List.take_zero,List.drop_nil,List.map_nil,List.foldr_nil]
  have hc : ColOffset s 0=0 := by simp only [ColOffset,sublist,Int.toNat_zero,List.take_zero,List.drop_nil,List.map_nil,List.foldr_nil]
  refine ⟨by omega,hr.symm,hc.symm,by omega,by omega,?_,⟨0,by omega,hr⟩,⟨0,by omega,hr⟩,⟨0,by omega,hc⟩,⟨0,by omega,hc⟩⟩
  intro p hp
  have he : p=0 := by omega
  rw [he,hr,hc]
  omega

theorem prefix_window_step_up_new_min__up_new_min (s : List Int) (i r c minr maxr minc maxc : Int)
    (hi : 0≤i ∧ i<Zlength s) (hcmd : Znth i s 0=85) (h : PrefixWindow s i r c minr maxr minc maxc)
    (hm : r-1<minr) (hc : minc≤c ∧ c≤maxc) : PrefixWindow s (i+1) (r-1) c (r-1) maxr minc maxc := by
  have ho := offset_step s i hi
  rw [hcmd] at ho
  change RowOffset s (i+1)=RowOffset s i+(-1) ∧ ColOffset s (i+1)=ColOffset s i+0 at ho
  have hr := h.2.1
  have hcol := h.2.2.1
  have hb := current_bounds s i r c minr maxr minc maxc h
  apply window_extend s i r c minr maxr minc maxc (r-1) c (r-1) maxr minc maxc hi h <;> omega

theorem prefix_window_step_up_inside__up_inside (s : List Int) (i r c minr maxr minc maxc : Int)
    (hi : 0≤i ∧ i<Zlength s) (hcmd : Znth i s 0=85) (h : PrefixWindow s i r c minr maxr minc maxc)
    (hm : minr≤r-1 ∧ r-1≤maxr) (hc : minc≤c ∧ c≤maxc) : PrefixWindow s (i+1) (r-1) c minr maxr minc maxc := by
  have ho := offset_step s i hi
  rw [hcmd] at ho
  change RowOffset s (i+1)=RowOffset s i+(-1) ∧ ColOffset s (i+1)=ColOffset s i+0 at ho
  have hr := h.2.1
  have hcol := h.2.2.1
  apply window_extend s i r c minr maxr minc maxc (r-1) c minr maxr minc maxc hi h <;> omega

theorem Znth_app_left__termination_optimality (A : Type) (l1 l2 : List A) (d : A) (i : Int)
    (hi : 0≤i ∧ i<Zlength l1) : Znth i (l1++l2) d=Znth i l1 d := by
  have hn : i.toNat<l1.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

theorem Znth_app_left__down_new_max (l1 l2 : List Int) (d i : Int) (hi : 0≤i ∧ i<Zlength l1) : Znth i (l1++l2) d=Znth i l1 d :=
  Znth_app_left__termination_optimality Int l1 l2 d i hi

theorem Znth_app_last__down_new_max (l : List Int) (d x : Int) : Znth (Zlength l) (l++[x]) d=x := by
  rw [app_Znth2 d l [x] (Zlength l) (le_refl _),sub_self]
  rfl

theorem prefix_window_step_down_new_max__down_new_max (moves : List Int) (i r c minr maxr minc maxc : Int)
    (hi : 0≤i ∧ i<Zlength moves) (hcmd : Znth i moves 0=68) (h : PrefixWindow moves i r c minr maxr minc maxc)
    (hm : maxr<r+1) : PrefixWindow moves (i+1) (r+1) c minr (r+1) minc maxc := by
  have ho := offset_step moves i hi
  rw [hcmd] at ho
  change RowOffset moves (i+1)=RowOffset moves i+1 ∧ ColOffset moves (i+1)=ColOffset moves i+0 at ho
  have hr := h.2.1
  have hcol := h.2.2.1
  have hb := current_bounds moves i r c minr maxr minc maxc h
  apply window_extend moves i r c minr maxr minc maxc (r+1) c minr (r+1) minc maxc hi h <;> omega

theorem prefix_window_step_down_inside__down_inside (moves : List Int) (i r c minr maxr minc maxc : Int)
    (hi : 0≤i ∧ i<Zlength moves) (hcmd : Znth i moves 0=68) (h : PrefixWindow moves i r c minr maxr minc maxc)
    (hm : minr≤r+1 ∧ r+1≤maxr) (hc : minc≤c ∧ c≤maxc) : PrefixWindow moves (i+1) (r+1) c minr maxr minc maxc := by
  have ho := offset_step moves i hi
  rw [hcmd] at ho
  change RowOffset moves (i+1)=RowOffset moves i+1 ∧ ColOffset moves (i+1)=ColOffset moves i+0 at ho
  have hr := h.2.1
  have hcol := h.2.2.1
  apply window_extend moves i r c minr maxr minc maxc (r+1) c minr maxr minc maxc hi h <;> omega

theorem Znth_app_last__left_impossible_low_row (l : List Int) (d x : Int) : Znth (Zlength l) (l++[x]) d=x := Znth_app_last__down_new_max l d x

theorem fold_right_add_base__left_valid_row (xs : List Int) (z : Int) : xs.foldr (·+·) z=xs.foldr (·+·) 0+z := by
  induction xs with
  | nil => simp only [List.foldr_nil,zero_add]
  | cons a xs ih => simp only [List.foldr_cons,ih,add_assoc]

theorem nonzero_Znth_sentinel_lt__left_valid_row (xs : List Int) (i : Int) (hi : 0≤i ∧ i≤Zlength xs)
    (hne : Znth i (xs++[0]) 0≠0) : i<Zlength xs := by
  by_contra h
  have he : i=Zlength xs := by omega
  exact hne (he ▸ Znth_app_last__down_new_max xs 0 0)

theorem prefix_window_step_left_cases__left_valid_row (s : List Int) (q r c minr maxr minc maxc : Int)
    (hi : 0≤q ∧ q<Zlength s) (hcmd : Znth q s 0=76) (h : PrefixWindow s q r c minr maxr minc maxc) :
    PrefixWindow s (q+1) r (c-1) minr maxr (min minc (c-1)) maxc := by
  have ho := offset_step s q hi
  rw [hcmd] at ho
  change RowOffset s (q+1)=RowOffset s q+0 ∧ ColOffset s (q+1)=ColOffset s q+(-1) at ho
  have hr := h.2.1
  have hcol := h.2.2.1
  have hb := current_bounds s q r c minr maxr minc maxc h
  change PrefixWindow s (q+1) r (c-1) minr maxr (min minc (c-1)) maxc
  by_cases hle : minc≤c-1
  · rw [min_eq_left hle]
    apply window_extend s q r c minr maxr minc maxc r (c-1) minr maxr minc maxc hi h <;> omega
  · rw [min_eq_right (by omega : c-1≤minc)]
    apply window_extend s q r c minr maxr minc maxc r (c-1) minr maxr (c-1) maxc hi h <;> omega

theorem fold_right_Z_add_base__right_valid_row (l : List Int) (z : Int) : l.foldr (·+·) z=l.foldr (·+·) 0+z := fold_right_add_base__left_valid_row l z

theorem row_col_offset_step_right__right_valid_row (s : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength s) (hc : Znth i s 0=82) :
    RowOffset s (i+1)=RowOffset s i ∧ ColOffset s (i+1)=ColOffset s i+1 := by
  have ho := offset_step s i hi
  rw [hc] at ho
  change RowOffset s (i+1)=RowOffset s i+0 ∧ ColOffset s (i+1)=ColOffset s i+1 at ho
  exact ⟨by omega,ho.2⟩

theorem prefix_window_step_right_cases__right_valid_row (s : List Int) (i r c minr maxr minc maxc : Int)
    (h : PrefixWindow s i r c minr maxr minc maxc) (hi : i<Zlength s) (hcmd : Znth i s 0=82)
    (hb : minr≤r ∧ r≤maxr) :
    (maxc<c+1 → PrefixWindow s (i+1) r (c+1) minr maxr minc (c+1)) ∧
    ((minc≤c+1 ∧ c+1≤maxc) → PrefixWindow s (i+1) r (c+1) minr maxr minc maxc) := by
  have hir : 0≤i ∧ i<Zlength s := ⟨h.1.1,hi⟩
  have ho := row_col_offset_step_right__right_valid_row s i hir hcmd
  have hr := h.2.1
  have hcol := h.2.2.1
  have hbc := current_bounds s i r c minr maxr minc maxc h
  constructor
  · intro hn
    apply window_extend s i r c minr maxr minc maxc r (c+1) minr maxr minc (c+1) hir h <;> omega
  · intro hn
    apply window_extend s i r c minr maxr minc maxc r (c+1) minr maxr minc maxc hir h <;> omega

private theorem fits_executes (n m : Int) (s : List Int) (q r c minr maxr minc maxc : Int)
    (h : PrefixWindow s q r c minr maxr minc maxc) (hf : WindowFits n m minr maxr minc maxc) :
    (1≤1-minr ∧ 1-minr≤n) ∧ (1≤1-minc ∧ 1-minc≤m) ∧ Executes n m s (1-minr,1-minc) q := by
  rcases h with ⟨hq,hr,hc,hzr,hzc,hall,hminr,hmaxr,hminc,hmaxc⟩
  rcases hf with ⟨hfr,hfc⟩
  refine ⟨by omega,by omega,hq,?_⟩
  intro p hp
  change (1≤1-minr+RowOffset s p ∧ 1-minr+RowOffset s p≤n) ∧ (1≤1-minc+ColOffset s p ∧ 1-minc+ColOffset s p≤m)
  have hh := hall p hp
  omega

theorem feasible_prefix_iff_window_fits__termination_optimality (n m : Int) (s : List Int) (q r c minr maxr minc maxc : Int)
    (h : PrefixWindow s q r c minr maxr minc maxc) : WindowFits n m minr maxr minc maxc ↔
      ∃ st:Int×Int, (1≤st.1 ∧ st.1≤n) ∧ (1≤st.2 ∧ st.2≤m) ∧ Executes n m s st q := by
  constructor
  · intro hf
    exact ⟨(1-minr,1-minc),fits_executes n m s q r c minr maxr minc maxc h hf⟩
  · rintro ⟨st,hsr,hsc,hq,hall⟩
    rcases h with ⟨hq',hr,hc,hzr,hzc,hbounds,⟨p1,hp1,he1⟩,⟨p2,hp2,he2⟩,⟨p3,hp3,he3⟩,⟨p4,hp4,he4⟩⟩
    have h1 := hall p1 hp1
    have h2 := hall p2 hp2
    have h3 := hall p3 hp3
    have h4 := hall p4 hp4
    change (1≤st.1+RowOffset s p1 ∧ st.1+RowOffset s p1≤n) ∧ (1≤st.2+ColOffset s p1 ∧ st.2+ColOffset s p1≤m) at h1
    change (1≤st.1+RowOffset s p2 ∧ st.1+RowOffset s p2≤n) ∧ (1≤st.2+ColOffset s p2 ∧ st.2+ColOffset s p2≤m) at h2
    change (1≤st.1+RowOffset s p3 ∧ st.1+RowOffset s p3≤n) ∧ (1≤st.2+ColOffset s p3 ∧ st.2+ColOffset s p3≤m) at h3
    change (1≤st.1+RowOffset s p4 ∧ st.1+RowOffset s p4≤n) ∧ (1≤st.2+ColOffset s p4 ∧ st.2+ColOffset s p4≤m) at h4
    unfold WindowFits
    omega

theorem optimal_prefix_at_end__termination_optimality (n m : Int) (s : List Int) (q r c minr maxr minc maxc : Int)
    (hq : q=Zlength s) (h : PrefixWindow s q r c minr maxr minc maxc) (hf : WindowFits n m minr maxr minc maxc) :
    OptimalPrefixWindow n m s minr maxr minc maxc := by
  refine ⟨q,r,c,h,hf,q,⟨(feasible_prefix_iff_window_fits__termination_optimality n m s q r c minr maxr minc maxc h).mp hf,?_⟩,rfl⟩
  rintro q' ⟨st,hsr,hsc,he⟩
  have hh := he.1.2
  change q'≤q
  omega

theorem optimal_prefix_before_overflow__termination_optimality (n m : Int) (s : List Int)
    (i oldr oldc r c minr maxr minc maxc nminr nmaxr nminc nmaxc : Int)
    (h : PrefixWindow s i oldr oldc minr maxr minc maxc) (hf : WindowFits n m minr maxr minc maxc)
    (hn : PrefixWindow s (i+1) r c nminr nmaxr nminc nmaxc) (hover : nmaxr-nminr≥n ∨ nmaxc-nminc≥m) :
    OptimalPrefixWindow n m s minr maxr minc maxc := by
  refine ⟨i,oldr,oldc,h,hf,i,⟨(feasible_prefix_iff_window_fits__termination_optimality n m s i oldr oldc minr maxr minc maxc h).mp hf,?_⟩,rfl⟩
  rintro q ⟨st,hsr,hsc,he⟩
  change q≤i
  by_contra hgt
  have hex : Executes n m s st (i+1) := by
    refine ⟨hn.1,?_⟩
    intro p hp
    exact he.2 p (by omega)
  have hfit := (feasible_prefix_iff_window_fits__termination_optimality n m s (i+1) r c nminr nmaxr nminc nmaxc hn).mpr ⟨st,hsr,hsc,hex⟩
  unfold WindowFits at hfit
  omega

theorem optimal_window_realizes_spec__final_result (n m : Int) (s : List Int) (minr maxr minc maxc : Int)
    (h : OptimalPrefixWindow n m s minr maxr minc maxc) : Spec n m s (1-minr,1-minc) := by
  rcases h with ⟨q,r,c,hp,hf,hmax⟩
  have hx := fits_executes n m s q r c minr maxr minc maxc hp hf
  exact ⟨hx.1,hx.2.1,q,hx.2.2,hmax⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib
