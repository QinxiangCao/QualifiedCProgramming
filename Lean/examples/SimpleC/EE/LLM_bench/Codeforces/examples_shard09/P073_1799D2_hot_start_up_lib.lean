import ListLib.General.Length
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib
open AUXLib


open MaxMinLib

def HotStart (prog cpu : List Int) (i j : Int) : Prop :=
  (0 ≤ j ∧ j < i) ∧ Znth j cpu 0 = Znth i cpu 0 ∧
    (∀ q, (j < q ∧ q < i) → Znth q cpu 0 ≠ Znth i cpu 0) ∧ Znth j prog 0 = Znth i prog 0

def RunTime (prog cold hot cpu times : List Int) (i : Int) : Prop :=
  (∃ j, HotStart prog cpu i j ∧ Znth i times 0 = Znth (Znth i prog 0 - 1) hot 0) ∨
    ((¬ ∃ j, HotStart prog cpu i j) ∧ Znth i times 0 = Znth (Znth i prog 0 - 1) cold 0)

def RunTimes (prog cold hot cpu times : List Int) : Prop :=
  Zlength times = Zlength prog ∧ ∀ i, (0 ≤ i ∧ i < Zlength prog) → RunTime prog cold hot cpu times i

def ValidSchedule (prog cpu : List Int) : Prop := Zlength cpu = Zlength prog ∧ Forall (fun x => x = 1 ∨ x = 2) cpu

def RunCost (prog cold hot cpu : List Int) (cost : Int) : Prop :=
  ValidSchedule prog cpu ∧ ∃ times, RunTimes prog cold hot cpu times ∧ cost = times.foldr (· + ·) 0

def Pre (prog cold hot : List Int) : Prop := True

def Spec (prog cold hot : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun v => ∃ cpu, RunCost prog cold hot cpu v) (fun x => x) out

def DP_INF : Int := 4557430888798830399

def OtherCpuLastProgram (prog cpu : List Int) (other : Int) : Prop :=
  0 < Zlength prog ∧ Zlength cpu = Zlength prog ∧
    (let active := Znth (Zlength prog - 1) cpu 0
     (other = 0 ∧ ∀ q, (0 ≤ q ∧ q < Zlength prog) → Znth q cpu 0 = active) ∨
     (∃ q, (0 ≤ q ∧ q < Zlength prog) ∧ Znth q cpu 0 ≠ active ∧ other = Znth q prog 0 ∧
       ∀ r, (q < r ∧ r < Zlength prog) → Znth r cpu 0 = active))

def PrefixStateCost (prog cold hot : List Int) (prefix_len other total : Int) : Prop :=
  ∃ cpu, RunCost (sublist 0 prefix_len prog) cold hot cpu total ∧ OtherCpuLastProgram (sublist 0 prefix_len prog) cpu other

def PrefixStateMinimum (prog cold hot : List Int) (prefix_len other total : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (PrefixStateCost prog cold hot prefix_len other) (fun x => x) total

def NormalizedScheduleCell (prog cold hot : List Int) (prefix_len other off value : Int) : Prop :=
  (value < DP_INF ∧ PrefixStateMinimum prog cold hot prefix_len other (off + value)) ∨
    (value = DP_INF ∧ ¬ ∃ total, PrefixStateCost prog cold hot prefix_len other total)

def NormalizedScheduleState (prog cold hot : List Int) (prefix_len : Int) (dp : List Int) (off mind : Int) : Prop :=
  (∀ other, (0 ≤ other ∧ other ≤ Zlength cold) → NormalizedScheduleCell prog cold hot prefix_len other off (Znth other dp DP_INF)) ∧
    min_value_of_subset (· ≤ ·) (fun value => ∃ other, (0 ≤ other ∧ other ≤ Zlength cold) ∧ value = Znth other dp DP_INF ∧ value < DP_INF) (fun x => x) mind ∧
    Spec (sublist 0 prefix_len prog) cold hot (off + mind)

def other_cpu_label (active : Int) : Int := if active = 1 then 2 else 1

theorem normalized_schedule_state_cell (prog cold hot : List Int) (prefix_len : Int)
    (dp : List Int) (off mind other : Int) (hs : NormalizedScheduleState prog cold hot prefix_len dp off mind)
    (ho : 0 ≤ other ∧ other ≤ Zlength cold) : NormalizedScheduleCell prog cold hot prefix_len other off (Znth other dp DP_INF) :=
  hs.1 other ho

theorem normalized_schedule_state_full_spec (prog cold hot dp : List Int) (off mind : Int)
    (hs : NormalizedScheduleState prog cold hot (Zlength prog) dp off mind) : Spec prog cold hot (off+mind) := by
  have h := hs.2.2
  simpa only [sublist_self prog (Zlength prog) rfl] using h

theorem sublist_0_succ__normalized_step (A : Type) (d : A) (xs : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength xs) : sublist 0 (i+1) xs=sublist 0 i xs++[Znth i xs d] := by
  rw [sublist_split 0 (i+1) i xs ⟨by omega,hi.1⟩ ⟨by omega,by omega⟩,
    sublist_single d i xs hi]

theorem Znth_app_left__normalized_step (A : Type) (d : A) (xs ys : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength xs) : Znth i (xs++ys) d=Znth i xs d := by
  have hn : i.toNat < xs.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

theorem Znth_app_last__normalized_step (A : Type) (d : A) (xs : List A) (x : A) :
    Znth (Zlength xs) (xs++[x]) d=x := by
  rw [app_Znth2 d xs [x] (Zlength xs) (le_refl _),sub_self]
  rfl

theorem fold_right_add_snoc__normalized_step (xs : List Int) (x : Int) :
    (xs++[x]).foldr (· + ·) 0=xs.foldr (· + ·) 0+x := by
  induction xs with
  | nil => simp
  | cons a l ih => simp only [List.cons_append,List.foldr_cons,ih]; omega

theorem other_cpu_label_valid__normalized_step (active : Int) (ha : active=1 ∨ active=2) :
    other_cpu_label active=1 ∨ other_cpu_label active=2 := by rcases ha with rfl | rfl <;> simp [other_cpu_label]

theorem other_cpu_label_neq__normalized_step (active : Int) (ha : active=1 ∨ active=2) :
    other_cpu_label active≠active := by rcases ha with rfl | rfl <;> simp [other_cpu_label]

theorem binary_label_other__normalized_step (active label : Int)
    (ha : active=1 ∨ active=2) (hl : label=1 ∨ label=2) (hne : label≠active) : label=other_cpu_label active := by
  rcases ha with rfl | rfl <;> rcases hl with rfl | rfl <;> simp_all [other_cpu_label]

private theorem znth_mem (l : List Int) (q : Int) (hq : 0 ≤ q ∧ q < Zlength l) : Znth q l 0 ∈ l := by
  have hn : q.toNat < l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hq; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

theorem valid_schedule_active_label__normalized_step (prog cpu : List Int)
    (hv : ValidSchedule prog cpu) (hp : 0 < Zlength prog) :
    Znth (Zlength prog-1) cpu 0=1 ∨ Znth (Zlength prog-1) cpu 0=2 :=
  Forall.iff_forall_mem.mp hv.2 _ (znth_mem cpu (Zlength prog-1) (by have h:=hv.1; omega))

theorem valid_schedule_snoc__normalized_step (prog cpu : List Int) (x label : Int)
    (hv : ValidSchedule prog cpu) (hl : label=1 ∨ label=2) : ValidSchedule (prog++[x]) (cpu++[label]) := by
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil]; have h:=hv.1; omega,?_⟩
  apply Forall.iff_forall_mem.mpr
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact Forall.iff_forall_mem.mp hv.2 y hy
  · have he := List.mem_singleton.mp hy; subst y; exact hl

theorem hot_start_snoc_old_iff__normalized_step (prog cpu : List Int) (x label pos previous : Int)
    (hlen : Zlength cpu=Zlength prog) (hpos : 0 ≤ pos ∧ pos < Zlength prog) :
    HotStart prog cpu pos previous ↔ HotStart (prog++[x]) (cpu++[label]) pos previous := by
  have hp := Znth_app_left__normalized_step Int 0 cpu [label] pos (by omega)
  have hpp := Znth_app_left__normalized_step Int 0 prog [x] pos hpos
  constructor
  · rintro ⟨hpr,he,hmid,hprog⟩
    refine ⟨hpr,?_,?_,?_⟩
    · rw [hp,Znth_app_left__normalized_step Int 0 cpu [label] previous (by omega)]; exact he
    · intro q hq
      rw [hp,Znth_app_left__normalized_step Int 0 cpu [label] q (by omega)]
      exact hmid q hq
    · rw [hpp,Znth_app_left__normalized_step Int 0 prog [x] previous (by omega)]; exact hprog
  · rintro ⟨hpr,he,hmid,hprog⟩
    refine ⟨hpr,?_,?_,?_⟩
    · rw [hp,Znth_app_left__normalized_step Int 0 cpu [label] previous (by omega)] at he; exact he
    · intro q hq
      have h := hmid q hq
      rw [hp,Znth_app_left__normalized_step Int 0 cpu [label] q (by omega)] at h
      exact h
    · rw [hpp,Znth_app_left__normalized_step Int 0 prog [x] previous (by omega)] at hprog; exact hprog

theorem run_time_snoc_old_iff__normalized_step (prog cold hot cpu times : List Int) (x label t pos : Int)
    (hlen : Zlength cpu=Zlength prog) (htlen : Zlength times=Zlength prog) (hpos : 0 ≤ pos ∧ pos < Zlength prog) :
    RunTime prog cold hot cpu times pos ↔ RunTime (prog++[x]) cold hot (cpu++[label]) (times++[t]) pos := by
  have hex : (∃ p, HotStart prog cpu pos p) ↔ ∃ p, HotStart (prog++[x]) (cpu++[label]) pos p :=
    exists_congr (fun p => hot_start_snoc_old_iff__normalized_step prog cpu x label pos p hlen hpos)
  unfold RunTime
  rw [Znth_app_left__normalized_step Int 0 times [t] pos (by omega),Znth_app_left__normalized_step Int 0 prog [x] pos hpos]
  constructor
  · rintro (⟨p,hp,ht⟩ | ⟨hn,ht⟩)
    · exact Or.inl ⟨p,(hot_start_snoc_old_iff__normalized_step prog cpu x label pos p hlen hpos).mp hp,ht⟩
    · exact Or.inr ⟨fun h => hn (hex.mpr h),ht⟩
  · rintro (⟨p,hp,ht⟩ | ⟨hn,ht⟩)
    · exact Or.inl ⟨p,(hot_start_snoc_old_iff__normalized_step prog cpu x label pos p hlen hpos).mpr hp,ht⟩
    · exact Or.inr ⟨fun h => hn (hex.mp h),ht⟩

theorem other_cpu_last_continue__normalized_step (prog cpu : List Int) (other x : Int)
    (ho : OtherCpuLastProgram prog cpu other) :
    OtherCpuLastProgram (prog++[x]) (cpu++[Znth (Zlength prog-1) cpu 0]) other := by
  obtain ⟨hpos,hlen,ho⟩ := ho
  have hpl : Zlength (prog++[x])=Zlength prog+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hcl : Zlength (cpu++[Znth (Zlength prog-1) cpu 0])=Zlength cpu+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hlast : Znth (Zlength (prog++[x])-1) (cpu++[Znth (Zlength prog-1) cpu 0]) 0=Znth (Zlength prog-1) cpu 0 := by
    rw [hpl,show Zlength prog+1-1=Zlength cpu by omega,Znth_app_last__normalized_step]
  refine ⟨by omega,by omega,?_⟩
  dsimp only
  rw [hlast]
  rcases ho with ⟨hz,hall⟩ | ⟨q,hq,hne,he,hall⟩
  · refine Or.inl ⟨hz,?_⟩
    intro q hq
    by_cases he : q=Zlength prog
    · rw [he,← hlen,Znth_app_last__normalized_step]
    · rw [Znth_app_left__normalized_step Int 0 cpu _ q (by omega)]
      exact hall q (by omega)
  · refine Or.inr ⟨q,⟨hq.1,by omega⟩,?_,?_,?_⟩
    · rw [Znth_app_left__normalized_step Int 0 cpu _ q (by omega)]; exact hne
    · rw [Znth_app_left__normalized_step Int 0 prog [x] q hq]; exact he
    · intro r hr
      by_cases he : r=Zlength prog
      · rw [he,← hlen,Znth_app_last__normalized_step]
      · rw [Znth_app_left__normalized_step Int 0 cpu _ r (by omega)]
        exact hall r (by omega)

theorem other_cpu_last_switch__normalized_step (prog cpu : List Int) (x : Int)
    (hv : ValidSchedule prog cpu) (hpos : 0 < Zlength prog) :
    OtherCpuLastProgram (prog++[x]) (cpu++[other_cpu_label (Znth (Zlength prog-1) cpu 0)]) (Znth (Zlength prog-1) prog 0) := by
  have hlen := hv.1
  have ha := valid_schedule_active_label__normalized_step prog cpu hv hpos
  have hne := other_cpu_label_neq__normalized_step _ ha
  have hpl : Zlength (prog++[x])=Zlength prog+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hcl : Zlength (cpu++[other_cpu_label (Znth (Zlength prog-1) cpu 0)])=Zlength cpu+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hlast : Znth (Zlength (prog++[x])-1) (cpu++[other_cpu_label (Znth (Zlength prog-1) cpu 0)]) 0=other_cpu_label (Znth (Zlength prog-1) cpu 0) := by
    rw [hpl,show Zlength prog+1-1=Zlength cpu by omega,Znth_app_last__normalized_step]
  refine ⟨by omega,by omega,?_⟩
  dsimp only
  rw [hlast]
  refine Or.inr ⟨Zlength prog-1,⟨by omega,by omega⟩,?_,?_,?_⟩
  · rw [Znth_app_left__normalized_step Int 0 cpu _ _ (by omega)]
    exact Ne.symm hne
  · rw [Znth_app_left__normalized_step Int 0 prog [x] _ (by omega)]
  · intro r hr
    have he : r=Zlength cpu := by omega
    rw [he,Znth_app_last__normalized_step]

theorem hot_start_continue_final_iff__normalized_step (prog cpu : List Int) (x : Int)
    (hlen : Zlength cpu=Zlength prog) (hpos : 0 < Zlength prog) :
    (∃ previous, HotStart (prog++[x]) (cpu++[Znth (Zlength prog-1) cpu 0]) (Zlength prog) previous) ↔
      x=Znth (Zlength prog-1) prog 0 := by
  have hlast : Znth (Zlength prog) (cpu++[Znth (Zlength prog-1) cpu 0]) 0=Znth (Zlength prog-1) cpu 0 := by
    rw [← hlen,Znth_app_last__normalized_step]
  constructor
  · rintro ⟨previous,hpr,he,hmid,hprog⟩
    have hp : previous=Zlength prog-1 := by
      by_contra hne
      have hh := hmid (Zlength prog-1) ⟨by omega,by omega⟩
      rw [hlast,Znth_app_left__normalized_step Int 0 cpu _ _ (by omega)] at hh
      exact hh rfl
    rw [hp,Znth_app_last__normalized_step,Znth_app_left__normalized_step Int 0 prog [x] _ (by omega)] at hprog
    exact hprog.symm
  · intro he
    refine ⟨Zlength prog-1,⟨by omega,by omega⟩,?_,?_,?_⟩
    · rw [hlast,Znth_app_left__normalized_step Int 0 cpu _ _ (by omega)]
    · intro q hq
      omega
    · rw [Znth_app_last__normalized_step,Znth_app_left__normalized_step Int 0 prog [x] _ (by omega)]
      exact he.symm

theorem hot_start_switch_final_iff__normalized_step (prog cpu : List Int) (other x : Int)
    (hv : ValidSchedule prog cpu) (ho : OtherCpuLastProgram prog cpu other)
    (hpos : 0 < Zlength prog) (hx : 0 < x) :
    (∃ previous, HotStart (prog++[x]) (cpu++[other_cpu_label (Znth (Zlength prog-1) cpu 0)]) (Zlength prog) previous) ↔ other=x := by
  have hlen := hv.1
  have ha := valid_schedule_active_label__normalized_step prog cpu hv hpos
  have hne := other_cpu_label_neq__normalized_step _ ha
  have hlast : Znth (Zlength prog) (cpu++[other_cpu_label (Znth (Zlength prog-1) cpu 0)]) 0=other_cpu_label (Znth (Zlength prog-1) cpu 0) := by
    rw [← hlen,Znth_app_last__normalized_step]
  have hlabels : ∀ q, (0 ≤ q ∧ q < Zlength prog) → Znth q cpu 0=1 ∨ Znth q cpu 0=2 := by
    intro q hq
    exact Forall.iff_forall_mem.mp hv.2 _ (znth_mem cpu q (by omega))
  obtain ⟨_,_,hcases⟩ := ho
  constructor
  · rintro ⟨p,hp,hsame,hbetween,hprog⟩
    rw [hlast,Znth_app_left__normalized_step Int 0 cpu _ p (by omega)] at hsame
    rw [Znth_app_last__normalized_step,Znth_app_left__normalized_step Int 0 prog [x] p hp] at hprog
    rcases hcases with ⟨_,hall⟩ | ⟨q,hq,hqne,hother,hafter⟩
    · exact False.elim (hne ((hall p hp).symm.trans hsame).symm)
    · have hqflip := binary_label_other__normalized_step _ _ ha (hlabels q hq) hqne
      have he : p=q := by
        rcases lt_trichotomy p q with hlt | he | hgt
        · have h := hbetween q ⟨hlt,hq.2⟩
          rw [hlast,Znth_app_left__normalized_step Int 0 cpu _ q (by omega),hqflip] at h
          exact False.elim (h rfl)
        · exact he
        · have h := hafter p ⟨hgt,hp.2⟩
          exact False.elim (hne (hsame.symm.trans h))
      subst p
      exact hother.trans hprog
  · intro he
    rcases hcases with ⟨hz,_⟩ | ⟨q,hq,hqne,hother,hafter⟩
    · omega
    · refine ⟨q,hq,?_,?_,?_⟩
      · rw [hlast,Znth_app_left__normalized_step Int 0 cpu _ q (by omega)]
        exact binary_label_other__normalized_step _ _ ha (hlabels q hq) hqne
      · intro r hr
        rw [hlast,Znth_app_left__normalized_step Int 0 cpu _ r (by omega),hafter r hr]
        exact Ne.symm hne
      · rw [Znth_app_last__normalized_step,Znth_app_left__normalized_step Int 0 prog [x] q hq]
        exact hother.symm.trans he

theorem run_time_continue_final_iff__normalized_step (prog cold hot cpu times : List Int) (x t : Int)
    (hlen : Zlength cpu=Zlength prog) (htlen : Zlength times=Zlength prog) (hpos : 0 < Zlength prog) :
    RunTime (prog++[x]) cold hot (cpu++[Znth (Zlength prog-1) cpu 0]) (times++[t]) (Zlength prog) ↔
      ((x=Znth (Zlength prog-1) prog 0 ∧ t=Znth (x-1) hot 0) ∨
      (x≠Znth (Zlength prog-1) prog 0 ∧ t=Znth (x-1) cold 0)) := by
  have ht : Znth (Zlength prog) (times++[t]) 0=t := by rw [← htlen,Znth_app_last__normalized_step]
  simp only [RunTime,exists_and_right,hot_start_continue_final_iff__normalized_step prog cpu x hlen hpos,
    ht,Znth_app_last__normalized_step]

theorem run_time_switch_final_iff__normalized_step (prog cold hot cpu times : List Int) (other x t : Int)
    (hv : ValidSchedule prog cpu) (ho : OtherCpuLastProgram prog cpu other)
    (htlen : Zlength times=Zlength prog) (hpos : 0 < Zlength prog) (hx : 0 < x) :
    RunTime (prog++[x]) cold hot (cpu++[other_cpu_label (Znth (Zlength prog-1) cpu 0)]) (times++[t]) (Zlength prog) ↔
      ((other=x ∧ t=Znth (x-1) hot 0) ∨ (other≠x ∧ t=Znth (x-1) cold 0)) := by
  have ht : Znth (Zlength prog) (times++[t]) 0=t := by rw [← htlen,Znth_app_last__normalized_step]
  simp only [RunTime,exists_and_right,hot_start_switch_final_iff__normalized_step prog cpu other x hv ho hpos hx,
    ht,Znth_app_last__normalized_step]

theorem run_times_snoc__normalized_step (prog cold hot cpu times : List Int) (x label t : Int)
    (hlen : Zlength cpu=Zlength prog) (hrt : RunTimes prog cold hot cpu times)
    (hfinal : RunTime (prog++[x]) cold hot (cpu++[label]) (times++[t]) (Zlength prog)) :
    RunTimes (prog++[x]) cold hot (cpu++[label]) (times++[t]) := by
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil]; have h:=hrt.1; omega,?_⟩
  intro i hi
  have hpl : Zlength (prog++[x])=Zlength prog+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  by_cases he : i=Zlength prog
  · subst i; exact hfinal
  · have hir : 0 ≤ i ∧ i < Zlength prog := by omega
    exact (run_time_snoc_old_iff__normalized_step prog cold hot cpu times x label t i hlen hrt.1 hir).mp (hrt.2 i hir)

theorem run_cost_snoc__normalized_step (prog cold hot cpu times : List Int) (total x label t : Int)
    (hv : ValidSchedule prog cpu) (hl : label=1 ∨ label=2) (hrt : RunTimes prog cold hot cpu times)
    (hsum : total=times.foldr (· + ·) 0)
    (hfinal : RunTime (prog++[x]) cold hot (cpu++[label]) (times++[t]) (Zlength prog)) :
    RunCost (prog++[x]) cold hot (cpu++[label]) (total+t) := by
  refine ⟨valid_schedule_snoc__normalized_step prog cpu x label hv hl,times++[t],
    run_times_snoc__normalized_step prog cold hot cpu times x label t hv.1 hrt hfinal,?_⟩
  rw [fold_right_add_snoc__normalized_step,hsum]

private theorem singleton_of_zlength (l : List Int) (hl : Zlength l=1) : ∃ x, l=[x] :=
by
  cases l with
  | nil => simp [Zlength] at hl
  | cons x xs =>
    have hn : xs.length=0 := by simp only [Zlength,List.length_cons,Int.ofNat_eq_coe] at hl; omega
    have he := List.length_eq_zero_iff.mp hn
    subst xs
    exact ⟨x,rfl⟩

theorem run_cost_single__initialization (p : Int) (cold hot cpu : List Int) (total : Int)
    (hr : RunCost [p] cold hot cpu total) : total=Znth (p-1) cold 0 := by
  obtain ⟨_,times,⟨hlen,hrt⟩,hsum⟩ := hr
  obtain ⟨t,rfl⟩ := singleton_of_zlength times hlen
  have hh := hrt 0 (by change 0 ≤ (0:Int) ∧ (0:Int) < 1; decide)
  rcases hh with ⟨j,⟨hj,_,_,_⟩,_⟩ | ⟨_,ht⟩
  · omega
  · simp only [List.foldr_cons,List.foldr_nil,add_zero] at hsum
    exact hsum.trans ht

theorem run_cost_single_exists__initialization (p : Int) (cold hot : List Int) :
    ∃ cpu, RunCost [p] cold hot cpu (Znth (p-1) cold 0) := by
  refine ⟨[1],⟨rfl,?_⟩,[Znth (p-1) cold 0],⟨rfl,?_⟩,by simp⟩
  · exact Forall.iff_forall_mem.mpr (by intro x hx; have h:=List.mem_singleton.mp hx; exact Or.inl h)
  · intro i hi
    have he : i=0 := by change 0 ≤ i ∧ i < 1 at hi; omega
    subst i
    refine Or.inr ⟨?_,rfl⟩
    rintro ⟨j,hj,_,_,_⟩
    omega

theorem other_cpu_single__initialization (p c other : Int) : OtherCpuLastProgram [p] [c] other ↔ other=0 := by
  constructor
  · rintro ⟨_,_,⟨he,_⟩ | ⟨q,hq,hne,_,_⟩⟩
    · exact he
    · have he : q=0 := by change 0 ≤ q ∧ q < 1 at hq; omega
      subst q
      exact False.elim (hne rfl)
  · intro he
    refine ⟨by change (0:Int) < 1; decide,rfl,Or.inl ⟨he,?_⟩⟩
    intro q hq
    have he : q=0 := by change 0 ≤ q ∧ q < 1 at hq; omega
    subst q
    rfl

theorem prefix_state_cost_one__initialization (prog cold hot : List Int) (other total : Int)
    (hlen : 1 ≤ Zlength prog) : PrefixStateCost prog cold hot 1 other total ↔
      other=0 ∧ total=Znth (Znth 0 prog 0-1) cold 0 := by
  have hsub : sublist 0 1 prog=[Znth 0 prog 0] := by simpa using sublist_single 0 0 prog (show 0 ≤ (0:Int) ∧ (0:Int)<Zlength prog by omega)
  unfold PrefixStateCost
  rw [hsub]
  constructor
  · rintro ⟨cpu,hr,ho⟩
    obtain ⟨c,hcpu⟩ := singleton_of_zlength cpu hr.1.1
    have hz : other=0 := by rw [hcpu] at ho; exact (other_cpu_single__initialization _ c other).mp ho
    exact ⟨hz,run_cost_single__initialization _ cold hot cpu total hr⟩
  · rintro ⟨rfl,rfl⟩
    obtain ⟨cpu,hr⟩ := run_cost_single_exists__initialization (Znth 0 prog 0) cold hot
    obtain ⟨c,hcpu⟩ := singleton_of_zlength cpu hr.1.1
    refine ⟨cpu,hr,?_⟩
    rw [hcpu]
    exact (other_cpu_single__initialization _ c 0).mpr rfl

theorem min_value_member_le__state_transitions (P : Int → Prop) (m z : Int)
    (hm : min_value_of_subset (· ≤ ·) P (fun x => x) m) (hz : P z) : m ≤ z := by
  obtain ⟨a,⟨ha,hmin⟩,rfl⟩ := hm
  exact hmin z hz

theorem min_value_member__state_transitions (P : Int → Prop) (m : Int)
    (hm : min_value_of_subset (· ≤ ·) P (fun x => x) m) : P m := by
  obtain ⟨a,⟨ha,_⟩,rfl⟩ := hm
  exact ha

theorem normalized_schedule_state_initial__initialization (prog cold hot initialized : List Int) (n k : Int)
    (hn : 1 ≤ n) (hnlen : n=Zlength prog) (hk : 1 ≤ k) (hkc : k=Zlength cold) (hkh : k=Zlength hot)
    (hp : ∀ q, (0 ≤ q ∧ q < n) → 1 ≤ Znth q prog 0 ∧ Znth q prog 0 ≤ k)
    (hc : ∀ q, (0 ≤ q ∧ q < k) → (1 ≤ Znth q hot 0 ∧ Znth q hot 0 ≤ Znth q cold 0) ∧ Znth q cold 0 ≤ 1000000000)
    (hinitlen : Zlength initialized=k+1) (hinit : ∀ q, (0 ≤ q ∧ q < k+1) → Znth q initialized 0=DP_INF) :
    NormalizedScheduleState prog cold hot 1 (replace_Znth 0 0 initialized) (Znth (Znth 0 prog 0) (0::cold) 0) 0 := by
  have hp0 := hp 0 (by omega)
  have hoff : Znth (Znth 0 prog 0) (0::cold) 0=Znth (Znth 0 prog 0-1) cold 0 :=
    Znth_cons 0 (Znth 0 prog 0) 0 cold (by omega)
  rw [hoff]
  have hz : Znth 0 (replace_Znth 0 0 initialized) DP_INF=0 := Znth_replace_Znth_Same DP_INF initialized 0 0 (by omega)
  have hother : ∀ q, (0 ≤ q ∧ q ≤ Zlength cold) → q≠0 → Znth q (replace_Znth 0 0 initialized) DP_INF=DP_INF := by
    intro q hq hne
    rw [Znth_replace_Znth_Diff DP_INF initialized 0 q 0 (by omega) (by omega) (Ne.symm hne),
      Znth_indep initialized q DP_INF 0 (by omega)]
    exact hinit q (by omega)
  have hsc : ∀ other total, PrefixStateCost prog cold hot 1 other total ↔
      other=0 ∧ total=Znth (Znth 0 prog 0-1) cold 0 :=
    fun other total => prefix_state_cost_one__initialization prog cold hot other total (by omega)
  refine ⟨?_,?_,?_⟩
  · intro other ho
    by_cases he : other=0
    · subst other
      rw [hz]
      refine Or.inl ⟨by decide,?_⟩
      refine ⟨_,⟨(hsc 0 _).mpr ⟨rfl,rfl⟩,?_⟩,by (try dsimp only); omega⟩
      intro v hv
      have h := (hsc 0 v).mp hv
      dsimp only at *
      omega
    · refine Or.inr ⟨hother other ho he,?_⟩
      rintro ⟨total,htotal⟩
      exact he ((hsc other total).mp htotal).1
  · refine ⟨0,⟨⟨0,⟨by omega,by (try dsimp only); omega⟩,hz.symm,by decide⟩,?_⟩,rfl⟩
    rintro v ⟨other,ho,he,hfinite⟩
    by_cases h0 : other=0
    · subst other
      rw [hz] at he
      dsimp only at *
      omega
    · rw [hother other ho h0] at he
      dsimp only at *
      omega
  · have hsub : sublist 0 1 prog=[Znth 0 prog 0] := by
      simpa using sublist_single 0 0 prog (show 0 ≤ (0:Int) ∧ (0:Int) < Zlength prog by omega)
    refine ⟨Znth (Znth 0 prog 0-1) cold 0,⟨?_,?_⟩,by (try dsimp only); omega⟩
    · rw [hsub]
      exact run_cost_single_exists__initialization _ cold hot
    · rintro v ⟨cpu,hr⟩
      rw [hsub] at hr
      have h := run_cost_single__initialization _ cold hot cpu v hr
      dsimp only at *
      omega

theorem normalized_schedule_state_min_le__state_transitions (prog cold hot : List Int) (prefix_len : Int)
    (dp : List Int) (off mind other : Int) (hs : NormalizedScheduleState prog cold hot prefix_len dp off mind)
    (ho : 0 ≤ other ∧ other ≤ Zlength cold) (hf : Znth other dp DP_INF < DP_INF) : mind ≤ Znth other dp DP_INF :=
  min_value_member_le__state_transitions _ mind _ hs.2.1 ⟨other,ho,rfl,hf⟩

private theorem snoc_of_positive (l : List Int) (hl : 0 < Zlength l) : ∃ xs x, l=xs++[x] := by
  cases he : l.reverse with
  | nil =>
    have hh := congrArg List.reverse he
    simp only [List.reverse_reverse,List.reverse_nil] at hh
    rw [hh] at hl
    exact False.elim (by simpa [Zlength] using hl)
  | cons x xs =>
    refine ⟨xs.reverse,x,?_⟩
    have hh := congrArg List.reverse he
    simpa only [List.reverse_reverse,List.reverse_cons] using hh

theorem run_cost_snoc_inv__state_transitions (prog cold hot sched : List Int) (total x : Int)
    (hr : RunCost (prog++[x]) cold hot sched total) :
    ∃ cpu times label t base,
      sched=cpu++[label] ∧ (label=1 ∨ label=2) ∧ ValidSchedule prog cpu ∧
      RunTimes prog cold hot cpu times ∧ base=times.foldr (· + ·) 0 ∧ total=base+t ∧
      RunTime (prog++[x]) cold hot (cpu++[label]) (times++[t]) (Zlength prog) := by
  obtain ⟨⟨hslen,hlabels⟩,alltimes,⟨htlen,hrt⟩,hsum⟩ := hr
  have hpl : Zlength (prog++[x])=Zlength prog+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hpn := Zlength_nonneg prog
  obtain ⟨cpu,label,rfl⟩ := snoc_of_positive sched (by omega)
  obtain ⟨times,t,rfl⟩ := snoc_of_positive alltimes (by omega)
  have hcl : Zlength cpu=Zlength prog := by simp only [Zlength_app,Zlength_cons,Zlength_nil] at hslen; omega
  have htl : Zlength times=Zlength prog := by simp only [Zlength_app,Zlength_cons,Zlength_nil] at htlen; omega
  have hlabel : label=1 ∨ label=2 := Forall.iff_forall_mem.mp hlabels label (List.mem_append_right cpu (List.mem_singleton_self label))
  have hold : Forall (fun z => z=1 ∨ z=2) cpu := Forall.iff_forall_mem.mpr (fun z hz =>
    Forall.iff_forall_mem.mp hlabels z (List.mem_append_left [label] hz))
  refine ⟨cpu,times,label,t,times.foldr (· + ·) 0,rfl,hlabel,⟨hcl,hold⟩,⟨htl,?_⟩,rfl,?_,?_⟩
  · intro pos hpos
    exact (run_time_snoc_old_iff__normalized_step prog cold hot cpu times x label t pos hcl htl hpos).mpr (hrt pos (by omega))
  · rwa [fold_right_add_snoc__normalized_step] at hsum
  · exact hrt (Zlength prog) (by omega)

theorem other_cpu_last_exists__state_transitions (prog cpu : List Int)
    (hv : ValidSchedule prog cpu) (hpos : 0 < Zlength prog) : ∃ other, OtherCpuLastProgram prog cpu other := by
  classical
  have hlen := hv.1
  by_cases hall : ∀ q, (0 ≤ q ∧ q < Zlength prog) → Znth q cpu 0=Znth (Zlength prog-1) cpu 0
  · exact ⟨0,hpos,hlen,Or.inl ⟨rfl,hall⟩⟩
  · have hex : ∃ q, (0 ≤ q ∧ q < Zlength prog) ∧ Znth q cpu 0≠Znth (Zlength prog-1) cpu 0 := by
      push_neg at hall
      obtain ⟨q,hq,hne⟩ := hall
      exact ⟨q,hq,hne⟩
    obtain ⟨q,hq,hne⟩ := hex
    obtain ⟨last,hlast,hlr,hmax⟩ := max_n_in_range
      (fun r => Znth r cpu 0≠Znth (Zlength prog-1) cpu 0) (Zlength prog-1) (by omega) ⟨q,⟨hq.1,by omega⟩,hne⟩
    refine ⟨Znth last prog 0,hpos,hlen,Or.inr ⟨last,⟨hlr.1,by omega⟩,hlast,rfl,?_⟩⟩
    intro r hr
    by_contra hne
    have hh := hmax r ⟨by omega,by omega⟩ hne
    omega

theorem other_cpu_last_continue_inv__state_transitions (prog cpu : List Int) (other x : Int)
    (hv : ValidSchedule prog cpu) (hpos : 0 < Zlength prog)
    (ho : OtherCpuLastProgram (prog++[x]) (cpu++[Znth (Zlength prog-1) cpu 0]) other) : OtherCpuLastProgram prog cpu other := by
  have hlen := hv.1
  have hpl : Zlength (prog++[x])=Zlength prog+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hlast : Znth (Zlength (prog++[x])-1) (cpu++[Znth (Zlength prog-1) cpu 0]) 0=Znth (Zlength prog-1) cpu 0 := by
    rw [hpl,show Zlength prog+1-1=Zlength cpu by omega,Znth_app_last__normalized_step]
  obtain ⟨_,_,ho⟩ := ho
  dsimp only at ho
  rw [hlast] at ho
  refine ⟨hpos,hlen,?_⟩
  rcases ho with ⟨hz,hall⟩ | ⟨q,hq,hne,he,hall⟩
  · refine Or.inl ⟨hz,?_⟩
    intro q hq
    have hh := hall q (by omega)
    rw [Znth_app_left__normalized_step Int 0 cpu _ q (by omega)] at hh
    exact hh
  · have hqold : q < Zlength prog := by
      by_contra h
      have hqeq : q=Zlength cpu := by omega
      rw [hqeq,Znth_app_last__normalized_step] at hne
      exact hne rfl
    refine Or.inr ⟨q,⟨hq.1,hqold⟩,?_,?_,?_⟩
    · rwa [Znth_app_left__normalized_step Int 0 cpu _ q (by omega)] at hne
    · rwa [Znth_app_left__normalized_step Int 0 prog [x] q ⟨hq.1,hqold⟩] at he
    · intro r hr
      have hh := hall r (by omega)
      rwa [Znth_app_left__normalized_step Int 0 cpu _ r (by omega)] at hh

theorem other_cpu_last_switch_value__state_transitions (prog cpu : List Int) (other x label : Int)
    (hv : ValidSchedule prog cpu) (hpos : 0 < Zlength prog)
    (hlne : label≠Znth (Zlength prog-1) cpu 0)
    (ho : OtherCpuLastProgram (prog++[x]) (cpu++[label]) other) : other=Znth (Zlength prog-1) prog 0 := by
  have hlen := hv.1
  have hpl : Zlength (prog++[x])=Zlength prog+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hlast : Znth (Zlength (prog++[x])-1) (cpu++[label]) 0=label := by
    rw [hpl,show Zlength prog+1-1=Zlength cpu by omega,Znth_app_last__normalized_step]
  obtain ⟨_,_,ho⟩ := ho
  dsimp only at ho
  rw [hlast] at ho
  rcases ho with ⟨_,hall⟩ | ⟨q,hq,hne,he,hall⟩
  · have hh := hall (Zlength prog-1) (by omega)
    rw [Znth_app_left__normalized_step Int 0 cpu [label] _ (by omega)] at hh
    exact False.elim (hlne hh.symm)
  · have hqold : q < Zlength prog := by
      by_contra h
      have hqeq : q=Zlength cpu := by omega
      rw [hqeq,Znth_app_last__normalized_step] at hne
      exact hne rfl
    have hqeq : q=Zlength prog-1 := by
      by_contra h
      have hh := hall (Zlength prog-1) (by omega)
      rw [Znth_app_left__normalized_step Int 0 cpu [label] _ (by omega)] at hh
      exact hlne hh.symm
    rw [Znth_app_left__normalized_step Int 0 prog [x] q ⟨hq.1,hqold⟩,hqeq] at he
    exact he

private theorem prefix_length (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i ≤ Zlength l) :
    Zlength (sublist 0 i l)=i := ListLib.Zlength_sublist0 i l hi

private theorem prefix_read (l : List Int) (i q : Int) (hq : 0 ≤ q ∧ q < i) :
    Znth q (sublist 0 i l) 0=Znth q l 0 := ListLib.Znth_sublist0 0 q i l hq

theorem prefix_state_cost_step_iff__state_transitions (prog cold hot : List Int) (i x y other total : Int)
    (hi : 1 ≤ i ∧ i < Zlength prog) (hx : x=Znth i prog 0) (hy : y=Znth (i-1) prog 0) (hxpos : 1 ≤ x) :
    PrefixStateCost prog cold hot (i+1) other total ↔
      ((∃ oldtotal, PrefixStateCost prog cold hot i other oldtotal ∧
        total=oldtotal+(if x=y then Znth (x-1) hot 0 else Znth (x-1) cold 0)) ∨
      (other=y ∧ ∃ oldother oldtotal, PrefixStateCost prog cold hot i oldother oldtotal ∧
        total=oldtotal+(if oldother=x then Znth (x-1) hot 0 else Znth (x-1) cold 0))) := by
  let pref := sublist 0 i prog
  have hplen : Zlength pref=i := prefix_length prog i (by omega)
  have hppos : 0 < Zlength pref := by omega
  have hprefix : sublist 0 (i+1) prog=pref++[x] := by
    rw [hx]
    exact sublist_0_succ__normalized_step Int 0 prog i (by omega)
  have hlast : Znth (Zlength pref-1) pref 0=y := by
    rw [hplen,prefix_read prog i (i-1) (by omega)]
    exact hy.symm
  constructor
  · rintro ⟨sched,hr,ho⟩
    rw [hprefix] at hr ho
    obtain ⟨cpu,times,label,t,base,rfl,hlabel,hvalid,htimes,hbase,htotal,hfinal⟩ :=
      run_cost_snoc_inv__state_transitions pref cold hot sched total x hr
    obtain ⟨oldother,holdother⟩ := other_cpu_last_exists__state_transitions pref cpu hvalid hppos
    by_cases hcont : label=Znth (Zlength pref-1) cpu 0
    · rw [hcont] at ho hfinal
      refine Or.inl ⟨base,⟨cpu,⟨hvalid,times,htimes,hbase⟩,
        other_cpu_last_continue_inv__state_transitions pref cpu other x hvalid hppos ho⟩,?_⟩
      have hf := (run_time_continue_final_iff__normalized_step pref cold hot cpu times x t hvalid.1 htimes.1 hppos).mp hfinal
      rw [hlast] at hf
      split <;> rcases hf with ⟨he,ht⟩ | ⟨hne,ht⟩ <;> omega
    · refine Or.inr ⟨(other_cpu_last_switch_value__state_transitions pref cpu other x label hvalid hppos hcont ho).trans hlast,
        oldother,base,⟨cpu,⟨hvalid,times,htimes,hbase⟩,holdother⟩,?_⟩
      have hflip := binary_label_other__normalized_step _ label (valid_schedule_active_label__normalized_step pref cpu hvalid hppos) hlabel hcont
      rw [hflip] at hfinal
      have hf := (run_time_switch_final_iff__normalized_step pref cold hot cpu times oldother x t hvalid holdother htimes.1 hppos (by omega)).mp hfinal
      split <;> rcases hf with ⟨he,ht⟩ | ⟨hne,ht⟩ <;> omega
  · rintro (⟨oldtotal,⟨cpu,⟨hv,times,ht,hbase⟩,hold⟩,htotal⟩ | ⟨hother,oldother,oldtotal,⟨cpu,⟨hv,times,ht,hbase⟩,hold⟩,htotal⟩)
    · let active := Znth (Zlength pref-1) cpu 0
      change ValidSchedule pref cpu at hv
      change RunTimes pref cold hot cpu times at ht
      change OtherCpuLastProgram pref cpu other at hold
      change ∃ sched, RunCost (sublist 0 (i+1) prog) cold hot sched total ∧ OtherCpuLastProgram (sublist 0 (i+1) prog) sched other
      rw [hprefix]
      refine ⟨cpu++[active],?_,other_cpu_last_continue__normalized_step pref cpu other x hold⟩
      rw [htotal]
      apply run_cost_snoc__normalized_step pref cold hot cpu times oldtotal x active _ hv
        (valid_schedule_active_label__normalized_step pref cpu hv hppos) ht hbase
      apply (run_time_continue_final_iff__normalized_step pref cold hot cpu times x _ hv.1 ht.1 hppos).mpr
      rw [hlast]
      by_cases he : x=y
      · exact Or.inl ⟨he,if_pos he⟩
      · exact Or.inr ⟨he,if_neg he⟩
    · let active := Znth (Zlength pref-1) cpu 0
      change ValidSchedule pref cpu at hv
      change RunTimes pref cold hot cpu times at ht
      change OtherCpuLastProgram pref cpu oldother at hold
      change ∃ sched, RunCost (sublist 0 (i+1) prog) cold hot sched total ∧ OtherCpuLastProgram (sublist 0 (i+1) prog) sched other
      rw [hprefix]
      refine ⟨cpu++[other_cpu_label active],?_,?_⟩
      · rw [htotal]
        apply run_cost_snoc__normalized_step pref cold hot cpu times oldtotal x (other_cpu_label active) _ hv
          (other_cpu_label_valid__normalized_step active (valid_schedule_active_label__normalized_step pref cpu hv hppos)) ht hbase
        apply (run_time_switch_final_iff__normalized_step pref cold hot cpu times oldother x _ hv hold ht.1 hppos (by omega)).mpr
        by_cases he : oldother=x
        · exact Or.inl ⟨he,if_pos he⟩
        · exact Or.inr ⟨he,if_neg he⟩
      · rw [hother,← hlast]
        exact other_cpu_last_switch__normalized_step pref cpu x hv hppos

theorem prefix_state_cost_other_bound__state_transitions (prog cold hot : List Int) (i other total : Int)
    (hi : 0 < i ∧ i ≤ Zlength prog)
    (hp : ∀ q, (0 ≤ q ∧ q < Zlength prog) → 1 ≤ Znth q prog 0 ∧ Znth q prog 0 ≤ Zlength cold)
    (hs : PrefixStateCost prog cold hot i other total) : 0 ≤ other ∧ other ≤ Zlength cold := by
  obtain ⟨cpu,_,_,_,⟨rfl,_⟩ | ⟨q,hq,_,rfl,_⟩⟩ := hs
  · have h := Zlength_nonneg cold; omega
  · rw [prefix_length prog i (by omega)] at hq
    rw [prefix_read prog i q hq]
    have hh := hp q (by omega)
    omega

theorem normalized_switch_minimum__state_transitions (prog cold hot : List Int) (i : Int) (dp : List Int)
    (off mind x cand : Int) (hi : 1 ≤ i ∧ i < Zlength prog) (hx : 1 ≤ x ∧ x ≤ Zlength cold)
    (hp : ∀ q, (0 ≤ q ∧ q < Zlength prog) → 1 ≤ Znth q prog 0 ∧ Znth q prog 0 ≤ Zlength cold)
    (hhc : Znth (x-1) hot 0 ≤ Znth (x-1) cold 0) (hs : NormalizedScheduleState prog cold hot i dp off mind)
    (hcc : cand ≤ mind+off+Znth (x-1) cold 0)
    (hch : Znth x dp DP_INF < DP_INF → cand ≤ Znth x dp DP_INF+off+Znth (x-1) hot 0)
    (hatt : cand=mind+off+Znth (x-1) cold 0 ∨
      (Znth x dp DP_INF < DP_INF ∧ cand=Znth x dp DP_INF+off+Znth (x-1) hot 0)) :
    min_value_of_subset (· ≤ ·)
      (fun total => ∃ oldother oldtotal, PrefixStateCost prog cold hot i oldother oldtotal ∧
        total=oldtotal+(if oldother=x then Znth (x-1) hot 0 else Znth (x-1) cold 0)) (fun z => z) cand := by
  refine ⟨cand,⟨?_,?_⟩,rfl⟩
  · rcases hatt with hcold | ⟨hfinite,hhot⟩
    · obtain ⟨oldother,hor,hval,hfin⟩ := min_value_member__state_transitions _ mind hs.2.1
      rcases hs.1 oldother hor with ⟨_,hmin⟩ | ⟨hinf,_⟩
      · have hold := min_value_member__state_transitions _ _ hmin
        rw [← hval] at hold
        refine ⟨oldother,off+mind,hold,?_⟩
        by_cases he : oldother=x
        · subst oldother
          have hh := hch (by omega)
          rw [if_pos rfl]
          omega
        · rw [if_neg he]
          omega
      · omega
    · rcases hs.1 x ⟨by omega,hx.2⟩ with ⟨_,hmin⟩ | ⟨hinf,_⟩
      · refine ⟨x,off+Znth x dp DP_INF,min_value_member__state_transitions _ _ hmin,?_⟩
        rw [if_pos rfl]
        omega
      · omega
  · rintro total ⟨oldother,oldtotal,hold,htotal⟩
    change cand ≤ total
    have hor := prefix_state_cost_other_bound__state_transitions prog cold hot i oldother oldtotal (by omega) hp hold
    rcases hs.1 oldother hor with ⟨hfin,hmin⟩ | ⟨_,hnone⟩
    · have hcell := min_value_member_le__state_transitions _ _ oldtotal hmin hold
      have hm := normalized_schedule_state_min_le__state_transitions prog cold hot i dp off mind oldother hs hor hfin
      by_cases he : oldother=x
      · subst oldother
        rw [if_pos rfl] at htotal
        have hh := hch (by omega)
        omega
      · rw [if_neg he] at htotal
        omega
    · exact False.elim (hnone ⟨oldtotal,hold⟩)

theorem normalized_cell_continue_step__state_transitions (prog cold hot : List Int) (i x y other off ca value : Int)
    (hi : 1 ≤ i ∧ i < Zlength prog) (hx : x=Znth i prog 0) (hy : y=Znth (i-1) prog 0) (hxpos : 1 ≤ x)
    (hca : ca=if x=y then Znth (x-1) hot 0 else Znth (x-1) cold 0) (hne : other≠y)
    (hc : NormalizedScheduleCell prog cold hot i other off value) :
    NormalizedScheduleCell prog cold hot (i+1) other (off+ca) value := by
  have he : ∀ total, PrefixStateCost prog cold hot (i+1) other total ↔
      ∃ oldtotal, PrefixStateCost prog cold hot i other oldtotal ∧ total=oldtotal+ca := by
    intro total
    rw [prefix_state_cost_step_iff__state_transitions prog cold hot i x y other total hi hx hy hxpos,← hca]
    simp only [hne,false_and,or_false]
  rcases hc with ⟨hfin,hmin⟩ | ⟨hinf,hnone⟩
  · refine Or.inl ⟨hfin,?_⟩
    refine ⟨off+ca+value,⟨(he _).mpr ⟨off+value,min_value_member__state_transitions _ _ hmin,by omega⟩,?_⟩,rfl⟩
    intro v hv
    change off+ca+value ≤ v
    obtain ⟨old,hold,heq⟩ := (he v).mp hv
    have hh := min_value_member_le__state_transitions _ _ old hmin hold
    omega
  · refine Or.inr ⟨hinf,?_⟩
    rintro ⟨total,htotal⟩
    obtain ⟨old,hold,_⟩ := (he total).mp htotal
    exact hnone ⟨old,hold⟩

theorem normalized_cells_min_spec__state_transitions (prog cold hot : List Int) (prefix_len : Int)
    (dp : List Int) (off mind : Int) (hi : 0 < prefix_len ∧ prefix_len ≤ Zlength prog)
    (hp : ∀ q, (0 ≤ q ∧ q < Zlength prog) → 1 ≤ Znth q prog 0 ∧ Znth q prog 0 ≤ Zlength cold)
    (hcells : ∀ other, (0 ≤ other ∧ other ≤ Zlength cold) →
      NormalizedScheduleCell prog cold hot prefix_len other off (Znth other dp DP_INF))
    (hmin : min_value_of_subset (· ≤ ·) (fun value => ∃ other,
      (0 ≤ other ∧ other ≤ Zlength cold) ∧ value=Znth other dp DP_INF ∧ value < DP_INF) (fun z => z) mind) :
    Spec (sublist 0 prefix_len prog) cold hot (off+mind) := by
  refine ⟨off+mind,⟨?_,?_⟩,rfl⟩
  · obtain ⟨other,hor,hval,hfin⟩ := min_value_member__state_transitions _ mind hmin
    rcases hcells other hor with ⟨_,hcell⟩ | ⟨hinf,_⟩
    · have hold := min_value_member__state_transitions _ _ hcell
      rw [← hval] at hold
      obtain ⟨cpu,hr,_⟩ := hold
      exact ⟨cpu,hr⟩
    · omega
  · rintro v ⟨cpu,hr⟩
    change off+mind ≤ v
    have hlen := prefix_length prog prefix_len (by omega)
    obtain ⟨other,ho⟩ := other_cpu_last_exists__state_transitions (sublist 0 prefix_len prog) cpu hr.1 (by omega)
    have hstate : PrefixStateCost prog cold hot prefix_len other v := ⟨cpu,hr,ho⟩
    have hor := prefix_state_cost_other_bound__state_transitions prog cold hot prefix_len other v hi hp hstate
    rcases hcells other hor with ⟨hfin,hcell⟩ | ⟨_,hnone⟩
    · have hle := min_value_member_le__state_transitions _ _ v hcell hstate
      have hm := min_value_member_le__state_transitions _ mind (Znth other dp DP_INF) hmin ⟨other,hor,rfl,hfin⟩
      omega
    · exact False.elim (hnone ⟨v,hstate⟩)

theorem Zlength_replace_Znth__state_write_update {A : Type} (xs : List A) (i : Int) (v : A) :
    Zlength (replace_Znth i v xs)=Zlength xs := Zlength_replace_Znth xs i v

theorem Znth_zero_replace_positive__state_write_update (xs : List Int) (i v : Int)
    (hi : 1 ≤ i ∧ i < Zlength xs) (hz : Znth 0 xs 0=0) : Znth 0 (replace_Znth i v xs) 0=0 := by
  rw [Znth_replace_Znth_Diff 0 xs i 0 v (by omega) (by omega) (by omega)]
  exact hz

theorem replace_Znth_dp_bounds__state_write_update (dp : List Int) (k i idx value : Int)
    (hlen : Zlength dp=k+1) (hi : 1 ≤ idx ∧ idx ≤ k)
    (hb : ∀ q, (0 ≤ q ∧ q ≤ k) → Znth q dp 0=4557430888798830399 ∨
      (-i)*1000000000 ≤ Znth q dp 0 ∧ Znth q dp 0 ≤ i*1000000000)
    (hlo : (-(i+1))*1000000000 ≤ value) (hhi : value ≤ (i+1)*1000000000)
    (q : Int) (hq : 0 ≤ q ∧ q ≤ k) :
    Znth q (replace_Znth idx value dp) 0=4557430888798830399 ∨
      (-(i+1))*1000000000 ≤ Znth q (replace_Znth idx value dp) 0 ∧
      Znth q (replace_Znth idx value dp) 0 ≤ (i+1)*1000000000 := by
  by_cases he : idx=q
  · subst q
    rw [Znth_replace_Znth_Same 0 dp idx value (by omega)]
    exact Or.inr ⟨hlo,hhi⟩
  · rw [Znth_replace_Znth_Diff 0 dp idx q value (by omega) (by omega) he]
    rcases hb q hq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega,by omega⟩

theorem normalized_cell_switch_step__state_transitions (prog cold hot : List Int)
    (i x y off ca oldvalue cand ny newvalue : Int) (hi : 1 ≤ i ∧ i < Zlength prog)
    (hx : x=Znth i prog 0) (hy : y=Znth (i-1) prog 0) (hxpos : 1 ≤ x)
    (hca : ca=if x=y then Znth (x-1) hot 0 else Znth (x-1) cold 0)
    (hcand : cand=off+ca+ny) (hny : ny < DP_INF)
    (hswitch : min_value_of_subset (· ≤ ·) (fun total => ∃ oldother oldtotal,
      PrefixStateCost prog cold hot i oldother oldtotal ∧
      total=oldtotal+(if oldother=x then Znth (x-1) hot 0 else Znth (x-1) cold 0)) (fun z => z) cand)
    (hold : NormalizedScheduleCell prog cold hot i y off oldvalue)
    (hsel : (ny < oldvalue ∧ newvalue=ny) ∨ (oldvalue ≤ ny ∧ newvalue=oldvalue)) :
    NormalizedScheduleCell prog cold hot (i+1) y (off+ca) newvalue := by
  have he := fun total => prefix_state_cost_step_iff__state_transitions prog cold hot i x y y total hi hx hy hxpos
  rcases hsel with ⟨hlt,hevalue⟩ | ⟨hle,hevalue⟩
  · rw [hevalue]
    refine Or.inl ⟨hny,cand,⟨?_,?_⟩,hcand⟩
    · exact (he cand).mpr (Or.inr ⟨rfl,min_value_member__state_transitions _ cand hswitch⟩)
    · intro total htotal
      change cand ≤ total
      rcases (he total).mp htotal with ⟨oldtotal,holdcost,heq⟩ | ⟨_,hs⟩
      · rcases hold with ⟨_,hmin⟩ | ⟨_,hnone⟩
        · have hh := min_value_member_le__state_transitions _ _ oldtotal hmin holdcost
          rw [← hca] at heq
          omega
        · exact False.elim (hnone ⟨oldtotal,holdcost⟩)
      · exact min_value_member_le__state_transitions _ cand total hswitch hs
  · rw [hevalue]
    rcases hold with ⟨hfin,hmin⟩ | ⟨hinf,_⟩
    · refine Or.inl ⟨hfin,off+ca+oldvalue,⟨?_,?_⟩,rfl⟩
      · apply (he _).mpr
        refine Or.inl ⟨off+oldvalue,min_value_member__state_transitions _ _ hmin,?_⟩
        rw [← hca]
        omega
      · intro total htotal
        change off+ca+oldvalue ≤ total
        rcases (he total).mp htotal with ⟨oldtotal,holdcost,heq⟩ | ⟨_,hs⟩
        · have hh := min_value_member_le__state_transitions _ _ oldtotal hmin holdcost
          rw [← hca] at heq
          omega
        · have hh := min_value_member_le__state_transitions _ cand total hswitch hs
          omega
    · omega

theorem normalized_vector_min_replace__state_transitions (cold dp : List Int) (mind y ny : Int)
    (newdp : List Int) (newmind : Int) (hlen : Zlength dp=Zlength cold+1)
    (hy : 0 ≤ y ∧ y ≤ Zlength cold) (hny : ny < DP_INF)
    (hmin : min_value_of_subset (· ≤ ·) (fun value => ∃ other,
      (0 ≤ other ∧ other ≤ Zlength cold) ∧ value=Znth other dp DP_INF ∧ value < DP_INF) (fun z => z) mind)
    (hdp : (ny < Znth y dp DP_INF ∧ newdp=replace_Znth y ny dp) ∨
      (Znth y dp DP_INF ≤ ny ∧ newdp=dp))
    (hmind : (ny < mind ∧ newmind=ny) ∨ (mind ≤ ny ∧ newmind=mind)) :
    min_value_of_subset (· ≤ ·) (fun value => ∃ other,
      (0 ≤ other ∧ other ≤ Zlength cold) ∧ value=Znth other newdp DP_INF ∧ value < DP_INF) (fun z => z) newmind := by
  have hyr : 0 ≤ y ∧ y < Zlength dp := by omega
  rcases hdp with ⟨hnyold,hedp⟩ | ⟨holdny,hedp⟩
  · rw [hedp]
    have hsame := Znth_replace_Znth_Same DP_INF dp y ny hyr
    have hdiff : ∀ q, (0 ≤ q ∧ q ≤ Zlength cold) → q≠y → Znth q (replace_Znth y ny dp) DP_INF=Znth q dp DP_INF := by
      intro q hq hne
      exact Znth_replace_Znth_Diff DP_INF dp y q ny hyr (by omega) (Ne.symm hne)
    rcases hmind with ⟨hnymin,hemind⟩ | ⟨hminny,hemind⟩
    · rw [hemind]
      refine ⟨ny,⟨⟨y,hy,hsame.symm,hny⟩,?_⟩,rfl⟩
      rintro value ⟨other,hor,hval,hfin⟩
      change ny ≤ value
      by_cases he : other=y
      · subst other
        rw [hsame] at hval
        omega
      · rw [hdiff other hor he] at hval
        have h := min_value_member_le__state_transitions _ mind value hmin ⟨other,hor,hval,hfin⟩
        omega
    · rw [hemind]
      obtain ⟨other,hor,hval,hfin⟩ := min_value_member__state_transitions _ mind hmin
      have hne : other≠y := by intro he; subst other; omega
      refine ⟨mind,⟨⟨other,hor,by rw [hdiff other hor hne]; exact hval,hfin⟩,?_⟩,rfl⟩
      rintro value ⟨q,hq,hvalue,hfinite⟩
      change mind ≤ value
      by_cases he : q=y
      · subst q
        rw [hsame] at hvalue
        omega
      · rw [hdiff q hq he] at hvalue
        exact min_value_member_le__state_transitions _ mind value hmin ⟨q,hq,hvalue,hfinite⟩
  · rw [hedp]
    rcases hmind with ⟨hnymin,_⟩ | ⟨_,hemind⟩
    · have h := min_value_member_le__state_transitions _ mind (Znth y dp DP_INF) hmin ⟨y,hy,rfl,by omega⟩
      omega
    · rw [hemind]; exact hmin

theorem normalized_schedule_state_step__state_transitions (prog cold hot : List Int) (i : Int)
    (dp : List Int) (off mind x y ca cand ny : Int) (newdp : List Int) (newmind : Int)
    (hi : 1 ≤ i ∧ i < Zlength prog) (hx : x=Znth i prog 0) (hy : y=Znth (i-1) prog 0)
    (hlen : Zlength dp=Zlength cold+1) (hxr : 1 ≤ x ∧ x ≤ Zlength cold) (hyr : 0 ≤ y ∧ y ≤ Zlength cold)
    (hp : ∀ q, (0 ≤ q ∧ q < Zlength prog) → 1 ≤ Znth q prog 0 ∧ Znth q prog 0 ≤ Zlength cold)
    (hhc : Znth (x-1) hot 0 ≤ Znth (x-1) cold 0) (hs : NormalizedScheduleState prog cold hot i dp off mind)
    (hca : ca=if x=y then Znth (x-1) hot 0 else Znth (x-1) cold 0)
    (hcand : cand=off+ca+ny) (hny : ny < DP_INF) (hcc : cand ≤ mind+off+Znth (x-1) cold 0)
    (hch : Znth x dp DP_INF < DP_INF → cand ≤ Znth x dp DP_INF+off+Znth (x-1) hot 0)
    (hatt : cand=mind+off+Znth (x-1) cold 0 ∨
      (Znth x dp DP_INF < DP_INF ∧ cand=Znth x dp DP_INF+off+Znth (x-1) hot 0))
    (hdp : (ny < Znth y dp DP_INF ∧ newdp=replace_Znth y ny dp) ∨ (Znth y dp DP_INF ≤ ny ∧ newdp=dp))
    (hmind : (ny < mind ∧ newmind=ny) ∨ (mind ≤ ny ∧ newmind=mind)) :
    NormalizedScheduleState prog cold hot (i+1) newdp (off+ca) newmind := by
  have hswitch := normalized_switch_minimum__state_transitions prog cold hot i dp off mind x cand hi hxr hp hhc hs hcc hch hatt
  have hm := normalized_vector_min_replace__state_transitions cold dp mind y ny newdp newmind hlen hyr hny hs.2.1 hdp hmind
  have hcells : ∀ other, (0 ≤ other ∧ other ≤ Zlength cold) →
      NormalizedScheduleCell prog cold hot (i+1) other (off+ca) (Znth other newdp DP_INF) := by
    intro other hor
    by_cases he : other=y
    · subst other
      apply normalized_cell_switch_step__state_transitions prog cold hot i x y off ca (Znth y dp DP_INF) cand ny _ hi hx hy hxr.1 hca hcand hny hswitch (hs.1 y hyr)
      rcases hdp with ⟨hlt,rfl⟩ | ⟨hle,rfl⟩
      · exact Or.inl ⟨hlt,Znth_replace_Znth_Same DP_INF dp y ny (by omega)⟩
      · exact Or.inr ⟨hle,rfl⟩
    · have hold := normalized_cell_continue_step__state_transitions prog cold hot i x y other off ca (Znth other dp DP_INF) hi hx hy hxr.1 hca he (hs.1 other hor)
      rcases hdp with ⟨_,rfl⟩ | ⟨_,rfl⟩
      · rw [Znth_replace_Znth_Diff DP_INF dp y other ny (by omega) (by omega) (Ne.symm he)]
        exact hold
      · exact hold
  exact ⟨hcells,hm,normalized_cells_min_spec__state_transitions prog cold hot (i+1) newdp (off+ca) newmind (by omega) hp hcells hm⟩

theorem normalized_unequal_transition_branches__state_transitions (prog cold hot : List Int) (i : Int)
    (dp : List Int) (off mind x y : Int) (hi : 1 ≤ i ∧ i < Zlength prog)
    (hx : x=Znth i prog 0) (hy : y=Znth (i-1) prog 0) (hlen : Zlength dp=Zlength cold+1)
    (hxr : 1 ≤ x ∧ x ≤ Zlength cold) (hyr : 1 ≤ y ∧ y ≤ Zlength cold)
    (hp : ∀ q, (0 ≤ q ∧ q < Zlength prog) → 1 ≤ Znth q prog 0 ∧ Znth q prog 0 ≤ Zlength cold)
    (hhc : Znth (x-1) hot 0 ≤ Znth (x-1) cold 0) (hs : NormalizedScheduleState prog cold hot i dp off mind)
    (hxy : x≠y) (hfinite : Znth x dp 0 < DP_INF)
    (hbetter : Znth x dp 0+off+Znth (x-1) hot 0 < mind+off+Znth (x-1) cold 0) :
    let hotc := Znth (x-1) hot 0
    let coldc := Znth (x-1) cold 0
    let ny := Znth x dp 0+hotc-coldc;
      (ny ≥ Znth y dp 0 → NormalizedScheduleState prog cold hot (i+1) dp (off+coldc) mind) ∧
      ((ny < Znth y dp 0 ∧ ny < mind) → NormalizedScheduleState prog cold hot (i+1) (replace_Znth y ny dp) (off+coldc) ny) ∧
      ((ny < Znth y dp 0 ∧ ny ≥ mind) → NormalizedScheduleState prog cold hot (i+1) (replace_Znth y ny dp) (off+coldc) mind) := by
  dsimp only
  let ny := Znth x dp 0+Znth (x-1) hot 0-Znth (x-1) cold 0
  have hdx : Znth x dp DP_INF=Znth x dp 0 := Znth_indep dp x DP_INF 0 (by omega)
  have hdy : Znth y dp DP_INF=Znth y dp 0 := Znth_indep dp y DP_INF 0 (by omega)
  have hny : ny < DP_INF := by dsimp [ny]; omega
  have hstep : ∀ nd nm,
      ((ny < Znth y dp 0 ∧ nd=replace_Znth y ny dp) ∨ (Znth y dp 0 ≤ ny ∧ nd=dp)) →
      ((ny < mind ∧ nm=ny) ∨ (mind ≤ ny ∧ nm=mind)) →
      NormalizedScheduleState prog cold hot (i+1) nd (off+Znth (x-1) cold 0) nm := by
    intro nd nm hdp hm
    apply normalized_schedule_state_step__state_transitions prog cold hot i dp off mind x y (Znth (x-1) cold 0)
      (Znth x dp 0+off+Znth (x-1) hot 0) ny nd nm hi hx hy hlen hxr ⟨by omega,hyr.2⟩ hp hhc hs
    · exact (if_neg hxy).symm
    · dsimp [ny]; omega
    · exact hny
    · omega
    · intro _; rw [hdx]
    · exact Or.inr ⟨by rw [hdx]; exact hfinite,by rw [hdx]⟩
    · simpa only [hdy] using hdp
    · exact hm
  refine ⟨?_,?_,?_⟩
  · intro ha
    have hf : Znth y dp DP_INF < DP_INF := by rw [hdy]; omega
    have hm := normalized_schedule_state_min_le__state_transitions prog cold hot i dp off mind y hs ⟨by omega,hyr.2⟩ hf
    exact hstep dp mind (Or.inr ⟨ha,rfl⟩) (Or.inr ⟨by rw [hdy] at hm; omega,rfl⟩)
  · rintro ⟨hless,hmin⟩
    exact hstep _ _ (Or.inl ⟨hless,rfl⟩) (Or.inl ⟨hmin,rfl⟩)
  · rintro ⟨hless,hmin⟩
    exact hstep _ _ (Or.inl ⟨hless,rfl⟩) (Or.inr ⟨hmin,rfl⟩)

theorem normalized_baseline_transition_branches__state_transitions (prog cold hot : List Int) (i : Int)
    (dp : List Int) (off mind x y ca : Int) (hi : 1 ≤ i ∧ i < Zlength prog)
    (hx : x=Znth i prog 0) (hy : y=Znth (i-1) prog 0) (hlen : Zlength dp=Zlength cold+1)
    (hxr : 1 ≤ x ∧ x ≤ Zlength cold) (hyr : 1 ≤ y ∧ y ≤ Zlength cold)
    (hp : ∀ q, (0 ≤ q ∧ q < Zlength prog) → 1 ≤ Znth q prog 0 ∧ Znth q prog 0 ≤ Zlength cold)
    (hhc : Znth (x-1) hot 0 ≤ Znth (x-1) cold 0) (hs : NormalizedScheduleState prog cold hot i dp off mind)
    (hca : ca=if x=y then Znth (x-1) hot 0 else Znth (x-1) cold 0)
    (hcar : 1 ≤ ca ∧ ca ≤ Znth (x-1) cold 0) (hcmax : Znth (x-1) cold 0 ≤ 1000000000)
    (hmnon : mind ≤ 0) (hbase : mind+off+Znth (x-1) cold 0 ≤ Znth x dp 0+off+Znth (x-1) hot 0) :
    let coldc := Znth (x-1) cold 0
    let ny := mind+coldc-ca;
      ((ny < Znth y dp 0 ∧ ny < mind) → NormalizedScheduleState prog cold hot (i+1) (replace_Znth y ny dp) (off+ca) ny) ∧
      ((ny < Znth y dp 0 ∧ ny ≥ mind) → NormalizedScheduleState prog cold hot (i+1) (replace_Znth y ny dp) (off+ca) mind) ∧
      (ny ≥ Znth y dp 0 → NormalizedScheduleState prog cold hot (i+1) dp (off+ca) mind) := by
  dsimp only
  let ny := mind+Znth (x-1) cold 0-ca
  have hdx : Znth x dp DP_INF=Znth x dp 0 := Znth_indep dp x DP_INF 0 (by omega)
  have hdy : Znth y dp DP_INF=Znth y dp 0 := Znth_indep dp y DP_INF 0 (by omega)
  have hny : ny < DP_INF := by dsimp [ny,DP_INF]; omega
  have hstep : ∀ nd nm,
      ((ny < Znth y dp 0 ∧ nd=replace_Znth y ny dp) ∨ (Znth y dp 0 ≤ ny ∧ nd=dp)) →
      ((ny < mind ∧ nm=ny) ∨ (mind ≤ ny ∧ nm=mind)) →
      NormalizedScheduleState prog cold hot (i+1) nd (off+ca) nm := by
    intro nd nm hdp hm
    apply normalized_schedule_state_step__state_transitions prog cold hot i dp off mind x y ca
      (mind+off+Znth (x-1) cold 0) ny nd nm hi hx hy hlen hxr ⟨by omega,hyr.2⟩ hp hhc hs hca
    · dsimp [ny]; omega
    · exact hny
    · exact le_refl _
    · intro _; rw [hdx]; exact hbase
    · exact Or.inl rfl
    · simpa only [hdy] using hdp
    · exact hm
  refine ⟨?_,?_,?_⟩
  · rintro ⟨hless,hmin⟩
    exact hstep _ _ (Or.inl ⟨hless,rfl⟩) (Or.inl ⟨hmin,rfl⟩)
  · rintro ⟨hless,hmin⟩
    exact hstep _ _ (Or.inl ⟨hless,rfl⟩) (Or.inr ⟨hmin,rfl⟩)
  · intro ha
    have hf : Znth y dp DP_INF < DP_INF := by rw [hdy]; omega
    have hm := normalized_schedule_state_min_le__state_transitions prog cold hot i dp off mind y hs ⟨by omega,hyr.2⟩ hf
    exact hstep dp mind (Or.inr ⟨ha,rfl⟩) (Or.inr ⟨by rw [hdy] at hm; omega,rfl⟩)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib
