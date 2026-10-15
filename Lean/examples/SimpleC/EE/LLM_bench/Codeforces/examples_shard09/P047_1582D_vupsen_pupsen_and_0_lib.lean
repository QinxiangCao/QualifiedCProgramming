import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib
open AUXLib

abbrev Some {A : Type} (x : A) : Option A := .some x
abbrev None {A : Type} : Option A := .none


def Pre (a : List Int) : Prop := True

def Spec (a out : List Int) : Prop :=
  Zlength out = Zlength a ∧ Forall (fun x => x ≠ 0) out ∧
    ((a.zip out).map (fun q => q.1 * q.2)).foldr (· + ·) 0 = 0 ∧
    (out.map Z.abs).foldr (· + ·) 0 ≤ 1000000000

def GcdValue (a b : Int) : Int := Z.gcd a b

def OutputPrefix (a out : List Int) (budget : Int) : Prop :=
  Zlength out = Zlength a ∧ Forall (fun x => x ≠ 0) out ∧
    ((a.zip out).map (fun q => q.1 * q.2)).foldr (· + ·) 0 = 0 ∧
    (out.map Z.abs).foldr (· + ·) 0 ≤ 10000 * Zlength out + budget

private theorem gcd_abs_eq (a b : Int) : Z.gcd (Z.abs a) (Z.abs b) = Z.gcd a b := by
  simp only [Z.gcd,Z.abs,Int.gcd_eq_natAbs_gcd_natAbs,Int.ofNat_eq_coe,Int.natAbs_natCast]

theorem gcd_abs_positive__pair_fill (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < Z.gcd (Z.abs a) (Z.abs b) := by
  rw [gcd_abs_eq]
  exact Int.ofNat_pos.mpr (Int.gcd_pos_of_ne_zero_left b ha)

theorem pair_output_prefix__pair_fill (a b : Int) (ha : -10000 ≤ a ∧ a ≤ 10000)
    (han : a ≠ 0) (hb : -10000 ≤ b ∧ b ≤ 10000) (hbn : b ≠ 0) :
    OutputPrefix [a,b] [Z.quot b (Z.gcd (Z.abs a) (Z.abs b)),Z.quot (-a) (Z.gcd (Z.abs a) (Z.abs b))] 0 := by
  let g := Z.gcd (Z.abs a) (Z.abs b)
  have hg : 0 < g := gcd_abs_positive__pair_fill a b han hbn
  have hga : Z.divide g a := by change Z.divide (Z.gcd (Z.abs a) (Z.abs b)) a; rw [gcd_abs_eq]; exact Z.gcd_divide_l a b
  have hgb : Z.divide g b := by change Z.divide (Z.gcd (Z.abs a) (Z.abs b)) b; rw [gcd_abs_eq]; exact Z.gcd_divide_r a b
  obtain ⟨ka,hka⟩ := hga
  obtain ⟨kb,hkb⟩ := hgb
  have hqb : Z.quot b g=kb := by rw [hkb]; exact Z.quot_mul _ _ (by omega)
  have hqa : Z.quot (-a) g= -ka := by rw [hka,show -(ka*g)=(-ka)*g by ring]; exact Z.quot_mul _ _ (by omega)
  have hkan : ka ≠ 0 := by intro he; rw [he] at hka; simp at hka; exact han hka
  have hkbn : kb ≠ 0 := by intro he; rw [he] at hkb; simp at hkb; exact hbn hkb
  have habsa : Z.abs a=g*Z.abs ka := by rw [hka,Z.abs_mul,(Z.abs_eq_iff g).mpr (by omega)]; ring
  have habsb : Z.abs b=g*Z.abs kb := by rw [hkb,Z.abs_mul,(Z.abs_eq_iff g).mpr (by omega)]; ring
  have hab : Z.abs a ≤ 10000 := (Z.abs_le_iff _ _).mpr ha
  have hbb : Z.abs b ≤ 10000 := (Z.abs_le_iff _ _).mpr hb
  have hak : Z.abs ka ≤ 10000 := by nlinarith [Z.abs_nonneg ka]
  have hbk : Z.abs kb ≤ 10000 := by nlinarith [Z.abs_nonneg kb]
  change OutputPrefix [a,b] [Z.quot b g,Z.quot (-a) g] 0
  rw [hqb,hqa]
  refine ⟨rfl,Forall.cons hkbn (Forall.cons (by omega) Forall.nil),?_,?_⟩
  · change a*kb+(b*(-ka)+0)=0
    rw [hka,hkb];ring
  · change Z.abs kb+(Z.abs (-ka)+0) ≤ 10000*2+0
    rw [Z.abs_neg]; omega

theorem output_prefix_three_case1__solver_initialization (x y z : Int)
    (hx : -10000 ≤ x ∧ x ≤ 10000) (hxn : x ≠ 0)
    (hy : -10000 ≤ y ∧ y ≤ 10000) (hyn : y ≠ 0)
    (hz : -10000 ≤ z ∧ z ≤ 10000) (hzn : z ≠ 0) (hxy : x+y ≠ 0) :
    OutputPrefix [x,y,z] [z,z,-(x+y)] 10000 := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  · dsimp only [List.zip_cons_cons,List.zip_nil_left,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]
    ring
  · change Z.abs z+(Z.abs z+(Z.abs (-(x+y))+0)) ≤ 10000*3+10000
    have hax := (Z.abs_le_iff x 10000).mpr hx
    have hay := (Z.abs_le_iff y 10000).mpr hy
    have haz := (Z.abs_le_iff z 10000).mpr hz
    have hsum := (Z.abs_le_iff (-(x+y)) 20000).mpr (by omega)
    omega

theorem output_prefix_three_case2__solver_initialization (x y z : Int)
    (hx : -10000 ≤ x ∧ x ≤ 10000) (hxn : x ≠ 0)
    (hy : -10000 ≤ y ∧ y ≤ 10000) (hyn : y ≠ 0)
    (hz : -10000 ≤ z ∧ z ≤ 10000) (hzn : z ≠ 0) (hxy : x+y=0) (hxz : x+z ≠ 0) :
    OutputPrefix [x,y,z] [y,-(x+z),y] 10000 := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  · dsimp only [List.zip_cons_cons,List.zip_nil_left,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]
    ring
  · change Z.abs y+(Z.abs (-(x+z))+(Z.abs y+0)) ≤ 10000*3+10000
    have hax := (Z.abs_le_iff x 10000).mpr hx
    have hay := (Z.abs_le_iff y 10000).mpr hy
    have haz := (Z.abs_le_iff z 10000).mpr hz
    have hsum := (Z.abs_le_iff (-(x+z)) 20000).mpr (by omega)
    omega

theorem output_prefix_three_case3__solver_initialization (x y z : Int)
    (hx : -10000 ≤ x ∧ x ≤ 10000) (hxn : x ≠ 0)
    (hy : -10000 ≤ y ∧ y ≤ 10000) (hyn : y ≠ 0)
    (hz : -10000 ≤ z ∧ z ≤ 10000) (hzn : z ≠ 0) (hxy : x+y=0) (hxz : x+z=0) :
    OutputPrefix [x,y,z] [-(y+z),x,x] 10000 := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  · dsimp only [List.zip_cons_cons,List.zip_nil_left,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]
    ring
  · change Z.abs (-(y+z))+(Z.abs x+(Z.abs x+0)) ≤ 10000*3+10000
    have hax := (Z.abs_le_iff x 10000).mpr hx
    have hay := (Z.abs_le_iff y 10000).mpr hy
    have haz := (Z.abs_le_iff z 10000).mpr hz
    have hsum := (Z.abs_le_iff (-(y+z)) 20000).mpr (by omega)
    omega

theorem combine_app__loop_extension {A B : Type} (l1 l2 : List A) (r1 r2 : List B)
    (hlen : l1.length=r1.length) : (l1++l2).zip (r1++r2)=l1.zip r1++l2.zip r2 := by
  induction l1 generalizing r1 with
  | nil => cases r1 with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih => cases r1 with
    | nil => simp at hlen
    | cons y ys => simpa using ih ys (by simpa using hlen)

private theorem sum_append (l r : List Int) : (l++r).foldr (·+·) 0=l.foldr (·+·) 0+r.foldr (·+·) 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simpa only [List.cons_append,List.foldr_cons,ih,Int.add_assoc]

theorem output_prefix_append_pair__loop_extension (values written pair_out : List Int) (budget i : Int)
    (hi : 0 ≤ i) (hbound : i+1 < Zlength values)
    (hp : OutputPrefix (sublist 0 i values) written budget)
    (hq : OutputPrefix [Znth i values 0,Znth (i+1) values 0] pair_out 0) :
    OutputPrefix (sublist 0 (i+2) values) (written++pair_out) budget := by
  have hpiece : sublist 0 (i+2) values=sublist 0 i values++[Znth i values 0,Znth (i+1) values 0] := by
    rw [sublist_split 0 (i+2) i values (by omega) (by omega),
      sublist_split i (i+2) (i+1) values (by omega) (by omega),
      sublist_single 0 i values (by omega),
      show sublist (i+1) (i+2) values=[Znth (i+1) values 0] by convert sublist_single 0 (i+1) values (by omega) using 1 <;> congr 1 <;> omega]
    rfl
  rcases hp with ⟨hplen,hpn,hpdot,hpb⟩
  rcases hq with ⟨hqlen,hqn,hqdot,hqb⟩
  rw [hpiece]
  refine ⟨by simp only [Zlength_app];omega,?_,?_,?_⟩
  · exact Forall.iff_forall_mem.mpr (fun x hx => (List.mem_append.mp hx).elim (fun h => hpn.mem h) (fun h => hqn.mem h))
  · rw [combine_app__loop_extension _ _ _ _ (Int.ofNat.inj hplen.symm),List.map_append,sum_append,hpdot,hqdot]
    rfl
  · rw [List.map_append,sum_append,Zlength_app]
    omega

theorem output_prefix_to_spec_by_parity__final_result (n : Int) (values written : List Int) (i start : Int)
    (hexit : i+1 ≥ n) (hnlo : 2 ≤ n) (hnhi : n ≤ 100000) (hlen : n=Zlength values)
    (hs : start=0 ∨ start=3) (hsi : start ≤ i) (hin : i ≤ n)
    (hmod : Z.rem n 2=Z.rem start 2) (himod : Z.rem (i-start) 2=0)
    (hp : OutputPrefix (sublist 0 i values) written (Z.quot (10000*start) 3)) : i=n ∧ Spec values written := by
  have hs0 : 0 ≤ start := by omega
  have hm1 : n % 2 = start % 2 := by simpa only [Z.rem,Int.tmod_eq_emod_of_nonneg (by omega : 0 ≤ n),Int.tmod_eq_emod_of_nonneg hs0] using hmod
  have hm2 : (i-start)%2=0 := by simpa only [Z.rem,Int.tmod_eq_emod_of_nonneg (by omega : 0 ≤ i-start)] using himod
  have he : i=n := by omega
  subst i
  rw [sublist_self values n hlen] at hp
  refine ⟨rfl,hp.1,hp.2.1,hp.2.2.1,?_⟩
  have hb := hp.2.2.2
  rw [hp.1,← hlen] at hb
  rcases hs with rfl | rfl
  · change _ ≤ 10000*n+0 at hb
    omega
  · change _ ≤ 10000*n+10000 at hb
    omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib
