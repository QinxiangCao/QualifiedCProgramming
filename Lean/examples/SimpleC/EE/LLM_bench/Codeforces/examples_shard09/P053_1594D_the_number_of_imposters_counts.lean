import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_closure

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem znth_replace_same__scan_and_component_closure {A : Type} (xs : List A) (i : Int) (v d : A)
    (hi : 0 ≤ i ∧ i < Zlength xs) : Znth i (replace_Znth i v xs) d = v :=
  Znth_replace_Znth_Same d xs i v hi

theorem znth_replace_diff__scan_and_component_closure {A : Type} (xs : List A) (i j : Int) (v d : A)
    (hi : 0 ≤ i ∧ i < Zlength xs) (hj : 0 ≤ j ∧ j < Zlength xs) (hne : i ≠ j) :
    Znth j (replace_Znth i v xs) d = Znth j xs d :=
  Znth_replace_Znth_Diff d xs i j v hi hj hne

theorem sum_replace__scan_and_component_closure (xs : List Int) (i v : Int)
    (hi : 0 ≤ i ∧ i < Zlength xs) :
    (replace_Znth i v xs).foldr (· + ·) 0 = xs.foldr (· + ·) 0 - Znth i xs 0 + v := by
  induction xs generalizing i with
  | nil => simp only [Zlength_nil] at hi; omega
  | cons a xs ih =>
    rw [Zlength_cons] at hi
    by_cases hz : i = 0
    · subst i
      change v + xs.foldr (· + ·) 0 = a + xs.foldr (· + ·) 0 - a + v
      omega
    · have hp : 0 < i := by omega
      rw [replace_Znth_cons i v a xs hp, Znth_cons 0 i a xs hp, List.foldr_cons, List.foldr_cons]
      rw [ih (i-1) ⟨by omega, by omega⟩]
      omega

theorem fold_replace_length__scan_and_component_closure (vertices : List Int) (n : Int) (base : List Int)
    (f : Int → Int) (hlen : Zlength base = n) :
    Zlength (vertices.foldr (fun v r => replace_Znth (v-1) (f v) r) base) = n := by
  induction vertices with
  | nil => exact hlen
  | cons x xs ih => simpa only [List.foldr_cons, Zlength_replace_Znth] using ih

theorem fold_replace_member__scan_and_component_closure (vertices : List Int) (n : Int) (base : List Int)
    (f : Int → Int) (v : Int) (hlen : Zlength base = n) (hb : Forall (fun x => 1 ≤ x ∧ x ≤ n) vertices)
    (hv : 1 ≤ v ∧ v ≤ n) (hm : v ∈ vertices) :
    Znth (v-1) (vertices.foldr (fun x r => replace_Znth (x-1) (f x) r) base) 0 = f v := by
  induction vertices with
  | nil => simp at hm
  | cons x xs ih =>
    have hbx := Forall.iff_forall_mem.mp hb x (by simp)
    have hbt : Forall (fun x => 1 ≤ x ∧ x ≤ n) xs := Forall.iff_forall_mem.mpr (fun y hy => Forall.iff_forall_mem.mp hb y (by simp [hy]))
    have htlen := fold_replace_length__scan_and_component_closure xs n base f hlen
    simp only [List.foldr_cons]
    by_cases hx : x = v
    · subst x
      exact znth_replace_same__scan_and_component_closure _ _ _ _ ⟨by omega,by omega⟩
    · rw [znth_replace_diff__scan_and_component_closure _ _ _ _ _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)]
      exact ih hbt ((List.mem_cons.mp hm).resolve_left (Ne.symm hx))

theorem fold_replace_outside__scan_and_component_closure (vertices : List Int) (n : Int) (base : List Int)
    (f : Int → Int) (v : Int) (hlen : Zlength base = n) (hb : Forall (fun x => 1 ≤ x ∧ x ≤ n) vertices)
    (hv : 1 ≤ v ∧ v ≤ n) (hm : v ∉ vertices) :
    Znth (v-1) (vertices.foldr (fun x r => replace_Znth (x-1) (f x) r) base) 0 = Znth (v-1) base 0 := by
  induction vertices with
  | nil => rfl
  | cons x xs ih =>
    have hbx := Forall.iff_forall_mem.mp hb x (by simp)
    have hbt : Forall (fun x => 1 ≤ x ∧ x ≤ n) xs := Forall.iff_forall_mem.mpr (fun y hy => Forall.iff_forall_mem.mp hb y (by simp [hy]))
    have hx : x ≠ v := by intro h; exact hm (by simp [h])
    have htlen := fold_replace_length__scan_and_component_closure xs n base f hlen
    simp only [List.foldr_cons]
    rw [znth_replace_diff__scan_and_component_closure _ _ _ _ _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)]
    exact ih hbt (fun ht => hm (by simp [ht]))

theorem fold_replace_sum__scan_and_component_closure (vertices : List Int) (n : Int) (base : List Int)
    (f : Int → Int) (hlen : Zlength base = n) (hnd : vertices.Nodup)
    (hb : Forall (fun x => 1 ≤ x ∧ x ≤ n) vertices)
    (hz : ∀ v, v ∈ vertices → Znth (v-1) base 0 = 0) :
    (vertices.foldr (fun x r => replace_Znth (x-1) (f x) r) base).foldr (· + ·) 0 =
    base.foldr (· + ·) 0 + (vertices.map f).foldr (· + ·) 0 := by
  induction vertices with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot,hndt⟩ := List.nodup_cons.mp hnd
    have hbx := Forall.iff_forall_mem.mp hb x (by simp)
    have hbt : Forall (fun x => 1 ≤ x ∧ x ≤ n) xs := Forall.iff_forall_mem.mpr (fun y hy => Forall.iff_forall_mem.mp hb y (by simp [hy]))
    have htlen := fold_replace_length__scan_and_component_closure xs n base f hlen
    have hiht := ih hndt hbt (fun y hy => hz y (by simp [hy]))
    simp only [List.foldr_cons,List.map_cons]
    rw [sum_replace__scan_and_component_closure _ _ _ ⟨by omega,by omega⟩,
      fold_replace_outside__scan_and_component_closure xs n base f x hlen hbt hbx hnot, hz x (by simp), hiht]
    omega

theorem binary_sum_count__scan_and_component_closure (xs : List Int)
    (hb : Forall (fun x => x = 0 ∨ x = 1) xs) :
    xs.foldr (· + ·) 0 = (xs.count 1 : Int) ∧
    (xs.map (fun x => Z.lxor x 1)).foldr (· + ·) 0 = (xs.count 0 : Int) := by
  induction hb with
  | nil => exact ⟨rfl,rfl⟩
  | @cons x xs hx ht ih =>
    rcases hx with rfl | rfl
    all_goals simp only [List.foldr_cons,List.map_cons,List.count_cons,
      show Z.lxor 0 1 = 1 by rfl,show Z.lxor 1 1 = 0 by rfl,
      show ((0:Int)==1)=false by decide,show ((1:Int)==0)=false by decide,
      beq_self_eq_true,Bool.false_eq_true,↓reduceIte,Nat.cast_add,Nat.cast_one,Nat.cast_zero]
    all_goals constructor <;> omega

private theorem p053_lxor_zero_right (x : Int) : Z.lxor x 0 = x := by
  cases x <;> simp only [Z.lxor]
  all_goals congr 1; change _ ^^^ (0:Nat) = _; exact Nat.xor_zero _

theorem component_bit_sum__scan_and_component_closure (n : Int) (cs vertices : List Int) (c0 c1 flip : Int)
    (hcv : ColourValues n cs) (hb : Forall (fun v => 1 ≤ v ∧ v ≤ n) vertices)
    (hc : ∀ v, v ∈ vertices → Znth v cs 0 ≠ -1) (h0 : ColourCount cs vertices 0 c0)
    (h1 : ColourCount cs vertices 1 c1) (hf : flip = 0 ∨ flip = 1) :
    (vertices.map (fun v => Z.lxor (Znth v cs 0) flip)).foldr (· + ·) 0 = if flip = 0 then c1 else c0 := by
  have hbits : Forall (fun x => x = 0 ∨ x = 1) (vertices.map (fun v => Znth v cs 0)) := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    have hh := hcv.2 v (Forall.iff_forall_mem.mp hb v hv)
    have hne := hc v hv
    omega
  obtain ⟨hs1,hs0⟩ := binary_sum_count__scan_and_component_closure _ hbits
  rcases hf with rfl | rfl
  · simp only [ite_true,p053_lxor_zero_right]
    exact hs1.trans h1.symm
  · simp only [show ¬ ((1:Int)=0) by decide,↓reduceIte]
    rw [List.map_map] at hs0
    exact hs0.trans h0.symm

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
