import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_goal
import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_proof_auto

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_proof_manual
open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open sort_point_goal sort_point_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem coord_product (x y : Int) (hx : -20000 ≤ x ∧ x ≤ 20000) (hy : -20000 ≤ y ∧ y ≤ 20000) :
    -400000000 ≤ x*y ∧ x*y ≤ 400000000 := by
  have h1 := Int.mul_nonneg (show 0 ≤ 20000-x by omega) (show 0 ≤ 20000-y by omega)
  have h2 := Int.mul_nonneg (show 0 ≤ 20000+x by omega) (show 0 ≤ 20000+y by omega)
  have h3 := Int.mul_nonneg (show 0 ≤ 20000-x by omega) (show 0 ≤ 20000+y by omega)
  have h4 := Int.mul_nonneg (show 0 ≤ 20000+x by omega) (show 0 ≤ 20000-y by omega)
  have he1 : (20000-x)*(20000-y)+(20000+x)*(20000+y) = 800000000+2*(x*y) := by grind
  have he2 : (20000-x)*(20000+y)+(20000+x)*(20000-y) = 800000000-2*(x*y) := by grind
  omega

private theorem perm_length (l l1 : List point) (hp : PointPermutation l l1) : Zlength l = Zlength l1 :=
  congrArg Int.ofNat hp.length_eq

private theorem bound_head (p : point) (l : List point) (h : PointCoordsBound (p::l)) : CoordInBounds (point_x p) ∧ CoordInBounds (point_y p) := by
  cases h with | cons hp _ => exact hp

private theorem bound_tail (p : point) (l : List point) (h : PointCoordsBound (p::l)) : PointCoordsBound l := by
  cases h with | cons _ ht => exact ht

private theorem coords_from_maps (pts : List point)
    (hxl : Forall (fun x : Int => -10000 ≤ x) (pts.map point_x))
    (hxu : Forall (fun x : Int => x ≤ 10000) (pts.map point_x))
    (hyl : Forall (fun y : Int => -10000 ≤ y) (pts.map point_y))
    (hyu : Forall (fun y : Int => y ≤ 10000) (pts.map point_y)) : PointCoordsBound pts := by
  apply Forall.iff_forall_mem.mpr
  intro p hp
  exact ⟨⟨hxl.mem (List.mem_map.mpr ⟨p,hp,rfl⟩),hxu.mem (List.mem_map.mpr ⟨p,hp,rfl⟩)⟩,
    ⟨hyl.mem (List.mem_map.mpr ⟨p,hp,rfl⟩),hyu.mem (List.mem_map.mpr ⟨p,hp,rfl⟩)⟩⟩

private theorem coords_map_tail (f : point → Int) (pts : List point) {gp : point} {P : Int → Prop}
    (h : Forall P ((gp :: pts).map f)) : Forall P (pts.map f) := by
  cases h with | cons _ ht => exact ht

private theorem coords_tail_from_maps (gp : point) (pts : List point)
    (hxl : Forall (fun x : Int => -10000 ≤ x) ((gp :: pts).map point_x))
    (hxu : Forall (fun x : Int => x ≤ 10000) ((gp :: pts).map point_x))
    (hyl : Forall (fun y : Int => -10000 ≤ y) ((gp :: pts).map point_y))
    (hyu : Forall (fun y : Int => y ≤ 10000) ((gp :: pts).map point_y)) : PointCoordsBound pts :=
  coords_from_maps pts (coords_map_tail _ _ hxl) (coords_map_tail _ _ hxu) (coords_map_tail _ _ hyl) (coords_map_tail _ _ hyu)

private theorem coords_permutation_from_maps (gp : point) (pts out : List point)
    (hp : PointPermutation pts out)
    (hxl : Forall (fun x : Int => -10000 ≤ x) ((gp :: pts).map point_x))
    (hxu : Forall (fun x : Int => x ≤ 10000) ((gp :: pts).map point_x))
    (hyl : Forall (fun y : Int => -10000 ≤ y) ((gp :: pts).map point_y))
    (hyu : Forall (fun y : Int => y ≤ 10000) ((gp :: pts).map point_y)) : PointCoordsBound out :=
  PointCoordsBound_permutation pts out hp (coords_tail_from_maps gp pts hxl hxu hyl hyu)

private theorem coords_bound_cons (gp : point) (pts : List point)
    (hgp : CoordInBounds (point_x gp) ∧ CoordInBounds (point_y gp))
    (hpts : PointCoordsBound pts) : PointCoordsBound (gp :: pts) := Forall.cons hgp hpts

private theorem coords_cons_permutation_from_maps (gp : point) (pts out : List point)
    (hp : PointPermutation pts out)
    (hxl : Forall (fun x : Int => -10000 ≤ x) ((gp :: pts).map point_x))
    (hxu : Forall (fun x : Int => x ≤ 10000) ((gp :: pts).map point_x))
    (hyl : Forall (fun y : Int => -10000 ≤ y) ((gp :: pts).map point_y))
    (hyu : Forall (fun y : Int => y ≤ 10000) ((gp :: pts).map point_y)) : PointCoordsBound (gp :: out) :=
  coords_bound_cons gp out (bound_head gp pts (coords_from_maps (gp::pts) hxl hxu hyl hyu))
    (coords_permutation_from_maps gp pts out hp hxl hxu hyl hyu)

private theorem point_model_cons_maps (gp : point) (flat : List Int) (n : Int) (pts : List point)
    (hlen : Zlength pts = n) (hflat : FlatPoints flat pts)
    (hxl : Forall (fun x : Int => -10000 ≤ x) ((gp :: pts).map point_x))
    (hxu : Forall (fun x : Int => x ≤ 10000) ((gp :: pts).map point_x))
    (hyl : Forall (fun y : Int => -10000 ≤ y) ((gp :: pts).map point_y))
    (hyu : Forall (fun y : Int => y ≤ 10000) ((gp :: pts).map point_y)) : PointMemoryModel gp flat n :=
  ⟨pts,hlen,hflat,coords_from_maps (gp::pts) hxl hxu hyl hyu⟩

private theorem coords_map_xl (pts : List point) (h : PointCoordsBound pts) : Forall (fun x : Int => -10000 ≤ x) (pts.map point_x) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_map.mp hx with ⟨p,hp,rfl⟩
  exact (h.mem hp).1.1

private theorem coords_map_xu (pts : List point) (h : PointCoordsBound pts) : Forall (fun x : Int => x ≤ 10000) (pts.map point_x) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_map.mp hx with ⟨p,hp,rfl⟩
  exact (h.mem hp).1.2

private theorem coords_map_yl (pts : List point) (h : PointCoordsBound pts) : Forall (fun y : Int => -10000 ≤ y) (pts.map point_y) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_map.mp hx with ⟨p,hp,rfl⟩
  exact (h.mem hp).2.1

private theorem coords_map_yu (pts : List point) (h : PointCoordsBound pts) : Forall (fun y : Int => y ≤ 10000) (pts.map point_y) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_map.mp hx with ⟨p,hp,rfl⟩
  exact (h.mem hp).2.2

private theorem cmp_result_bounds (gp a b : point) (ret : Int) (h : PolarCmpResult gp a b ret) : -1 ≤ ret ∧ ret ≤ 1 := by
  unfold PolarCmpResult at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> omega

private theorem coords_cons_from_maps (gp : point) (pts : List point)
    (hgp : CoordInBounds (point_x gp) ∧ CoordInBounds (point_y gp))
    (hxl : Forall (fun x : Int => -10000 ≤ x) (pts.map point_x))
    (hxu : Forall (fun x : Int => x ≤ 10000) (pts.map point_x))
    (hyl : Forall (fun y : Int => -10000 ≤ y) (pts.map point_y))
    (hyu : Forall (fun y : Int => y ≤ 10000) (pts.map point_y)) : PointCoordsBound (gp :: pts) :=
  Forall.cons hgp (coords_from_maps pts hxl hxu hyl hyu)

private theorem point_model_from_maps (gx gy : Int) (flat : List Int) (n : Int) (pts : List point)
    (hlen : Zlength pts = n) (hflat : FlatPoints flat pts)
    (hgp : CoordInBounds gx ∧ CoordInBounds gy)
    (hxl : Forall (fun x : Int => -10000 ≤ x) (pts.map point_x))
    (hxu : Forall (fun x : Int => x ≤ 10000) (pts.map point_x))
    (hyl : Forall (fun y : Int => -10000 ≤ y) (pts.map point_y))
    (hyu : Forall (fun y : Int => y ≤ 10000) (pts.map point_y)) : PointMemoryModel (mk_point gx gy) flat n :=
  ⟨pts,hlen,hflat,coords_cons_from_maps _ pts hgp hxl hxu hyl hyu⟩

private theorem coords_of_flat (pts : List point) (flat : List Int)
    (hf : flat_points_rec flat pts)
    (hl : Forall (fun x : Int => -10000 ≤ x) flat)
    (hu : Forall (fun x : Int => x ≤ 10000) flat) : PointCoordsBound pts := by
  induction pts generalizing flat with
  | nil => exact Forall.nil
  | cons p ps ih =>
    obtain ⟨rest, rfl, hr⟩ := hf
    cases hl with | cons hxl ht =>
      cases ht with | cons hyl hrest =>
        cases hu with | cons hxu ht =>
          cases ht with | cons hyu hrestu =>
            exact Forall.cons ⟨⟨hxl,hxu⟩,⟨hyl,hyu⟩⟩ (ih rest hr hrest hrestu)

private theorem flat_of_coords (pts : List point) (flat : List Int)
    (hf : flat_points_rec flat pts) (hb : PointCoordsBound pts) :
    Forall (fun x : Int => -10000 ≤ x) flat ∧ Forall (fun x : Int => x ≤ 10000) flat := by
  induction pts generalizing flat with
  | nil =>
    change flat = [] at hf
    subst flat
    exact ⟨Forall.nil, Forall.nil⟩
  | cons p ps ih =>
    obtain ⟨rest, rfl, hr⟩ := hf
    cases hb with | cons hp ht =>
      obtain ⟨hl, hu⟩ := ih rest hr ht
      exact ⟨Forall.cons hp.1.1 (Forall.cons hp.2.1 hl),
        Forall.cons hp.1.2 (Forall.cons hp.2.2 hu)⟩

private theorem point_model_of_flat (gx gy n : Int) (flat : List Int)
    (hf : PointFlatModel flat) (hn : Zlength flat = 2*n)
    (hx : CoordInBounds gx) (hy : CoordInBounds gy)
    (hl : Forall (fun x : Int => -10000 ≤ x) flat)
    (hu : Forall (fun x : Int => x ≤ 10000) flat) : PointMemoryModel (mk_point gx gy) flat n := by
  obtain ⟨pts, hp⟩ := hf
  refine ⟨pts, ?_, hp, Forall.cons ⟨hx,hy⟩ (coords_of_flat pts flat hp.2 hl hu)⟩
  have := hp.1
  omega

private theorem coords_of_range_result (gp : point) (flat : List Int)
    (before after : List point) (lo hi : Int)
    (hr : PointRangeSortResult gp flat after lo hi) (hf : FlatPoints flat before)
    (hb : PointCoordsBound (gp :: before)) : PointCoordsBound (gp :: after) :=
  Forall.cons (bound_head gp before hb)
    (PointCoordsBound_permutation before after (hr before hf hb).1 (bound_tail gp before hb))

theorem completed_proof_of_cmp_polar_values_safety_wit_1 : cmp_polar_values_safety_wit_1 := by
  unfold cmp_polar_values_safety_wit_1
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_2 : cmp_polar_values_safety_wit_2 := by
  unfold cmp_polar_values_safety_wit_2
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_3 : cmp_polar_values_safety_wit_3 := by
  unfold cmp_polar_values_safety_wit_3
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_4 : cmp_polar_values_safety_wit_4 := by
  unfold cmp_polar_values_safety_wit_4
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_5 : cmp_polar_values_safety_wit_5 := by
  unfold cmp_polar_values_safety_wit_5
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_6 : cmp_polar_values_safety_wit_6 := by
  unfold cmp_polar_values_safety_wit_6
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_7 : cmp_polar_values_safety_wit_7 := by
  unfold cmp_polar_values_safety_wit_7
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_8 : cmp_polar_values_safety_wit_8 := by
  unfold cmp_polar_values_safety_wit_8
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_9 : cmp_polar_values_safety_wit_9 := by
  unfold cmp_polar_values_safety_wit_9
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_10 : cmp_polar_values_safety_wit_10 := by
  unfold cmp_polar_values_safety_wit_10
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_11 : cmp_polar_values_safety_wit_11 := by
  unfold cmp_polar_values_safety_wit_11
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_12 : cmp_polar_values_safety_wit_12 := by
  unfold cmp_polar_values_safety_wit_12
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem completed_proof_of_cmp_polar_values_safety_wit_13 : cmp_polar_values_safety_wit_13 := by
  unfold cmp_polar_values_safety_wit_13
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH2 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH3 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH4 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have h1 := coord_product (a_x_pre-gx_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h2 := coord_product (a_y_pre-gy_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h3 := coord_product (a_x_pre-gx_pre) (a_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h4 := coord_product (a_y_pre-gy_pre) (a_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h5 := coord_product (b_x_pre-gx_pre) (b_x_pre-gx_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  have h6 := coord_product (b_y_pre-gy_pre) (b_y_pre-gy_pre) (by unfold CoordInBounds at *; omega) (by unfold CoordInBounds at *; omega)
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals unfold CoordInBounds at *; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_cmp_polar_values_return_wit_1 : cmp_polar_values_return_wit_1 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22
  have PreH1 : (a_y_pre <= b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH10
  have PreH11 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_2 : cmp_polar_values_return_wit_2 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26
  have PreH1 : (a_y_pre <= b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH9
  have PreH10 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH10
  have PreH11 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH11
  have PreH12 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH12
  have PreH13 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH13
  have PreH14 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH14
  have PreH15 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH19 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH20 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_3 : cmp_polar_values_return_wit_3 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26
  have PreH1 : (a_y_pre <= b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH9
  have PreH10 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH10
  have PreH11 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH11
  have PreH12 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH12
  have PreH13 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH13
  have PreH14 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH14
  have PreH15 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH19 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH20 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_4 : cmp_polar_values_return_wit_4 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have PreH1 : (a_y_pre <= b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH9
  have PreH10 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH11
  have PreH12 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH12
  have PreH13 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  have hy : a_y_pre = b_y_pre := by omega
  subst b_y_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_5 : cmp_polar_values_return_wit_5 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22
  have PreH1 : (a_y_pre > b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH10
  have PreH11 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_6 : cmp_polar_values_return_wit_6 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have PreH1 : (a_y_pre > b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH9
  have PreH10 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH10
  have PreH11 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH11
  have PreH12 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH12
  have PreH13 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_7_split_goal_1 : cmp_polar_values_return_wit_7_split_goal_1 := by
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have PreH1 : (a_y_pre > b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH9
  have PreH10 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH11
  have PreH12 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH12
  have PreH13 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  (ring_nf at *; grind (splits := 40))

theorem proof_of_cmp_polar_values_return_wit_7 : cmp_polar_values_return_wit_7 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have PreH1 : (a_y_pre > b_y_pre) := current_PreH1
  have PreH2 : (a_y_pre >= b_y_pre) := current_PreH2
  have PreH3 : (a_x_pre <= b_x_pre) := current_PreH3
  have PreH4 : (a_x_pre >= b_x_pre) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH7
  have PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH9
  have PreH10 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH11
  have PreH12 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH12
  have PreH13 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_8 : cmp_polar_values_return_wit_8 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21
  have PreH1 : (a_y_pre < b_y_pre) := current_PreH1
  have PreH2 : (a_x_pre <= b_x_pre) := current_PreH2
  have PreH3 : (a_x_pre >= b_x_pre) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH9
  have PreH10 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_9 : cmp_polar_values_return_wit_9 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23
  have PreH1 : (a_y_pre < b_y_pre) := current_PreH1
  have PreH2 : (a_x_pre <= b_x_pre) := current_PreH2
  have PreH3 : (a_x_pre >= b_x_pre) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH8
  have PreH9 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH11
  have PreH12 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_10 : cmp_polar_values_return_wit_10 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23
  have PreH1 : (a_y_pre < b_y_pre) := current_PreH1
  have PreH2 : (a_x_pre <= b_x_pre) := current_PreH2
  have PreH3 : (a_x_pre >= b_x_pre) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH6
  have PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH11
  have PreH12 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have hx : a_x_pre = b_x_pre := by omega
  subst b_x_pre
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_11 : cmp_polar_values_return_wit_11 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20
  have PreH1 : (a_x_pre > b_x_pre) := current_PreH1
  have PreH2 : (a_x_pre >= b_x_pre) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH8
  have PreH9 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_12 : cmp_polar_values_return_wit_12 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22
  have PreH1 : (a_x_pre > b_x_pre) := current_PreH1
  have PreH2 : (a_x_pre >= b_x_pre) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH7
  have PreH8 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH10
  have PreH11 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_13 : cmp_polar_values_return_wit_13 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22
  have PreH1 : (a_x_pre > b_x_pre) := current_PreH1
  have PreH2 : (a_x_pre >= b_x_pre) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH6
  have PreH7 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH10
  have PreH11 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_14 : cmp_polar_values_return_wit_14 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have PreH1 : (a_x_pre > b_x_pre) := current_PreH1
  have PreH2 : (a_x_pre >= b_x_pre) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH6
  have PreH7 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH11
  have PreH12 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH12
  have PreH13 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_15 : cmp_polar_values_return_wit_15 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have PreH1 : (a_x_pre > b_x_pre) := current_PreH1
  have PreH2 : (a_x_pre >= b_x_pre) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH6
  have PreH7 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH8
  have PreH9 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH11
  have PreH12 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH12
  have PreH13 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH18 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_16 : cmp_polar_values_return_wit_16 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22
  have PreH1 : (a_x_pre > b_x_pre) := current_PreH1
  have PreH2 : (a_x_pre >= b_x_pre) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH5
  have PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH10
  have PreH11 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_17 : cmp_polar_values_return_wit_17 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19
  have PreH1 : (a_x_pre < b_x_pre) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH6
  have PreH7 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH7
  have PreH8 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_18 : cmp_polar_values_return_wit_18 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21
  have PreH1 : (a_x_pre < b_x_pre) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH6
  have PreH7 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_19 : cmp_polar_values_return_wit_19 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21
  have PreH1 : (a_x_pre < b_x_pre) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH5
  have PreH6 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH9
  have PreH10 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_20 : cmp_polar_values_return_wit_20 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23
  have PreH1 : (a_x_pre < b_x_pre) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH5
  have PreH6 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH8
  have PreH9 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH11
  have PreH12 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_21 : cmp_polar_values_return_wit_21 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23
  have PreH1 : (a_x_pre < b_x_pre) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH5
  have PreH6 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH7
  have PreH8 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH8
  have PreH9 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH10
  have PreH11 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH11
  have PreH12 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH17 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_22 : cmp_polar_values_return_wit_22 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21
  have PreH1 : (a_x_pre < b_x_pre) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH4
  have PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_23 : cmp_polar_values_return_wit_23 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH6
  have PreH7 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_24 : cmp_polar_values_return_wit_24 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH5
  have PreH6 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH6
  have PreH7 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH8
  have PreH9 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_25 : cmp_polar_values_return_wit_25 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH4
  have PreH5 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH8
  have PreH9 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_26 : cmp_polar_values_return_wit_26 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH4
  have PreH5 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH7
  have PreH8 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH10
  have PreH11 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_27 : cmp_polar_values_return_wit_27 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH4
  have PreH5 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH6
  have PreH7 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH7
  have PreH8 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH9
  have PreH10 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH10
  have PreH11 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH16 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_28 : cmp_polar_values_return_wit_28 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH3
  have PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH8
  have PreH9 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_29 : cmp_polar_values_return_wit_29 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH3
  have PreH4 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH5
  have PreH6 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_30 : cmp_polar_values_return_wit_30 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH3
  have PreH4 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH4
  have PreH5 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH6
  have PreH7 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH7
  have PreH8 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_31 : cmp_polar_values_return_wit_31 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH3
  have PreH4 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH7
  have PreH8 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_32 : cmp_polar_values_return_wit_32 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH3
  have PreH4 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_33 : cmp_polar_values_return_wit_33 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH3
  have PreH4 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH5
  have PreH6 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH7
  have PreH8 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH8
  have PreH9 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH9
  have PreH10 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH14 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH15 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_34 : cmp_polar_values_return_wit_34 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19
  have PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int)) := current_PreH2
  have PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH3
  have PreH4 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH6
  have PreH7 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH7
  have PreH8 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_35 : cmp_polar_values_return_wit_35 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int)) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH3
  have PreH4 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH4
  have PreH5 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_36 : cmp_polar_values_return_wit_36 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int)) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH2
  have PreH3 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH3
  have PreH4 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH6
  have PreH7 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_37 : cmp_polar_values_return_wit_37 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int)) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH2
  have PreH3 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH3
  have PreH4 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH4
  have PreH5 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH6
  have PreH7 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH7
  have PreH8 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH13 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_38 : cmp_polar_values_return_wit_38 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int)) := current_PreH1
  have PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH3
  have PreH4 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_39 : cmp_polar_values_return_wit_39 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH2
  have PreH3 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH3
  have PreH4 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_40 : cmp_polar_values_return_wit_40 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH2
  have PreH3 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH3
  have PreH4 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH5
  have PreH6 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_41 : cmp_polar_values_return_wit_41 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH3
  have PreH4 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_42 : cmp_polar_values_return_wit_42 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17
  have PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH3
  have PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH5
  have PreH6 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_43 : cmp_polar_values_return_wit_43 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16
  have PreH1 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH1
  have PreH2 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH2
  have PreH3 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH3
  have PreH4 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH4
  have PreH5 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_44 : cmp_polar_values_return_wit_44 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15
  have PreH1 : ((b_y_pre - gy_pre) > (0 : Int)) := current_PreH1
  have PreH2 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH2
  have PreH3 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH3
  have PreH4 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_45 : cmp_polar_values_return_wit_45 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18
  have PreH1 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH3
  have PreH4 : ((a_x_pre - gx_pre) < (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_46 : cmp_polar_values_return_wit_46 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17
  have PreH1 : ((b_x_pre - gx_pre) >= (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH3
  have PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH5
  have PreH6 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_47 : cmp_polar_values_return_wit_47 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16
  have PreH1 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH3
  have PreH4 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH4
  have PreH5 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_48 : cmp_polar_values_return_wit_48 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18
  have PreH1 : ((b_x_pre - gx_pre) < (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) = (0 : Int)) := current_PreH2
  have PreH3 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH3
  have PreH4 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH5
  have PreH6 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH6
  have PreH7 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH12 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_49 : cmp_polar_values_return_wit_49 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15
  have PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH2
  have PreH3 : ((a_y_pre - gy_pre) > (0 : Int)) := current_PreH3
  have PreH4 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH5 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH6 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_cmp_polar_values_return_wit_50 : cmp_polar_values_return_wit_50 := by
  right
  intro gx_pre gy_pre a_x_pre a_y_pre b_x_pre b_y_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17
  have PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int)) := current_PreH1
  have PreH2 : ((b_y_pre - gy_pre) <= (0 : Int)) := current_PreH2
  have PreH3 : ((a_x_pre - gx_pre) >= (0 : Int)) := current_PreH3
  have PreH4 : ((a_y_pre - gy_pre) = (0 : Int)) := current_PreH4
  have PreH5 : ((a_y_pre - gy_pre) <= (0 : Int)) := current_PreH5
  have PreH6 : (CoordInBounds gx_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH7 : (CoordInBounds gy_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH8 : (CoordInBounds a_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH9 : (CoordInBounds a_y_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH10 : (CoordInBounds b_x_pre) := by unfold CoordInBounds; constructor <;> omega
  have PreH11 : (CoordInBounds b_y_pre) := by unfold CoordInBounds; constructor <;> omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | omega | (simp only [PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y, mk_point]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; (ring_nf at *; grind (splits := 40)))

theorem proof_of_swap_points_return_wit_1 : swap_points_return_wit_1 := by
  right
  intro pts_l flat n_pre i_pre j_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12
  have PreH1 : ((0 : Int) <= i_pre) := current_PreH1
  have PreH2 : (i_pre < n_pre) := current_PreH2
  have PreH3 : ((0 : Int) <= j_pre) := current_PreH3
  have PreH4 : (j_pre < n_pre) := current_PreH4
  have PreH5 : ((0 : Int) <= n_pre) := current_PreH5
  have PreH6 : (n_pre <= 50000) := current_PreH6
  have PreH7 : ((Zlength (pts_l)) = n_pre) := current_PreH7
  have PreH8 : (FlatPoints flat pts_l) := current_PreH8
  have PreH9 : (PointCoordsBound pts_l) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have hi : 0 ≤ i_pre ∧ i_pre < Zlength pts_l := by omega
  have hj : 0 ≤ j_pre ∧ j_pre < Zlength pts_l := by omega
  have hp := PointPermutation_swap_points_any pts_l i_pre j_pre hi hj
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact PointCoordsBound_permutation _ _ hp PreH9
      | exact hp
      | exact FlatPoints_swap_points flat pts_l i_pre j_pre PreH8 hi hj
      | exact point_swap_flat_preprocess_form flat n_pre i_pre j_pre (by have := PreH8.1; omega) (by omega) (by omega)

theorem proof_of_partition_points_entail_wit_1 : partition_points_entail_wit_1 := by
  right
  intro pts_l flat n_pre low_pre high_pre gx_pre gy_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11
  have tail_current_PreH8 := (coords_map_tail _ _ current_PreH8)
  have tail_current_PreH9 := (coords_map_tail _ _ current_PreH9)
  have tail_current_PreH10 := (coords_map_tail _ _ current_PreH10)
  have tail_current_PreH11 := (coords_map_tail _ _ current_PreH11)
  have PreH1 : ((0 : Int) <= low_pre) := current_PreH1
  have PreH2 : (low_pre <= high_pre) := current_PreH2
  have PreH3 : (high_pre < n_pre) := current_PreH3
  have PreH4 : ((0 : Int) <= n_pre) := current_PreH4
  have PreH5 : (n_pre <= 50000) := current_PreH5
  have PreH6 : ((Zlength (pts_l)) = n_pre) := current_PreH6
  have PreH7 : (FlatPoints flat pts_l) := current_PreH7
  have PreH8 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_l)) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have hp := flat_points_lookup_point flat pts_l high_pre (by omega) PreH7
  Exists pts_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega
    · refine ⟨List.Perm.refl _, PointSameOutsideRange_refl _ _ _, hp.symm, ?_, ?_⟩
      · intro k hk; omega
      · intro k hk; omega
    all_goals first
      | exact coords_map_xl _ (bound_tail _ _ PreH8)
      | exact coords_map_xu _ (bound_tail _ _ PreH8)
      | exact coords_map_yl _ (bound_tail _ _ PreH8)
      | exact coords_map_yu _ (bound_tail _ _ PreH8)
      | exact coords_map_xl _ (bound_tail _ _ (bound_tail _ _ PreH8))
      | exact coords_map_xu _ (bound_tail _ _ (bound_tail _ _ PreH8))
      | exact coords_map_yl _ (bound_tail _ _ (bound_tail _ _ PreH8))
      | exact coords_map_yu _ (bound_tail _ _ (bound_tail _ _ PreH8))
      | exact bound_tail _ _ PreH8

theorem proof_of_partition_points_entail_wit_2_1 : partition_points_entail_wit_2_1 := by
  right
  intro pts_l n_pre low_pre high_pre gx_pre gy_pre pivot_x pivot_y j i retval flat_cur_2 pts_cur_2 current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26
  have tail_current_PreH22 := (coords_map_tail _ _ current_PreH22)
  have tail_current_PreH23 := (coords_map_tail _ _ current_PreH23)
  have tail_current_PreH24 := (coords_map_tail _ _ current_PreH24)
  have tail_current_PreH25 := (coords_map_tail _ _ current_PreH25)
  have PreH1 : (FlatPoints (point_swap_flat (flat_cur_2) ((i + 1)) (j)) (point_swap_points (pts_cur_2) ((i + 1)) (j))) := current_PreH1
  have PreH2 : (PointPermutation pts_cur_2 (point_swap_points (pts_cur_2) ((i + 1)) (j))) := current_PreH2
  have PreH3 : (PointCoordsBound (point_swap_points (pts_cur_2) ((i + 1)) (j))) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH4 : (retval <= (0 : Int)) := current_PreH3
  have PreH5 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur_2 (0 : Int))) ((Znth ((2 * j) + 1) flat_cur_2 (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval) := current_PreH4
  have PreH6 : ((-1) <= retval) := by first | omega | (have hr := cmp_result_bounds _ _ _ retval (by assumption); omega)
  have PreH7 : (retval <= 1) := by first | omega | (have hr := cmp_result_bounds _ _ _ retval (by assumption); omega)
  have PreH8 : (j < high_pre) := current_PreH5
  have PreH9 : ((0 : Int) <= low_pre) := current_PreH6
  have PreH10 : (low_pre <= high_pre) := current_PreH7
  have PreH11 : (high_pre < n_pre) := current_PreH8
  have PreH12 : ((0 : Int) <= n_pre) := current_PreH9
  have PreH13 : (n_pre <= 50000) := current_PreH10
  have PreH14 : ((low_pre - 1) <= i) := current_PreH11
  have PreH15 : (i < j) := current_PreH12
  have PreH16 : (j <= high_pre) := current_PreH13
  have PreH17 : ((Zlength (pts_l)) = n_pre) := current_PreH14
  have PreH18 : ((Zlength (pts_cur_2)) = n_pre) := current_PreH15
  have PreH19 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point))) := current_PreH16
  have PreH20 : (FlatPoints flat_cur_2 pts_cur_2) := current_PreH17
  have PreH21 : (PointCoordsBound pts_cur_2) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH22 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_cur_2)) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH23 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) := current_PreH26
  have hj : 0 ≤ j ∧ j < Zlength pts_cur_2 := by omega
  have hi : 0 ≤ i+1 ∧ i+1 < Zlength pts_cur_2 := by omega
  have hh : 0 ≤ high_pre ∧ high_pre < Zlength pts_cur_2 := by omega
  have hpt := FlatPoints_Znth_point flat_cur_2 pts_cur_2 j PreH20 hj
  have hle := PolarCmpResult_nonpos_le _ _ _ _ PreH5 PreH4
  rw [← hpt] at hle
  have hpiv := Znth_point_swap_points_other pts_cur_2 (i+1) j high_pre default_point hi hj hh (by omega) (by omega)
  have hscan : PointPartitionScanInv (mk_point gx_pre gy_pre) pts_l (point_swap_points pts_cur_2 (i+1) j) low_pre high_pre (mk_point pivot_x pivot_y) (i+1) (j+1) := by
    refine ⟨PreH23.1.trans PreH2, ?_, hpiv.trans PreH23.2.2.1, ?_, ?_⟩
    · exact PointSameOutsideRange_trans _ _ _ _ _ PreH23.2.1 (PointSameOutsideRange_swap_inside _ _ _ _ _ PreH9 (by omega) (by omega) (by omega))
    · intro k hk
      by_cases he : k = i+1
      · subst k; rw [Znth_point_swap_points_left _ _ _ _ hi hj]; exact hle
      · rw [Znth_point_swap_points_other _ _ _ _ _ hi hj (by omega) he (by omega)]
        exact PreH23.2.2.2.1 k (by omega)
    · intro k hk
      by_cases he : k = j
      · subst k; rw [Znth_point_swap_points_right _ _ _ _ hi hj]
        exact PreH23.2.2.2.2 (i+1) (by omega)
      · rw [Znth_point_swap_points_other _ _ _ _ _ hi hj (by omega) (by omega) he]
        exact PreH23.2.2.2.2 k (by omega)
  Exists (point_swap_points pts_cur_2 (i+1) j)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega
    all_goals first
      | (rw [Zlength_point_swap_points]; omega)
      | exact PreH19.trans hpiv.symm
              | exact coords_map_xl _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3)
        | exact coords_map_xu _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3)
        | exact coords_map_yl _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3)
        | exact coords_map_yu _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3)
        | exact coords_map_xl _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3))
        | exact coords_map_xu _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3))
        | exact coords_map_yl _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3))
        | exact coords_map_yu _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3))
        | exact coords_bound_cons _ _ (bound_head _ _ PreH22) PreH3

theorem proof_of_partition_points_entail_wit_2_2 : partition_points_entail_wit_2_2 := by
  right
  intro pts_l n_pre low_pre high_pre gx_pre gy_pre pivot_x pivot_y j i retval flat_cur_2 pts_cur_2 current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have tail_current_PreH20 := (coords_map_tail _ _ current_PreH20)
  have tail_current_PreH21 := (coords_map_tail _ _ current_PreH21)
  have tail_current_PreH22 := (coords_map_tail _ _ current_PreH22)
  have tail_current_PreH23 := (coords_map_tail _ _ current_PreH23)
  have PreH1 : (retval > (0 : Int)) := current_PreH1
  have PreH2 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur_2 (0 : Int))) ((Znth ((2 * j) + 1) flat_cur_2 (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval) := current_PreH2
  have PreH3 : ((-1) <= retval) := by first | omega | (have hr := cmp_result_bounds _ _ _ retval (by assumption); omega)
  have PreH4 : (retval <= 1) := by first | omega | (have hr := cmp_result_bounds _ _ _ retval (by assumption); omega)
  have PreH5 : (j < high_pre) := current_PreH3
  have PreH6 : ((0 : Int) <= low_pre) := current_PreH4
  have PreH7 : (low_pre <= high_pre) := current_PreH5
  have PreH8 : (high_pre < n_pre) := current_PreH6
  have PreH9 : ((0 : Int) <= n_pre) := current_PreH7
  have PreH10 : (n_pre <= 50000) := current_PreH8
  have PreH11 : ((low_pre - 1) <= i) := current_PreH9
  have PreH12 : (i < j) := current_PreH10
  have PreH13 : (j <= high_pre) := current_PreH11
  have PreH14 : ((Zlength (pts_l)) = n_pre) := current_PreH12
  have PreH15 : ((Zlength (pts_cur_2)) = n_pre) := current_PreH13
  have PreH16 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point))) := current_PreH14
  have PreH17 : (FlatPoints flat_cur_2 pts_cur_2) := current_PreH15
  have PreH18 : (PointCoordsBound pts_cur_2) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH19 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_cur_2)) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH20 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) := current_PreH24
  have he : retval = 1 := by omega
  rw [he] at PreH2
  have hp := FlatPoints_Znth_point flat_cur_2 pts_cur_2 j PreH17 (by omega)
  have hlt := PolarCmpResult_one_implies_PolarLt_flip _ _ _ PreH2
  rw [← hp] at hlt
  have hscan : PointPartitionScanInv (mk_point gx_pre gy_pre) pts_l pts_cur_2 low_pre high_pre (mk_point pivot_x pivot_y) i (j+1) := by
    refine ⟨PreH20.1, PreH20.2.1, PreH20.2.2.1, PreH20.2.2.2.1, ?_⟩
    intro k hk
    by_cases he : k = j
    · subst k; exact hlt
    · exact PreH20.2.2.2.2 k (by omega)
  Exists pts_cur_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega

theorem proof_of_partition_points_return_wit_1 : partition_points_return_wit_1 := by
  right
  intro pts_l n_pre low_pre high_pre gx_pre gy_pre pivot_x pivot_y j i flat_cur pts_cur current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24
  have tail_current_PreH20 := (coords_map_tail _ _ current_PreH20)
  have tail_current_PreH21 := (coords_map_tail _ _ current_PreH21)
  have tail_current_PreH22 := (coords_map_tail _ _ current_PreH22)
  have tail_current_PreH23 := (coords_map_tail _ _ current_PreH23)
  have PreH1 : (FlatPoints (point_swap_flat (flat_cur) ((i + 1)) (high_pre)) (point_swap_points (pts_cur) ((i + 1)) (high_pre))) := current_PreH1
  have PreH2 : (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1)) (high_pre))) := current_PreH2
  have PreH3 : (PointCoordsBound (point_swap_points (pts_cur) ((i + 1)) (high_pre))) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH4 : (j >= high_pre) := current_PreH3
  have PreH5 : ((0 : Int) <= low_pre) := current_PreH4
  have PreH6 : (low_pre <= high_pre) := current_PreH5
  have PreH7 : (high_pre < n_pre) := current_PreH6
  have PreH8 : ((0 : Int) <= n_pre) := current_PreH7
  have PreH9 : (n_pre <= 50000) := current_PreH8
  have PreH10 : ((low_pre - 1) <= i) := current_PreH9
  have PreH11 : (i < j) := current_PreH10
  have PreH12 : (j <= high_pre) := current_PreH11
  have PreH13 : ((Zlength (pts_l)) = n_pre) := current_PreH12
  have PreH14 : ((Zlength (pts_cur)) = n_pre) := current_PreH13
  have PreH15 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) := current_PreH14
  have PreH16 : (FlatPoints flat_cur pts_cur) := current_PreH15
  have PreH17 : (PointCoordsBound pts_cur) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH18 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_cur)) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH19 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) := current_PreH24
  have he : j = high_pre := by omega
  subst j
  have hp := PointPartitionedAt_after_final_swap _ pts_l pts_cur low_pre high_pre (mk_point pivot_x pivot_y) i PreH5 (by omega) PreH10 (by omega) PreH19
  have hs := PointSameOutsideRange_trans _ _ _ _ _ PreH19.2.1
    (PointSameOutsideRange_swap_inside pts_cur low_pre high_pre (i+1) high_pre PreH5 (by omega) (by omega) (by omega))
  have hperm := PreH19.1.trans PreH2
  Exists (point_swap_points pts_cur (i+1) high_pre)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega
    all_goals first
      | exact coords_map_xl _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3)
      | exact coords_map_xu _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3)
      | exact coords_map_yl _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3)
      | exact coords_map_yu _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3)
      | exact coords_map_xl _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3))
      | exact coords_map_xu _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3))
      | exact coords_map_yl _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3))
      | exact coords_map_yu _ (bound_tail _ _ (coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3))
      | exact coords_bound_cons _ _ (bound_head _ _ PreH18) PreH3

theorem proof_of_partition_points_partial_solve_wit_5_pure : partition_points_partial_solve_wit_5_pure := by
  right
  intro pts_l coords_pre n_pre low_pre high_pre gx_pre gy_pre flat_cur pivot_x pivot_y pts_cur j i current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26 current_PreH27 current_PreH28 current_PreH29 current_PreH30 current_PreH31 current_PreH32 current_PreH33 current_PreH34 current_PreH35 current_PreH36 current_PreH37 current_PreH38 current_PreH39 current_PreH40 current_PreH41 current_PreH42 current_PreH43 current_PreH44
  have tail_current_PreH40 := (coords_map_tail _ _ current_PreH40)
  have tail_current_PreH41 := (coords_map_tail _ _ current_PreH41)
  have tail_current_PreH42 := (coords_map_tail _ _ current_PreH42)
  have tail_current_PreH43 := (coords_map_tail _ _ current_PreH43)
  have PreH1 : (pivot_x <= INT_MAX) := current_PreH1
  have PreH2 : (pivot_y <= INT_MAX) := current_PreH2
  have PreH3 : (j <= INT_MAX) := current_PreH3
  have PreH4 : (i <= INT_MAX) := current_PreH4
  have PreH5 : (gy_pre <= INT_MAX) := current_PreH5
  have PreH6 : (gx_pre <= INT_MAX) := current_PreH6
  have PreH7 : (high_pre <= INT_MAX) := current_PreH7
  have PreH8 : (low_pre <= INT_MAX) := current_PreH8
  have PreH9 : (n_pre <= INT_MAX) := current_PreH9
  have PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX) := current_PreH10
  have PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX) := current_PreH11
  have PreH12 : (pivot_x >= INT_MIN) := current_PreH12
  have PreH13 : (pivot_y >= INT_MIN) := current_PreH13
  have PreH14 : (j >= INT_MIN) := current_PreH14
  have PreH15 : (i >= INT_MIN) := current_PreH15
  have PreH16 : (gy_pre >= INT_MIN) := current_PreH16
  have PreH17 : (gx_pre >= INT_MIN) := current_PreH17
  have PreH18 : (high_pre >= INT_MIN) := current_PreH18
  have PreH19 : (low_pre >= INT_MIN) := current_PreH19
  have PreH20 : (n_pre >= INT_MIN) := current_PreH20
  have PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN) := current_PreH21
  have PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN) := current_PreH22
  have PreH23 : (j < high_pre) := current_PreH23
  have PreH24 : ((0 : Int) <= low_pre) := current_PreH24
  have PreH25 : (low_pre <= high_pre) := current_PreH25
  have PreH26 : (high_pre < n_pre) := current_PreH26
  have PreH27 : ((0 : Int) <= n_pre) := current_PreH27
  have PreH28 : (n_pre <= 50000) := current_PreH28
  have PreH29 : ((low_pre - 1) <= i) := current_PreH29
  have PreH30 : (i < j) := current_PreH30
  have PreH31 : (j <= high_pre) := current_PreH31
  have PreH32 : ((Zlength (pts_l)) = n_pre) := current_PreH32
  have PreH33 : ((Zlength (pts_cur)) = n_pre) := current_PreH33
  have PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) := current_PreH34
  have PreH35 : (FlatPoints flat_cur pts_cur) := current_PreH35
  have PreH36 : (PointCoordsBound pts_cur) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH37 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_cur)) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH38 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) := current_PreH44
  have hg := bound_head _ _ PreH37
  have hj := point_coords_bound_lookup pts_cur j (by omega) PreH36
  have hp := point_coords_bound_lookup pts_cur high_pre (by omega) PreH36
  have hpt := flat_points_lookup_point flat_cur pts_cur j (by omega) PreH35
  rw [← PreH34] at hp
  rw [← hpt] at hj
  change CoordInBounds gx_pre ∧ CoordInBounds gy_pre at hg
  change CoordInBounds pivot_x ∧ CoordInBounds pivot_y at hp
  change CoordInBounds (Znth (2*j) flat_cur 0) ∧ CoordInBounds (Znth (2*j+1) flat_cur 0) at hj
  split_pures <;> dump_pre_spatial
  all_goals try (simp only [CoordInBounds] at *; omega)
  all_goals first | exact hg.1 | exact hg.2 | exact hj.1 | exact hj.2 | exact hp.1 | exact hp.2

theorem proof_of_quicksort_points_range_entail_wit_1 : quicksort_points_range_entail_wit_1 := by
  right
  intro flat n_pre left_pre right_pre gx_pre gy_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14
  have PreH1 : (left_pre < right_pre) := current_PreH1
  have PreH2 : ((0 : Int) <= n_pre) := current_PreH2
  have PreH3 : (n_pre <= 50000) := current_PreH3
  have PreH4 : ((0 : Int) <= left_pre) := current_PreH4
  have PreH5 : ((-1) <= right_pre) := current_PreH5
  have PreH6 : (right_pre < n_pre) := current_PreH6
  have PreH7 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by
    apply point_model_of_flat <;> first | assumption | (unfold CoordInBounds; constructor <;> omega)
  obtain ⟨pts, hn, hf, hb⟩ := PreH7
  Exists pts
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact coords_map_xl _ hb | exact coords_map_xu _ hb | exact coords_map_yl _ hb | exact coords_map_yu _ hb

theorem proof_of_quicksort_points_range_return_wit_4 : quicksort_points_range_return_wit_4 := by
  right
  intro flat n_pre left_pre right_pre gx_pre gy_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14
  have PreH1 : (left_pre >= right_pre) := current_PreH1
  have PreH2 : ((0 : Int) <= n_pre) := current_PreH2
  have PreH3 : (n_pre <= 50000) := current_PreH3
  have PreH4 : ((0 : Int) <= left_pre) := current_PreH4
  have PreH5 : ((-1) <= right_pre) := current_PreH5
  have PreH6 : (right_pre < n_pre) := current_PreH6
  have PreH7 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by
    apply point_model_of_flat <;> first | assumption | (unfold CoordInBounds; constructor <;> omega)
  obtain ⟨pts, hn, hf, hb⟩ := PreH7
  Exists pts
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | exact coords_map_xl _ hb | exact coords_map_xu _ hb | exact coords_map_yl _ hb | exact coords_map_yu _ hb
    intro pts_in hf' hb'
    have he := FlatPoints_functional flat pts_in pts hf' hf
    subst pts_in
    exact ⟨List.Perm.refl _, PointSameOutsideRange_refl _ _ _, PointSortedRange_degenerate _ _ _ _ PreH1⟩

theorem proof_of_quicksort_points_range_return_wit_3 : quicksort_points_range_return_wit_3 := by
  right
  intro flat n_pre left_pre right_pre gx_pre gy_pre pts_l flat_out_2 pts_out_2 retval flat_out_3 pts_out_3 current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26 current_PreH27 current_PreH28 current_PreH29
  have tail_current_PreH26 := (coords_map_tail _ _ current_PreH26)
  have tail_current_PreH27 := (coords_map_tail _ _ current_PreH27)
  have tail_current_PreH28 := (coords_map_tail _ _ current_PreH28)
  have tail_current_PreH29 := (coords_map_tail _ _ current_PreH29)
  have PreH1 : (retval >= right_pre) := current_PreH1
  have PreH2 : (FlatPoints flat_out_3 pts_out_3) := current_PreH2
  have PreH4 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1)) := current_PreH3
  have PreH5 : (retval > left_pre) := current_PreH4
  have PreH6 : (left_pre <= retval) := current_PreH5
  have PreH7 : (retval <= right_pre) := current_PreH6
  have PreH8 : (FlatPoints flat_out_2 pts_out_2) := current_PreH7
  have PreH10 : (PointPermutation pts_l pts_out_2) := current_PreH8
  have PreH11 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre) := current_PreH9
  have PreH12 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval) := current_PreH10
  have PreH13 : ((0 : Int) <= n_pre) := current_PreH11
  have PreH14 : (n_pre <= 50000) := current_PreH12
  have PreH15 : ((0 : Int) <= left_pre) := current_PreH13
  have PreH16 : (left_pre < right_pre) := current_PreH14
  have PreH17 : (right_pre < n_pre) := current_PreH15
  have PreH18 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by apply point_model_cons_maps (mk_point gx_pre gy_pre) flat n_pre pts_l <;> assumption
  have PreH19 : ((Zlength (pts_l)) = n_pre) := current_PreH24
  have PreH20 : (FlatPoints flat pts_l) := current_PreH25
  have PreH21 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_l)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH9 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_2)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH3 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_3)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  obtain ⟨hp, hs, hsort⟩ := PreH4 pts_out_2 PreH8 PreH9
  have hn2 : Zlength pts_out_2 = n_pre := by have := perm_length _ _ PreH10; omega
  have hn3 : Zlength pts_out_3 = n_pre := by have := perm_length _ _ hp; omega
  have hpart := PointPartitionedAt_preserved_by_left _ _ _ _ _ _ hp PreH15 hs (by omega) PreH12
  have hsorted := PointSortedRange_from_left_boundary _ _ _ _ _ PreH15 PreH1 (by omega) hpart hsort
  Exists pts_out_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try assumption
    intro pts_in hf hb
    have he := FlatPoints_functional flat pts_in pts_l hf PreH20
    subst pts_in
    refine ⟨PreH10.trans hp, ?_, hsorted⟩
    exact PointSameOutsideRange_trans _ _ _ _ _ PreH11
      (PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs)

theorem proof_of_quicksort_points_range_return_wit_1 : quicksort_points_range_return_wit_1 := by
  right
  intro flat n_pre left_pre right_pre gx_pre gy_pre pts_l flat_out_2 pts_out_2 retval flat_out_3 pts_out_3 flat_out_4 pts_out_4 current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26 current_PreH27 current_PreH28 current_PreH29 current_PreH30 current_PreH31
  have tail_current_PreH28 := (coords_map_tail _ _ current_PreH28)
  have tail_current_PreH29 := (coords_map_tail _ _ current_PreH29)
  have tail_current_PreH30 := (coords_map_tail _ _ current_PreH30)
  have tail_current_PreH31 := (coords_map_tail _ _ current_PreH31)
  have PreH1 : (FlatPoints flat_out_4 pts_out_4) := current_PreH1
  have PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_3 pts_out_4 (retval + 1) right_pre) := current_PreH2
  have PreH4 : (retval < right_pre) := current_PreH3
  have PreH5 : (FlatPoints flat_out_3 pts_out_3) := current_PreH4
  have PreH7 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1)) := current_PreH5
  have PreH8 : (retval > left_pre) := current_PreH6
  have PreH9 : (left_pre <= retval) := current_PreH7
  have PreH10 : (retval <= right_pre) := current_PreH8
  have PreH11 : (FlatPoints flat_out_2 pts_out_2) := current_PreH9
  have PreH13 : (PointPermutation pts_l pts_out_2) := current_PreH10
  have PreH14 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre) := current_PreH11
  have PreH15 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval) := current_PreH12
  have PreH16 : ((0 : Int) <= n_pre) := current_PreH13
  have PreH17 : (n_pre <= 50000) := current_PreH14
  have PreH18 : ((0 : Int) <= left_pre) := current_PreH15
  have PreH19 : (left_pre < right_pre) := current_PreH16
  have PreH20 : (right_pre < n_pre) := current_PreH17
  have PreH21 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by apply point_model_cons_maps (mk_point gx_pre gy_pre) flat n_pre pts_l <;> assumption
  have PreH22 : ((Zlength (pts_l)) = n_pre) := current_PreH26
  have PreH23 : (FlatPoints flat pts_l) := current_PreH27
  have PreH24 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_l)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH12 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_2)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH6 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_3)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH2 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_4)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  obtain ⟨hp23, hs23, hsort23⟩ := PreH7 pts_out_2 PreH11 PreH12
  obtain ⟨hp34, hs34, hsort34⟩ := PreH3 pts_out_3 PreH5 PreH6
  have hn2 : Zlength pts_out_2 = n_pre := by have := perm_length _ _ PreH13; omega
  have hn3 : Zlength pts_out_3 = n_pre := by have := perm_length _ _ hp23; omega
  have hn4 : Zlength pts_out_4 = n_pre := by have := perm_length _ _ hp34; omega
  have hpart3 := PointPartitionedAt_preserved_by_left _ _ _ _ _ _ hp23 PreH18 hs23 (by omega) PreH15
  have hpart4 := PointPartitionedAt_preserved_by_right _ _ _ _ _ _ hp34 PreH18 hs34 (by omega) hpart3
  have hleft : PointSortedRange (mk_point gx_pre gy_pre) pts_out_4 left_pre (retval-1) := by
    apply PointSortedRange_ext _ pts_out_3 _ _ _ PreH18 (by omega) (by omega) _ hsort23
    intro k hk
    exact hs34.2 k (by omega) (Or.inl (by omega))
  have hsorted := PointSortedRange_from_middle_partition _ _ _ _ _ PreH18 PreH8 PreH4 (by omega) hpart4 hleft hsort34
  Exists pts_out_4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try assumption
    intro pts_in hf hb
    have he := FlatPoints_functional flat pts_in pts_l hf PreH23
    subst pts_in
    refine ⟨PreH13.trans (hp23.trans hp34), ?_, hsorted⟩
    apply PointSameOutsideRange_trans _ pts_out_3 _ _ _
    · exact PointSameOutsideRange_trans _ _ _ _ _ PreH14
        (PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs23)
    · exact PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs34

theorem proof_of_quicksort_points_range_return_wit_2 : quicksort_points_range_return_wit_2 := by
  right
  intro flat n_pre left_pre right_pre gx_pre gy_pre pts_l flat_out_2 pts_out_2 retval flat_out_3 pts_out_3 current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26 current_PreH27 current_PreH28 current_PreH29
  have tail_current_PreH26 := (coords_map_tail _ _ current_PreH26)
  have tail_current_PreH27 := (coords_map_tail _ _ current_PreH27)
  have tail_current_PreH28 := (coords_map_tail _ _ current_PreH28)
  have tail_current_PreH29 := (coords_map_tail _ _ current_PreH29)
  have PreH1 : (FlatPoints flat_out_3 pts_out_3) := current_PreH1
  have PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 (retval + 1) right_pre) := current_PreH2
  have PreH4 : (retval < right_pre) := current_PreH3
  have PreH5 : (retval <= left_pre) := current_PreH4
  have PreH6 : (left_pre <= retval) := current_PreH5
  have PreH7 : (retval <= right_pre) := current_PreH6
  have PreH8 : (FlatPoints flat_out_2 pts_out_2) := current_PreH7
  have PreH10 : (PointPermutation pts_l pts_out_2) := current_PreH8
  have PreH11 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre) := current_PreH9
  have PreH12 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval) := current_PreH10
  have PreH13 : ((0 : Int) <= n_pre) := current_PreH11
  have PreH14 : (n_pre <= 50000) := current_PreH12
  have PreH15 : ((0 : Int) <= left_pre) := current_PreH13
  have PreH16 : (left_pre < right_pre) := current_PreH14
  have PreH17 : (right_pre < n_pre) := current_PreH15
  have PreH18 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by apply point_model_cons_maps (mk_point gx_pre gy_pre) flat n_pre pts_l <;> assumption
  have PreH19 : ((Zlength (pts_l)) = n_pre) := current_PreH24
  have PreH20 : (FlatPoints flat pts_l) := current_PreH25
  have PreH21 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_l)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH9 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_2)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH2 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_3)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  obtain ⟨hp, hs, hsort⟩ := PreH3 pts_out_2 PreH8 PreH9
  have hn2 : Zlength pts_out_2 = n_pre := by have := perm_length _ _ PreH10; omega
  have hn3 : Zlength pts_out_3 = n_pre := by have := perm_length _ _ hp; omega
  have hpart := PointPartitionedAt_preserved_by_right _ _ _ _ _ _ hp PreH15 hs (by omega) PreH12
  have hsorted := PointSortedRange_from_right_boundary _ _ _ _ _ PreH15 PreH5 (by omega) hpart hsort
  Exists pts_out_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try assumption
    intro pts_in hf hb
    have he := FlatPoints_functional flat pts_in pts_l hf PreH20
    subst pts_in
    refine ⟨PreH10.trans hp, ?_, hsorted⟩
    exact PointSameOutsideRange_trans _ _ _ _ _ PreH11
      (PointSameOutsideRange_weaken _ _ _ _ _ _ (by omega) (by omega) hs)

theorem proof_of_quicksort_points_range_partial_solve_wit_2_pure : quicksort_points_range_partial_solve_wit_2_pure := by
  right
  intro flat coords_pre n_pre left_pre right_pre gx_pre gy_pre pts_l flat_out pts_out retval current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26 current_PreH27 current_PreH28 current_PreH29 current_PreH30 current_PreH31 current_PreH32 current_PreH33 current_PreH34 current_PreH35 current_PreH36 current_PreH37 current_PreH38
  have tail_current_PreH35 := (coords_map_tail _ _ current_PreH35)
  have tail_current_PreH36 := (coords_map_tail _ _ current_PreH36)
  have tail_current_PreH37 := (coords_map_tail _ _ current_PreH37)
  have tail_current_PreH38 := (coords_map_tail _ _ current_PreH38)
  have PreH1 : (gy_pre <= INT_MAX) := current_PreH1
  have PreH2 : (gx_pre <= INT_MAX) := current_PreH2
  have PreH3 : (right_pre <= INT_MAX) := current_PreH3
  have PreH4 : (left_pre <= INT_MAX) := current_PreH4
  have PreH5 : (n_pre <= INT_MAX) := current_PreH5
  have PreH6 : (retval <= INT_MAX) := current_PreH6
  have PreH7 : (gy_pre >= INT_MIN) := current_PreH7
  have PreH8 : (gx_pre >= INT_MIN) := current_PreH8
  have PreH9 : (right_pre >= INT_MIN) := current_PreH9
  have PreH10 : (left_pre >= INT_MIN) := current_PreH10
  have PreH11 : (n_pre >= INT_MIN) := current_PreH11
  have PreH12 : (retval >= INT_MIN) := current_PreH12
  have PreH13 : (retval > left_pre) := current_PreH13
  have PreH14 : (left_pre <= retval) := current_PreH14
  have PreH15 : (retval <= right_pre) := current_PreH15
  have PreH16 : (FlatPoints flat_out pts_out) := current_PreH16
  have PreH18 : (PointPermutation pts_l pts_out) := current_PreH17
  have PreH19 : (PointSameOutsideRange pts_l pts_out left_pre right_pre) := current_PreH18
  have PreH20 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval) := current_PreH19
  have PreH21 : ((0 : Int) <= n_pre) := current_PreH20
  have PreH22 : (n_pre <= 50000) := current_PreH21
  have PreH23 : ((0 : Int) <= left_pre) := current_PreH22
  have PreH24 : (left_pre < right_pre) := current_PreH23
  have PreH25 : (right_pre < n_pre) := current_PreH24
  have PreH26 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by apply point_model_cons_maps (mk_point gx_pre gy_pre) flat n_pre pts_l <;> assumption
  have PreH27 : ((Zlength (pts_l)) = n_pre) := current_PreH33
  have PreH28 : (FlatPoints flat pts_l) := current_PreH34
  have PreH29 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_l)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH17 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have hn : Zlength pts_out = n_pre := by have := perm_length _ _ PreH18; omega
  have hmodel : PointFlatModel flat_out := ⟨pts_out, PreH16⟩
  have hlen : Zlength flat_out = 2*n_pre := by have := PreH16.1; omega
  obtain ⟨hlo,hhi⟩ := flat_of_coords pts_out flat_out PreH16.2 (bound_tail _ _ PreH17)
  split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_quicksort_points_range_partial_solve_wit_3_pure : quicksort_points_range_partial_solve_wit_3_pure := by
  right
  intro flat coords_pre n_pre left_pre right_pre gx_pre gy_pre pts_l flat_out_2 pts_out retval flat_out pts_out_2 current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26 current_PreH27 current_PreH28 current_PreH29 current_PreH30 current_PreH31 current_PreH32 current_PreH33 current_PreH34 current_PreH35 current_PreH36 current_PreH37 current_PreH38 current_PreH39 current_PreH40 current_PreH41
  have tail_current_PreH38 := (coords_map_tail _ _ current_PreH38)
  have tail_current_PreH39 := (coords_map_tail _ _ current_PreH39)
  have tail_current_PreH40 := (coords_map_tail _ _ current_PreH40)
  have tail_current_PreH41 := (coords_map_tail _ _ current_PreH41)
  have PreH1 : (gy_pre <= INT_MAX) := current_PreH1
  have PreH2 : (gx_pre <= INT_MAX) := current_PreH2
  have PreH3 : (right_pre <= INT_MAX) := current_PreH3
  have PreH4 : (left_pre <= INT_MAX) := current_PreH4
  have PreH5 : (n_pre <= INT_MAX) := current_PreH5
  have PreH6 : (retval <= INT_MAX) := current_PreH6
  have PreH7 : (gy_pre >= INT_MIN) := current_PreH7
  have PreH8 : (gx_pre >= INT_MIN) := current_PreH8
  have PreH9 : (right_pre >= INT_MIN) := current_PreH9
  have PreH10 : (left_pre >= INT_MIN) := current_PreH10
  have PreH11 : (n_pre >= INT_MIN) := current_PreH11
  have PreH12 : (retval >= INT_MIN) := current_PreH12
  have PreH13 : (retval < right_pre) := current_PreH13
  have PreH14 : (FlatPoints flat_out pts_out_2) := current_PreH14
  have PreH16 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1)) := current_PreH15
  have PreH17 : (retval > left_pre) := current_PreH16
  have PreH18 : (left_pre <= retval) := current_PreH17
  have PreH19 : (retval <= right_pre) := current_PreH18
  have PreH20 : (FlatPoints flat_out_2 pts_out) := current_PreH19
  have PreH22 : (PointPermutation pts_l pts_out) := current_PreH20
  have PreH23 : (PointSameOutsideRange pts_l pts_out left_pre right_pre) := current_PreH21
  have PreH24 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval) := current_PreH22
  have PreH25 : ((0 : Int) <= n_pre) := current_PreH23
  have PreH26 : (n_pre <= 50000) := current_PreH24
  have PreH27 : ((0 : Int) <= left_pre) := current_PreH25
  have PreH28 : (left_pre < right_pre) := current_PreH26
  have PreH29 : (right_pre < n_pre) := current_PreH27
  have PreH30 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by apply point_model_cons_maps (mk_point gx_pre gy_pre) flat n_pre pts_l <;> assumption
  have PreH31 : ((Zlength (pts_l)) = n_pre) := current_PreH36
  have PreH32 : (FlatPoints flat pts_l) := current_PreH37
  have PreH33 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_l)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH21 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH15 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out_2)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have hp := (PreH16 pts_out PreH20 PreH21).1
  have hn : Zlength pts_out_2 = n_pre := by have := perm_length _ _ (PreH22.trans hp); omega
  have hmodel : PointFlatModel flat_out := ⟨pts_out_2, PreH14⟩
  have hlen : Zlength flat_out = 2*n_pre := by have := PreH14.1; omega
  obtain ⟨hlo,hhi⟩ := flat_of_coords pts_out_2 flat_out PreH14.2 (bound_tail _ _ PreH15)
  split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_quicksort_points_range_partial_solve_wit_4_pure : quicksort_points_range_partial_solve_wit_4_pure := by
  right
  intro flat coords_pre n_pre left_pre right_pre gx_pre gy_pre pts_l flat_out pts_out retval current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14 current_PreH15 current_PreH16 current_PreH17 current_PreH18 current_PreH19 current_PreH20 current_PreH21 current_PreH22 current_PreH23 current_PreH24 current_PreH25 current_PreH26 current_PreH27 current_PreH28 current_PreH29 current_PreH30 current_PreH31 current_PreH32 current_PreH33 current_PreH34 current_PreH35 current_PreH36 current_PreH37 current_PreH38 current_PreH39
  have tail_current_PreH36 := (coords_map_tail _ _ current_PreH36)
  have tail_current_PreH37 := (coords_map_tail _ _ current_PreH37)
  have tail_current_PreH38 := (coords_map_tail _ _ current_PreH38)
  have tail_current_PreH39 := (coords_map_tail _ _ current_PreH39)
  have PreH1 : (gy_pre <= INT_MAX) := current_PreH1
  have PreH2 : (gx_pre <= INT_MAX) := current_PreH2
  have PreH3 : (right_pre <= INT_MAX) := current_PreH3
  have PreH4 : (left_pre <= INT_MAX) := current_PreH4
  have PreH5 : (n_pre <= INT_MAX) := current_PreH5
  have PreH6 : (retval <= INT_MAX) := current_PreH6
  have PreH7 : (gy_pre >= INT_MIN) := current_PreH7
  have PreH8 : (gx_pre >= INT_MIN) := current_PreH8
  have PreH9 : (right_pre >= INT_MIN) := current_PreH9
  have PreH10 : (left_pre >= INT_MIN) := current_PreH10
  have PreH11 : (n_pre >= INT_MIN) := current_PreH11
  have PreH12 : (retval >= INT_MIN) := current_PreH12
  have PreH13 : (retval < right_pre) := current_PreH13
  have PreH14 : (retval <= left_pre) := current_PreH14
  have PreH15 : (left_pre <= retval) := current_PreH15
  have PreH16 : (retval <= right_pre) := current_PreH16
  have PreH17 : (FlatPoints flat_out pts_out) := current_PreH17
  have PreH19 : (PointPermutation pts_l pts_out) := current_PreH18
  have PreH20 : (PointSameOutsideRange pts_l pts_out left_pre right_pre) := current_PreH19
  have PreH21 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval) := current_PreH20
  have PreH22 : ((0 : Int) <= n_pre) := current_PreH21
  have PreH23 : (n_pre <= 50000) := current_PreH22
  have PreH24 : ((0 : Int) <= left_pre) := current_PreH23
  have PreH25 : (left_pre < right_pre) := current_PreH24
  have PreH26 : (right_pre < n_pre) := current_PreH25
  have PreH27 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre) := by apply point_model_cons_maps (mk_point gx_pre gy_pre) flat n_pre pts_l <;> assumption
  have PreH28 : ((Zlength (pts_l)) = n_pre) := current_PreH34
  have PreH29 : (FlatPoints flat pts_l) := current_PreH35
  have PreH30 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_l)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH18 : (PointCoordsBound ((mk_point (gx_pre) (gy_pre)) :: pts_out)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have hn : Zlength pts_out = n_pre := by have := perm_length _ _ PreH19; omega
  have hmodel : PointFlatModel flat_out := ⟨pts_out, PreH17⟩
  have hlen : Zlength flat_out = 2*n_pre := by have := PreH17.1; omega
  obtain ⟨hlo,hhi⟩ := flat_of_coords pts_out flat_out PreH17.2 (bound_tail _ _ PreH18)
  split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_sort_return_wit_1 : sort_return_wit_1 := by
  right
  intro gy gx pts_l flat n_pre flat_out_2 pts_out_2 current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10
  have tail_current_PreH7 := (coords_map_tail _ _ current_PreH7)
  have tail_current_PreH8 := (coords_map_tail _ _ current_PreH8)
  have tail_current_PreH9 := (coords_map_tail _ _ current_PreH9)
  have tail_current_PreH10 := (coords_map_tail _ _ current_PreH10)
  have PreH1 : (FlatPoints flat_out_2 pts_out_2) := current_PreH1
  have PreH3 : (PointRangeSortResult (mk_point (gx) (gy)) flat pts_out_2 (0 : Int) (n_pre - 1)) := current_PreH2
  have PreH4 : ((0 : Int) <= n_pre) := current_PreH3
  have PreH5 : (n_pre <= 50000) := current_PreH4
  have PreH6 : ((Zlength (pts_l)) = n_pre) := current_PreH5
  have PreH7 : (FlatPoints flat pts_l) := current_PreH6
  have PreH8 : (PointCoordsBound ((mk_point (gx) (gy)) :: pts_l)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have PreH2 : (PointCoordsBound ((mk_point (gx) (gy)) :: pts_out_2)) := by first | (apply coords_of_range_result <;> assumption) | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  obtain ⟨hp, hs, hsort⟩ := PreH3 pts_l PreH7 PreH8
  have hn : Zlength pts_out_2 = n_pre := by have := perm_length _ _ hp; omega
  Exists pts_out_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption
    intro i j hi hij hj
    exact hsort i j hi hij (by omega)

theorem proof_of_sort_partial_solve_wit_1_pure : sort_partial_solve_wit_1_pure := by
  right
  intro gy gx pts_l flat pts_pre n_pre current_PreH1 current_PreH2 current_PreH3 current_PreH4 current_PreH5 current_PreH6 current_PreH7 current_PreH8 current_PreH9 current_PreH10 current_PreH11 current_PreH12 current_PreH13 current_PreH14
  have tail_current_PreH11 := (coords_map_tail _ _ current_PreH11)
  have tail_current_PreH12 := (coords_map_tail _ _ current_PreH12)
  have tail_current_PreH13 := (coords_map_tail _ _ current_PreH13)
  have tail_current_PreH14 := (coords_map_tail _ _ current_PreH14)
  have PreH1 : (n_pre <= INT_MAX) := current_PreH3
  have PreH2 : (gx <= INT_MAX) := current_PreH2
  have PreH3 : (gy <= INT_MAX) := current_PreH1
  have PreH4 : (n_pre >= INT_MIN) := current_PreH6
  have PreH5 : (gx >= INT_MIN) := current_PreH5
  have PreH6 : (gy >= INT_MIN) := current_PreH4
  have PreH7 : ((0 : Int) <= n_pre) := current_PreH7
  have PreH8 : (n_pre <= 50000) := current_PreH8
  have PreH9 : ((Zlength (pts_l)) = n_pre) := current_PreH9
  have PreH10 : (FlatPoints flat pts_l) := current_PreH10
  have PreH11 : (PointCoordsBound ((mk_point (gx) (gy)) :: pts_l)) := by first | apply coords_from_maps <;> assumption | apply coords_tail_from_maps <;> assumption | (apply coords_permutation_from_maps <;> assumption) | (apply coords_cons_permutation_from_maps <;> assumption) | (apply coords_cons_from_maps <;> first | assumption | (constructor <;> unfold CoordInBounds <;> simp only [point_x, point_y, mk_point] <;> omega))
  have hmodel : PointFlatModel flat := ⟨pts_l, PreH10⟩
  have hlen : Zlength flat = 2*n_pre := by have := PreH10.1; omega
  obtain ⟨hlo,hhi⟩ := flat_of_coords pts_l flat PreH10.2 (bound_tail _ _ PreH11)
  obtain ⟨⟨hxl,hxu⟩,⟨hyl,hyu⟩⟩ := bound_head _ _ PreH11
  split_pures <;> dump_pre_spatial <;> first | assumption | exact hxl | exact hxu | exact hyl | exact hyu

end SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_proof_manual
