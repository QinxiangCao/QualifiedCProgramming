import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P044_837C_two_seals_goal P044_837C_two_seals_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem product_bounds (x y : Int) (hx : 1≤x ∧ x≤100) (hy : 1≤y ∧ y≤100) :
    0≤x*y ∧ x*y≤10000 := by
  have hh := Int.mul_le_mul_of_nonneg_right hx.2 (show 0≤y by omega)
  have hg := Int.mul_le_mul_of_nonneg_left hy.2 (show (0:Int)≤100 by omega)
  exact ⟨Int.mul_nonneg (by omega) (by omega),by omega⟩

theorem proof_of_fits_return_wit_1_split_goal_1 : fits_return_wit_1_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_2_split_goal_1 : fits_return_wit_2_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_3_split_goal_1 : fits_return_wit_3_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_4_split_goal_1 : fits_return_wit_4_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_5_split_goal_1 : fits_return_wit_5_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_6_split_goal_1 : fits_return_wit_6_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_7_split_goal_1 : fits_return_wit_7_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_8_split_goal_1 : fits_return_wit_8_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_fits_return_wit_9_split_goal_1 : fits_return_wit_9_split_goal_1 := by
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  unfold FitsDims TwoFit
  dsimp
  omega

theorem proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))))
  omega

theorem proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))
  omega

theorem proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))))
  omega

theorem proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))))
  omega

theorem proof_of_solver_safety_wit_27_split_goal_1 : solver_safety_wit_27_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_27_split_goal_2 : solver_safety_wit_27_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))
  omega

theorem proof_of_solver_safety_wit_28_split_goal_1 : solver_safety_wit_28_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))))
  omega

theorem proof_of_solver_safety_wit_29_split_goal_1 : solver_safety_wit_29_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_29_split_goal_2 : solver_safety_wit_29_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))))
  omega

theorem proof_of_solver_safety_wit_30_split_goal_1 : solver_safety_wit_30_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_30_split_goal_2 : solver_safety_wit_30_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))
  omega

theorem proof_of_solver_safety_wit_31_split_goal_1 : solver_safety_wit_31_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_31_split_goal_2 : solver_safety_wit_31_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))))
  omega

theorem proof_of_solver_safety_wit_32_split_goal_1 : solver_safety_wit_32_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_32_split_goal_2 : solver_safety_wit_32_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))))
  omega

theorem proof_of_solver_safety_wit_33_split_goal_1 : solver_safety_wit_33_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_33_split_goal_2 : solver_safety_wit_33_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))
  omega

theorem proof_of_solver_safety_wit_34_split_goal_1 : solver_safety_wit_34_split_goal_1 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_34_split_goal_2 : solver_safety_wit_34_split_goal_2 := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  have hix : 1≤Znth i xs_spec 0 ∧ Znth i xs_spec 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec 0 ∧ Znth i ys_spec 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec 0 ∧ Znth j xs_spec 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec 0 ∧ Znth j ys_spec 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  dump_pre_spatial
  change (((-2147483648)) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))))
  omega

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro seals paper xs_spec_2 ys_spec_2 n_pre a_pre b_pre __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact best_before_initial__invariant_init paper seals

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro seals paper xs_spec_2 ys_spec_2 n_pre a_pre b_pre __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  intro k hk
  have hb := PreH7 k hk
  have he := PreH13 k hk
  exact ⟨⟨hb,he.1⟩,he.2⟩

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact PreH13

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH13

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH13

theorem proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hj : j=n_pre := by omega
  rw [hj] at PreH20
  exact best_before_finish_j__loop_transitions paper seals i n_pre best (by assumption) PreH20

theorem proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hr : ri=2 := by omega
  rw [hr] at PreH21
  exact best_before_finish_ri__loop_transitions paper seals i j best PreH21

theorem proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hr : rj=2 := by omega
  rw [hr] at PreH23
  exact best_before_finish_rj__loop_transitions paper seals i j ri best PreH23

theorem proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH13

theorem proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH13

theorem proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH13

theorem proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=1 := by omega
  have hrj : rj=1 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 1 1 (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (1:Int)=0 ↔ False by decide,show (1:Int)=0 ↔ False by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_take_current__choice_improve paper seals i j 1 1 best (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  have hix : 1≤Znth i xs_spec_2 0 ∧ Znth i xs_spec_2 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec_2 0 ∧ Znth i ys_spec_2 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec_2 0 ∧ Znth j xs_spec_2 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec_2 0 ∧ Znth j ys_spec_2 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  omega

theorem proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=1 := by omega
  have hrj : rj=0 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 1 0 (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (1:Int)=0 ↔ False by decide,show (0:Int)=0 ↔ True by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_take_current__choice_improve paper seals i j 1 0 best (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_2_split_goal_2 : solver_entail_wit_10_2_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  have hix : 1≤Znth i xs_spec_2 0 ∧ Znth i xs_spec_2 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec_2 0 ∧ Znth i ys_spec_2 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec_2 0 ∧ Znth j xs_spec_2 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec_2 0 ∧ Znth j ys_spec_2 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  omega

theorem proof_of_solver_entail_wit_10_3_split_goal_1 : solver_entail_wit_10_3_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=0 := by omega
  have hrj : rj=1 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 0 1 (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (0:Int)=0 ↔ True by decide,show (1:Int)=0 ↔ False by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_take_current__choice_improve paper seals i j 0 1 best (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_3_split_goal_2 : solver_entail_wit_10_3_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  have hix : 1≤Znth i xs_spec_2 0 ∧ Znth i xs_spec_2 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec_2 0 ∧ Znth i ys_spec_2 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec_2 0 ∧ Znth j xs_spec_2 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec_2 0 ∧ Znth j ys_spec_2 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  omega

theorem proof_of_solver_entail_wit_10_4_split_goal_1 : solver_entail_wit_10_4_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=0 := by omega
  have hrj : rj=0 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 0 0 (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (0:Int)=0 ↔ True by decide,show (0:Int)=0 ↔ True by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_take_current__choice_improve paper seals i j 0 0 best (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_4_split_goal_2 : solver_entail_wit_10_4_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  have hix : 1≤Znth i xs_spec_2 0 ∧ Znth i xs_spec_2 0≤100 := by omega
  have hiy : 1≤Znth i ys_spec_2 0 ∧ Znth i ys_spec_2 0≤100 := by omega
  have hjx : 1≤Znth j xs_spec_2 0 ∧ Znth j xs_spec_2 0≤100 := by omega
  have hjy : 1≤Znth j ys_spec_2 0 ∧ Znth j ys_spec_2 0≤100 := by omega
  have hpi := product_bounds _ _ hix hiy
  have hpi' := product_bounds _ _ hiy hix
  have hpj := product_bounds _ _ hjx hjy
  have hpj' := product_bounds _ _ hjy hjx
  omega

theorem proof_of_solver_entail_wit_10_5_split_goal_1 : solver_entail_wit_10_5_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=1 := by omega
  have hrj : rj=1 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 1 1 (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (1:Int)=0 ↔ False by decide,show (1:Int)=0 ↔ False by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_skip_dominated__choice_retain_fit paper seals i j 1 1 best (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_6_split_goal_1 : solver_entail_wit_10_6_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=1 := by omega
  have hrj : rj=0 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 1 0 (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (1:Int)=0 ↔ False by decide,show (0:Int)=0 ↔ True by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_skip_dominated__choice_retain_fit paper seals i j 1 0 best (Znth i ys_spec_2 0*Znth i xs_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_7_split_goal_1 : solver_entail_wit_10_7_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=0 := by omega
  have hrj : rj=1 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 0 1 (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (0:Int)=0 ↔ True by decide,show (1:Int)=0 ↔ False by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_skip_dominated__choice_retain_fit paper seals i j 0 1 best (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j ys_spec_2 0*Znth j xs_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_8_split_goal_1 : solver_entail_wit_10_8_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have Hi := PreH20 i (by omega)
  have Hj := PreH20 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=0 := by omega
  have hrj : rj=0 := by omega
  subst ri rj
  have hc : SealChoice paper seals i j 0 0 (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩,?_⟩
    simp only [rotate_seal,show (0:Int)=0 ↔ True by decide,show (0:Int)=0 ↔ True by decide,ite_true,ite_false,hpairi,hpairj]
    constructor
    · change TwoFit (fst paper) (snd paper) _ _
      rw [PreH15,PreH16]
      exact PreH3
    · trivial
  exact best_before_skip_dominated__choice_retain_fit paper seals i j 0 0 best (Znth i xs_spec_2 0*Znth i ys_spec_2 0+Znth j xs_spec_2 0*Znth j ys_spec_2 0) PreH30 hc PreH1

theorem proof_of_solver_entail_wit_10_9_split_goal_1 : solver_entail_wit_10_9_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=1 := by omega
  have hrj : rj=1 := by omega
  subst ri rj
  apply best_before_skip_invalid__choice_retain_invalid paper seals i j 1 1 best PreH29
  intro area hc
  apply PreH2
  have hf := hc.2.2.2.2.1
  simp only [rotate_seal,show (1:Int)=0 ↔ False by decide,show (1:Int)=0 ↔ False by decide,ite_true,ite_false,hpairi,hpairj] at hf
  change TwoFit (fst paper) (snd paper) _ _ at hf
  rw [PreH14,PreH15] at hf
  exact hf

theorem proof_of_solver_entail_wit_10_10_split_goal_1 : solver_entail_wit_10_10_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=1 := by omega
  have hrj : rj=0 := by omega
  subst ri rj
  apply best_before_skip_invalid__choice_retain_invalid paper seals i j 1 0 best PreH29
  intro area hc
  apply PreH2
  have hf := hc.2.2.2.2.1
  simp only [rotate_seal,show (1:Int)=0 ↔ False by decide,show (0:Int)=0 ↔ True by decide,ite_true,ite_false,hpairi,hpairj] at hf
  change TwoFit (fst paper) (snd paper) _ _ at hf
  rw [PreH14,PreH15] at hf
  exact hf

theorem proof_of_solver_entail_wit_10_11_split_goal_1 : solver_entail_wit_10_11_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=0 := by omega
  have hrj : rj=1 := by omega
  subst ri rj
  apply best_before_skip_invalid__choice_retain_invalid paper seals i j 0 1 best PreH29
  intro area hc
  apply PreH2
  have hf := hc.2.2.2.2.1
  simp only [rotate_seal,show (0:Int)=0 ↔ True by decide,show (1:Int)=0 ↔ False by decide,ite_true,ite_false,hpairi,hpairj] at hf
  change TwoFit (fst paper) (snd paper) _ _ at hf
  rw [PreH14,PreH15] at hf
  exact hf

theorem proof_of_solver_entail_wit_10_12_split_goal_1 : solver_entail_wit_10_12_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have Hi := PreH19 i (by omega)
  have Hj := PreH19 j (by omega)
  rw [Znth_indep seals i __default__Prod_Z_Z (0,0) (by omega)] at Hi
  rw [Znth_indep seals j __default__Prod_Z_Z (0,0) (by omega)] at Hj
  have hpairi : Znth i seals (0,0)=(Znth i xs_spec_2 0,Znth i ys_spec_2 0) :=
    Prod.ext Hi.1.2.symm Hi.2.symm
  have hpairj : Znth j seals (0,0)=(Znth j xs_spec_2 0,Znth j ys_spec_2 0) :=
    Prod.ext Hj.1.2.symm Hj.2.symm
  have hri : ri=0 := by omega
  have hrj : rj=0 := by omega
  subst ri rj
  apply best_before_skip_invalid__choice_retain_invalid paper seals i j 0 0 best PreH29
  intro area hc
  apply PreH2
  have hf := hc.2.2.2.2.1
  simp only [rotate_seal,show (0:Int)=0 ↔ True by decide,show (0:Int)=0 ↔ True by decide,ite_true,ite_false,hpairi,hpairj] at hf
  change TwoFit (fst paper) (snd paper) _ _ at hf
  rw [PreH14,PreH15] at hf
  exact hf

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro seals paper n_pre a_pre b_pre best i_2 ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  intro i hi
  have hh := PreH13 i hi
  exact ⟨hh.1.2,hh.2⟩

theorem proof_of_solver_return_wit_1_split_goal_2 : solver_return_wit_1_split_goal_2 := by
  intro seals paper n_pre a_pre b_pre best i_2 ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact best_before_complete__final_result paper seals i_2 best (by omega) (by assumption)

theorem proof_of_fits_return_wit_1 : fits_return_wit_1 := by
  unfold fits_return_wit_1
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_1_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_fits_return_wit_2 : fits_return_wit_2 := by
  unfold fits_return_wit_2
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_2_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_fits_return_wit_3 : fits_return_wit_3 := by
  unfold fits_return_wit_3
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_3_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_fits_return_wit_4 : fits_return_wit_4 := by
  unfold fits_return_wit_4
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_4_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_fits_return_wit_5 : fits_return_wit_5 := by
  unfold fits_return_wit_5
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_5_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_fits_return_wit_6 : fits_return_wit_6 := by
  unfold fits_return_wit_6
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_6_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_fits_return_wit_7 : fits_return_wit_7 := by
  unfold fits_return_wit_7
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_7_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_fits_return_wit_8 : fits_return_wit_8 := by
  unfold fits_return_wit_8
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_8_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_fits_return_wit_9 : fits_return_wit_9 := by
  unfold fits_return_wit_9
  right
  intro w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_fits_return_wit_9_split_goal_1 w1_pre h1_pre w2_pre h2_pre a_pre b_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_solver_safety_wit_23 : solver_safety_wit_23 := by
  unfold solver_safety_wit_23
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_23_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_23_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_24 : solver_safety_wit_24 := by
  unfold solver_safety_wit_24
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_24_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_24_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_25 : solver_safety_wit_25 := by
  unfold solver_safety_wit_25
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_25_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_25_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_26 : solver_safety_wit_26 := by
  unfold solver_safety_wit_26
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_26_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_26_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_27 : solver_safety_wit_27 := by
  unfold solver_safety_wit_27
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_27_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_27_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_28 : solver_safety_wit_28 := by
  unfold solver_safety_wit_28
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_28_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_28_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_29 : solver_safety_wit_29 := by
  unfold solver_safety_wit_29
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_29_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_29_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_30 : solver_safety_wit_30 := by
  unfold solver_safety_wit_30
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_30_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_30_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_31 : solver_safety_wit_31 := by
  unfold solver_safety_wit_31
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_31_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_31_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_32 : solver_safety_wit_32 := by
  unfold solver_safety_wit_32
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_32_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_32_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_33 : solver_safety_wit_33 := by
  unfold solver_safety_wit_33
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_33_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_33_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_safety_wit_34 : solver_safety_wit_34 := by
  unfold solver_safety_wit_34
  right
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_safety_wit_34_split_goal_1 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  · exact proof_of_solver_safety_wit_34_split_goal_2 seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro seals paper xs_spec_2 ys_spec_2 n_pre a_pre b_pre __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 seals paper xs_spec_2 ys_spec_2 n_pre a_pre b_pre __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_1_split_goal_2 seals paper xs_spec_2 ys_spec_2 n_pre a_pre b_pre __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro seals paper n_pre a_pre b_pre best i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_split_goal_1 seals paper n_pre a_pre b_pre best i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_3_split_goal_1 seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_4_split_goal_1 seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_7_split_goal_1 seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_solver_entail_wit_7_split_goal_2 seals paper n_pre a_pre b_pre best j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  right
  intro seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_split_goal_1 seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_solver_entail_wit_8_split_goal_2 seals paper n_pre a_pre b_pre best ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_9 : solver_entail_wit_9 := by
  unfold solver_entail_wit_9
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      | exact proof_of_solver_entail_wit_9_split_goal_2 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  unfold solver_entail_wit_10_1
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_1_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_10_1_split_goal_2 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2 := by
  unfold solver_entail_wit_10_2
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_2_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_10_2_split_goal_2 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3 := by
  unfold solver_entail_wit_10_3
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_3_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_10_3_split_goal_2 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4 := by
  unfold solver_entail_wit_10_4
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_10_4_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
      | exact proof_of_solver_entail_wit_10_4_split_goal_2 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5 := by
  unfold solver_entail_wit_10_5
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_5_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_6 : solver_entail_wit_10_6 := by
  unfold solver_entail_wit_10_6
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_6_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_7 : solver_entail_wit_10_7 := by
  unfold solver_entail_wit_10_7
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_7_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_8 : solver_entail_wit_10_8 := by
  unfold solver_entail_wit_10_8
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_8_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

theorem proof_of_solver_entail_wit_10_9 : solver_entail_wit_10_9 := by
  unfold solver_entail_wit_10_9
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_9_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_entail_wit_10_10 : solver_entail_wit_10_10 := by
  unfold solver_entail_wit_10_10
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_10_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_entail_wit_10_11 : solver_entail_wit_10_11 := by
  unfold solver_entail_wit_10_11
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_11_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_entail_wit_10_12 : solver_entail_wit_10_12 := by
  unfold solver_entail_wit_10_12
  right
  intro seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_12_split_goal_1 seals paper n_pre a_pre b_pre best rj ri j i ys_spec_2 xs_spec_2 retval __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro seals paper n_pre a_pre b_pre best i_2 ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_1_split_goal_1 seals paper n_pre a_pre b_pre best i_2 ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_solver_return_wit_1_split_goal_2 seals paper n_pre a_pre b_pre best i_2 ys_spec_2 xs_spec_2 __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proved_auto_solver_partial_solve_wit_13_pure : solver_partial_solve_wit_13_pure := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have Hi := PreH17 i (by omega)
  have Hj := PreH17 j (by omega)
  split_pures <;> dump_pre_spatial <;> omega

theorem proved_auto_solver_partial_solve_wit_14_pure : solver_partial_solve_wit_14_pure := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have Hi := PreH17 i (by omega)
  have Hj := PreH17 j (by omega)
  split_pures <;> dump_pre_spatial <;> omega

theorem proved_auto_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have Hi := PreH17 i (by omega)
  have Hj := PreH17 j (by omega)
  split_pures <;> dump_pre_spatial <;> omega

theorem proved_auto_solver_partial_solve_wit_16_pure : solver_partial_solve_wit_16_pure := by
  intro seals paper x_pre y_pre n_pre a_pre b_pre best rj ri j i ys_spec xs_spec __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have Hi := PreH17 i (by omega)
  have Hj := PreH17 j (by omega)
  split_pures <;> dump_pre_spatial <;> omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_proof_manual
