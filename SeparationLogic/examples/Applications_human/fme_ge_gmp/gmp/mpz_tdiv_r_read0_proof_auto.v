Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_swap_entail_wit_1 : mpz_swap_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_swap_entail_wit_2 : mpz_swap_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_swap_return_wit_1 : mpz_swap_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_1 : mpz_swap_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_2 : mpz_swap_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_3 : mpz_swap_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_1 : mpn_normalized_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_2 : mpn_normalized_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_3 : mpn_normalized_size_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_4 : mpn_normalized_size_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_5 : mpn_normalized_size_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_partial_solve_wit_1 : mpn_normalized_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_partial_solve_wit_2 : mpn_normalized_size_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_1_nonalias : mpz_div_qr_safety_wit_1_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_2_r_eq_n_read0 : mpz_div_qr_safety_wit_2_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_3_nonalias : mpz_div_qr_safety_wit_3_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_4_r_eq_n_read0 : mpz_div_qr_safety_wit_4_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_5_r_eq_n_read0 : mpz_div_qr_safety_wit_5_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_6_r_eq_n_read0 : mpz_div_qr_safety_wit_6_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_7_nonalias : mpz_div_qr_safety_wit_7_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_8_r_eq_n_read0 : mpz_div_qr_safety_wit_8_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_9_nonalias : mpz_div_qr_safety_wit_9_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_10_r_eq_n_read0 : mpz_div_qr_safety_wit_10_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_11_nonalias : mpz_div_qr_safety_wit_11_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_12_r_eq_n_read0 : mpz_div_qr_safety_wit_12_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_13_nonalias : mpz_div_qr_safety_wit_13_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_14_r_eq_n_read0 : mpz_div_qr_safety_wit_14_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_15_nonalias : mpz_div_qr_safety_wit_15_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_16_nonalias : mpz_div_qr_safety_wit_16_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_17_nonalias : mpz_div_qr_safety_wit_17_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_18_r_eq_n_read0 : mpz_div_qr_safety_wit_18_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_19_nonalias : mpz_div_qr_safety_wit_19_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_20_r_eq_n_read0 : mpz_div_qr_safety_wit_20_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_21_r_eq_n_read0 : mpz_div_qr_safety_wit_21_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_22_nonalias : mpz_div_qr_safety_wit_22_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_23_r_eq_n_read0 : mpz_div_qr_safety_wit_23_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_24_nonalias : mpz_div_qr_safety_wit_24_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_25_r_eq_n_read0 : mpz_div_qr_safety_wit_25_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_26_nonalias : mpz_div_qr_safety_wit_26_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_27_r_eq_n_read0 : mpz_div_qr_safety_wit_27_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_28_nonalias : mpz_div_qr_safety_wit_28_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_29_nonalias : mpz_div_qr_safety_wit_29_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_30_r_eq_n_read0 : mpz_div_qr_safety_wit_30_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_31_nonalias : mpz_div_qr_safety_wit_31_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_32_nonalias : mpz_div_qr_safety_wit_32_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_33_r_eq_n_read0 : mpz_div_qr_safety_wit_33_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_34_nonalias : mpz_div_qr_safety_wit_34_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_37_nonalias : mpz_div_qr_safety_wit_37_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_40_r_eq_n_read0 : mpz_div_qr_safety_wit_40_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_41_nonalias : mpz_div_qr_safety_wit_41_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_42_r_eq_n_read0 : mpz_div_qr_safety_wit_42_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_43_nonalias_q : mpz_div_qr_safety_wit_43_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_44_r_eq_n_q : mpz_div_qr_safety_wit_44_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_45_nonalias_noq : mpz_div_qr_safety_wit_45_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_46_r_eq_n_noq : mpz_div_qr_safety_wit_46_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_47_nonalias_q : mpz_div_qr_safety_wit_47_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_48_r_eq_n_q : mpz_div_qr_safety_wit_48_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_49_nonalias_noq : mpz_div_qr_safety_wit_49_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_50_r_eq_n_noq : mpz_div_qr_safety_wit_50_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_51_nonalias_q : mpz_div_qr_safety_wit_51_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_52_r_eq_n_q : mpz_div_qr_safety_wit_52_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_53_nonalias_noq : mpz_div_qr_safety_wit_53_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_54_r_eq_n_noq : mpz_div_qr_safety_wit_54_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_55_nonalias_q : mpz_div_qr_safety_wit_55_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_56_nonalias_q : mpz_div_qr_safety_wit_56_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_57_nonalias_q : mpz_div_qr_safety_wit_57_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_58_nonalias_q : mpz_div_qr_safety_wit_58_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_59_nonalias_q : mpz_div_qr_safety_wit_59_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_60_r_eq_n_q : mpz_div_qr_safety_wit_60_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_61_r_eq_n_q : mpz_div_qr_safety_wit_61_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_62_r_eq_n_q : mpz_div_qr_safety_wit_62_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_63_r_eq_n_q : mpz_div_qr_safety_wit_63_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_64_r_eq_n_q : mpz_div_qr_safety_wit_64_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_65_nonalias_q : mpz_div_qr_safety_wit_65_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_66_nonalias_q : mpz_div_qr_safety_wit_66_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_67_nonalias_q : mpz_div_qr_safety_wit_67_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_68_nonalias_q : mpz_div_qr_safety_wit_68_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_69_r_eq_n_q : mpz_div_qr_safety_wit_69_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_70_r_eq_n_q : mpz_div_qr_safety_wit_70_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_71_r_eq_n_q : mpz_div_qr_safety_wit_71_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_72_r_eq_n_q : mpz_div_qr_safety_wit_72_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_73_nonalias_q_done : mpz_div_qr_safety_wit_73_nonalias_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_74_nonalias_q_done : mpz_div_qr_safety_wit_74_nonalias_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_75_r_eq_n_q_done : mpz_div_qr_safety_wit_75_r_eq_n_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_76_r_eq_n_q_done : mpz_div_qr_safety_wit_76_r_eq_n_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_77_nonalias_noq : mpz_div_qr_safety_wit_77_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_78_nonalias_noq : mpz_div_qr_safety_wit_78_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_79_r_eq_n_noq : mpz_div_qr_safety_wit_79_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_80_r_eq_n_noq : mpz_div_qr_safety_wit_80_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_81_nonalias_q_rem : mpz_div_qr_safety_wit_81_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_82_r_eq_n_q_rem : mpz_div_qr_safety_wit_82_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_83_nonalias_noq_rem : mpz_div_qr_safety_wit_83_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_84_r_eq_n_noq_rem : mpz_div_qr_safety_wit_84_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_85_nonalias_q_rem : mpz_div_qr_safety_wit_85_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_86_r_eq_n_q_rem : mpz_div_qr_safety_wit_86_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_87_nonalias_noq_rem : mpz_div_qr_safety_wit_87_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_88_r_eq_n_noq_rem : mpz_div_qr_safety_wit_88_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_89_nonalias_q_rem : mpz_div_qr_safety_wit_89_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_90_r_eq_n_q_rem : mpz_div_qr_safety_wit_90_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_91_nonalias_noq_rem : mpz_div_qr_safety_wit_91_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_92_r_eq_n_noq_rem : mpz_div_qr_safety_wit_92_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_93_nonalias_q_rem : mpz_div_qr_safety_wit_93_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_94_r_eq_n_q_rem : mpz_div_qr_safety_wit_94_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_95_nonalias_noq_rem : mpz_div_qr_safety_wit_95_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_96_r_eq_n_noq_rem : mpz_div_qr_safety_wit_96_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_97_nonalias_q_rem : mpz_div_qr_safety_wit_97_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_98_r_eq_n_q_rem : mpz_div_qr_safety_wit_98_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_99_nonalias_noq_rem : mpz_div_qr_safety_wit_99_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_100_r_eq_n_noq_rem : mpz_div_qr_safety_wit_100_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_101_r_eq_n_q_rem : mpz_div_qr_safety_wit_101_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_102_r_eq_n_noq_rem : mpz_div_qr_safety_wit_102_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_103_nonalias_done : mpz_div_qr_safety_wit_103_nonalias_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_safety_wit_104_r_eq_n_done : mpz_div_qr_safety_wit_104_r_eq_n_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_1_nonalias : mpz_div_qr_entail_wit_1_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_2_r_eq_n_read0 : mpz_div_qr_entail_wit_2_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_5_1_nonalias : mpz_div_qr_entail_wit_5_1_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_5_2_r_eq_n_read0 : mpz_div_qr_entail_wit_5_2_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_5_3_nonalias : mpz_div_qr_entail_wit_5_3_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_5_4_r_eq_n_read0 : mpz_div_qr_entail_wit_5_4_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_6_1_nonalias : mpz_div_qr_entail_wit_6_1_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_6_2_r_eq_n_read0 : mpz_div_qr_entail_wit_6_2_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_7_1_nonalias_q : mpz_div_qr_entail_wit_7_1_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_7_2_nonalias_noq : mpz_div_qr_entail_wit_7_2_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_7_3_r_eq_n_q : mpz_div_qr_entail_wit_7_3_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_7_4_r_eq_n_noq : mpz_div_qr_entail_wit_7_4_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_8_1_nonalias_q : mpz_div_qr_entail_wit_8_1_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_8_2_nonalias_noq : mpz_div_qr_entail_wit_8_2_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_8_3_r_eq_n_q : mpz_div_qr_entail_wit_8_3_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_8_4_r_eq_n_noq : mpz_div_qr_entail_wit_8_4_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_13_1_nonalias_q : mpz_div_qr_entail_wit_13_1_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_13_2_r_eq_n_q : mpz_div_qr_entail_wit_13_2_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_13_3_nonalias_noq : mpz_div_qr_entail_wit_13_3_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_13_4_r_eq_n_noq : mpz_div_qr_entail_wit_13_4_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_14_1_nonalias_q : mpz_div_qr_entail_wit_14_1_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_14_2_r_eq_n_q : mpz_div_qr_entail_wit_14_2_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_14_3_nonalias_noq : mpz_div_qr_entail_wit_14_3_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_14_4_r_eq_n_noq : mpz_div_qr_entail_wit_14_4_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_17_1_nonalias_q : mpz_div_qr_entail_wit_17_1_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_17_2_nonalias_q : mpz_div_qr_entail_wit_17_2_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_17_3_nonalias_q : mpz_div_qr_entail_wit_17_3_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_17_4_nonalias_q : mpz_div_qr_entail_wit_17_4_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_18_1_r_eq_n_q : mpz_div_qr_entail_wit_18_1_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_18_2_r_eq_n_q : mpz_div_qr_entail_wit_18_2_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_18_3_r_eq_n_q : mpz_div_qr_entail_wit_18_3_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_18_4_r_eq_n_q : mpz_div_qr_entail_wit_18_4_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_23_1_nonalias_q_done : mpz_div_qr_entail_wit_23_1_nonalias_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_23_2_nonalias_q_done : mpz_div_qr_entail_wit_23_2_nonalias_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_24_1_nonalias_noq : mpz_div_qr_entail_wit_24_1_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_24_2_nonalias_noq : mpz_div_qr_entail_wit_24_2_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_25_1_r_eq_n_q_done : mpz_div_qr_entail_wit_25_1_r_eq_n_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_25_2_r_eq_n_q_done : mpz_div_qr_entail_wit_25_2_r_eq_n_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_26_1_r_eq_n_noq : mpz_div_qr_entail_wit_26_1_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_26_2_r_eq_n_noq : mpz_div_qr_entail_wit_26_2_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_27_1_nonalias_q_rem : mpz_div_qr_entail_wit_27_1_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_27_2_r_eq_n_q_rem : mpz_div_qr_entail_wit_27_2_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_27_3_nonalias_noq_rem : mpz_div_qr_entail_wit_27_3_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_27_4_r_eq_n_noq_rem : mpz_div_qr_entail_wit_27_4_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_28_1_nonalias_q_rem : mpz_div_qr_entail_wit_28_1_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_28_2_r_eq_n_q_rem : mpz_div_qr_entail_wit_28_2_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_28_3_nonalias_noq_rem : mpz_div_qr_entail_wit_28_3_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_28_4_r_eq_n_noq_rem : mpz_div_qr_entail_wit_28_4_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_29_1_nonalias_q_rem : mpz_div_qr_entail_wit_29_1_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_29_2_r_eq_n_q_rem : mpz_div_qr_entail_wit_29_2_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_29_3_nonalias_noq_rem : mpz_div_qr_entail_wit_29_3_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_entail_wit_29_4_r_eq_n_noq_rem : mpz_div_qr_entail_wit_29_4_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_1_nonalias : mpz_div_qr_partial_solve_wit_1_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_2_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_2_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_3_nonalias : mpz_div_qr_partial_solve_wit_3_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_4_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_4_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_5_nonalias : mpz_div_qr_partial_solve_wit_5_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_6_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_6_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_7_nonalias : mpz_div_qr_partial_solve_wit_7_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_8_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_8_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_9_nonalias : mpz_div_qr_partial_solve_wit_9_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_10_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_10_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_11_nonalias : mpz_div_qr_partial_solve_wit_11_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_12_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_12_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_13_nonalias : mpz_div_qr_partial_solve_wit_13_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_14_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_14_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_15_nonalias : mpz_div_qr_partial_solve_wit_15_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_16_r_eq_n_read0_pure : mpz_div_qr_partial_solve_wit_16_r_eq_n_read0_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_16_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_16_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_17_nonalias : mpz_div_qr_partial_solve_wit_17_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_18_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_18_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_19_nonalias : mpz_div_qr_partial_solve_wit_19_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_20_nonalias : mpz_div_qr_partial_solve_wit_20_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_21_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_21_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_22_nonalias : mpz_div_qr_partial_solve_wit_22_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_23_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_23_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_24_nonalias : mpz_div_qr_partial_solve_wit_24_nonalias.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_25_r_eq_n_read0 : mpz_div_qr_partial_solve_wit_25_r_eq_n_read0.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_26_nonalias_q : mpz_div_qr_partial_solve_wit_26_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_27_r_eq_n_q : mpz_div_qr_partial_solve_wit_27_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_28_nonalias_q : mpz_div_qr_partial_solve_wit_28_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_29_r_eq_n_q : mpz_div_qr_partial_solve_wit_29_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_30_nonalias_q_pure : mpz_div_qr_partial_solve_wit_30_nonalias_q_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_30_nonalias_q : mpz_div_qr_partial_solve_wit_30_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_31_r_eq_n_q_pure : mpz_div_qr_partial_solve_wit_31_r_eq_n_q_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_31_r_eq_n_q : mpz_div_qr_partial_solve_wit_31_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_32_nonalias_noq_pure : mpz_div_qr_partial_solve_wit_32_nonalias_noq_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_32_nonalias_noq : mpz_div_qr_partial_solve_wit_32_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_33_r_eq_n_noq_pure : mpz_div_qr_partial_solve_wit_33_r_eq_n_noq_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_33_r_eq_n_noq : mpz_div_qr_partial_solve_wit_33_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_34_r_eq_n_noq_pure : mpz_div_qr_partial_solve_wit_34_r_eq_n_noq_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_34_r_eq_n_noq : mpz_div_qr_partial_solve_wit_34_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_35_nonalias_noq_pure : mpz_div_qr_partial_solve_wit_35_nonalias_noq_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_35_nonalias_noq : mpz_div_qr_partial_solve_wit_35_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_36_r_eq_n_q_pure : mpz_div_qr_partial_solve_wit_36_r_eq_n_q_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_36_r_eq_n_q : mpz_div_qr_partial_solve_wit_36_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_37_nonalias_q_pure : mpz_div_qr_partial_solve_wit_37_nonalias_q_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_37_nonalias_q : mpz_div_qr_partial_solve_wit_37_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_38_nonalias_q : mpz_div_qr_partial_solve_wit_38_nonalias_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_39_r_eq_n_q : mpz_div_qr_partial_solve_wit_39_r_eq_n_q.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_40_nonalias_q_done_pure : mpz_div_qr_partial_solve_wit_40_nonalias_q_done_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_40_nonalias_q_done : mpz_div_qr_partial_solve_wit_40_nonalias_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_41_r_eq_n_q_done_pure : mpz_div_qr_partial_solve_wit_41_r_eq_n_q_done_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_41_r_eq_n_q_done : mpz_div_qr_partial_solve_wit_41_r_eq_n_q_done.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_42_nonalias_noq_pure : mpz_div_qr_partial_solve_wit_42_nonalias_noq_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_42_nonalias_noq : mpz_div_qr_partial_solve_wit_42_nonalias_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_43_r_eq_n_noq_pure : mpz_div_qr_partial_solve_wit_43_r_eq_n_noq_pure.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_43_r_eq_n_noq : mpz_div_qr_partial_solve_wit_43_r_eq_n_noq.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_44_nonalias_q_rem : mpz_div_qr_partial_solve_wit_44_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_45_r_eq_n_q_rem : mpz_div_qr_partial_solve_wit_45_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_46_nonalias_q_rem : mpz_div_qr_partial_solve_wit_46_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_47_r_eq_n_q_rem : mpz_div_qr_partial_solve_wit_47_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_48_nonalias_q_rem : mpz_div_qr_partial_solve_wit_48_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_49_r_eq_n_q_rem : mpz_div_qr_partial_solve_wit_49_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_50_nonalias_q_rem : mpz_div_qr_partial_solve_wit_50_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_51_r_eq_n_q_rem : mpz_div_qr_partial_solve_wit_51_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_52_nonalias_noq_rem : mpz_div_qr_partial_solve_wit_52_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_53_r_eq_n_noq_rem : mpz_div_qr_partial_solve_wit_53_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_54_nonalias_q_rem : mpz_div_qr_partial_solve_wit_54_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_55_r_eq_n_q_rem : mpz_div_qr_partial_solve_wit_55_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_56_nonalias_noq_rem : mpz_div_qr_partial_solve_wit_56_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_57_r_eq_n_noq_rem : mpz_div_qr_partial_solve_wit_57_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_58_nonalias_q_rem : mpz_div_qr_partial_solve_wit_58_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_59_nonalias_noq_rem : mpz_div_qr_partial_solve_wit_59_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_60_nonalias_q_rem : mpz_div_qr_partial_solve_wit_60_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_61_r_eq_n_q_rem : mpz_div_qr_partial_solve_wit_61_r_eq_n_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_62_nonalias_noq_rem : mpz_div_qr_partial_solve_wit_62_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_63_r_eq_n_noq_rem : mpz_div_qr_partial_solve_wit_63_r_eq_n_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_64_nonalias_q_rem : mpz_div_qr_partial_solve_wit_64_nonalias_q_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_partial_solve_wit_65_nonalias_noq_rem : mpz_div_qr_partial_solve_wit_65_nonalias_noq_rem.
Proof. Admitted. 

Lemma proof_of_mpz_div_qr_which_implies_wit_1 : mpz_div_qr_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_safety_wit_1 : mpz_tdiv_r_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_safety_wit_2 : mpz_tdiv_r_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_entail_wit_2 : mpz_tdiv_r_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_partial_solve_wit_1_pure : mpz_tdiv_r_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mpz_tdiv_r_partial_solve_wit_1 : mpz_tdiv_r_partial_solve_wit_1.
Proof. Admitted. 

