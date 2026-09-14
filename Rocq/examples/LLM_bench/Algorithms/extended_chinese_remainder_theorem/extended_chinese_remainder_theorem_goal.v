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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib.
Require Import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib.
Local Open Scope sac.

(*----- Function extended_chinese_remainder_theorem -----*)

Definition extended_chinese_remainder_theorem_safety_wit_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  ((( &( "lcm" ) )) # Int  |->_)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((( &( "answer" ) )) # Int  |-> (Znth 0 residue_values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_3 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "lcm" ) )) # Int  |-> (Znth 0 modulus_values 0))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((( &( "answer" ) )) # Int  |-> (Znth 0 residue_values 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_4 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_callee_v)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i modulus_values 0) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_5 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_callee_v)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i modulus_values 0) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_6 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (0 <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH13 : (0 < gcd)) (PreH14 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH15 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH16 : (0 < reduced_modulus)) (PreH17 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH18 : ((0 - reduced_modulus ) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH21 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth (i) (residue_values) (0)) - answer ) <> (INT_MIN)) \/ (gcd <> (-1))) ” 
  &&  “ (gcd <> 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_7 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (0 <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH13 : (0 < gcd)) (PreH14 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH15 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH16 : (0 < reduced_modulus)) (PreH17 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH18 : ((0 - reduced_modulus ) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH21 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth (i) (residue_values) (0)) - answer ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i) (residue_values) (0)) - answer )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (0 <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH13 : (0 < gcd)) (PreH14 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH15 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH16 : (0 < reduced_modulus)) (PreH17 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH18 : ((0 - reduced_modulus ) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH21 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth (i) (residue_values) (0)) - answer ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i) (residue_values) (0)) - answer )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (0 <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH13 : (0 < gcd)) (PreH14 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH15 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH16 : (0 < reduced_modulus)) (PreH17 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH18 : ((0 - reduced_modulus ) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH21 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth (i) (residue_values) (0)) - answer ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (0 <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH13 : (0 < gcd)) (PreH14 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH15 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH16 : (0 < reduced_modulus)) (PreH17 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH18 : ((0 - reduced_modulus ) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH21 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= ((Znth (i) (residue_values) (0)) - answer )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_8 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH5 : (0 <= i)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= answer)) (PreH9 : (answer < lcm)) (PreH10 : (0 < lcm)) (PreH11 : (lcm <= INT_MAX)) (PreH12 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH13 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH14 : (0 < gcd)) (PreH15 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH16 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH17 : (0 < reduced_modulus)) (PreH18 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH19 : ((0 - reduced_modulus ) < x)) (PreH20 : (x < reduced_modulus)) (PreH21 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH22 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (IntArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_9 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (IntArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval + reduced_modulus ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + reduced_modulus )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_10 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((answer + (x * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + (x * lcm ) )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((answer + (x * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + (x * lcm ) )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((answer + (x * lcm ) ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((INT_MIN) <= (answer + (x * lcm ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_11 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((x * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x * lcm )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((x * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x * lcm )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((x * lcm ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((INT_MIN) <= (x * lcm )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_12 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + (x * lcm ) ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
|--
  “ ((lcm * reduced_modulus ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lcm * reduced_modulus )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_13 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + (x * lcm ) ))
  **  ((( &( "lcm" ) )) # Int  |-> (lcm * reduced_modulus ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition extended_chinese_remainder_theorem_entail_wit_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (1 <= n_pre)
.

Definition extended_chinese_remainder_theorem_entail_wit_2 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= (Znth 0 residue_values 0)) ” 
  &&  “ ((Znth 0 residue_values 0) < (Znth 0 modulus_values 0)) ” 
  &&  “ (0 < (Znth 0 modulus_values 0)) ” 
  &&  “ ((Znth 0 modulus_values 0) <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values 1 (Znth 0 residue_values 0) (Znth 0 modulus_values 0) ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values 1 (Znth 0 residue_values 0) (Znth 0 modulus_values 0) ) ” 
  &&  “ ((Znth 0 modulus_values 0) <= INT_MAX) ” 
  &&  “ (0 < (Znth 0 modulus_values 0)) ” 
  &&  “ ((Znth 0 residue_values 0) < (Znth 0 modulus_values 0)) ” 
  &&  “ (0 <= (Znth 0 residue_values 0)) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (CRTPrefixMeaning residue_values modulus_values 1 (Znth 0 residue_values 0) (Znth 0 modulus_values 0) )
.

Definition extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  ((Znth 0 modulus_values 0) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (0 < (Znth 0 modulus_values 0))
.

Definition extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  ((Znth 0 residue_values 0) < (Znth 0 modulus_values 0))
.

Definition extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (0 <= (Znth 0 residue_values 0))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) (0))))) ” 
  &&  “ (0 < retval) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth (i) (modulus_values) (0)) * y_callee_v ) ) = retval) ” 
  &&  “ (((Znth i modulus_values 0) ÷ retval ) = ((Znth (i) (modulus_values) (0)) ÷ retval )) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ retval )) ” 
  &&  “ ((((Znth (i) (residue_values) (0)) - answer ) ÷ retval ) <= INT_MAX) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ ((((Znth (i) (residue_values) (0)) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ retval )) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth (i) (modulus_values) (0)) * y_callee_v ) ) = retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) (0))))) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((((Znth (i) (residue_values) (0)) - answer ) ÷ retval ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (x_callee_v < ((Znth i modulus_values 0) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (0 < ((Znth i modulus_values 0) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (((lcm * x_callee_v ) + ((Znth (i) (modulus_values) (0)) * y_callee_v ) ) = retval)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) (0))))) ” 
  &&  “ (0 < retval) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth (i) (modulus_values) (0)) * y_callee_v ) ) = retval) ” 
  &&  “ (((Znth i modulus_values 0) ÷ retval ) = ((Znth (i) (modulus_values) (0)) ÷ retval )) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ retval )) ” 
  &&  “ ((((Znth (i) (residue_values) (0)) - answer ) ÷ retval ) <= INT_MAX) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ ((((Znth (i) (residue_values) (0)) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ retval )) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ (((lcm * 0 ) + ((Znth (i) (modulus_values) (0)) * y_callee_v ) ) = retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) (0))))) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((((Znth (i) (residue_values) (0)) - answer ) ÷ retval ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (0 < ((Znth i modulus_values 0) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (0 < ((Znth i modulus_values 0) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (((lcm * 0 ) + ((Znth (i) (modulus_values) (0)) * y_callee_v ) ) = retval)
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))
.

Definition extended_chinese_remainder_theorem_entail_wit_4_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (IntArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) )
  **  ((( &( "y" ) )) # Int  |-> y)
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ” 
  &&  “ (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0))))) ” 
  &&  “ (0 < gcd) ” 
  &&  “ (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd )) ” 
  &&  “ (0 < reduced_modulus) ” 
  &&  “ (reduced_modulus <= INT_MAX) ” 
  &&  “ (0 <= (retval + reduced_modulus )) ” 
  &&  “ ((retval + reduced_modulus ) < reduced_modulus) ” 
  &&  “ (0 < (lcm * reduced_modulus )) ” 
  &&  “ ((lcm * reduced_modulus ) <= INT_MAX) ” 
  &&  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval + reduced_modulus ) ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval + reduced_modulus ) ) ” 
  &&  “ ((lcm * reduced_modulus ) <= INT_MAX) ” 
  &&  “ (0 <= (retval + reduced_modulus )) ” 
  &&  “ ((replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) = residue_values) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval + reduced_modulus ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((lcm * reduced_modulus ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (0 <= (retval + reduced_modulus ))
.

Definition extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) = residue_values)
.

Definition extended_chinese_remainder_theorem_entail_wit_4_2 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (IntArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) )
  **  ((( &( "y" ) )) # Int  |-> y)
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ” 
  &&  “ (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0))))) ” 
  &&  “ (0 < gcd) ” 
  &&  “ (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd )) ” 
  &&  “ (0 < reduced_modulus) ” 
  &&  “ (reduced_modulus <= INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < reduced_modulus) ” 
  &&  “ (0 < (lcm * reduced_modulus )) ” 
  &&  “ ((lcm * reduced_modulus ) <= INT_MAX) ” 
  &&  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval ) ” 
  &&  “ ((lcm * reduced_modulus ) <= INT_MAX) ” 
  &&  “ (retval < reduced_modulus) ” 
  &&  “ ((replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) = residue_values) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )
.

Definition extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((lcm * reduced_modulus ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (retval < reduced_modulus)
.

Definition extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (ModularMul x (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) reduced_modulus retval )) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH6 : (0 <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer < lcm)) (PreH11 : (0 < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH15 : (0 < gcd)) (PreH16 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH17 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH18 : (0 < reduced_modulus)) (PreH19 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH20 : ((0 - reduced_modulus ) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH23 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((replace_Znth (i) ((Znth (i) (residue_values) (0))) (residue_values)) = residue_values)
.

Definition extended_chinese_remainder_theorem_entail_wit_5 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (answer + (x * lcm ) )) ” 
  &&  “ ((answer + (x * lcm ) ) < (lcm * reduced_modulus )) ” 
  &&  “ (0 < (lcm * reduced_modulus )) ” 
  &&  “ ((lcm * reduced_modulus ) <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (x * lcm ) ) (lcm * reduced_modulus ) ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (x * lcm ) ) (lcm * reduced_modulus ) ) ” 
  &&  “ ((answer + (x * lcm ) ) < (lcm * reduced_modulus )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (x * lcm ) ) (lcm * reduced_modulus ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (reduced_modulus: Z) (x: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= answer)) (PreH7 : (answer < lcm)) (PreH8 : (0 < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH12 : (0 < gcd)) (PreH13 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH14 : (0 < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : (0 <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : (0 < (lcm * reduced_modulus ))) (PreH19 : ((lcm * reduced_modulus ) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) x )) ,
  ((answer + (x * lcm ) ) < (lcm * reduced_modulus ))
.

Definition extended_chinese_remainder_theorem_return_wit_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |-> lcm)
|--
  EX (combined_modulus_pre_v: Z) ,
  “ (ExtendedCRTSystemResult residue_values modulus_values n_pre answer combined_modulus_pre_v ) ”
  &&  ((combined_modulus_pre) # Int  |-> combined_modulus_pre_v)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm ) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm )
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ”
  &&  (((residues_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 residue_values 0))
  **  (IntArray.missing_i residues_pre 0 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ”
  &&  (((moduli_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 modulus_values 0))
  **  (IntArray.missing_i moduli_pre 0 0 n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_3 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (i < n_pre) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int  |-> (Znth i modulus_values 0))
  **  (IntArray.missing_i moduli_pre i 0 n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_4_pure := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "gcd" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ ((Znth i modulus_values 0) <= INT_MAX) ” 
  &&  “ (0 < (Znth i modulus_values 0)) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH11 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer < lcm)) (PreH16 : (0 < lcm)) (PreH17 : (lcm <= INT_MAX)) (PreH18 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "gcd" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < (Znth i modulus_values 0)) ” 
  &&  “ ((Znth i modulus_values 0) <= INT_MAX) ”
).

Definition extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH11 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer < lcm)) (PreH16 : (0 < lcm)) (PreH17 : (lcm <= INT_MAX)) (PreH18 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "gcd" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < (Znth i modulus_values 0)) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH11 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer < lcm)) (PreH16 : (0 < lcm)) (PreH17 : (lcm <= INT_MAX)) (PreH18 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "gcd" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((Znth i modulus_values 0) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_4_aux := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ ((Znth i modulus_values 0) <= INT_MAX) ” 
  &&  “ (0 < (Znth i modulus_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_4 := extended_chinese_remainder_theorem_partial_solve_wit_4_pure -> extended_chinese_remainder_theorem_partial_solve_wit_4_aux.

Definition extended_chinese_remainder_theorem_partial_solve_wit_5 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer < lcm)) (PreH14 : (0 < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int  |-> (Znth i modulus_values 0))
  **  (IntArray.missing_i moduli_pre i 0 n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_6 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer < lcm)) (PreH15 : (0 < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) = 0) ” 
  &&  “ (x_callee_v = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int  |-> (Znth i modulus_values 0))
  **  (IntArray.missing_i moduli_pre i 0 n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_7_pure := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (0 <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH13 : (0 < gcd)) (PreH14 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH15 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH16 : (0 < reduced_modulus)) (PreH17 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH18 : ((0 - reduced_modulus ) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH21 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "gcd" ) )) # Int  |-> gcd)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> reduced_modulus)
  **  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - reduced_modulus ) < x) ” 
  &&  “ (x < reduced_modulus) ” 
  &&  “ (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd )) ” 
  &&  “ ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX) ” 
  &&  “ (0 < reduced_modulus) ” 
  &&  “ ((reduced_modulus * 2 ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_7_aux := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (i: Z) (answer: Z) (lcm: Z) (gcd: Z) (x: Z) (y: Z) (reduced_modulus: Z) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre )) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre )) (PreH4 : (0 <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= answer)) (PreH8 : (answer < lcm)) (PreH9 : (0 < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0)))))) (PreH13 : (0 < gcd)) (PreH14 : (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd)) (PreH15 : (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd ))) (PreH16 : (0 < reduced_modulus)) (PreH17 : ((reduced_modulus * 2 ) <= INT_MAX)) (PreH18 : ((0 - reduced_modulus ) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ))) (PreH21 : ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX)) ,
  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - reduced_modulus ) < x) ” 
  &&  “ (x < reduced_modulus) ” 
  &&  “ (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd )) ” 
  &&  “ ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX) ” 
  &&  “ (0 < reduced_modulus) ” 
  &&  “ ((reduced_modulus * 2 ) <= INT_MAX) ” 
  &&  “ (ExtendedCRTInputs residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (ExtendedCRTIntSafe modulus_values n_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ” 
  &&  “ (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) (0))))) ” 
  &&  “ (0 < gcd) ” 
  &&  “ (((lcm * x ) + ((Znth (i) (modulus_values) (0)) * y ) ) = gcd) ” 
  &&  “ (reduced_modulus = ((Znth (i) (modulus_values) (0)) ÷ gcd )) ” 
  &&  “ (0 < reduced_modulus) ” 
  &&  “ ((reduced_modulus * 2 ) <= INT_MAX) ” 
  &&  “ ((0 - reduced_modulus ) < x) ” 
  &&  “ (x < reduced_modulus) ” 
  &&  “ (INT_MIN < (((Znth (i) (residue_values) (0)) - answer ) ÷ gcd )) ” 
  &&  “ ((((Znth (i) (residue_values) (0)) - answer ) ÷ gcd ) <= INT_MAX) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i) (residue_values) (0)))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_7 := extended_chinese_remainder_theorem_partial_solve_wit_7_pure -> extended_chinese_remainder_theorem_partial_solve_wit_7_aux.

Module Type VC_Correct.


Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_1 : extended_chinese_remainder_theorem_safety_wit_1.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_2 : extended_chinese_remainder_theorem_safety_wit_2.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_3 : extended_chinese_remainder_theorem_safety_wit_3.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_4 : extended_chinese_remainder_theorem_safety_wit_4.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_5 : extended_chinese_remainder_theorem_safety_wit_5.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_6 : extended_chinese_remainder_theorem_safety_wit_6.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_8 : extended_chinese_remainder_theorem_safety_wit_8.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_9 : extended_chinese_remainder_theorem_safety_wit_9.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_10 : extended_chinese_remainder_theorem_safety_wit_10.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_11 : extended_chinese_remainder_theorem_safety_wit_11.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_12 : extended_chinese_remainder_theorem_safety_wit_12.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_13 : extended_chinese_remainder_theorem_safety_wit_13.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_2 : extended_chinese_remainder_theorem_entail_wit_2.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_4_1 : extended_chinese_remainder_theorem_entail_wit_4_1.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_4_2 : extended_chinese_remainder_theorem_entail_wit_4_2.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_5 : extended_chinese_remainder_theorem_entail_wit_5.
Axiom proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_1 : extended_chinese_remainder_theorem_partial_solve_wit_1.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_2 : extended_chinese_remainder_theorem_partial_solve_wit_2.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_3 : extended_chinese_remainder_theorem_partial_solve_wit_3.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4 : extended_chinese_remainder_theorem_partial_solve_wit_4.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_5 : extended_chinese_remainder_theorem_partial_solve_wit_5.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_6 : extended_chinese_remainder_theorem_partial_solve_wit_6.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_7_pure : extended_chinese_remainder_theorem_partial_solve_wit_7_pure.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_7 : extended_chinese_remainder_theorem_partial_solve_wit_7.

End VC_Correct.
