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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i residue_values 0) - answer ) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_7 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i residue_values 0) - answer ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i residue_values 0) - answer )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i residue_values 0) - answer ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i residue_values 0) - answer )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i residue_values 0) - answer ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= ((Znth i residue_values 0) - answer )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_8 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i residue_values 0) - answer ) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_9 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i residue_values 0) - answer ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i residue_values 0) - answer )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i residue_values 0) - answer ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i residue_values 0) - answer )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_9_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((Znth i residue_values 0) - answer ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_9_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= ((Znth i residue_values 0) - answer )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_10 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH2 : (0 < retval)) (PreH3 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH4 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH5 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH6 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_11 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH2 : (0 < retval)) (PreH3 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH4 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH5 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH6 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH7 : (x_callee_v = 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_12 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_12_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_12_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_13 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_13_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_13_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_14 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_14_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_14_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_15 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_15_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_15_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_16 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_16_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_16_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_17 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_17_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_17_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_18 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + (retval * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + (retval * lcm ) )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + (retval * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + (retval * lcm ) )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_18_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + (retval * lcm ) ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_18_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (answer + (retval * lcm ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_19 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * lcm )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * lcm )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_19_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval * lcm ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_19_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (retval * lcm )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_20 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + (retval * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + (retval * lcm ) )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + (retval * lcm ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer + (retval * lcm ) )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_20_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((answer + (retval * lcm ) ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_20_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (answer + (retval * lcm ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_21 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * lcm )) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval * lcm ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * lcm )) ”
).

Definition extended_chinese_remainder_theorem_safety_wit_21_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((retval * lcm ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_21_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval_2 ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval )) (PreH5 : (retval >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval_2 ) ((Znth i modulus_values 0) ÷ retval_2 ) retval )) (PreH7 : (0 < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval_2)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval_2 ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval_2 ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (retval * lcm )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_22 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_23 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_24 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + (retval_2 * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_25 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
  **  ((( &( "lcm" ) )) # Int  |-> lcm)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + (retval_2 * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "gcd" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_26 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "lcm" ) )) # Int  |-> (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_27 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "lcm" ) )) # Int  |-> (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_28 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "lcm" ) )) # Int  |-> (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + (retval_2 * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition extended_chinese_remainder_theorem_safety_wit_29 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((( &( "lcm" ) )) # Int  |-> (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer + (retval_2 * lcm ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "residues" ) )) # Ptr  |-> residues_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "combined_modulus" ) )) # Ptr  |-> combined_modulus_pre)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition extended_chinese_remainder_theorem_entail_wit_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
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
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values 1 (Znth 0 residue_values 0) (Znth 0 modulus_values 0) ) ” 
  &&  “ ((Znth 0 modulus_values 0) <= INT_MAX) ” 
  &&  “ (0 < (Znth 0 modulus_values 0)) ” 
  &&  “ ((Znth 0 residue_values 0) < (Znth 0 modulus_values 0)) ” 
  &&  “ (0 <= (Znth 0 residue_values 0)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  (CRTPrefixMeaning residue_values modulus_values 1 (Znth 0 residue_values 0) (Znth 0 modulus_values 0) )
.

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  ((Znth 0 modulus_values 0) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  (0 < (Znth 0 modulus_values 0))
.

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  ((Znth 0 residue_values 0) < (Znth 0 modulus_values 0))
.

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_5 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  (0 <= (Znth 0 residue_values 0))
.

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_6 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))
.

Definition extended_chinese_remainder_theorem_entail_wit_1_split_goal_7 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count_2: Z) , (((1 <= count_2) /\ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2: Z) , (((1 <= index_2) /\ (index_2 < n_pre)) -> ((2 * ((Znth (index_2) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))
.

Definition extended_chinese_remainder_theorem_entail_wit_2_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 ) ” 
  &&  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  ((( &( "x" ) )) # Int  |-> (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))
.

Definition extended_chinese_remainder_theorem_entail_wit_2_2 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "x" ) )) # Int  |-> (retval_3 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= (retval_3 + ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ ((retval_3 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_3 + ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ (retval_3 < 0) ” 
  &&  “ (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 ) ” 
  &&  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) = 0) ” 
  &&  “ (x_callee_v_2 = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  ((( &( "x" ) )) # Int  |-> (retval_3 + ((Znth i modulus_values 0) ÷ retval ) ))
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_3 + ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (0 <= (retval_3 + ((Znth i modulus_values 0) ÷ retval ) )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_3 + ((Znth i modulus_values 0) ÷ retval ) ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_2_2_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (0 <= (retval_3 + ((Znth i modulus_values 0) ÷ retval ) ))
.

Definition extended_chinese_remainder_theorem_entail_wit_2_3 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "x" ) )) # Int  |-> retval_2)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 ) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 ) ” 
  &&  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  ((( &( "x" ) )) # Int  |-> retval_2)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 ) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (retval_2 < ((Znth i modulus_values 0) ÷ retval )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_2_3_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )
.

Definition extended_chinese_remainder_theorem_entail_wit_2_3_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_2_3_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (retval_2 < ((Znth i modulus_values 0) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_2_4 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "x" ) )) # Int  |-> retval_3)
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_3 ) ” 
  &&  “ (retval_3 >= 0) ” 
  &&  “ (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 ) ” 
  &&  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) = 0) ” 
  &&  “ (x_callee_v_2 = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  ((( &( "x" ) )) # Int  |-> retval_3)
  **  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_3 ) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (retval_3 < ((Znth i modulus_values 0) ÷ retval )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_2_4_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_3 )
.

Definition extended_chinese_remainder_theorem_entail_wit_2_4_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)
.

Definition extended_chinese_remainder_theorem_entail_wit_2_4_split_goal_3 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (ModularMul x_callee_v_2 (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_3 )) (PreH3 : (0 < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH5 : (((lcm * x_callee_v_2 ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH6 : ((Zabs (x_callee_v_2)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH7 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH8 : (x_callee_v_2 = 0)) (PreH9 : (i < n_pre)) (PreH10 : (Forall (Z.lt (0)) modulus_values )) (PreH11 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH12 : (Forall (Z.le (0)) residue_values )) (PreH13 : (Forall2 Z.lt residue_values modulus_values )) (PreH14 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer < lcm)) (PreH21 : (0 < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (retval_3 < ((Znth i modulus_values 0) ÷ retval ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ” 
  &&  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ (0 < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) )) ” 
  &&  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ (0 < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ))) (PreH2 : ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) (retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) )) (PreH5 : (retval_2 < 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((answer + ((retval_2 + ((Znth i modulus_values 0) ÷ retval ) ) * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_3 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (answer + (retval_2 * lcm ) )) ” 
  &&  “ ((answer + (retval_2 * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ (0 < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (retval_2 * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (retval_2 * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ ((answer + (retval_2 * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_3_3_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (retval_2 * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_3_3_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (Forall (Z.lt (0)) modulus_values )) (PreH14 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH15 : (Forall (Z.le (0)) residue_values )) (PreH16 : (Forall2 Z.lt residue_values modulus_values )) (PreH17 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= answer)) (PreH23 : (answer < lcm)) (PreH24 : (0 < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((answer + (retval_2 * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
.

Definition extended_chinese_remainder_theorem_entail_wit_3_4 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (answer + (retval_2 * lcm ) )) ” 
  &&  “ ((answer + (retval_2 * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ (0 < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ” 
  &&  “ ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (retval_2 * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (retval_2 * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) ) ” 
  &&  “ ((answer + (retval_2 * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) )) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_entail_wit_3_4_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1 ) (answer + (retval_2 * lcm ) ) (lcm * ((Znth i modulus_values 0) ÷ retval ) ) )
.

Definition extended_chinese_remainder_theorem_entail_wit_3_4_split_goal_2 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < ((Znth i modulus_values 0) ÷ retval ))) (PreH3 : ((lcm * ((Znth i modulus_values 0) ÷ retval ) ) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) (0)) (Znth (i) (modulus_values) (0)) retval_2 )) (PreH5 : (retval_2 >= 0)) (PreH6 : (ModularMul x_callee_v (((Znth i residue_values 0) - answer ) ÷ retval ) ((Znth i modulus_values 0) ÷ retval ) retval_2 )) (PreH7 : (0 < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH9 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH10 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH11 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH12 : (x_callee_v = 0)) (PreH13 : (i < n_pre)) (PreH14 : (Forall (Z.lt (0)) modulus_values )) (PreH15 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH16 : (Forall (Z.le (0)) residue_values )) (PreH17 : (Forall2 Z.lt residue_values modulus_values )) (PreH18 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= answer)) (PreH24 : (answer < lcm)) (PreH25 : (0 < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  ((answer + (retval_2 * lcm ) ) < (lcm * ((Znth i modulus_values 0) ÷ retval ) ))
.

Definition extended_chinese_remainder_theorem_return_wit_1 := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer < lcm)) (PreH13 : (0 < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer < lcm)) (PreH13 : (0 < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  TT && emp 
|--
  “ (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm ) ”
  &&  emp
).

Definition extended_chinese_remainder_theorem_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer < lcm)) (PreH13 : (0 < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm )
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ”
  &&  (((residues_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 residue_values 0))
  **  (IntArray.missing_i residues_pre 0 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ”
  &&  (((moduli_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 modulus_values 0))
  **  (IntArray.missing_i moduli_pre 0 0 n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_3 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer < lcm)) (PreH13 : (0 < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer < lcm)) (PreH13 : (0 < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (Forall (Z.lt (0)) modulus_values )) (PreH10 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH11 : (Forall (Z.le (0)) residue_values )) (PreH12 : (Forall2 Z.lt residue_values modulus_values )) (PreH13 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer < lcm)) (PreH20 : (0 < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (Forall (Z.lt (0)) modulus_values )) (PreH3 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH4 : (Forall (Z.le (0)) residue_values )) (PreH5 : (Forall2 Z.lt residue_values modulus_values )) (PreH6 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer < lcm)) (PreH13 : (0 < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full moduli_pre n_pre modulus_values )
  **  (IntArray.full residues_pre n_pre residue_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ ((Znth i modulus_values 0) <= INT_MAX) ” 
  &&  “ (0 < (Znth i modulus_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
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
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
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

Definition extended_chinese_remainder_theorem_partial_solve_wit_7 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth i residue_values 0))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_pure := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH21 : (i < n_pre)) (PreH22 : (Forall (Z.lt (0)) modulus_values )) (PreH23 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH24 : (Forall (Z.le (0)) residue_values )) (PreH25 : (Forall2 Z.lt residue_values modulus_values )) (PreH26 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= answer)) (PreH32 : (answer < lcm)) (PreH33 : (0 < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ” 
  &&  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ”
).

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH21 : (i < n_pre)) (PreH22 : (Forall (Z.lt (0)) modulus_values )) (PreH23 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH24 : (Forall (Z.le (0)) residue_values )) (PreH25 : (Forall2 Z.lt residue_values modulus_values )) (PreH26 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= answer)) (PreH32 : (answer < lcm)) (PreH33 : (0 < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH21 : (i < n_pre)) (PreH22 : (Forall (Z.lt (0)) modulus_values )) (PreH23 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH24 : (Forall (Z.le (0)) residue_values )) (PreH25 : (Forall2 Z.lt residue_values modulus_values )) (PreH26 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= answer)) (PreH32 : (answer < lcm)) (PreH33 : (0 < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_3 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH21 : (i < n_pre)) (PreH22 : (Forall (Z.lt (0)) modulus_values )) (PreH23 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH24 : (Forall (Z.le (0)) residue_values )) (PreH25 : (Forall2 Z.lt residue_values modulus_values )) (PreH26 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= answer)) (PreH32 : (answer < lcm)) (PreH33 : (0 < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_4 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH21 : (i < n_pre)) (PreH22 : (Forall (Z.lt (0)) modulus_values )) (PreH23 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH24 : (Forall (Z.le (0)) residue_values )) (PreH25 : (Forall2 Z.lt residue_values modulus_values )) (PreH26 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= answer)) (PreH32 : (answer < lcm)) (PreH33 : (0 < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_5 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH21 : (i < n_pre)) (PreH22 : (Forall (Z.lt (0)) modulus_values )) (PreH23 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH24 : (Forall (Z.le (0)) residue_values )) (PreH25 : (Forall2 Z.lt residue_values modulus_values )) (PreH26 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= answer)) (PreH32 : (answer < lcm)) (PreH33 : (0 < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_6 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH21 : (i < n_pre)) (PreH22 : (Forall (Z.lt (0)) modulus_values )) (PreH23 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH24 : (Forall (Z.le (0)) residue_values )) (PreH25 : (Forall2 Z.lt residue_values modulus_values )) (PreH26 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= answer)) (PreH32 : (answer < lcm)) (PreH33 : (0 < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8_aux := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (Forall (Z.lt (0)) modulus_values )) (PreH8 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH9 : (Forall (Z.le (0)) residue_values )) (PreH10 : (Forall2 Z.lt residue_values modulus_values )) (PreH11 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer < lcm)) (PreH18 : (0 < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ” 
  &&  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_8 := extended_chinese_remainder_theorem_partial_solve_wit_8_pure -> extended_chinese_remainder_theorem_partial_solve_wit_8_aux.

Definition extended_chinese_remainder_theorem_partial_solve_wit_9 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
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
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int  |-> (Znth i residue_values 0))
  **  (IntArray.missing_i residues_pre i 0 n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure := 
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0) ”
) \/
(
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ” 
  &&  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0) ”
).

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_1 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_2 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_3 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_4 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_5 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_6 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_7 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_8 := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_callee_v <= INT_MAX)) (PreH6 : (x_callee_v <= INT_MAX)) (PreH7 : (((Znth i modulus_values 0) ÷ retval ) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_callee_v >= INT_MIN)) (PreH14 : (x_callee_v >= INT_MIN)) (PreH15 : (((Znth i modulus_values 0) ÷ retval ) >= INT_MIN)) (PreH16 : (0 < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH18 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH19 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH20 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH21 : (x_callee_v = 0)) (PreH22 : (i < n_pre)) (PreH23 : (Forall (Z.lt (0)) modulus_values )) (PreH24 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH25 : (Forall (Z.le (0)) residue_values )) (PreH26 : (Forall2 Z.lt residue_values modulus_values )) (PreH27 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (0 <= answer)) (PreH33 : (answer < lcm)) (PreH34 : (0 < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((( &( "reduced_modulus" ) )) # Int  |-> ((Znth i modulus_values 0) ÷ retval ))
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
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0) ”
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10_aux := 
forall (combined_modulus_pre: Z) (moduli_pre: Z) (residues_pre: Z) (n_pre: Z) (modulus_values: (@list Z)) (residue_values: (@list Z)) (lcm: Z) (answer: Z) (i: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (0 < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values 0))))) (PreH3 : (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval ))) (PreH5 : ((lcm % ( (Znth i modulus_values 0) ) ) = 0)) (PreH6 : (x_callee_v = 0)) (PreH7 : (i < n_pre)) (PreH8 : (Forall (Z.lt (0)) modulus_values )) (PreH9 : (Forall (Z.ge (INT_MAX)) modulus_values )) (PreH10 : (Forall (Z.le (0)) residue_values )) (PreH11 : (Forall2 Z.lt residue_values modulus_values )) (PreH12 : forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre )) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer < lcm)) (PreH19 : (0 < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm )) ,
  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
|--
  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < x_callee_v) ” 
  &&  “ (x_callee_v < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i modulus_values 0) ÷ retval ) * 2 ) <= INT_MAX) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((((Znth i residue_values 0) - answer ) ÷ retval ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (((Znth i residue_values 0) - answer ) ÷ retval )) ” 
  &&  “ (0 < ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((0 - ((Znth i modulus_values 0) ÷ retval ) ) < 0) ” 
  &&  “ (0 < retval) ” 
  &&  “ (retval = (Zgcd (lcm) ((Znth i modulus_values 0)))) ” 
  &&  “ (((lcm * x_callee_v ) + ((Znth i modulus_values 0) * y_callee_v ) ) = retval) ” 
  &&  “ ((Zabs (x_callee_v)) <= ((Znth i modulus_values 0) ÷ retval )) ” 
  &&  “ ((lcm % ( (Znth i modulus_values 0) ) ) = 0) ” 
  &&  “ (x_callee_v = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (Forall (Z.lt (0)) modulus_values ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) modulus_values ) ” 
  &&  “ (Forall (Z.le (0)) residue_values ) ” 
  &&  “ (Forall2 Z.lt residue_values modulus_values ) ” 
  &&  “ forall (count: Z) , (((1 <= count) /\ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” 
  &&  “ forall (index: Z) , (((1 <= index) /\ (index < n_pre)) -> ((2 * ((Znth (index) (modulus_values) (0)) ÷ (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) (0)))) ) ) <= INT_MAX)) ” 
  &&  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer < lcm) ” 
  &&  “ (0 < lcm) ” 
  &&  “ (lcm <= INT_MAX) ” 
  &&  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm ) ”
  &&  (IntArray.full residues_pre n_pre residue_values )
  **  (IntArray.full moduli_pre n_pre modulus_values )
  **  ((combined_modulus_pre) # Int  |->_)
.

Definition extended_chinese_remainder_theorem_partial_solve_wit_10 := extended_chinese_remainder_theorem_partial_solve_wit_10_pure -> extended_chinese_remainder_theorem_partial_solve_wit_10_aux.

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
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_14 : extended_chinese_remainder_theorem_safety_wit_14.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_15 : extended_chinese_remainder_theorem_safety_wit_15.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_16 : extended_chinese_remainder_theorem_safety_wit_16.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_17 : extended_chinese_remainder_theorem_safety_wit_17.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_18 : extended_chinese_remainder_theorem_safety_wit_18.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_19 : extended_chinese_remainder_theorem_safety_wit_19.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_20 : extended_chinese_remainder_theorem_safety_wit_20.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_21 : extended_chinese_remainder_theorem_safety_wit_21.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_22 : extended_chinese_remainder_theorem_safety_wit_22.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_23 : extended_chinese_remainder_theorem_safety_wit_23.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_24 : extended_chinese_remainder_theorem_safety_wit_24.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_25 : extended_chinese_remainder_theorem_safety_wit_25.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_26 : extended_chinese_remainder_theorem_safety_wit_26.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_27 : extended_chinese_remainder_theorem_safety_wit_27.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_28 : extended_chinese_remainder_theorem_safety_wit_28.
Axiom proof_of_extended_chinese_remainder_theorem_safety_wit_29 : extended_chinese_remainder_theorem_safety_wit_29.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_2_1 : extended_chinese_remainder_theorem_entail_wit_2_1.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_2_2 : extended_chinese_remainder_theorem_entail_wit_2_2.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_2_3 : extended_chinese_remainder_theorem_entail_wit_2_3.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_2_4 : extended_chinese_remainder_theorem_entail_wit_2_4.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_3_3 : extended_chinese_remainder_theorem_entail_wit_3_3.
Axiom proof_of_extended_chinese_remainder_theorem_entail_wit_3_4 : extended_chinese_remainder_theorem_entail_wit_3_4.
Axiom proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_1 : extended_chinese_remainder_theorem_partial_solve_wit_1.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_2 : extended_chinese_remainder_theorem_partial_solve_wit_2.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_3 : extended_chinese_remainder_theorem_partial_solve_wit_3.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4 : extended_chinese_remainder_theorem_partial_solve_wit_4.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_5 : extended_chinese_remainder_theorem_partial_solve_wit_5.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_6 : extended_chinese_remainder_theorem_partial_solve_wit_6.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_7 : extended_chinese_remainder_theorem_partial_solve_wit_7.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_8_pure : extended_chinese_remainder_theorem_partial_solve_wit_8_pure.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_8 : extended_chinese_remainder_theorem_partial_solve_wit_8.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_9 : extended_chinese_remainder_theorem_partial_solve_wit_9.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_10_pure : extended_chinese_remainder_theorem_partial_solve_wit_10_pure.
Axiom proof_of_extended_chinese_remainder_theorem_partial_solve_wit_10 : extended_chinese_remainder_theorem_partial_solve_wit_10.

End VC_Correct.
