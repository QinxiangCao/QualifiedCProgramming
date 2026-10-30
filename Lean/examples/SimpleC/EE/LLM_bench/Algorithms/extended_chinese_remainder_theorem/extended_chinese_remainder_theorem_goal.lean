import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance extended_chinese_remainder_theorem_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def extended_chinese_remainder_theorem_safety_wit_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  ((( &( "lcm" ) )) # Int |->_)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((( &( "answer" ) )) # Int |-> ((Znth (0 : Int) residue_values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "lcm" ) )) # Int |-> ((Znth (0 : Int) modulus_values (0 : Int))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((( &( "answer" ) )) # Int |-> ((Znth (0 : Int) residue_values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_4 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i modulus_values (0 : Int)) ≠ (INT_MIN)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_5 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i modulus_values (0 : Int)) ≠ (INT_MIN)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_6 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((((Znth i residue_values (0 : Int)) - answer) ≠ (INT_MIN)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_7 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i residue_values (0 : Int)) - answer) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i residue_values (0 : Int)) - answer)) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i residue_values (0 : Int)) - answer) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i residue_values (0 : Int)) - answer)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i residue_values (0 : Int)) - answer) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= ((Znth i residue_values (0 : Int)) - answer)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_8 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((((Znth i residue_values (0 : Int)) - answer) ≠ (INT_MIN)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_9 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i residue_values (0 : Int)) - answer) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i residue_values (0 : Int)) - answer)) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i residue_values (0 : Int)) - answer) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i residue_values (0 : Int)) - answer)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_9_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i residue_values (0 : Int)) - answer) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_9_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= ((Znth i residue_values (0 : Int)) - answer)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_10 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH2 : ((0 : Int) < retval)) (PreH3 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH4 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH5 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH6 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_11 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH2 : ((0 : Int) < retval)) (PreH3 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH4 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH5 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH6 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH7 : (x_v = (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_12 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_12_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_12_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_13 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_13_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_13_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_14 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_14_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_14_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_15 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_15_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_15_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_16 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_16_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_16_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_17 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_17_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_17_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_18 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + (retval * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + (retval * lcm))) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + (retval * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + (retval * lcm))) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_18_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + (retval * lcm)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_18_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (answer + (retval * lcm))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_19 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval * lcm)) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval * lcm)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_19_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval * lcm) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_19_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (retval * lcm)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_20 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + (retval * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + (retval * lcm))) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + (retval * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + (retval * lcm))) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_20_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((answer + (retval * lcm)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_20_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (answer + (retval * lcm))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_21 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval * lcm)) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval * lcm)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_21_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval * lcm) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_21_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval_2 : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval_2)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)) (PreH5 : (retval >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval_2) (Z.quot (Znth i modulus_values (0 : Int)) retval_2) retval)) (PreH7 : ((0 : Int) < retval_2)) (PreH8 : (retval_2 = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval_2)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval_2))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval_2)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval_2))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= (retval * lcm)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_22 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_23 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_24 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + (retval_2 * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_25 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + (retval_2 * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_26 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "lcm" ) )) # Int |-> ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_27 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "lcm" ) )) # Int |-> ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_28 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "lcm" ) )) # Int |-> ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + (retval_2 * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_29 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((( &( "lcm" ) )) # Int |-> ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + (retval_2 * lcm))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def extended_chinese_remainder_theorem_entail_wit_1 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) residue_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) residue_values (0 : Int)) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((0 : Int) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values 1 (Znth (0 : Int) residue_values (0 : Int)) (Znth (0 : Int) modulus_values (0 : Int))) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values 1 (Znth (0 : Int) residue_values (0 : Int)) (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ ((0 : Int) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) residue_values (0 : Int)) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) residue_values (0 : Int))) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  (CRTPrefixMeaning residue_values modulus_values 1 (Znth (0 : Int) residue_values (0 : Int)) (Znth (0 : Int) modulus_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  ((Znth (0 : Int) modulus_values (0 : Int)) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  ((0 : Int) < (Znth (0 : Int) modulus_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_4 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  ((Znth (0 : Int) residue_values (0 : Int)) < (Znth (0 : Int) modulus_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_5 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  ((0 : Int) <= (Znth (0 : Int) residue_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_6 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_7 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count_2 : Int) , (((1 <= count_2) ∧ (count_2 <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count_2)) <= INT_MAX))) (PreH7 : forall (index_2 : Int) , (((1 <= index_2) ∧ (index_2 < n_pre)) -> ((2 * (Z.quot (Znth (index_2) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index_2))) ((Znth (index_2) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_1 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  ((( &( "x" ) )) # Int |-> ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_1_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_1_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_1_split_goal_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_2 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 < (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "x" ) )) # Int |-> ((retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= (retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ (retval_3 < (0 : Int)) ” &&
  “ (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int)) ” &&
  “ (x_v_2 = (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  ((( &( "x" ) )) # Int |-> ((retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 < (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ ((0 : Int) <= (retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_2_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 < (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_2_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 < (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_2_split_goal_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 < (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((0 : Int) <= (retval_3 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_3 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "x" ) )) # Int |-> (retval_2))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  ((( &( "x" ) )) # Int |-> (retval_2))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_3_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_3_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_3_split_goal_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_4 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 >= (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "x" ) )) # Int |-> (retval_3))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= retval_3) ” &&
  “ (retval_3 < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_3) ” &&
  “ (retval_3 >= (0 : Int)) ” &&
  “ (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int)) ” &&
  “ (x_v_2 = (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  ((( &( "x" ) )) # Int |-> (retval_3))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 >= (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_3) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (retval_3 < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_4_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 >= (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_3)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_4_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 >= (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_4_split_goal_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v_2 : Int) (retval : Int) (retval_3 : Int) (PreH1 : (retval_3 >= (0 : Int))) (PreH2 : (ModularMul x_v_2 (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_3)) (PreH3 : ((0 : Int) < retval)) (PreH4 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH5 : (((lcm * x_v_2) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH6 : ((Zabs (x_v_2)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH7 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH8 : (x_v_2 = (0 : Int))) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH11 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH13 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH14 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH15 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH16 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH17 : (1 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer < lcm)) (PreH21 : ((0 : Int) < lcm)) (PreH22 : (lcm <= INT_MAX)) (PreH23 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (retval_3 < (Z.quot (Znth i modulus_values (0 : Int)) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ” &&
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((0 : Int) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm))) ” &&
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((0 : Int) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH2 : ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)))) (PreH5 : (retval_2 < (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((answer + ((retval_2 + (Z.quot (Znth i modulus_values (0 : Int)) retval)) * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_3 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (answer + (retval_2 * lcm))) ” &&
  “ ((answer + (retval_2 * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((0 : Int) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (retval_2 * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (retval_2 * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((answer + (retval_2 * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_3_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (retval_2 * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_3_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH12 : (i < n_pre)) (PreH13 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH14 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH16 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH17 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH18 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH19 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH20 : (1 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer < lcm)) (PreH24 : ((0 : Int) < lcm)) (PreH25 : (lcm <= INT_MAX)) (PreH26 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((answer + (retval_2 * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_4 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (answer + (retval_2 * lcm))) ” &&
  “ ((answer + (retval_2 * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((0 : Int) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (retval_2 * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (retval_2 * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ” &&
  “ ((answer + (retval_2 * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_4_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (retval_2 * lcm)) (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_4_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (retval_2 : Int) (PreH1 : ((0 : Int) <= retval_2)) (PreH2 : (retval_2 < (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH3 : ((lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)) <= INT_MAX)) (PreH4 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval_2)) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (ModularMul x_v (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) (Z.quot (Znth i modulus_values (0 : Int)) retval) retval_2)) (PreH7 : ((0 : Int) < retval)) (PreH8 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH9 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH10 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH11 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH12 : (x_v = (0 : Int))) (PreH13 : (i < n_pre)) (PreH14 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH15 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH17 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH18 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH19 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH20 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= answer)) (PreH24 : (answer < lcm)) (PreH25 : ((0 : Int) < lcm)) (PreH26 : (lcm <= INT_MAX)) (PreH27 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((answer + (retval_2 * lcm)) < (lcm * (Z.quot (Znth i modulus_values (0 : Int)) retval)))

noncomputable def extended_chinese_remainder_theorem_return_wit_1 : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer < lcm)) (PreH13 : ((0 : Int) < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |-> (lcm))
|--
  EX combined_modulus_v : Int,
  “ (ExtendedCRTSystemResult residue_values modulus_values n_pre answer combined_modulus_v) ”
  &&  ((combined_modulus_pre) # Int |-> (combined_modulus_v))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer < lcm)) (PreH13 : ((0 : Int) < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer < lcm)) (PreH13 : ((0 : Int) < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (1 <= n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ”
  &&  (((residues_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) residue_values (0 : Int))))
  ** (intArray.missing_i residues_pre (0 : Int) (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (1 <= n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ”
  &&  (((moduli_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre (0 : Int) (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer < lcm)) (PreH13 : ((0 : Int) < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_pure : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer < lcm)) (PreH13 : ((0 : Int) < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ” &&
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ”
)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH10 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH12 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH13 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH14 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH15 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((0 : Int) <= answer)) (PreH19 : (answer < lcm)) (PreH20 : ((0 : Int) < lcm)) (PreH21 : (lcm <= INT_MAX)) (PreH22 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_aux : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH3 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH5 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH6 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH7 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer < lcm)) (PreH13 : ((0 : Int) < lcm)) (PreH14 : (lcm <= INT_MAX)) (PreH15 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4 : Prop := extended_chinese_remainder_theorem_partial_solve_wit_4_pure -> extended_chinese_remainder_theorem_partial_solve_wit_4_aux

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_5 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_6 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int)) ” &&
  “ (x_v = (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_7 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth i residue_values (0 : Int))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_pure : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ” &&
  “ (x_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_v) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH21 : (i < n_pre)) (PreH22 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH23 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH25 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH26 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : ((0 : Int) <= answer)) (PreH32 : (answer < lcm)) (PreH33 : ((0 : Int) < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_v) ” &&
  “ (x_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ” &&
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ”
)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH21 : (i < n_pre)) (PreH22 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH23 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH25 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH26 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : ((0 : Int) <= answer)) (PreH32 : (answer < lcm)) (PreH33 : ((0 : Int) < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_v) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH21 : (i < n_pre)) (PreH22 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH23 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH25 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH26 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : ((0 : Int) <= answer)) (PreH32 : (answer < lcm)) (PreH33 : ((0 : Int) < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (x_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH21 : (i < n_pre)) (PreH22 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH23 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH25 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH26 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : ((0 : Int) <= answer)) (PreH32 : (answer < lcm)) (PreH33 : ((0 : Int) < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_4 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH21 : (i < n_pre)) (PreH22 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH23 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH25 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH26 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : ((0 : Int) <= answer)) (PreH32 : (answer < lcm)) (PreH33 : ((0 : Int) < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_5 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH21 : (i < n_pre)) (PreH22 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH23 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH25 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH26 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : ((0 : Int) <= answer)) (PreH32 : (answer < lcm)) (PreH33 : ((0 : Int) < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_pure_split_goal_6 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH21 : (i < n_pre)) (PreH22 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH23 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH25 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH26 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH27 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH28 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH29 : (1 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : ((0 : Int) <= answer)) (PreH32 : (answer < lcm)) (PreH33 : ((0 : Int) < lcm)) (PreH34 : (lcm <= INT_MAX)) (PreH35 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8_aux : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH10 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH11 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH12 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH13 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer < lcm)) (PreH18 : ((0 : Int) < lcm)) (PreH19 : (lcm <= INT_MAX)) (PreH20 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ” &&
  “ (x_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_v) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_8 : Prop := extended_chinese_remainder_theorem_partial_solve_wit_8_pure -> extended_chinese_remainder_theorem_partial_solve_wit_8_aux

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_9 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int)) ” &&
  “ (x_v = (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth i residue_values (0 : Int))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure : Prop :=
  (
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_v) ” &&
  “ (x_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int)) ”
) \/
(
forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int)) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ” &&
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int)) ”
)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_1 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_2 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_3 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_4 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_5 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_6 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_7 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_pure_split_goal_8 : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (y_v <= INT_MAX)) (PreH6 : (x_v <= INT_MAX)) (PreH7 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) <= INT_MAX)) (PreH8 : (lcm >= INT_MIN)) (PreH9 : (answer >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (y_v >= INT_MIN)) (PreH14 : (x_v >= INT_MIN)) (PreH15 : ((Z.quot (Znth i modulus_values (0 : Int)) retval) >= INT_MIN)) (PreH16 : ((0 : Int) < retval)) (PreH17 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH18 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH19 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH20 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH21 : (x_v = (0 : Int))) (PreH22 : (i < n_pre)) (PreH23 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH24 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH26 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH27 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH28 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH29 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : ((0 : Int) <= answer)) (PreH33 : (answer < lcm)) (PreH34 : ((0 : Int) < lcm)) (PreH35 : (lcm <= INT_MAX)) (PreH36 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |-> ((Z.quot (Znth i modulus_values (0 : Int)) retval)))
  ** ((( &( "x" ) )) # Int |-> (x_v))
  ** ((( &( "y" ) )) # Int |-> (y_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10_aux : Prop :=
  forall (modulus_values : (List Int)) (residue_values : (List Int)) (n_pre : Int) (residues_pre : Int) (moduli_pre : Int) (combined_modulus_pre : Int) (lcm : Int) (answer : Int) (i : Int) (y_v : Int) (x_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval)) (PreH4 : ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values)) (PreH9 : (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values)) (PreH11 : (Forall2 (LT.lt (α := Int)) residue_values modulus_values)) (PreH12 : forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX))) (PreH13 : forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX))) (PreH14 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : ((0 : Int) <= answer)) (PreH18 : (answer < lcm)) (PreH19 : ((0 : Int) < lcm)) (PreH20 : (lcm <= INT_MAX)) (PreH21 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_v) ” &&
  “ (x_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.quot ((Znth i residue_values (0 : Int)) - answer) retval) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot ((Znth i residue_values (0 : Int)) - answer) retval)) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int)) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_v) + ((Znth i modulus_values (0 : Int)) * y_v)) = retval) ” &&
  “ ((Zabs (x_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int)) ” &&
  “ (x_v = (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LT.lt (α := Int)) ((0 : Int))) modulus_values) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) modulus_values) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) residue_values) ” &&
  “ (Forall2 (LT.lt (α := Int)) residue_values modulus_values) ” &&
  “ forall (count : Int) , (((1 <= count) ∧ (count <= n_pre)) -> ((CRTLCMPrefix (modulus_values) (count)) <= INT_MAX)) ” &&
  “ forall (index : Int) , (((1 <= index) ∧ (index < n_pre)) -> ((2 * (Z.quot (Znth (index) (modulus_values) ((0 : Int))) (Zgcd ((CRTLCMPrefix (modulus_values) (index))) ((Znth (index) (modulus_values) ((0 : Int))))))) <= INT_MAX)) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_10 : Prop := extended_chinese_remainder_theorem_partial_solve_wit_10_pure -> extended_chinese_remainder_theorem_partial_solve_wit_10_aux


structure VC_Correct : Type where
  proof_of_extended_chinese_remainder_theorem_safety_wit_1 : extended_chinese_remainder_theorem_safety_wit_1
  proof_of_extended_chinese_remainder_theorem_safety_wit_2 : extended_chinese_remainder_theorem_safety_wit_2
  proof_of_extended_chinese_remainder_theorem_safety_wit_3 : extended_chinese_remainder_theorem_safety_wit_3
  proof_of_extended_chinese_remainder_theorem_safety_wit_4 : extended_chinese_remainder_theorem_safety_wit_4
  proof_of_extended_chinese_remainder_theorem_safety_wit_5 : extended_chinese_remainder_theorem_safety_wit_5
  proof_of_extended_chinese_remainder_theorem_safety_wit_6 : extended_chinese_remainder_theorem_safety_wit_6
  proof_of_extended_chinese_remainder_theorem_safety_wit_8 : extended_chinese_remainder_theorem_safety_wit_8
  proof_of_extended_chinese_remainder_theorem_safety_wit_10 : extended_chinese_remainder_theorem_safety_wit_10
  proof_of_extended_chinese_remainder_theorem_safety_wit_11 : extended_chinese_remainder_theorem_safety_wit_11
  proof_of_extended_chinese_remainder_theorem_safety_wit_22 : extended_chinese_remainder_theorem_safety_wit_22
  proof_of_extended_chinese_remainder_theorem_safety_wit_23 : extended_chinese_remainder_theorem_safety_wit_23
  proof_of_extended_chinese_remainder_theorem_safety_wit_24 : extended_chinese_remainder_theorem_safety_wit_24
  proof_of_extended_chinese_remainder_theorem_safety_wit_25 : extended_chinese_remainder_theorem_safety_wit_25
  proof_of_extended_chinese_remainder_theorem_safety_wit_26 : extended_chinese_remainder_theorem_safety_wit_26
  proof_of_extended_chinese_remainder_theorem_safety_wit_27 : extended_chinese_remainder_theorem_safety_wit_27
  proof_of_extended_chinese_remainder_theorem_safety_wit_28 : extended_chinese_remainder_theorem_safety_wit_28
  proof_of_extended_chinese_remainder_theorem_safety_wit_29 : extended_chinese_remainder_theorem_safety_wit_29
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_1 : extended_chinese_remainder_theorem_partial_solve_wit_1
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_2 : extended_chinese_remainder_theorem_partial_solve_wit_2
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_3 : extended_chinese_remainder_theorem_partial_solve_wit_3
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4 : extended_chinese_remainder_theorem_partial_solve_wit_4
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_5 : extended_chinese_remainder_theorem_partial_solve_wit_5
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_6 : extended_chinese_remainder_theorem_partial_solve_wit_6
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_7 : extended_chinese_remainder_theorem_partial_solve_wit_7
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_8 : extended_chinese_remainder_theorem_partial_solve_wit_8
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_9 : extended_chinese_remainder_theorem_partial_solve_wit_9
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_10 : extended_chinese_remainder_theorem_partial_solve_wit_10
  proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7
  proof_of_extended_chinese_remainder_theorem_safety_wit_9 : extended_chinese_remainder_theorem_safety_wit_9
  proof_of_extended_chinese_remainder_theorem_safety_wit_12 : extended_chinese_remainder_theorem_safety_wit_12
  proof_of_extended_chinese_remainder_theorem_safety_wit_13 : extended_chinese_remainder_theorem_safety_wit_13
  proof_of_extended_chinese_remainder_theorem_safety_wit_14 : extended_chinese_remainder_theorem_safety_wit_14
  proof_of_extended_chinese_remainder_theorem_safety_wit_15 : extended_chinese_remainder_theorem_safety_wit_15
  proof_of_extended_chinese_remainder_theorem_safety_wit_16 : extended_chinese_remainder_theorem_safety_wit_16
  proof_of_extended_chinese_remainder_theorem_safety_wit_17 : extended_chinese_remainder_theorem_safety_wit_17
  proof_of_extended_chinese_remainder_theorem_safety_wit_18 : extended_chinese_remainder_theorem_safety_wit_18
  proof_of_extended_chinese_remainder_theorem_safety_wit_19 : extended_chinese_remainder_theorem_safety_wit_19
  proof_of_extended_chinese_remainder_theorem_safety_wit_20 : extended_chinese_remainder_theorem_safety_wit_20
  proof_of_extended_chinese_remainder_theorem_safety_wit_21 : extended_chinese_remainder_theorem_safety_wit_21
  proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1
  proof_of_extended_chinese_remainder_theorem_entail_wit_2_1 : extended_chinese_remainder_theorem_entail_wit_2_1
  proof_of_extended_chinese_remainder_theorem_entail_wit_2_2 : extended_chinese_remainder_theorem_entail_wit_2_2
  proof_of_extended_chinese_remainder_theorem_entail_wit_2_3 : extended_chinese_remainder_theorem_entail_wit_2_3
  proof_of_extended_chinese_remainder_theorem_entail_wit_2_4 : extended_chinese_remainder_theorem_entail_wit_2_4
  proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1
  proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2
  proof_of_extended_chinese_remainder_theorem_entail_wit_3_3 : extended_chinese_remainder_theorem_entail_wit_3_3
  proof_of_extended_chinese_remainder_theorem_entail_wit_3_4 : extended_chinese_remainder_theorem_entail_wit_3_4
  proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_8_pure : extended_chinese_remainder_theorem_partial_solve_wit_8_pure
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_10_pure : extended_chinese_remainder_theorem_partial_solve_wit_10_pure

end SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_goal
