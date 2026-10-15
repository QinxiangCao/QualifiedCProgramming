import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P048_1771C_hossam_and_trainees_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def solver_safety_wit_1 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  ((( &( "pc" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "primes" ) ) 4000)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full values_pre n_pre a)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (ucharArray.full ( &( "composite" ) ) 31624 (repeat_Z ((0 : Int)) (31624)))
  ** ((( &( "pc" ) )) # Int |-> ((0 : Int)))
  ** (intArray.undef_full ( &( "primes" ) ) 4000)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full values_pre n_pre a)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : (2 <= i)) (PreH6 : (i <= 31624)) (PreH7 : (pc = (Zlength (prime_data)))) (PreH8 : ((0 : Int) <= pc)) (PreH9 : (pc < 4000)) (PreH10 : ((Zlength (composite_data)) = 31624)) (PreH11 : (PrimePrefixTable2 i prime_data composite_data)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ (31623 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 31623) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data (0 : Int)) = (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (intArray.full ( &( "primes" ) ) (pc + 1) (prime_data ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
|--
  “ ((pc + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pc + 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data (0 : Int)) = (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (intArray.full ( &( "primes" ) ) (pc + 1) (prime_data ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> ((pc + 1)))
  ** (intArray.full values_pre n_pre a)
|--
  “ ((i * i) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (i * i)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data (0 : Int)) = (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (intArray.full ( &( "primes" ) ) (pc + 1) (prime_data ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> ((pc + 1)))
  ** (intArray.full values_pre n_pre a)
|--
  “ (31623 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 31623) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) <= 31623)) (PreH2 : ((Znth i composite_data (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data composite_data)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.full ( &( "primes" ) ) (pc + 1) (prime_data ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> ((pc + 1)))
  ** (intArray.full values_pre n_pre a)
|--
  “ ((i * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * i)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (j : Int) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : (2 <= i)) (PreH6 : (i <= 177)) (PreH7 : (pc = (Zlength (prime_data)))) (PreH8 : (1 <= pc)) (PreH9 : (pc < 4000)) (PreH10 : ((i * i) <= j)) (PreH11 : (j <= (31623 + i))) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimeMarkTable2 i j prime_data composite_data)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ (31623 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 31623) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (j : Int) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data)) ,
  (ucharArray.full ( &( "composite" ) ) 31624 (replace_Znth (j) (1) (composite_data)))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
|--
  “ ((j + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + i)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (j : Int) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data)) ,
  ((( &( "factors" ) )) # Ptr |->_)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ ((n_pre * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * 10)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data)) ,
  ((( &( "factors" ) )) # Ptr |->_)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (j : Int) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) > 31623)) (PreH2 : ((Znth i composite_data (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (intArray.full ( &( "primes" ) ) (pc + 1) (prime_data ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> ((pc + 1)))
  ** (intArray.full values_pre n_pre a)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data (0 : Int)) ≠ (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data)) ,
  ((( &( "count" ) )) # Int |->_)
  ** (intArray.undef_full retval (n_pre * 10))
  ** ((( &( "factors" ) )) # Ptr |-> (retval))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "count" ) )) # Int |-> ((0 : Int)))
  ** (intArray.undef_full retval (n_pre * 10))
  ** ((( &( "factors" ) )) # Ptr |-> (retval))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data)) (PreH16 : (PrimeFactorBagPrefix a i factor_data)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.full values_pre n_pre a)
  ** ((( &( "x" ) )) # Int |-> ((Znth i a (0 : Int))))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : ((0 : Int) <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorScanState a prime_data i j x factor_data)) (PreH21 : (FactorScanState2 a prime_data i j x factor_data)) (PreH22 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : ((0 : Int) <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorScanState a prime_data i j x factor_data)) (PreH21 : (FactorScanState2 a prime_data i j x factor_data)) (PreH22 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int)))) ”
)

noncomputable def solver_safety_wit_19_split_goal_1 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : ((0 : Int) <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorScanState a prime_data i j x factor_data)) (PreH21 : (FactorScanState2 a prime_data i j x factor_data)) (PreH22 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_19_split_goal_2 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : ((0 : Int) <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorScanState a prime_data i j x factor_data)) (PreH21 : (FactorScanState2 a prime_data i j x factor_data)) (PreH22 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((-9223372036854775808) <= ((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int)))) ”

noncomputable def solver_safety_wit_20 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”
) \/
(
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”
)

noncomputable def solver_safety_wit_20_split_goal_1 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ”

noncomputable def solver_safety_wit_20_split_goal_2 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full factors (count + 1) (factor_data ++ ((Znth j prime_data (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
|--
  “ ((count + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (count + 1)) ”

noncomputable def solver_safety_wit_23 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10) + 9))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (FactorDivideState a prime_data i j x factor_data)) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”
) \/
(
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10) + 9))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (FactorDivideState a prime_data i j x factor_data)) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”
)

noncomputable def solver_safety_wit_23_split_goal_1 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10) + 9))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (FactorDivideState a prime_data i j x factor_data)) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ”

noncomputable def solver_safety_wit_23_split_goal_2 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10) + 9))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (FactorDivideState a prime_data i j x factor_data)) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10) + 9))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (FactorDivideState a prime_data i j x factor_data)) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_25 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorDivideState a prime_data i j x factor_data)) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”
) \/
(
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorDivideState a prime_data i j x factor_data)) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”
)

noncomputable def solver_safety_wit_25_split_goal_1 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorDivideState a prime_data i j x factor_data)) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((x ≠ (INT_MIN)) ∨ ((Znth j prime_data (0 : Int)) ≠ (-1))) ”

noncomputable def solver_safety_wit_25_split_goal_2 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorDivideState a prime_data i j x factor_data)) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((Znth j prime_data (0 : Int)) ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorDivideState a prime_data i j x factor_data)) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (j >= pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : ((0 : Int) <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorScanState a prime_data i j x factor_data)) (PreH21 : (FactorScanState2 a prime_data i j x factor_data)) (PreH22 : (FactorAppendCapacity prime_data i j x count)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) > x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full factors (count + 1) (factor_data ++ (x :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
|--
  “ ((count + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (count + 1)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full factors (count + 1) (factor_data ++ (x :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
|--
  “ ((count + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (count + 1)) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full factors (count + 1) (factor_data ++ (x :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> ((count + 1)))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full factors (count + 1) (factor_data ++ (x :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> ((count + 1)))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (sorted : (List Int)) (PreH1 : (Permutation factor_data sorted)) (PreH2 : (increasing sorted)) (PreH3 : ((Zlength (sorted)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : ((0 : Int) <= count)) (PreH17 : (count <= (i * 10))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (PrimeFactorBagPrefix a i factor_data)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** (intArray.full factors count sorted)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (sorted : (List Int)) (PreH1 : (Permutation factor_data sorted)) (PreH2 : (increasing sorted)) (PreH3 : ((Zlength (sorted)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : ((0 : Int) <= count)) (PreH17 : (count <= (i * 10))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (PrimeFactorBagPrefix a i factor_data)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "ok" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full factors count sorted)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH16 : (DuplicateScanLoopState sorted count i ok)) ,
  (intArray.full factors count sorted)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "ok" ) )) # Int |-> (ok))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH16 : (DuplicateScanLoopState sorted count i ok)) ,
  (intArray.full factors count sorted)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "ok" ) )) # Int |-> (ok))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted (0 : Int)) = (Znth (i - 1) sorted (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : ((Zlength (sorted)) = count)) (PreH15 : (increasing sorted)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH17 : (DuplicateScanLoopState sorted count i ok)) ,
  (intArray.full factors count sorted)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "ok" ) )) # Int |-> (ok))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted (0 : Int)) = (Znth (i - 1) sorted (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : ((Zlength (sorted)) = count)) (PreH15 : (increasing sorted)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH17 : (DuplicateScanLoopState sorted count i ok)) ,
  (intArray.full factors count sorted)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "ok" ) )) # Int |-> (1))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted (0 : Int)) ≠ (Znth (i - 1) sorted (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : ((Zlength (sorted)) = count)) (PreH15 : (increasing sorted)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH17 : (DuplicateScanLoopState sorted count i ok)) ,
  (intArray.full factors count sorted)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "ok" ) )) # Int |-> (ok))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  (ucharArray.full ( &( "composite" ) ) 31624 (repeat_Z ((0 : Int)) (31624)))
  ** (intArray.undef_full ( &( "primes" ) ) 4000)
  ** (intArray.full values_pre n_pre a)
|--
  EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= 31624) ” &&
  “ ((0 : Int) = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimePrefixTable2 2 prime_data composite_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) (0 : Int) prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) (0 : Int) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
) \/
(
forall (n_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  TT && emp 
|--
  “ (PrimePrefixTable2 2 (@List.nil Int) (repeat_Z ((0 : Int)) (31624))) ” &&
  “ ((Zlength ((repeat_Z ((0 : Int)) (31624)))) = 31624) ” &&
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  (PrimePrefixTable2 2 (@List.nil Int) (repeat_Z ((0 : Int)) (31624)))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  ((Zlength ((repeat_Z ((0 : Int)) (31624)))) = 31624)

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  ((0 : Int) = (Zlength ((@List.nil Int))))

noncomputable def solver_entail_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (PreH1 : (2 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (a)))) -> ((1 <= (Znth i a (0 : Int))) ∧ ((Znth i a (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (a)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) <= 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (intArray.full ( &( "primes" ) ) (pc + 1) (prime_data_2 ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full values_pre n_pre a)
|--
  EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= i) ” &&
  “ (i <= 177) ” &&
  “ ((pc + 1) = (Zlength (prime_data))) ” &&
  “ (1 <= (pc + 1)) ” &&
  “ ((pc + 1) < 4000) ” &&
  “ ((i * i) <= (i * i)) ” &&
  “ ((i * i) <= (31623 + i)) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimeMarkTable2 i (i * i) prime_data composite_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) (pc + 1) prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
) \/
(
forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) <= 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  TT && emp 
|--
  “ (PrimeMarkTable2 i (i * i) (prime_data_2 ++ (i :: (@List.nil Int))) composite_data_2) ” &&
  “ ((pc + 1) < 4000) ” &&
  “ ((pc + 1) = (Zlength ((prime_data_2 ++ (i :: (@List.nil Int)))))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) <= 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (PrimeMarkTable2 i (i * i) (prime_data_2 ++ (i :: (@List.nil Int))) composite_data_2)

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) <= 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  ((pc + 1) < 4000)

noncomputable def solver_entail_wit_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) <= 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  ((pc + 1) = (Zlength ((prime_data_2 ++ (i :: (@List.nil Int))))))

noncomputable def solver_entail_wit_2_split_goal_4 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) <= 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  (ucharArray.full ( &( "composite" ) ) 31624 (replace_Znth (j) (1) (composite_data_2)))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
|--
  EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= i) ” &&
  “ (i <= 177) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ (1 <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((i * i) <= (j + i)) ” &&
  “ ((j + i) <= (31623 + i)) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimeMarkTable2 i (j + i) prime_data composite_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
) \/
(
forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  TT && emp 
|--
  “ (PrimeMarkTable2 i (j + i) prime_data_2 (replace_Znth (j) (1) (composite_data_2))) ” &&
  “ ((Zlength ((replace_Znth (j) (1) (composite_data_2)))) = 31624) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  (PrimeMarkTable2 i (j + i) prime_data_2 (replace_Znth (j) (1) (composite_data_2)))

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  ((Zlength ((replace_Znth (j) (1) (composite_data_2)))) = 31624)

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
|--
  EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= 31624) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimePrefixTable2 (i + 1) prime_data composite_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
) \/
(
forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  TT && emp 
|--
  “ (PrimePrefixTable2 (i + 1) prime_data_2 composite_data_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  (PrimePrefixTable2 (i + 1) prime_data_2 composite_data_2)

noncomputable def solver_entail_wit_4_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (j : Int) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (j > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data_2 composite_data_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) > 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (intArray.full ( &( "primes" ) ) (pc + 1) (prime_data_2 ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full values_pre n_pre a)
|--
  EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= 31624) ” &&
  “ ((pc + 1) = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= (pc + 1)) ” &&
  “ ((pc + 1) < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimePrefixTable2 (i + 1) prime_data composite_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) (pc + 1) prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
) \/
(
forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) > 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  TT && emp 
|--
  “ (PrimePrefixTable2 (i + 1) (prime_data_2 ++ (i :: (@List.nil Int))) composite_data_2) ” &&
  “ ((pc + 1) < 4000) ” &&
  “ ((pc + 1) = (Zlength ((prime_data_2 ++ (i :: (@List.nil Int)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) > 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (PrimePrefixTable2 (i + 1) (prime_data_2 ++ (i :: (@List.nil Int))) composite_data_2)

noncomputable def solver_entail_wit_4_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) > 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  ((pc + 1) < 4000)

noncomputable def solver_entail_wit_4_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((i * i) > 31623)) (PreH2 : ((Znth i composite_data_2 (0 : Int)) = (0 : Int))) (PreH3 : (i <= 31623)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : (2 <= i)) (PreH9 : (i <= 31624)) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  ((pc + 1) = (Zlength ((prime_data_2 ++ (i :: (@List.nil Int))))))

noncomputable def solver_entail_wit_4_3 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
|--
  EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= 31624) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimePrefixTable2 (i + 1) prime_data composite_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
) \/
(
forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  TT && emp 
|--
  “ (PrimePrefixTable2 (i + 1) prime_data_2 composite_data_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (PrimePrefixTable2 (i + 1) prime_data_2 composite_data_2)

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (intArray.undef_full retval (n_pre * 10))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((0 : Int) = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((0 : Int) * 10)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (PrimeFactorBagPrefix a (0 : Int) factor_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full retval (0 : Int) factor_data)
  ** (intArray.undef_seg retval (0 : Int) (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (0 : Int) (@List.nil Int)) ” &&
  “ (CompletePrimeTable prime_data_2) ” &&
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (PrimeFactorBagPrefix a (0 : Int) (@List.nil Int))

noncomputable def solver_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  (CompletePrimeTable prime_data_2)

noncomputable def solver_entail_wit_5_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  ((0 : Int) = (Zlength ((@List.nil Int))))

noncomputable def solver_entail_wit_5_split_goal_4 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (i > 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data_2 composite_data_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data_2)) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full factors count factor_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (1 <= (Znth i a (0 : Int))) ” &&
  “ ((Znth i a (0 : Int)) <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i (0 : Int) (Znth i a (0 : Int)) factor_data) ” &&
  “ (FactorScanState2 a prime_data i (0 : Int) (Znth i a (0 : Int)) factor_data) ” &&
  “ (FactorAppendCapacity prime_data i (0 : Int) (Znth i a (0 : Int)) count) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data_2)) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2)) ,
  TT && emp 
|--
  “ (FactorAppendCapacity prime_data_2 i (0 : Int) (Znth i a (0 : Int)) count) ” &&
  “ (FactorScanState2 a prime_data_2 i (0 : Int) (Znth i a (0 : Int)) factor_data_2) ” &&
  “ (FactorScanState a prime_data_2 i (0 : Int) (Znth i a (0 : Int)) factor_data_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data_2)) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2)) ,
  (FactorAppendCapacity prime_data_2 i (0 : Int) (Znth i a (0 : Int)) count)

noncomputable def solver_entail_wit_6_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data_2)) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2)) ,
  (FactorScanState2 a prime_data_2 i (0 : Int) (Znth i a (0 : Int)) factor_data_2)

noncomputable def solver_entail_wit_6_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data_2)) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2)) ,
  (FactorScanState a prime_data_2 i (0 : Int) (Znth i a (0 : Int)) factor_data_2)

noncomputable def solver_entail_wit_6_split_goal_4 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data_2)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data_2)) = 31624)) (PreH12 : (count = (Zlength (factor_data_2)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data_2)) (PreH16 : (PrimeFactorBagPrefix a i factor_data_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (intArray.full factors (count + 1) (factor_data_2 ++ ((Znth j prime_data_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((count + 1) = (Zlength (factor_data))) ” &&
  “ (1 <= (count + 1)) ” &&
  “ ((count + 1) <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorDivideState a prime_data i j x factor_data) ” &&
  “ (FactorDivideState2 a prime_data i j x factor_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors (count + 1) factor_data)
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  TT && emp 
|--
  “ (FactorDivideState2 a prime_data_2 i j x (factor_data_2 ++ ((Znth j prime_data_2 (0 : Int)) :: (@List.nil Int)))) ” &&
  “ (FactorDivideState a prime_data_2 i j x (factor_data_2 ++ ((Znth j prime_data_2 (0 : Int)) :: (@List.nil Int)))) ” &&
  “ ((count + 1) <= ((i * 10) + 9)) ” &&
  “ ((count + 1) = (Zlength ((factor_data_2 ++ ((Znth j prime_data_2 (0 : Int)) :: (@List.nil Int)))))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (FactorDivideState2 a prime_data_2 i j x (factor_data_2 ++ ((Znth j prime_data_2 (0 : Int)) :: (@List.nil Int))))

noncomputable def solver_entail_wit_7_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (FactorDivideState a prime_data_2 i j x (factor_data_2 ++ ((Znth j prime_data_2 (0 : Int)) :: (@List.nil Int))))

noncomputable def solver_entail_wit_7_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  ((count + 1) <= ((i * 10) + 9))

noncomputable def solver_entail_wit_7_split_goal_4 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  ((count + 1) = (Zlength ((factor_data_2 ++ ((Znth j prime_data_2 (0 : Int)) :: (@List.nil Int))))))

noncomputable def solver_entail_wit_7_split_goal_5 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full factors count factor_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < pc) ” &&
  “ (1 <= (Z.quot x (Znth j prime_data_2 (0 : Int)))) ” &&
  “ ((Z.quot x (Znth j prime_data_2 (0 : Int))) <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ (1 <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorDivideState a prime_data i j (Z.quot x (Znth j prime_data_2 (0 : Int))) factor_data) ” &&
  “ (FactorDivideState2 a prime_data i j (Z.quot x (Znth j prime_data_2 (0 : Int))) factor_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  TT && emp 
|--
  “ (FactorDivideState2 a prime_data_2 i j (Z.quot x (Znth j prime_data_2 (0 : Int))) factor_data_2) ” &&
  “ (FactorDivideState a prime_data_2 i j (Z.quot x (Znth j prime_data_2 (0 : Int))) factor_data_2) ” &&
  “ ((Z.quot x (Znth j prime_data_2 (0 : Int))) <= 1000000000) ” &&
  “ (1 <= (Z.quot x (Znth j prime_data_2 (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (FactorDivideState2 a prime_data_2 i j (Z.quot x (Znth j prime_data_2 (0 : Int))) factor_data_2)

noncomputable def solver_entail_wit_8_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (FactorDivideState a prime_data_2 i j (Z.quot x (Znth j prime_data_2 (0 : Int))) factor_data_2)

noncomputable def solver_entail_wit_8_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  ((Z.quot x (Znth j prime_data_2 (0 : Int))) <= 1000000000)

noncomputable def solver_entail_wit_8_split_goal_4 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (1 <= (Z.quot x (Znth j prime_data_2 (0 : Int))))

noncomputable def solver_entail_wit_9_1 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full factors count factor_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i (j + 1) x factor_data) ” &&
  “ (FactorScanState2 a prime_data i (j + 1) x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i (j + 1) x count) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  TT && emp 
|--
  “ (FactorAppendCapacity prime_data_2 i (j + 1) x count) ” &&
  “ (FactorScanState2 a prime_data_2 i (j + 1) x factor_data_2) ” &&
  “ (FactorScanState a prime_data_2 i (j + 1) x factor_data_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (FactorAppendCapacity prime_data_2 i (j + 1) x count)

noncomputable def solver_entail_wit_9_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (FactorScanState2 a prime_data_2 i (j + 1) x factor_data_2)

noncomputable def solver_entail_wit_9_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  (FactorScanState a prime_data_2 i (j + 1) x factor_data_2)

noncomputable def solver_entail_wit_9_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data_2)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data_2)) = 31624)) (PreH16 : (count = (Zlength (factor_data_2)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data_2)) (PreH20 : (FactorDivideState a prime_data_2 i j x factor_data_2)) (PreH21 : (FactorDivideState2 a prime_data_2 i j x factor_data_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_9_2 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full factors count factor_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i (j + 1) x factor_data) ” &&
  “ (FactorScanState2 a prime_data i (j + 1) x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i (j + 1) x count) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  TT && emp 
|--
  “ (FactorAppendCapacity prime_data_2 i (j + 1) x count) ” &&
  “ (FactorScanState2 a prime_data_2 i (j + 1) x factor_data_2) ” &&
  “ (FactorScanState a prime_data_2 i (j + 1) x factor_data_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (FactorAppendCapacity prime_data_2 i (j + 1) x count)

noncomputable def solver_entail_wit_9_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (FactorScanState2 a prime_data_2 i (j + 1) x factor_data_2)

noncomputable def solver_entail_wit_9_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (FactorScanState a prime_data_2 i (j + 1) x factor_data_2)

noncomputable def solver_entail_wit_10_1 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (intArray.full factors (count + 1) (factor_data_2 ++ (x :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((count + 1) = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= (count + 1)) ” &&
  “ ((count + 1) <= ((i + 1) * 10)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (PrimeFactorBagPrefix a (i + 1) factor_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors (count + 1) factor_data)
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1) (factor_data_2 ++ (x :: (@List.nil Int)))) ” &&
  “ ((count + 1) = (Zlength ((factor_data_2 ++ (x :: (@List.nil Int)))))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (PrimeFactorBagPrefix a (i + 1) (factor_data_2 ++ (x :: (@List.nil Int))))

noncomputable def solver_entail_wit_10_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  ((count + 1) = (Zlength ((factor_data_2 ++ (x :: (@List.nil Int))))))

noncomputable def solver_entail_wit_10_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_10_2 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (intArray.full factors (count + 1) (factor_data_2 ++ (x :: (@List.nil Int))))
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((count + 1) = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= (count + 1)) ” &&
  “ ((count + 1) <= ((i + 1) * 10)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (PrimeFactorBagPrefix a (i + 1) factor_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors (count + 1) factor_data)
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1) (factor_data_2 ++ (x :: (@List.nil Int)))) ” &&
  “ ((count + 1) = (Zlength ((factor_data_2 ++ (x :: (@List.nil Int)))))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (PrimeFactorBagPrefix a (i + 1) (factor_data_2 ++ (x :: (@List.nil Int))))

noncomputable def solver_entail_wit_10_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  ((count + 1) = (Zlength ((factor_data_2 ++ (x :: (@List.nil Int))))))

noncomputable def solver_entail_wit_10_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_10_3 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full factors count factor_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i + 1) * 10)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (PrimeFactorBagPrefix a (i + 1) factor_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1) factor_data_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (PrimeFactorBagPrefix a (i + 1) factor_data_2)

noncomputable def solver_entail_wit_10_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data_2)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data_2)) = 31624)) (PreH17 : (count = (Zlength (factor_data_2)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data_2)) (PreH21 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH22 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_10_4 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full factors count factor_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX factor_data : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i + 1) * 10)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (PrimeFactorBagPrefix a (i + 1) factor_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  TT && emp 
|--
  “ (PrimeFactorBagPrefix a (i + 1) factor_data_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  (PrimeFactorBagPrefix a (i + 1) factor_data_2)

noncomputable def solver_entail_wit_10_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data_2 : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x <= 1)) (PreH2 : (((Znth j prime_data_2 (0 : Int)) * (Znth j prime_data_2 (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (a)))) -> ((1 <= (Znth k_2 a (0 : Int))) ∧ ((Znth k_2 a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data_2)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data_2)) = 31624)) (PreH18 : (count = (Zlength (factor_data_2)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data_2)) (PreH22 : (FactorScanState a prime_data_2 i j x factor_data_2)) (PreH23 : (FactorScanState2 a prime_data_2 i j x factor_data_2)) (PreH24 : (FactorAppendCapacity prime_data_2 i j x count)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_11 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : (Permutation factor_data sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : ((0 : Int) <= count)) (PreH17 : (count <= (i * 10))) (PreH18 : (CompletePrimeTable prime_data_2)) (PreH19 : (PrimeFactorBagPrefix a i factor_data)) ,
  (intArray.full factors count sorted_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX sorted : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (count + 1)) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (increasing sorted) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted) ” &&
  “ (DuplicateScanLoopState sorted count 1 (0 : Int)) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (factor_data : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : (Permutation factor_data sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : ((0 : Int) <= count)) (PreH17 : (count <= (i * 10))) (PreH18 : (CompletePrimeTable prime_data_2)) (PreH19 : (PrimeFactorBagPrefix a i factor_data)) ,
  TT && emp 
|--
  “ (DuplicateScanLoopState sorted_2 count 1 (0 : Int)) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_11_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : (Permutation factor_data sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : ((0 : Int) <= count)) (PreH17 : (count <= (i * 10))) (PreH18 : (CompletePrimeTable prime_data_2)) (PreH19 : (PrimeFactorBagPrefix a i factor_data)) ,
  (DuplicateScanLoopState sorted_2 count 1 (0 : Int))

noncomputable def solver_entail_wit_11_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (factor_data : (List Int)) (count : Int) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : (Permutation factor_data sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = count)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : (2 <= (Zlength (a)))) (PreH7 : ((Zlength (a)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (pc = (Zlength (prime_data_2)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data_2)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : ((0 : Int) <= count)) (PreH17 : (count <= (i * 10))) (PreH18 : (CompletePrimeTable prime_data_2)) (PreH19 : (PrimeFactorBagPrefix a i factor_data)) ,
  (PrimeFactorBagPrefix a n_pre sorted_2)

noncomputable def solver_entail_wit_12 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.full factors count sorted_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX sorted : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (increasing sorted) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted) ” &&
  “ (DuplicatePrefixState sorted count ok) ” &&
  “ (Spec a ok) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  TT && emp 
|--
  “ (Spec a ok) ” &&
  “ (DuplicatePrefixState sorted_2 count ok) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  (Spec a ok)

noncomputable def solver_entail_wit_12_split_goal_2 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i >= count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data_2)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data_2)) = 31624)) (PreH13 : ((Zlength (sorted_2)) = count)) (PreH14 : (increasing sorted_2)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH16 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  (DuplicatePrefixState sorted_2 count ok)

noncomputable def solver_entail_wit_13_1 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted_2 (0 : Int)) = (Znth (i - 1) sorted_2 (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  (intArray.full factors count sorted_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX sorted : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (count + 1)) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (increasing sorted) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted) ” &&
  “ (DuplicateScanLoopState sorted count (i + 1) 1) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted_2 (0 : Int)) = (Znth (i - 1) sorted_2 (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  TT && emp 
|--
  “ (DuplicateScanLoopState sorted_2 count (i + 1) 1) ”
  &&  emp
)

noncomputable def solver_entail_wit_13_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted_2 (0 : Int)) = (Znth (i - 1) sorted_2 (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  (DuplicateScanLoopState sorted_2 count (i + 1) 1)

noncomputable def solver_entail_wit_13_2 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted_2 (0 : Int)) ≠ (Znth (i - 1) sorted_2 (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  (intArray.full factors count sorted_2)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data_2)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data_2)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  EX sorted : (List Int), EX composite_data : (List Int), EX prime_data : (List Int),
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (count + 1)) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (increasing sorted) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted) ” &&
  “ (DuplicateScanLoopState sorted count (i + 1) ok) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
) \/
(
forall (n_pre : Int) (a : (List Int)) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted_2 (0 : Int)) ≠ (Znth (i - 1) sorted_2 (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  TT && emp 
|--
  “ (DuplicateScanLoopState sorted_2 count (i + 1) ok) ”
  &&  emp
)

noncomputable def solver_entail_wit_13_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (a : (List Int)) (ok : Int) (sorted_2 : (List Int)) (composite_data_2 : (List Int)) (prime_data_2 : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : ((Znth i sorted_2 (0 : Int)) ≠ (Znth (i - 1) sorted_2 (0 : Int)))) (PreH2 : (i < count)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : ((0 : Int) <= count)) (PreH7 : (count <= (n_pre * 10))) (PreH8 : (1 <= i)) (PreH9 : (i <= (count + 1))) (PreH10 : (pc = (Zlength (prime_data_2)))) (PreH11 : ((0 : Int) <= pc)) (PreH12 : (pc < 4000)) (PreH13 : ((Zlength (composite_data_2)) = 31624)) (PreH14 : ((Zlength (sorted_2)) = count)) (PreH15 : (increasing sorted_2)) (PreH16 : (PrimeFactorBagPrefix a n_pre sorted_2)) (PreH17 : (DuplicateScanLoopState sorted_2 count i ok)) ,
  (DuplicateScanLoopState sorted_2 count (i + 1) ok)

noncomputable def solver_entail_wit_14 : Prop :=
  (
forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (prime_data : (List Int)) (composite_data : (List Int)) (sorted : (List Int)) (count : Int) (pc : Int) (ok : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : ((0 : Int) <= count)) (PreH5 : (count <= (n_pre * 10))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : ((0 : Int) <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted)) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH13 : (DuplicatePrefixState sorted count ok)) (PreH14 : (Spec a ok)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ (Spec a ok) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.undef_full ( &( "primes" ) ) 4000)
  ** (ucharArray.undef_full ( &( "composite" ) ) 31624)
) \/
(
forall (n_pre : Int) (a : (List Int)) (prime_data : (List Int)) (composite_data : (List Int)) (sorted : (List Int)) (count : Int) (pc : Int) (ok : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : ((0 : Int) <= count)) (PreH5 : (count <= (n_pre * 10))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : ((0 : Int) <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted)) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH13 : (DuplicatePrefixState sorted count ok)) (PreH14 : (Spec a ok)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  (intArray.undef_full ( &( "primes" ) ) 4000)
  ** (ucharArray.undef_full ( &( "composite" ) ) 31624)
)

noncomputable def solver_entail_wit_14_split_goal_spatial : Prop :=
  forall (n_pre : Int) (a : (List Int)) (prime_data : (List Int)) (composite_data : (List Int)) (sorted : (List Int)) (count : Int) (pc : Int) (ok : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : ((0 : Int) <= count)) (PreH5 : (count <= (n_pre * 10))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : ((0 : Int) <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted)) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH13 : (DuplicatePrefixState sorted count ok)) (PreH14 : (Spec a ok)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  (intArray.undef_full ( &( "primes" ) ) 4000)
  ** (ucharArray.undef_full ( &( "composite" ) ) 31624)

noncomputable def solver_return_wit_1 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (ok : Int) (PreH1 : (Spec a ok)) ,
  (intArray.full values_pre n_pre a)
|--
  “ (Spec a ok) ”
  &&  (intArray.full values_pre n_pre a)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ (i <= 31623) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= i) ” &&
  “ (i <= 31624) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimePrefixTable2 i prime_data composite_data) ”
  &&  (((( &( "composite" ) ) + (i * sizeof(UCHAR)))) # UChar |-> ((Znth i composite_data (0 : Int))))
  ** (ucharArray.missing_i ( &( "composite" ) ) i (0 : Int) 31624 composite_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : ((Znth i composite_data (0 : Int)) = (0 : Int))) (PreH2 : (i <= 31623)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : (2 <= i)) (PreH8 : (i <= 31624)) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
|--
  “ ((Znth i composite_data (0 : Int)) = (0 : Int)) ” &&
  “ (i <= 31623) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= i) ” &&
  “ (i <= 31624) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimePrefixTable2 i prime_data composite_data) ”
  &&  (((( &( "primes" ) ) + (pc * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "primes" ) ) (pc + 1) 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (j : Int) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (j <= 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 177)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : (1 <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((i * i) <= j)) (PreH12 : (j <= (31623 + i))) (PreH13 : ((Zlength (composite_data)) = 31624)) (PreH14 : (PrimeMarkTable2 i j prime_data composite_data)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ (j <= 31623) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= i) ” &&
  “ (i <= 177) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ (1 <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((i * i) <= j) ” &&
  “ (j <= (31623 + i)) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimeMarkTable2 i j prime_data composite_data) ”
  &&  (((( &( "composite" ) ) + (j * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i ( &( "composite" ) ) j (0 : Int) 31624 composite_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)

noncomputable def solver_partial_solve_wit_4_pure : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data)) ,
  ((( &( "factors" ) )) # Ptr |->_)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ ((0 : Int) <= (n_pre * 10)) ” &&
  “ (((n_pre * 10) * sizeof(INT)) <= UINT_MAX) ” &&
  “ (((n_pre * 10) * sizeof(INT)) = ((n_pre * 10) * sizeof(INT))) ”

noncomputable def solver_partial_solve_wit_4_aux : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i > 31623)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : (2 <= i)) (PreH7 : (i <= 31624)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (PrimePrefixTable2 i prime_data composite_data)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
|--
  “ ((0 : Int) <= (n_pre * 10)) ” &&
  “ (((n_pre * 10) * sizeof(INT)) <= UINT_MAX) ” &&
  “ (((n_pre * 10) * sizeof(INT)) = ((n_pre * 10) * sizeof(INT))) ” &&
  “ (i > 31623) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ (2 <= i) ” &&
  “ (i <= 31624) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (PrimePrefixTable2 i prime_data composite_data) ”
  &&  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)

noncomputable def solver_partial_solve_wit_4 : Prop := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data)) (PreH16 : (PrimeFactorBagPrefix a i factor_data)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (i * 10)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (PrimeFactorBagPrefix a i factor_data) ”
  &&  (((values_pre + (i * sizeof(INT)))) # Int |-> ((Znth i a (0 : Int))))
  ** (intArray.missing_i values_pre i (0 : Int) n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : ((0 : Int) <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorScanState a prime_data i j x factor_data)) (PreH21 : (FactorScanState2 a prime_data i j x factor_data)) (PreH22 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (j < pc) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i j x factor_data) ” &&
  “ (FactorScanState2 a prime_data i j x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i j x count) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int |-> ((Znth j prime_data (0 : Int))))
  ** (intArray.missing_i ( &( "primes" ) ) j (0 : Int) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (j < pc)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : ((0 : Int) <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorScanState a prime_data i j x factor_data)) (PreH21 : (FactorScanState2 a prime_data i j x factor_data)) (PreH22 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (j < pc) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i j x factor_data) ” &&
  “ (FactorScanState2 a prime_data i j x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i j x count) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int |-> ((Znth j prime_data (0 : Int))))
  ** (intArray.missing_i ( &( "primes" ) ) j (0 : Int) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH2 : (j < pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x) ” &&
  “ (j < pc) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i j x factor_data) ” &&
  “ (FactorScanState2 a prime_data i j x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i j x count) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int |-> ((Znth j prime_data (0 : Int))))
  ** (intArray.missing_i ( &( "primes" ) ) j (0 : Int) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int)) ” &&
  “ (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x) ” &&
  “ (j < pc) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i j x factor_data) ” &&
  “ (FactorScanState2 a prime_data i j x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i j x count) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int |-> ((Znth j prime_data (0 : Int))))
  ** (intArray.missing_i ( &( "primes" ) ) j (0 : Int) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int)) ” &&
  “ (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) <= x) ” &&
  “ (j < pc) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i j x factor_data) ” &&
  “ (FactorScanState2 a prime_data i j x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i j x count) ”
  &&  (((factors + (count * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j < pc)) (PreH9 : (1 <= x)) (PreH10 : (x <= 1000000000)) (PreH11 : (pc = (Zlength (prime_data)))) (PreH12 : ((0 : Int) <= pc)) (PreH13 : (pc < 4000)) (PreH14 : ((Zlength (composite_data)) = 31624)) (PreH15 : (count = (Zlength (factor_data)))) (PreH16 : (1 <= count)) (PreH17 : (count <= ((i * 10) + 9))) (PreH18 : (CompletePrimeTable prime_data)) (PreH19 : (FactorDivideState a prime_data i j x factor_data)) (PreH20 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ (1 <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorDivideState a prime_data i j x factor_data) ” &&
  “ (FactorDivideState2 a prime_data i j x factor_data) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int |-> ((Znth j prime_data (0 : Int))))
  ** (intArray.missing_i ( &( "primes" ) ) j (0 : Int) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int))) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j < pc)) (PreH10 : (1 <= x)) (PreH11 : (x <= 1000000000)) (PreH12 : (pc = (Zlength (prime_data)))) (PreH13 : ((0 : Int) <= pc)) (PreH14 : (pc < 4000)) (PreH15 : ((Zlength (composite_data)) = 31624)) (PreH16 : (count = (Zlength (factor_data)))) (PreH17 : (1 <= count)) (PreH18 : (count <= ((i * 10) + 9))) (PreH19 : (CompletePrimeTable prime_data)) (PreH20 : (FactorDivideState a prime_data i j x factor_data)) (PreH21 : (FactorDivideState2 a prime_data i j x factor_data)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((Z.rem x (Znth j prime_data (0 : Int))) = (0 : Int)) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ (1 <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorDivideState a prime_data i j x factor_data) ” &&
  “ (FactorDivideState2 a prime_data i j x factor_data) ”
  &&  (((( &( "primes" ) ) + (j * sizeof(INT)))) # Int |-> ((Znth j prime_data (0 : Int))))
  ** (intArray.missing_i ( &( "primes" ) ) j (0 : Int) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (j >= pc)) (PreH3 : (n_pre = (Zlength (a)))) (PreH4 : (2 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= pc)) (PreH11 : (1 <= x)) (PreH12 : (x <= 1000000000)) (PreH13 : (pc = (Zlength (prime_data)))) (PreH14 : ((0 : Int) <= pc)) (PreH15 : (pc < 4000)) (PreH16 : ((Zlength (composite_data)) = 31624)) (PreH17 : (count = (Zlength (factor_data)))) (PreH18 : ((0 : Int) <= count)) (PreH19 : (count <= ((i * 10) + 9))) (PreH20 : (CompletePrimeTable prime_data)) (PreH21 : (FactorScanState a prime_data i j x factor_data)) (PreH22 : (FactorScanState2 a prime_data i j x factor_data)) (PreH23 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (x > 1) ” &&
  “ (j >= pc) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i j x factor_data) ” &&
  “ (FactorScanState2 a prime_data i j x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i j x count) ”
  &&  (((factors + (count * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (x : Int) (pc : Int) (j : Int) (i : Int) (PreH1 : (x > 1)) (PreH2 : (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) > x)) (PreH3 : (j < pc)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : (2 <= (Zlength (a)))) (PreH6 : ((Zlength (a)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= pc)) (PreH12 : (1 <= x)) (PreH13 : (x <= 1000000000)) (PreH14 : (pc = (Zlength (prime_data)))) (PreH15 : ((0 : Int) <= pc)) (PreH16 : (pc < 4000)) (PreH17 : ((Zlength (composite_data)) = 31624)) (PreH18 : (count = (Zlength (factor_data)))) (PreH19 : ((0 : Int) <= count)) (PreH20 : (count <= ((i * 10) + 9))) (PreH21 : (CompletePrimeTable prime_data)) (PreH22 : (FactorScanState a prime_data i j x factor_data)) (PreH23 : (FactorScanState2 a prime_data i j x factor_data)) (PreH24 : (FactorAppendCapacity prime_data i j x count)) ,
  (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (x > 1) ” &&
  “ (((Znth j prime_data (0 : Int)) * (Znth j prime_data (0 : Int))) > x) ” &&
  “ (j < pc) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= pc) ” &&
  “ (1 <= x) ” &&
  “ (x <= 1000000000) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= ((i * 10) + 9)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (FactorScanState a prime_data i j x factor_data) ” &&
  “ (FactorScanState2 a prime_data i j x factor_data) ” &&
  “ (FactorAppendCapacity prime_data i j x count) ”
  &&  (((factors + (count * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg factors (count + 1) (n_pre * 10))
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)

noncomputable def solver_partial_solve_wit_15_pure : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data)) (PreH16 : (PrimeFactorBagPrefix a i factor_data)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (count = (Zlength (factor_data))) ” &&
  “ (sizeof(INT) = sizeof(INT)) ”

noncomputable def solver_partial_solve_wit_15_aux : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (factor_data : (List Int)) (count : Int) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (pc = (Zlength (prime_data)))) (PreH9 : ((0 : Int) <= pc)) (PreH10 : (pc < 4000)) (PreH11 : ((Zlength (composite_data)) = 31624)) (PreH12 : (count = (Zlength (factor_data)))) (PreH13 : ((0 : Int) <= count)) (PreH14 : (count <= (i * 10))) (PreH15 : (CompletePrimeTable prime_data)) (PreH16 : (PrimeFactorBagPrefix a i factor_data)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count factor_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (count = (Zlength (factor_data))) ” &&
  “ (sizeof(INT) = sizeof(INT)) ” &&
  “ (i >= n_pre) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (a)))) -> ((1 <= (Znth k a (0 : Int))) ∧ ((Znth k a (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ (count = (Zlength (factor_data))) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (i * 10)) ” &&
  “ (CompletePrimeTable prime_data) ” &&
  “ (PrimeFactorBagPrefix a i factor_data) ”
  &&  (intArray.full factors count factor_data)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_15 : Prop := solver_partial_solve_wit_15_pure -> solver_partial_solve_wit_15_aux

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH16 : (DuplicateScanLoopState sorted count i ok)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (i < count) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ (1 <= i) ” &&
  “ (i <= (count + 1)) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (increasing sorted) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted) ” &&
  “ (DuplicateScanLoopState sorted count i ok) ”
  &&  (((factors + (i * sizeof(INT)))) # Int |-> ((Znth i sorted (0 : Int))))
  ** (intArray.missing_i factors i (0 : Int) count sorted)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_17 : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (factors : Int) (ok : Int) (sorted : (List Int)) (composite_data : (List Int)) (prime_data : (List Int)) (pc : Int) (i : Int) (count : Int) (PreH1 : (i < count)) (PreH2 : (n_pre = (Zlength (a)))) (PreH3 : (2 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 100000)) (PreH5 : ((0 : Int) <= count)) (PreH6 : (count <= (n_pre * 10))) (PreH7 : (1 <= i)) (PreH8 : (i <= (count + 1))) (PreH9 : (pc = (Zlength (prime_data)))) (PreH10 : ((0 : Int) <= pc)) (PreH11 : (pc < 4000)) (PreH12 : ((Zlength (composite_data)) = 31624)) (PreH13 : ((Zlength (sorted)) = count)) (PreH14 : (increasing sorted)) (PreH15 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH16 : (DuplicateScanLoopState sorted count i ok)) ,
  (intArray.full factors count sorted)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ (i < count) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ (1 <= i) ” &&
  “ (i <= (count + 1)) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (increasing sorted) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted) ” &&
  “ (DuplicateScanLoopState sorted count i ok) ”
  &&  (((factors + ((i - 1) * sizeof(INT)))) # Int |-> ((Znth (i - 1) sorted (0 : Int))))
  ** (intArray.missing_i factors (i - 1) (0 : Int) count sorted)
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.undef_seg factors count (n_pre * 10))

noncomputable def solver_partial_solve_wit_18_pure : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (prime_data : (List Int)) (composite_data : (List Int)) (sorted : (List Int)) (count : Int) (pc : Int) (ok : Int) (factors : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : ((0 : Int) <= count)) (PreH5 : (count <= (n_pre * 10))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : ((0 : Int) <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted)) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH13 : (DuplicatePrefixState sorted count ok)) (PreH14 : (Spec a ok)) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "count" ) )) # Int |-> (count))
  ** ((( &( "pc" ) )) # Int |-> (pc))
  ** ((( &( "ok" ) )) # Int |-> (ok))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** ((( &( "factors" ) )) # Ptr |-> (factors))
  ** (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ ((Zlength (sorted)) = count) ”

noncomputable def solver_partial_solve_wit_18_aux : Prop :=
  forall (n_pre : Int) (values_pre : Int) (a : (List Int)) (prime_data : (List Int)) (composite_data : (List Int)) (sorted : (List Int)) (count : Int) (pc : Int) (ok : Int) (factors : Int) (PreH1 : (n_pre = (Zlength (a)))) (PreH2 : (2 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 100000)) (PreH4 : ((0 : Int) <= count)) (PreH5 : (count <= (n_pre * 10))) (PreH6 : (pc = (Zlength (prime_data)))) (PreH7 : ((0 : Int) <= pc)) (PreH8 : (pc < 4000)) (PreH9 : ((Zlength (composite_data)) = 31624)) (PreH10 : ((Zlength (sorted)) = count)) (PreH11 : (increasing sorted)) (PreH12 : (PrimeFactorBagPrefix a n_pre sorted)) (PreH13 : (DuplicatePrefixState sorted count ok)) (PreH14 : (Spec a ok)) ,
  (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)
  ** (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
|--
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (2 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 100000) ” &&
  “ ((0 : Int) <= count) ” &&
  “ (count <= (n_pre * 10)) ” &&
  “ (pc = (Zlength (prime_data))) ” &&
  “ ((0 : Int) <= pc) ” &&
  “ (pc < 4000) ” &&
  “ ((Zlength (composite_data)) = 31624) ” &&
  “ ((Zlength (sorted)) = count) ” &&
  “ (increasing sorted) ” &&
  “ (PrimeFactorBagPrefix a n_pre sorted) ” &&
  “ (DuplicatePrefixState sorted count ok) ” &&
  “ (Spec a ok) ”
  &&  (intArray.full factors count sorted)
  ** (intArray.undef_seg factors count (n_pre * 10))
  ** (intArray.full values_pre n_pre a)
  ** (intArray.full ( &( "primes" ) ) pc prime_data)
  ** (intArray.undef_seg ( &( "primes" ) ) pc 4000)
  ** (ucharArray.full ( &( "composite" ) ) 31624 composite_data)

noncomputable def solver_partial_solve_wit_18 : Prop := solver_partial_solve_wit_18_pure -> solver_partial_solve_wit_18_aux


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_21 : solver_safety_wit_21
  proof_of_solver_safety_wit_22 : solver_safety_wit_22
  proof_of_solver_safety_wit_24 : solver_safety_wit_24
  proof_of_solver_safety_wit_26 : solver_safety_wit_26
  proof_of_solver_safety_wit_27 : solver_safety_wit_27
  proof_of_solver_safety_wit_28 : solver_safety_wit_28
  proof_of_solver_safety_wit_29 : solver_safety_wit_29
  proof_of_solver_safety_wit_30 : solver_safety_wit_30
  proof_of_solver_safety_wit_31 : solver_safety_wit_31
  proof_of_solver_safety_wit_32 : solver_safety_wit_32
  proof_of_solver_safety_wit_33 : solver_safety_wit_33
  proof_of_solver_safety_wit_34 : solver_safety_wit_34
  proof_of_solver_safety_wit_35 : solver_safety_wit_35
  proof_of_solver_safety_wit_36 : solver_safety_wit_36
  proof_of_solver_safety_wit_37 : solver_safety_wit_37
  proof_of_solver_safety_wit_38 : solver_safety_wit_38
  proof_of_solver_safety_wit_39 : solver_safety_wit_39
  proof_of_solver_safety_wit_40 : solver_safety_wit_40
  proof_of_solver_safety_wit_41 : solver_safety_wit_41
  proof_of_solver_safety_wit_42 : solver_safety_wit_42
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8
  proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9
  proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10
  proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11
  proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12
  proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13
  proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14
  proof_of_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17
  proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure
  proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_safety_wit_23 : solver_safety_wit_23
  proof_of_solver_safety_wit_25 : solver_safety_wit_25
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_entail_wit_8 : solver_entail_wit_8
  proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1
  proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2
  proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1
  proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2
  proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3
  proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4
  proof_of_solver_entail_wit_11 : solver_entail_wit_11
  proof_of_solver_entail_wit_12 : solver_entail_wit_12
  proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1
  proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2
  proof_of_solver_entail_wit_14 : solver_entail_wit_14

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_goal
