import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance sieve_of_euler_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def get_prime_safety_wit_1 : Prop :=
  forall (prime_pre : Int) (tot_pre : Int) (n_pre : Int) (prime0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "z" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "flag" ) ) 46341)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def get_prime_safety_wit_2 : Prop :=
  forall (prime_pre : Int) (tot_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_init : (List Int)) (z : Int) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init)) = (z - 2))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot_pre))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 z flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) z (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def get_prime_safety_wit_3 : Prop :=
  forall (prime_pre : Int) (tot_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_init : (List Int)) (z : Int) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init)) = (z - 2))) ,
  (intArray.seg ( &( "flag" ) ) 2 (z + 1) (flag_init ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "flag" ) ) (z + 1) (n_pre + 1))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot_pre))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((z + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (z + 1)) ”

noncomputable def get_prime_safety_wit_4 : Prop :=
  forall (prime_pre : Int) (tot_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_init : (List Int)) (z : Int) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init)) = (z - 2))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot_pre))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 z flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) z (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def get_prime_safety_wit_5 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_init : (List Int)) (z : Int) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init)) = (z - 2))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> ((0 : Int)))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 z flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) z (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def get_prime_safety_wit_6 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l)) (PreH8 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) (replace_Znth ((i - 2)) (i) (flag_l)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def get_prime_safety_wit_7 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l : (List Int)) (i : Int) (tot : Int) (PreH1 : (i > n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l)) (PreH8 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def get_prime_safety_wit_8 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((tot + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tot + 1)) ”

noncomputable def get_prime_safety_wit_9 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def get_prime_safety_wit_10 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.seg prime_pre 1 (n_pre + 1) (replace_Znth (((tot + 1) - 1)) (i) (prime_l)))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> ((tot + 1)))
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def get_prime_safety_wit_11 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def get_prime_safety_wit_12 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH10 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH11 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * (Znth (j - 1) prime_l (0 : Int)))) ”

noncomputable def get_prime_safety_wit_13 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j > tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ False ”

noncomputable def get_prime_safety_wit_14 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * (Znth (j - 1) prime_l (0 : Int)))) ”

noncomputable def get_prime_safety_wit_15 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l)) (PreH11 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1))) (PreH16 : (¬((Z.divide (Znth (j - 1) prime_l (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((i ≠ (INT_MIN)) ∨ ((Znth (j - 1) prime_l (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) ≠ (0 : Int)) ”

noncomputable def get_prime_safety_wit_16 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l)) (PreH11 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1))) (PreH16 : (¬((Z.divide (Znth (j - 1) prime_l (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def get_prime_safety_wit_17 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l prime_l)) (PreH10 : (2 <= (Znth j prime_l (0 : Int)))) (PreH11 : ((Znth j prime_l (0 : Int)) <= i)) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (tot < (i + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def get_prime_safety_wit_18 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH11 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def get_prime_safety_wit_19 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH10 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1) tot flag_l prime_l)) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (2 <= (i + 1))) (PreH15 : ((i + 1) <= (n_pre + 1))) (PreH16 : ((0 : Int) <= tot)) (PreH17 : (tot < (i + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def get_prime_entail_wit_1 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.undef_full ( &( "flag" ) ) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  EX flag_init : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((Zlength (prime0)) = n_pre) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ ((Zlength (flag_init)) = (2 - 2)) ”
  &&  (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 2 flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) 2 (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
) \/
(
forall (n_pre : Int) (prime0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.undef_full ( &( "flag" ) ) 46341)
|--
  “ ((Zlength ((@List.nil Int))) = (2 - 2)) ”
  &&  (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) 2 (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
)

noncomputable def get_prime_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.undef_full ( &( "flag" ) ) 46341)
|--
  “ ((Zlength ((@List.nil Int))) = (2 - 2)) ”

noncomputable def get_prime_entail_wit_1_split_goal_spatial : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.undef_full ( &( "flag" ) ) 46341)
|--
  (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) 2 (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)

noncomputable def get_prime_entail_wit_2 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_init_2 : (List Int)) (z : Int) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init_2)) = (z - 2))) ,
  (intArray.seg ( &( "flag" ) ) 2 (z + 1) (flag_init_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "flag" ) ) (z + 1) (n_pre + 1))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_init : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((Zlength (prime0)) = n_pre) ” &&
  “ (2 <= (z + 1)) ” &&
  “ ((z + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (flag_init)) = ((z + 1) - 2)) ”
  &&  (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 (z + 1) flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) (z + 1) (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
) \/
(
forall (n_pre : Int) (prime0 : (List Int)) (flag_init_2 : (List Int)) (z : Int) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init_2)) = (z - 2))) ,
  TT && emp 
|--
  “ ((Zlength ((flag_init_2 ++ ((0 : Int) :: (@List.nil Int))))) = ((z + 1) - 2)) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (flag_init_2 : (List Int)) (z : Int) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init_2)) = (z - 2))) ,
  ((Zlength ((flag_init_2 ++ ((0 : Int) :: (@List.nil Int))))) = ((z + 1) - 2))

noncomputable def get_prime_entail_wit_3 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_init : (List Int)) (z : Int) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init)) = (z - 2))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 z flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) z (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_l : (List Int),
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ (EulerInitPrefix n_pre 2 flag_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime0)) = n_pre) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
) \/
(
forall (n_pre : Int) (prime0 : (List Int)) (flag_init : (List Int)) (z : Int) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init)) = (z - 2))) ,
  (intArray.seg ( &( "flag" ) ) 2 z flag_init)
|--
  EX flag_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ (EulerInitPrefix n_pre 2 flag_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime0)) = n_pre) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
)

noncomputable def get_prime_entail_wit_4 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) (replace_Znth ((i - 2)) (i) (flag_l_2)))
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  EX flag_l : (List Int),
  “ (tot = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (EulerInitPrefix n_pre (i + 1) flag_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime0)) = n_pre) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
) \/
(
forall (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth ((i - 2)) (i) (flag_l_2)))) = (n_pre - 1)) ” &&
  “ (EulerInitPrefix n_pre (i + 1) (replace_Znth ((i - 2)) (i) (flag_l_2))) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  ((Zlength ((replace_Znth ((i - 2)) (i) (flag_l_2)))) = (n_pre - 1))

noncomputable def get_prime_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (EulerInitPrefix n_pre (i + 1) (replace_Znth ((i - 2)) (i) (flag_l_2)))

noncomputable def get_prime_entail_wit_5 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i > n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < 2) ” &&
  “ (EulerOuterState n_pre 2 tot flag_l prime_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i > n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre 2 (0 : Int) flag_l_2 prime0) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i > n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (EulerOuterState n_pre 2 (0 : Int) flag_l_2 prime0)

noncomputable def get_prime_entail_wit_6_1 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)))
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= (tot + 1)) ” &&
  “ ((tot + 1) <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (tot + 1)) ” &&
  “ (EulerInnerState n_pre i 1 (tot + 1) flag_l prime_l) ” &&
  “ (2 <= (Znth (1 - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (1 - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ ((tot + 1) < (i + 1)) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)))) = n_pre) ” &&
  “ ((Znth (1 - 1) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int)) <= i) ” &&
  “ (2 <= (Znth (1 - 1) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int))) ” &&
  “ (EulerInnerState n_pre i 1 (tot + 1) flag_l_2 (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2))) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_6_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  ((Zlength ((replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)))) = n_pre)

noncomputable def get_prime_entail_wit_6_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  ((Znth (1 - 1) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_6_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (2 <= (Znth (1 - 1) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int)))

noncomputable def get_prime_entail_wit_6_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (EulerInnerState n_pre i 1 (tot + 1) flag_l_2 (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)))

noncomputable def get_prime_entail_wit_6_2 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= tot) ” &&
  “ (EulerInnerState n_pre i 1 tot flag_l prime_l) ” &&
  “ (2 <= (Znth (1 - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (1 - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  TT && emp 
|--
  “ ((Znth (1 - 1) prime_l_2 (0 : Int)) <= i) ” &&
  “ (2 <= (Znth (1 - 1) prime_l_2 (0 : Int))) ” &&
  “ (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2) ” &&
  “ (1 <= tot) ” &&
  “ (1 <= tot) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_6_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  ((Znth (1 - 1) prime_l_2 (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_6_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (2 <= (Znth (1 - 1) prime_l_2 (0 : Int)))

noncomputable def get_prime_entail_wit_6_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_6_2_split_goal_4 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (1 <= tot)

noncomputable def get_prime_entail_wit_6_2_split_goal_5 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (1 <= tot)

noncomputable def get_prime_entail_wit_7 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) (replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (EulerInnerMarkedState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ” &&
  “ (¬((Z.divide (Znth (j - 1) prime_l (0 : Int)) i)) -> ((j + 1) <= tot)) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  TT && emp 
|--
  “ (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot)) ” &&
  “ ((Zlength ((replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)))) = (n_pre - 1)) ” &&
  “ (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)) prime_l_2) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))

noncomputable def get_prime_entail_wit_7_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  ((Zlength ((replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)))) = (n_pre - 1))

noncomputable def get_prime_entail_wit_7_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)) prime_l_2)

noncomputable def get_prime_entail_wit_8 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ (EulerOuterState n_pre (i + 1) tot flag_l prime_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < (i + 1)) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_9 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= tot) ” &&
  “ (EulerInnerState n_pre i (j + 1) tot flag_l prime_l) ” &&
  “ (2 <= (Znth j prime_l (0 : Int))) ” &&
  “ ((Znth j prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  TT && emp 
|--
  “ ((Znth j prime_l_2 (0 : Int)) <= i) ” &&
  “ (2 <= (Znth j prime_l_2 (0 : Int))) ” &&
  “ (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2) ” &&
  “ ((j + 1) <= tot) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  ((Znth j prime_l_2 (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_9_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (2 <= (Znth j prime_l_2 (0 : Int)))

noncomputable def get_prime_entail_wit_9_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_9_split_goal_4 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1))) (PreH17 : (¬((Z.divide (Znth (j - 1) prime_l_2 (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  ((j + 1) <= tot)

noncomputable def get_prime_entail_wit_10 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1))) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= tot) ” &&
  “ (EulerInnerState n_pre i (j + 1) tot flag_l prime_l) ” &&
  “ (2 <= (Znth ((j + 1) - 1) prime_l (0 : Int))) ” &&
  “ ((Znth ((j + 1) - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1))) ,
  TT && emp 
|--
  “ ((Znth ((j + 1) - 1) prime_l_2 (0 : Int)) <= i) ” &&
  “ (2 <= (Znth ((j + 1) - 1) prime_l_2 (0 : Int))) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_10_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1))) ,
  ((Znth ((j + 1) - 1) prime_l_2 (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_10_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1))) ,
  (2 <= (Znth ((j + 1) - 1) prime_l_2 (0 : Int)))

noncomputable def get_prime_entail_wit_11_1 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH11 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH13 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH14 : ((Zlength (prime_l_2)) = n_pre)) (PreH15 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < (i + 1)) ” &&
  “ (EulerOuterState n_pre (i + 1) tot flag_l prime_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH11 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH13 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH14 : ((Zlength (prime_l_2)) = n_pre)) (PreH15 : (tot < (i + 1))) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_11_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH11 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH13 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH14 : ((Zlength (prime_l_2)) = n_pre)) (PreH15 : (tot < (i + 1))) ,
  (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_11_2 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH10 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (2 <= (i + 1))) (PreH15 : ((i + 1) <= (n_pre + 1))) (PreH16 : ((0 : Int) <= tot)) (PreH17 : (tot < (i + 1))) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l_2)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < (i + 1)) ” &&
  “ (EulerOuterState n_pre (i + 1) tot flag_l prime_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_entail_wit_12 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : ((0 : Int) <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH9 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH10 : ((Zlength (prime_l)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  EX flag_out : (List Int), EX prime_out : (List Int),
  “ ((0 : Int) <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerSieveResult n_pre tot flag_out prime_out) ”
  &&  (intArray.seg prime_pre 1 (n_pre + 1) prime_out)
  ** (intArray.undef_full ( &( "flag" ) ) 46341)
) \/
(
forall (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : ((0 : Int) <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH9 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH10 : ((Zlength (prime_l)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  EX flag_out : (List Int),
  “ ((0 : Int) <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerSieveResult n_pre tot flag_out prime_l) ”
  &&  (intArray.undef_full ( &( "flag" ) ) 46341)
)

noncomputable def get_prime_return_wit_1 : Prop :=
  (
forall (prime_pre : Int) (n_pre : Int) (flag_out : (List Int)) (prime_out_2 : (List Int)) (tot : Int) (PreH1 : ((0 : Int) <= tot)) (PreH2 : (tot <= n_pre)) (PreH3 : (EulerSieveResult n_pre tot flag_out prime_out_2)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_out_2)
|--
  EX prime_out : (List Int), EX final_tot : Int,
  “ (prime_pre = prime_pre) ” &&
  “ ((0 : Int) <= final_tot) ” &&
  “ (final_tot <= n_pre) ” &&
  “ (Modern.PrimePrefixList n_pre final_tot prime_out) ”
  &&  (intArray.seg prime_pre 1 (n_pre + 1) prime_out)
) \/
(
forall (n_pre : Int) (flag_out : (List Int)) (prime_out_2 : (List Int)) (tot : Int) (PreH1 : ((0 : Int) <= tot)) (PreH2 : (tot <= n_pre)) (PreH3 : (EulerSieveResult n_pre tot flag_out prime_out_2)) ,
  TT && emp 
|--
  EX final_tot : Int,
  “ ((0 : Int) <= final_tot) ” &&
  “ (final_tot <= n_pre) ” &&
  “ (Modern.PrimePrefixList n_pre final_tot prime_out_2) ”
  &&  emp
)

noncomputable def get_prime_partial_solve_wit_1 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_init : (List Int)) (z : Int) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1))) (PreH7 : ((Zlength (flag_init)) = (z - 2))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 z flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) z (n_pre + 1))
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ (z <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((Zlength (prime0)) = n_pre) ” &&
  “ (2 <= z) ” &&
  “ (z <= (n_pre + 1)) ” &&
  “ ((Zlength (flag_init)) = (z - 2)) ”
  &&  (((( &( "flag" ) ) + (z * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "flag" ) ) (z + 1) (n_pre + 1))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.seg ( &( "flag" ) ) 2 z flag_init)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)

noncomputable def get_prime_partial_solve_wit_2 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l)) (PreH8 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ (i <= n_pre) ” &&
  “ (tot = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ (EulerInitPrefix n_pre i flag_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime0)) = n_pre) ”
  &&  (((( &( "flag" ) ) + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "flag" ) ) i 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)

noncomputable def get_prime_partial_solve_wit_3 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : ((0 : Int) <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH9 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH10 : ((Zlength (prime_l)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (i <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < i) ” &&
  “ (EulerOuterState n_pre i tot flag_l prime_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (((( &( "flag" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth (i - 2) flag_l (0 : Int))))
  ** (intArray.missing_i ( &( "flag" ) ) i 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_partial_solve_wit_4 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((Znth (i - 2) flag_l (0 : Int)) = i) ” &&
  “ (i <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < i) ” &&
  “ (EulerOuterState n_pre i tot flag_l prime_l) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (((prime_pre + ((tot + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i prime_pre (tot + 1) 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)

noncomputable def get_prime_partial_solve_wit_5 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH10 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH11 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (tot < (i + 1))) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)

noncomputable def get_prime_partial_solve_wit_6 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)

noncomputable def get_prime_partial_solve_wit_7 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)

noncomputable def get_prime_partial_solve_wit_8 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1))) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
|--
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ”
  &&  (((( &( "flag" ) ) + ((i * (Znth (j - 1) prime_l (0 : Int))) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "flag" ) ) (i * (Znth (j - 1) prime_l (0 : Int))) 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)

noncomputable def get_prime_partial_solve_wit_9 : Prop :=
  forall (prime_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l)) (PreH11 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1))) (PreH16 : (¬((Z.divide (Znth (j - 1) prime_l (0 : Int)) i)) -> ((j + 1) <= tot))) ,
  (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (EulerInnerMarkedState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((Zlength (flag_l)) = (n_pre - 1)) ” &&
  “ ((Zlength (prime_l)) = n_pre) ” &&
  “ (tot < (i + 1)) ” &&
  “ (¬((Z.divide (Znth (j - 1) prime_l (0 : Int)) i)) -> ((j + 1) <= tot)) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg ( &( "flag" ) ) 2 (n_pre + 1) flag_l)
  ** (intArray.undef_seg ( &( "flag" ) ) (0 : Int) 2)
  ** (intArray.undef_seg ( &( "flag" ) ) (n_pre + 1) 46341)


structure VC_Correct : Type where
  proof_of_get_prime_safety_wit_1 : get_prime_safety_wit_1
  proof_of_get_prime_safety_wit_2 : get_prime_safety_wit_2
  proof_of_get_prime_safety_wit_3 : get_prime_safety_wit_3
  proof_of_get_prime_safety_wit_4 : get_prime_safety_wit_4
  proof_of_get_prime_safety_wit_5 : get_prime_safety_wit_5
  proof_of_get_prime_safety_wit_6 : get_prime_safety_wit_6
  proof_of_get_prime_safety_wit_7 : get_prime_safety_wit_7
  proof_of_get_prime_safety_wit_8 : get_prime_safety_wit_8
  proof_of_get_prime_safety_wit_9 : get_prime_safety_wit_9
  proof_of_get_prime_safety_wit_10 : get_prime_safety_wit_10
  proof_of_get_prime_safety_wit_11 : get_prime_safety_wit_11
  proof_of_get_prime_safety_wit_12 : get_prime_safety_wit_12
  proof_of_get_prime_safety_wit_13 : get_prime_safety_wit_13
  proof_of_get_prime_safety_wit_14 : get_prime_safety_wit_14
  proof_of_get_prime_safety_wit_15 : get_prime_safety_wit_15
  proof_of_get_prime_safety_wit_16 : get_prime_safety_wit_16
  proof_of_get_prime_safety_wit_17 : get_prime_safety_wit_17
  proof_of_get_prime_safety_wit_18 : get_prime_safety_wit_18
  proof_of_get_prime_safety_wit_19 : get_prime_safety_wit_19
  proof_of_get_prime_entail_wit_11_2 : get_prime_entail_wit_11_2
  proof_of_get_prime_partial_solve_wit_1 : get_prime_partial_solve_wit_1
  proof_of_get_prime_partial_solve_wit_2 : get_prime_partial_solve_wit_2
  proof_of_get_prime_partial_solve_wit_3 : get_prime_partial_solve_wit_3
  proof_of_get_prime_partial_solve_wit_4 : get_prime_partial_solve_wit_4
  proof_of_get_prime_partial_solve_wit_5 : get_prime_partial_solve_wit_5
  proof_of_get_prime_partial_solve_wit_6 : get_prime_partial_solve_wit_6
  proof_of_get_prime_partial_solve_wit_7 : get_prime_partial_solve_wit_7
  proof_of_get_prime_partial_solve_wit_8 : get_prime_partial_solve_wit_8
  proof_of_get_prime_partial_solve_wit_9 : get_prime_partial_solve_wit_9
  proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1
  proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2
  proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3
  proof_of_get_prime_entail_wit_4 : get_prime_entail_wit_4
  proof_of_get_prime_entail_wit_5 : get_prime_entail_wit_5
  proof_of_get_prime_entail_wit_6_1 : get_prime_entail_wit_6_1
  proof_of_get_prime_entail_wit_6_2 : get_prime_entail_wit_6_2
  proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7
  proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8
  proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9
  proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10
  proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1
  proof_of_get_prime_entail_wit_12 : get_prime_entail_wit_12
  proof_of_get_prime_return_wit_1 : get_prime_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_goal
