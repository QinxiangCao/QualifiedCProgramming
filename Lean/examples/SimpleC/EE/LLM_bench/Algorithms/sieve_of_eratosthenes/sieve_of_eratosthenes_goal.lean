import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance sieve_of_eratosthenes_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def solve_safety_wit_1 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (initial : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** (intArray.seg f_pre 1 (n_pre + 1) initial)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_2 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_3 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((i - 1)) (1) (current)))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solve_safety_wit_4 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_5 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_6 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((1 - 1)) ((0 : Int)) (current)))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solve_safety_wit_7 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((1 - 1)) ((0 : Int)) (current)))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_8 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((2 - 1)) (1) ((replace_Znth ((1 - 1)) ((0 : Int)) (current)))))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solve_safety_wit_9 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_10 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current (0 : Int)) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.seg f_pre 1 (n_pre + 1) current)
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * 2)) ”

noncomputable def solve_safety_wit_11 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current (0 : Int)) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.seg f_pre 1 (n_pre + 1) current)
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solve_safety_wit_12 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current)) ,
  ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_13 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((j - 1)) ((0 : Int)) (current)))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + i)) ”

noncomputable def solve_safety_wit_14 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current)) ,
  ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solve_safety_wit_15 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current (0 : Int)) ≠ 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solve_entail_wit_1 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (initial : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  (intArray.seg f_pre 1 (n_pre + 1) initial)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (SieveInitPrefix n_pre 1 current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (initial : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  TT && emp 
|--
  “ (SieveInitPrefix n_pre 1 initial) ”
  &&  emp
)

noncomputable def solve_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (initial : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  (SieveInitPrefix n_pre 1 initial)

noncomputable def solve_entail_wit_2 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((i - 1)) (1) (current_2)))
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (SieveInitPrefix n_pre (i + 1) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current_2)) ,
  TT && emp 
|--
  “ (SieveInitPrefix n_pre (i + 1) (replace_Znth ((i - 1)) (1) (current_2))) ”
  &&  emp
)

noncomputable def solve_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current_2)) ,
  (SieveInitPrefix n_pre (i + 1) (replace_Znth ((i - 1)) (1) (current_2)))

noncomputable def solve_entail_wit_3 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((2 - 1)) (1) ((replace_Znth ((1 - 1)) ((0 : Int)) (current_2)))))
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ (SieveStage n_pre 2 current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current_2)) ,
  TT && emp 
|--
  “ (SieveStage n_pre 2 (replace_Znth ((2 - 1)) (1) ((replace_Znth ((1 - 1)) ((0 : Int)) (current_2))))) ”
  &&  emp
)

noncomputable def solve_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current_2)) ,
  (SieveStage n_pre 2 (replace_Znth ((2 - 1)) (1) ((replace_Znth ((1 - 1)) ((0 : Int)) (current_2)))))

noncomputable def solve_entail_wit_4 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current_2)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((2 * i) <= (i * 2)) ” &&
  “ ((i * 2) <= (n_pre + i)) ” &&
  “ (SieveMarkState n_pre i (i * 2) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  TT && emp 
|--
  “ (SieveMarkState n_pre i (i * 2) current_2) ”
  &&  emp
)

noncomputable def solve_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  (SieveMarkState n_pre i (i * 2) current_2)

noncomputable def solve_entail_wit_5 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((j - 1)) ((0 : Int)) (current_2)))
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((2 * i) <= (j + i)) ” &&
  “ ((j + i) <= (n_pre + i)) ” &&
  “ (SieveMarkState n_pre i (j + i) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  TT && emp 
|--
  “ (SieveMarkState n_pre i (j + i) (replace_Znth ((j - 1)) ((0 : Int)) (current_2))) ”
  &&  emp
)

noncomputable def solve_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (SieveMarkState n_pre i (j + i) (replace_Znth ((j - 1)) ((0 : Int)) (current_2)))

noncomputable def solve_entail_wit_6_1 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current_2)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (SieveStage n_pre (i + 1) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  TT && emp 
|--
  “ (SieveStage n_pre (i + 1) current_2) ”
  &&  emp
)

noncomputable def solve_entail_wit_6_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (current_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current_2)) ,
  (SieveStage n_pre (i + 1) current_2)

noncomputable def solve_entail_wit_6_2 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) ≠ 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current_2)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (SieveStage n_pre (i + 1) current) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) current)
) \/
(
forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) ≠ 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  TT && emp 
|--
  “ (SieveStage n_pre (i + 1) current_2) ”
  &&  emp
)

noncomputable def solve_entail_wit_6_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (current_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) current_2 (0 : Int)) ≠ 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (SieveStage n_pre i current_2)) ,
  (SieveStage n_pre (i + 1) current_2)

noncomputable def solve_return_wit_1 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  EX result : (List Int),
  “ (PrimeIndicatorList n_pre result) ”
  &&  (intArray.seg f_pre 1 (n_pre + 1) result)
) \/
(
forall (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  TT && emp 
|--
  “ (PrimeIndicatorList n_pre current) ”
  &&  emp
)

noncomputable def solve_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  (PrimeIndicatorList n_pre current)

noncomputable def solve_partial_solve_wit_1 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ (i <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ (SieveInitPrefix n_pre i current) ”
  &&  (((f_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i f_pre i 1 (n_pre + 1) current)

noncomputable def solve_partial_solve_wit_2 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ (i > n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ (SieveInitPrefix n_pre i current) ”
  &&  (((f_pre + (1 * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i f_pre 1 1 (n_pre + 1) current)

noncomputable def solve_partial_solve_wit_3 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveInitPrefix n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) (replace_Znth ((1 - 1)) ((0 : Int)) (current)))
|--
  “ (i > n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ (SieveInitPrefix n_pre i current) ”
  &&  (((f_pre + (2 * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i f_pre 2 1 (n_pre + 1) (replace_Znth ((1 - 1)) ((0 : Int)) (current)))

noncomputable def solve_partial_solve_wit_4 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (SieveStage n_pre i current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ (i <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ (SieveStage n_pre i current) ”
  &&  (((f_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - 1) current (0 : Int))))
  ** (intArray.missing_i f_pre i 1 (n_pre + 1) current)

noncomputable def solve_partial_solve_wit_5 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (current : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i) <= j)) (PreH7 : (j <= (n_pre + i))) (PreH8 : (SieveMarkState n_pre i j current)) ,
  (intArray.seg f_pre 1 (n_pre + 1) current)
|--
  “ (j <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((2 * i) <= j) ” &&
  “ (j <= (n_pre + i)) ” &&
  “ (SieveMarkState n_pre i j current) ”
  &&  (((f_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i f_pre j 1 (n_pre + 1) current)


structure VC_Correct : Type where
  proof_of_solve_safety_wit_1 : solve_safety_wit_1
  proof_of_solve_safety_wit_2 : solve_safety_wit_2
  proof_of_solve_safety_wit_3 : solve_safety_wit_3
  proof_of_solve_safety_wit_4 : solve_safety_wit_4
  proof_of_solve_safety_wit_5 : solve_safety_wit_5
  proof_of_solve_safety_wit_6 : solve_safety_wit_6
  proof_of_solve_safety_wit_7 : solve_safety_wit_7
  proof_of_solve_safety_wit_8 : solve_safety_wit_8
  proof_of_solve_safety_wit_9 : solve_safety_wit_9
  proof_of_solve_safety_wit_10 : solve_safety_wit_10
  proof_of_solve_safety_wit_11 : solve_safety_wit_11
  proof_of_solve_safety_wit_12 : solve_safety_wit_12
  proof_of_solve_safety_wit_13 : solve_safety_wit_13
  proof_of_solve_safety_wit_14 : solve_safety_wit_14
  proof_of_solve_safety_wit_15 : solve_safety_wit_15
  proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1
  proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2
  proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3
  proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4
  proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5
  proof_of_solve_entail_wit_1 : solve_entail_wit_1
  proof_of_solve_entail_wit_2 : solve_entail_wit_2
  proof_of_solve_entail_wit_3 : solve_entail_wit_3
  proof_of_solve_entail_wit_4 : solve_entail_wit_4
  proof_of_solve_entail_wit_5 : solve_entail_wit_5
  proof_of_solve_entail_wit_6_1 : solve_entail_wit_6_1
  proof_of_solve_entail_wit_6_2 : solve_entail_wit_6_2
  proof_of_solve_return_wit_1 : solve_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_goal
