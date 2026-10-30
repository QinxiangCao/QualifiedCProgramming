import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P023_765B_code_obfuscation_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (text : (List Int)) (s_pre : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  ((( &( "next" ) )) # Char |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (97 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 97) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next" ) )) # Char |-> (97))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next)) (PreH10 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "next" ) )) # Char |-> (next))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next)) (PreH11 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "next" ) )) # Char |-> (next))
|--
  “ (122 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 122) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (next < 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "next" ) )) # Char |-> (next))
|--
  “ ((next + 1) <= 127) ” &&
  “ ((-128) <= (next + 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (next < 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "next" ) )) # Char |-> ((next + 1)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ next)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next)) (PreH11 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "next" ) )) # Char |-> (next))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "next" ) )) # Char |-> (next))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next)) (PreH9 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "next" ) )) # Char |-> (next))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 500) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (text))) ” &&
  “ (97 <= 97) ” &&
  “ (97 <= 122) ” &&
  “ (ObfuscationPrefixState text (0 : Int) 97) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (text : (List Int)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  TT && emp 
|--
  “ (ObfuscationPrefixState text (0 : Int) 97) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (text : (List Int)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  (ObfuscationPrefixState text (0 : Int) 97)

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (text : (List Int)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (next < 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 500) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ” &&
  “ (97 <= (next + 1)) ” &&
  “ ((next + 1) <= 122) ” &&
  “ (ObfuscationPrefixState text (i + 1) (next + 1)) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (next < 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (ObfuscationPrefixState text (i + 1) (next + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (next < 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (ObfuscationPrefixState text (i + 1) (next + 1))

noncomputable def solver_entail_wit_2_1_split_goal_2 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (next < 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  ((i + 1) <= (Zlength (text)))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ next)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next)) (PreH11 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 500) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ” &&
  “ (97 <= next) ” &&
  “ (next <= 122) ” &&
  “ (ObfuscationPrefixState text (i + 1) next) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ next)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next)) (PreH11 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (ObfuscationPrefixState text (i + 1) next) ” &&
  “ ((i + 1) <= (Zlength (text))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ next)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next)) (PreH11 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (ObfuscationPrefixState text (i + 1) next)

noncomputable def solver_entail_wit_2_2_split_goal_2 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ next)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 500)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (97 <= next)) (PreH9 : (next <= 122)) (PreH10 : (ObfuscationPrefixState text i next)) (PreH11 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  ((i + 1) <= (Zlength (text)))

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 500) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ” &&
  “ (97 <= next) ” &&
  “ (next <= 122) ” &&
  “ (ObfuscationPrefixState text (i + 1) next) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (ObfuscationPrefixState text (i + 1) next) ” &&
  “ ((i + 1) <= (Zlength (text))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (ObfuscationPrefixState text (i + 1) next)

noncomputable def solver_entail_wit_2_3_split_goal_2 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (next >= 122)) (PreH2 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = next)) (PreH3 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 500)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (Zlength (text)))) (PreH9 : (97 <= next)) (PreH10 : (next <= 122)) (PreH11 : (ObfuscationPrefixState text i next)) (PreH12 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  ((i + 1) <= (Zlength (text)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next)) (PreH9 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (Spec text 1) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next)) (PreH9 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  TT && emp 
|--
  “ (Spec text 1) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next)) (PreH9 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (Spec text 1)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next)) (PreH10 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (Spec text (0 : Int)) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next)) (PreH10 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (Spec text (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (text : (List Int)) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) > next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next)) (PreH10 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (Spec text (0 : Int))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next)) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 500) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ (97 <= next) ” &&
  “ (next <= 122) ” &&
  “ (ObfuscationPrefixState text i next) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 500)) (PreH3 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (97 <= next)) (PreH7 : (next <= 122)) (PreH8 : (ObfuscationPrefixState text i next)) (PreH9 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 500) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ (97 <= next) ” &&
  “ (next <= 122) ” &&
  “ (ObfuscationPrefixState text i next) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (next : Int) (i : Int) (PreH1 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 500)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (97 <= next)) (PreH8 : (next <= 122)) (PreH9 : (ObfuscationPrefixState text i next)) (PreH10 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= next) ” &&
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 500) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (text)))) -> ((97 <= (Znth k text (0 : Int))) ∧ ((Znth k text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ (97 <= next) ” &&
  “ (next <= 122) ” &&
  “ (ObfuscationPrefixState text i next) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))


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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_goal
