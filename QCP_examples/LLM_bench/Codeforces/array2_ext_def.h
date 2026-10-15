#ifndef ARRAY2_EXT_DEF_H
#define ARRAY2_EXT_DEF_H

/*@ Extern Coq (IntArray2::full : Z -> Z -> Z -> list (list Z) -> Assertion)
               (IntArray2::missing_i : Z -> Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (IntArray2::mixed_full : Z -> Z -> Z -> list (list (option Z)) -> Assertion)
               (IntArray2::mixed_missing_i : Z -> Z -> Z -> Z -> Z -> list (list (option Z)) -> Assertion)
               (IntArray2::undef_full : Z -> Z -> Z -> Assertion)
               (IntArray2::undef_missing_i : Z -> Z -> Z -> Z -> Z -> Assertion)
               (IntArray::full : Z -> Z -> list Z -> Assertion)
               (IntArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
               (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
               (IntArray::undef_full : Z -> Z -> Assertion)
               (IntArray::undef_missing_i : Z -> Z -> Z -> Z -> Assertion)
               (CharArray2::full : Z -> Z -> Z -> list (list Z) -> Assertion)
               (CharArray2::missing_i : Z -> Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (CharArray2::mixed_full : Z -> Z -> Z -> list (list (option Z)) -> Assertion)
               (CharArray2::mixed_missing_i : Z -> Z -> Z -> Z -> Z -> list (list (option Z)) -> Assertion)
               (CharArray2::undef_full : Z -> Z -> Z -> Assertion)
               (CharArray2::undef_missing_i : Z -> Z -> Z -> Z -> Z -> Assertion)
               (CharArray::full : Z -> Z -> list Z -> Assertion)
               (CharArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (CharArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
               (CharArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
               (CharArray::undef_full : Z -> Z -> Assertion)
               (CharArray::undef_missing_i : Z -> Z -> Z -> Z -> Assertion)
               (Array2::mixed_cell : list (option Z) -> Z -> Z -> Prop)
               (Array2::mixed_val : list (option Z) -> Z -> Z)
               (Array2::mixed_def : list (option Z) -> Z -> Prop)
               (Array2::replace_row : Z -> list Z -> list (list Z) -> list (list Z))
               (Array2::some_rows : list (list Z) -> list (list (option Z)))
               (Array2::replace_mixed_row : Z -> list (option Z) -> list (list (option Z)) -> list (list (option Z)))
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
*/

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib */

/*@ include strategies "array2.strategies" */
/*@ include strategies "array2_char.strategies" */
/*@ include strategies "int_array.strategies" */
/*@ include strategies "char_array.strategies" */
/*@ include strategies "array2_ext.strategies" */


#endif
