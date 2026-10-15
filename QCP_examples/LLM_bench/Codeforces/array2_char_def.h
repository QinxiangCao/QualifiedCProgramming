#ifndef ARRAY2_CHAR_DEF_H
#define ARRAY2_CHAR_DEF_H

/* Declarations only, no strategy includes: array2_char.strategies includes
   this, and array2_ext_def.h includes array2_char.strategies, so pulling the
   full array2_ext_def.h in here would be circular. */

/*@ Extern Coq (CharArray2::full : Z -> Z -> Z -> list (list Z) -> Assertion)
               (CharArray2::missing_i : Z -> Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (CharArray::full : Z -> Z -> list Z -> Assertion)
               (CharArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
*/

#endif
