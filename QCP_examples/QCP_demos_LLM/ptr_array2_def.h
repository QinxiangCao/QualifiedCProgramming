/*@ Extern Coq (CharPtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
               (CharPtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (CharArray::full : Z -> Z -> list Z -> Assertion)
               (CharArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
*/

/*@ include strategies "ptr_array2.strategies" */
