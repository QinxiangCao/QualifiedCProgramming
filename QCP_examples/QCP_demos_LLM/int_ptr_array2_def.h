/*@ Extern Coq (IntPtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
               (IntPtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (IntArray::full : Z -> Z -> list Z -> Assertion)
               (IntArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
*/

/*@ include strategies "int_ptr_array2.strategies" */
