/*@ Extern Coq (IntArray3::full : Z -> Z -> Z -> Z -> list (list (list Z)) -> Assertion)
               (IntArray3::missing_i : Z -> Z -> Z -> Z -> Z -> Z -> list (list (list Z)) -> Assertion)
               (IntArray2::full : Z -> Z -> Z -> list (list Z) -> Assertion)
               (IntArray2::missing_i : Z -> Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (IntArray::full : Z -> Z -> list Z -> Assertion)
               (IntArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
*/

/*@ include strategies "array3.strategies" */
/*@ include strategies "array2.strategies" */
/*@ include strategies "int_array.strategies" */
