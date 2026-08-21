#include "array2_def.h"
#include "int_ptr_array2_def.h"

/*@ Extern Coq
      (GraphMatrixFlat::graph_rep :
        Z -> (list (list Z) -> Prop) -> Z -> list (list Z) -> Assertion)
      (GraphMatrixPtr::graph_rep :
        Z -> (list (list Z) -> Prop) -> Z -> list (list Z) -> Assertion)
      (GraphMatrixPtr::row_rep :
        Z -> (list (list Z) -> Prop) -> Z -> Z -> Z ->
        list (list Z) -> Assertion)
*/

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib */

/*@ include strategies "graph_matrix.strategies" */
