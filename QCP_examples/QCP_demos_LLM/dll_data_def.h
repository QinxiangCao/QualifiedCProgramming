struct list {
    struct list *next;
    struct list *prev;
    int data;
};

/*@ Extern Coq (dlistrep : Z -> Z -> list Z -> Assertion)
               (dllseg : Z -> Z -> Z -> Z -> list Z -> Assertion)
 */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.dll_shape_lib */

struct list *malloc_dlist(int data);
void free_dlist(struct list *x);
