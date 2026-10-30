
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def*/
/*@ Extern Coq (nil : {A} -> list A)

               (cons : {A} -> A -> list A -> list A)

               (app : {A} -> list A -> list A -> list A)

               (rev : {A} -> list A -> list A)

               (map : {A} {B} -> (A -> B) -> list A -> list B)

               (concat : {A} -> list (list A) -> list A)

               (NoDup : {A} -> list A -> Prop)

               (Znth: {A} -> Z -> list A -> A -> A)

               (replace_Znth: {A} -> Z -> A -> list A -> list A)

 */
/*@ Extern Coq addr := Z */
/*@ Extern Coq TaskID := Z */
/*@ Extern Coq SwtmrID := Z */
/*@ Extern Coq Record StableGlobVars {
  g_taskCBArray: Z;
  g_swtmrCBArray: Z;
  g_allSem: Z;
  g_allQueue: Z;
}
*/
/*@ Extern Coq Record tickState {
  ts_period : Z;
  ts_val : Z;
  ts_ctrl : Z;
  ts_startTime : Z;
  ts_timeBase : Z;
  ts_oldTimeBase : Z;
  ts_timeBaseUpdate : Z;
} */
/*@ Extern Coq Record archTickTimer {
  freqNum : Z;
  irqNum : Z;
  periodMax : Z;
} */
/*@ Extern Coq (sortedLinkNode :: * => *) */
/*@ Extern Coq (DL_Node :: * => *) */
/*@ Extern Coq (sl_data: {A} -> sortedLinkNode A -> A)
               (responseTime: {A} -> sortedLinkNode A -> Z)*/
/*@ Extern Coq (data: {A} -> DL_Node A -> A)
               (ptr: {A} -> DL_Node A -> Z)*/
/*@ Extern Coq (storesortedLinkNode: {A} -> (Z -> A -> Assertion) -> Z -> sortedLinkNode A -> Assertion)
               (task_store: StableGlobVars -> Z -> TaskID -> Assertion)
               (storesortedLinkTaskNode: (StableGlobVars -> Z -> TaskID -> Assertion) -> StableGlobVars -> Z -> sortedLinkNode TaskID -> Assertion)
               (store_sorted_dll: {A} -> (Z -> A -> Assertion)  -> Z -> list (DL_Node(sortedLinkNode A)) -> Assertion)
               (store_task_sorted_dll: StableGlobVars -> list (DL_Node(sortedLinkNode TaskID)) -> Assertion)
               (store_swtmr_sorted_dll: StableGlobVars -> list (DL_Node(sortedLinkNode SwtmrID)) -> Assertion)
               (mksortedLinkNode: {A} -> A -> Z -> sortedLinkNode A)
               (getFirstNodeExpireTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> Z) 
               (increasingSortedNode: {A} -> list (DL_Node(sortedLinkNode A)) -> Prop)
               (getNodeExpireTime: {A} -> DL_Node(sortedLinkNode A) -> Z -> Z -> Z)
               (getminExpireTime: {A} -> list (DL_Node(sortedLinkNode A)) -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> Z)
               (updateNodeTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> list (DL_Node(sortedLinkNode A)))
               (getFirstNodeResponseTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z)
               (sortedLinkNodeMapping : {A} -> (DL_Node(sortedLinkNode A)) -> (DL_Node(sortedLinkNode A)))
               (getFirstNodeData: {A} -> list (DL_Node(sortedLinkNode A)) -> A) 
               (storeTick: Z -> Z -> tickState -> archTickTimer -> Assertion)
               (timebase_turnover: tickState -> tickState)
               (tick_getcycle_ret: tickState -> Z)
               (ULLONG_MAX : Z)
               (obtian_first_pointer: {A} -> Z -> list (DL_Node(sortedLinkNode A)) -> Z)
*/
/*@ Extern Coq (eq_dec: Z -> Z -> Prop) */
/*@ Extern Coq (Build_DL_Node: {A} -> A -> Z -> DL_Node A)
               (store_dll: {A} -> (Z -> A -> Assertion) -> Z -> list (DL_Node A) -> Assertion)
               (dllseg: {A} -> (Z -> A -> Assertion) -> Z -> Z -> Z -> Z-> list (DL_Node A) -> Assertion)
               (dllseg_shift: {A} -> (Z -> A -> Assertion) -> Z -> Z-> list (DL_Node A) -> Assertion)
               (dll_para: {A} -> (Z -> A -> Assertion) -> Prop)
               (dllseg_shift_rev: {A} -> (Z -> A -> Assertion) -> Z -> Z-> list (DL_Node A) -> Assertion)
*/
/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (increasing: list Z -> Prop)
               (rev : {A} -> list A -> list A)
               (sll : {A} -> (Z -> A -> Assertion) -> Z -> list A -> Assertion)
               (sllseg : {A} -> (Z -> A -> Assertion) -> Z -> Z -> list A -> Assertion)
               (map : {A} {B} -> (A -> B) -> list A -> list B)
 */
/*@ include strategies "../los_sortlink.strategies" */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll*/
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup*/
typedef enum {
    OS_SORT_LINK_DEFAULT,
    OS_SORT_LINK_TASK,
    OS_SORT_LINK_SWTMR
} SortLinkType;
typedef struct LOS_DL_LIST{
    struct LOS_DL_LIST * pstPrev;
    struct LOS_DL_LIST * pstNext;
} LOS_DL_LIST;
typedef struct SortLinkList{
    LOS_DL_LIST sortLinkNode;
    unsigned long long responseTime;
} SortLinkList;
typedef struct SortLinkAttribute{
    LOS_DL_LIST sortLink;
} SortLinkAttribute;
unsigned int TASKID;
unsigned int SWMTRID;
extern SortLinkAttribute g_taskSortLink;
extern SortLinkAttribute g_swtmrSortLink;
static inline void LOS_ListDelete(LOS_DL_LIST *node)
/*@ mid_level_spec <= low_level_spec
    With {A} (storeA1 : addr -> A -> Assertion) (p : addr) (a : A) (l1 l2 : list (DL_Node A))
    Require store_dll(storeA1, p, app(l1, cons(Build_DL_Node(a, node), l2)))
    Ensure  store_dll(storeA1, p, app(l1, l2)) &&
            undef_data_at(&node->pstNext) &&
            undef_data_at(&node->pstPrev) &&
            storeA1(node, a)
*/
;
static inline void LOS_ListDelete(LOS_DL_LIST *node)
/*@ low_level_spec
    With {A} (storeA : addr -> A -> Assertion) (a : A) (prev next : addr)
    Require node->pstNext == next &&
            next->pstPrev == node &&
            dllseg_shift(storeA, prev, node, cons(Build_DL_Node(a, node), nil()))
    Ensure  undef_data_at(&node->pstNext) &&
            undef_data_at(&node->pstPrev) &&
            storeA(node, a) &&
            prev->pstNext == next &&
            next->pstPrev == prev
*/
;
static inline void LOS_ListInit(LOS_DL_LIST *list)
/*@ With {A} (storeA1: Z -> A -> Assertion) 
    Require  undef_data_at(&(list -> pstPrev)) *
            undef_data_at(&(list -> pstNext))
    Ensure store_dll(storeA1,list,nil)
*/
;
static inline void LOS_ListDelInit(LOS_DL_LIST *list)
/*@ 
    With {A} (storeA : addr -> A -> Assertion) (a : A) (prev next : addr)
    Require list->pstNext == next &&
            next->pstPrev == list &&
            dllseg_shift(storeA, prev, list, cons(Build_DL_Node(a, list), nil()))
    Ensure  store_dll(storeA,list,nil) *
            storeA(list, a) &&
            prev->pstNext == next &&
            next->pstPrev == prev
*/
{
    list->pstNext->pstPrev = list->pstPrev;
    list->pstPrev->pstNext = list->pstNext;
    LOS_ListInit(list) /*@ where {A = A} storeA1 = storeA */;
}
