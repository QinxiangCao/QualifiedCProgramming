
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
unsigned long long OS_SORT_LINK_UINT64_MAX = 2^64-1;
unsigned long long g_schedResponseTime = OS_SORT_LINK_UINT64_MAX;
SortLinkList* LOS_DL_LIST_ENTRY(LOS_DL_LIST *item)
/*@
  Require emp
  Ensure  &(__return -> sortLinkNode) == item
*/
;
static inline int LOS_ListEmpty(LOS_DL_LIST *node)
/*@ highSpec
    With {A} (storeA: Z -> A -> Assertion) (l: list (DL_Node A))
    Require store_dll(storeA,node,l)
    Ensure ((l == nil && __return == 1) || (l != nil && __return == 0)) &&
           store_dll(storeA,node,l)
*/
;
static inline int LOS_ListEmpty(LOS_DL_LIST *node)
/*@ getfirstSpec <= highSpec
    With {A} (storeA: Z -> A -> Assertion) (l: list (DL_Node A))
    Require store_dll(storeA,node,l)
    Ensure (l == nil && __return == 1 && store_dll(storeA,node,l)) ||
           ( exists (a: DL_Node A)(l1: list (DL_Node A)),
             l != nil && __return == 0 &&
             l == cons(a, l1) &&
             store_dll(storeA,node,cons(a, l1))
           )
*/
;
static inline unsigned long long GetSortLinkNextExpireTime(SortLinkAttribute *sortHead, unsigned long long startTime, unsigned long long tickPrecision)
/*@
  With {A}(storeA: Z -> A -> Assertion) (l: list(DL_Node(sortedLinkNode A)))
  Require (startTime + tickPrecision) <= ULLONG_MAX && store_sorted_dll(storeA, &(sortHead->sortLink), l) * 
          store(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, Zpow(2,64)-1) &&
          startTime >= 0 &&
          startTime <= ULLONG_MAX &&
          tickPrecision >=0 &&
          tickPrecision <= ULLONG_MAX
  Ensure  (__return == getFirstNodeExpireTime(l, startTime, tickPrecision)) &&
           store_sorted_dll(storeA, &(sortHead->sortLink), l) * store(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, Zpow(2,64)-1) 
*/
{
    /*@ store_sorted_dll(storeA, &(sortHead->sortLink), l)
        which implies
        exists pt h,
        increasingSortedNode(l) &&
        store(field_addr(&(sortHead->sortLink),struct LOS_DL_LIST,pstNext),struct LOS_DL_LIST *, h) *
        store(field_addr(&(sortHead->sortLink),struct LOS_DL_LIST,pstPrev),struct LOS_DL_LIST *, pt) *
        dllseg(storesortedLinkNode(storeA), h, &(sortHead->sortLink), &(sortHead->sortLink), pt, map(sortedLinkNodeMapping, l))
    */
    LOS_DL_LIST *head = &sortHead->sortLink;
    LOS_DL_LIST *list = head->pstNext; /*@ list == obtian_first_pointer(&(sortHead->sortLink), map(sortedLinkNodeMapping, l))*/
    /*@
    exists h pt,
    store(field_addr(&(sortHead->sortLink),struct LOS_DL_LIST,pstNext),struct LOS_DL_LIST *, h) *
    store(field_addr(&(sortHead->sortLink),struct LOS_DL_LIST,pstPrev),struct LOS_DL_LIST *, pt) *
    dllseg(storesortedLinkNode(storeA), h, &(sortHead->sortLink), &(sortHead->sortLink), pt, map(sortedLinkNodeMapping, l))
    which implies
    store_dll(storesortedLinkNode(storeA), &(sortHead->sortLink), map(sortedLinkNodeMapping, l))
    */
    if (LOS_ListEmpty(head)/*@ where (getfirstSpec) {A = sortedLinkNode(A)} storeA = storesortedLinkNode(storeA) , l = map(sortedLinkNodeMapping, l) */) {
        return OS_SORT_LINK_UINT64_MAX - tickPrecision;
    }
    SortLinkList *listSorted = LOS_DL_LIST_ENTRY(list)/*@where item = list*/;
    /*@
    exists al t l1,
    store_dll(storesortedLinkNode(storeA), &(sortHead->sortLink), cons(Build_DL_Node(mksortedLinkNode(al,t), &(listSorted->sortLinkNode)), l1))
    which implies
    exists pl pt,
    store(field_addr(&(listSorted->sortLinkNode),struct LOS_DL_LIST,pstNext),struct LOS_DL_LIST *,pl) *
    store(field_addr(&(listSorted->sortLinkNode),struct LOS_DL_LIST,pstPrev),struct LOS_DL_LIST *,&(sortHead->sortLink)) *
    store(field_addr(&(sortHead->sortLink),struct LOS_DL_LIST,pstNext),struct LOS_DL_LIST *,&(listSorted->sortLinkNode)) *
    store(field_addr(&(sortHead->sortLink),struct LOS_DL_LIST,pstPrev),struct LOS_DL_LIST *,pt) *
    dllseg(storesortedLinkNode(storeA), pl, &(listSorted->sortLinkNode), &(sortHead->sortLink), pt, l1) *
    storesortedLinkNode(storeA, &(listSorted->sortLinkNode), mksortedLinkNode(al,t))
    */
    /*@
     exists al t,
     storesortedLinkNode(storeA, &(listSorted->sortLinkNode), mksortedLinkNode(al,t))
     which implies
     storeA(&(listSorted->sortLinkNode), al) && listSorted->responseTime == t 
     */
    if (listSorted->responseTime <= (startTime + tickPrecision)) {
        return (startTime + tickPrecision);
    }
    return listSorted->responseTime;
}
