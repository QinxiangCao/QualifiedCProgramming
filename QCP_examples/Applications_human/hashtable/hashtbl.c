

#include "hashtbl.h"
/*@ Import Coq Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib */

/*@ Extern Coq (zeros: Z -> list Z)
               (sll : Z -> list Z -> Assertion)
               (sllseg: Z -> Z -> list Z -> Assertion)
               (sllbseg: Z -> Z -> list Z -> Assertion)
               (dll: Z -> Z -> list Z -> Assertion)
               (dllseg: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (store_string: Z -> list Z -> Assertion)
               (store_sll: Z -> (Z * list Z) -> Assertion)
               (store_name: list Z -> Z -> Assertion)
               (contain_all_addrs: (list Z -> option Z) -> list Z -> Prop)
               (key_list_for_addrs: (list Z -> option Z) -> list Z -> list (list Z) -> Prop)
               (current_bucket_key_list: (list Z -> option Z) -> (Z -> option (Z * list Z)) -> Z -> list Z -> list (list Z) -> Prop)
               (current_bucket_suffix: (list Z -> option Z) -> (Z -> option (Z * list Z)) -> Z -> list Z -> list Z -> Prop)
               (remaining_after_bucket_index: (list Z -> option Z) -> (list Z -> option Z) -> Z -> Prop)
               (repr_all_heads: list Z -> (Z -> option (Z * list Z)) -> Prop)
               (contain_all_correct_addrs: (list Z -> option Z) -> (Z -> option (Z * list Z)) -> Prop)
               (node_value_map: (list Z -> option Z) -> (list Z -> option Z) -> Prop)
               (bucket_cells_nonnull: Z -> Prop)
               (store_hash_skeleton: Z -> (list Z -> option Z) -> Assertion)
               (map_compose: (list Z -> option Z) -> (Z -> option Z) -> (Z -> option Z) -> Prop)
               (map_composable: (list Z -> option Z) -> (Z -> option Z) -> Prop)
               (empty_map: {A} {B} -> A -> option B)
               (KP::insert_map: (list Z -> option Z) -> list Z -> Z -> (list Z -> option Z))
               (KP::remove_map: (list Z -> option Z) -> list Z -> (list Z -> option Z))
               (PV::insert_map: (Z -> option Z) -> Z -> Z -> (Z -> option Z))
               (PV::remove_map: (Z -> option Z) -> Z -> (Z -> option Z))
               (KP::remove_keys: (list Z -> option Z) -> list (list Z) -> (list Z -> option Z))
               (PV::remove_addrs: (Z -> option Z) -> list Z -> (Z -> option Z))
               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)
               (store_map_missing_i: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> A -> Assertion)
               (store_map_missing_first_i_Z: {B} -> (Z -> B -> Assertion) -> (Z -> option B) -> Z -> Assertion)
               (store_hashtbl: Z -> (list Z -> option Z) -> Assertion)
               (hash_string_k: list Z -> Z)
               (not_key: list Z -> list Z -> (list Z -> option Z) -> Prop)
               (NoDup: {A} -> list A -> Prop)
               (pair: {A} {B} -> A -> B -> A * B)
*/

/*@ include strategies "hashtbl.strategies" */

int NBUCK = 211;

struct blist ** malloc_blist_array()
/*@ Require emp
    Ensure __return != 0 &&
      bucket_cells_nonnull(__return) &&
      exists content, PtrArray::full(__return, 211, content)
*/;

struct hashtbl * malloc_hashtbl()
/*@ Require emp
    Ensure __return != 0 &&
            exists bucks_ph top_ph,
              store(&(__return -> bucks), bucks_ph) *
              store(&(__return -> top), top_ph)
*/;

struct blist * malloc_blist()
/*@ Require emp
    Ensure __return != 0 &&
           &(__return->next) != 0 &&
           store(&(__return -> key), 0) *
           store(&(__return -> val), 0) *
           store(&(__return -> next), 0) *
           store(&(__return -> down), 0) *
           store(&(__return -> up), 0)
*/;

void free_string(char *key)
/*@
  With p m1 m2 k
  Require store_map(store_name, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          store_ptr(&(p->key), key)
  Ensure store_map(store_name, m1)*
        store_map(store_uint, m2)
*/
;

void free_blist_array(struct blist **i)
/*@ With lh
  Require PtrArray::full(i, 211, lh) 
  Ensure emp
*/;

void free_blist(struct blist *b)
/*@
  Require has_ptr_permission(&(b -> next))
  Ensure emp
*/;

unsigned int hash_string(char *key)
/*@ With k
    Require store_string(key, k)
    Ensure 0 <= __return && __return <= 4294967295 &&
           __return == hash_string_k(k) &&
           store_string(key, k)
*/;

int string_equal(char *k1, char *k2)
/*@
  With k1_list k2_list
  Require store_string(k1, k1_list) * 
          store_string(k2, k2_list) 
  Ensure store_string(k1, k1_list) * 
           store_string(k2, k2_list) * 
           ((__return == 1 && k1_list == k2_list) ||
            (__return == 0 && k1_list != k2_list))
*/;

void free_hashtbl_struct(struct hashtbl *h)
/*@
  With l m1 m2 list_head
  Require store(&h->top, 0) *
          store(&h->bucks, 0) *
          dll(list_head, (void*) 0, l) *
          store_map(store_name, m1) *
          store_map(store_uint, m2)
  Ensure emp
*/;

void create_bucks(struct hashtbl *h)
/*@ With bucks_random
    Require store(&(h->bucks), bucks_random)
    Ensure exists bucks_base,
           bucket_cells_nonnull(bucks_base) &&
           store(&(h->bucks), bucks_base) *
           PtrArray::full(bucks_base, 211, zeros(211))
*/
{
  int i;
  h->bucks = malloc_blist_array();
  /*@ Inv exists content bucks_base,
          0 <= i && i <= 211 &&
          bucket_cells_nonnull(bucks_base) &&
          store(&(h@pre->bucks), bucks_base) *
          PtrArray::full(bucks_base, 211, content) *
          (sublist(0, i, content) == zeros(i))
  */
  for (i = 0; i < 211; i++) {
    h->bucks[i] = 0;
  }
}

void init_hashtbl(struct hashtbl *h)
/*@ With bucks_ph top_ph
    Require store(&(h->bucks), bucks_ph) *
            store(&(h->top), top_ph)
    Ensure store_hash_skeleton(h, empty_map)
*/
{
  h->bucks = 0;
  h->top = 0;
  create_bucks(h);
}

struct hashtbl *create_hashtbl()
/*@
  Require emp
  Ensure store_hash_skeleton(__return, empty_map) *
         store_map(store_uint, empty_map)
*/
{
  struct hashtbl *h;
  h = malloc_hashtbl();
  /*@ exists bucks_ph top_ph,
        store(&(h->bucks), bucks_ph) *
        store(&(h->top), top_ph) */
  init_hashtbl(h);
  return h;
}

void hashtbl_add(struct hashtbl *h, char *key, unsigned int val)
/*@
  With m1 m2 k
  Require m1(k) == None &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store_string(key, k)
  Ensure exists p,
           store_hash_skeleton(h, KP::insert_map(m1, k, &(p->val))) *
           store_map(store_uint, PV::insert_map(m2, &(p->val), val))
*/
{
  /*@ store_hash_skeleton(h, m1)
        which implies
        exists m_node top_ph bucks_ph l lh b,
          node_value_map(m_node, m1) &&
          contain_all_addrs(m_node, l) *
          repr_all_heads(lh, b) *
          contain_all_correct_addrs(m_node, b) *
          bucket_cells_nonnull(bucks_ph) *
          store(&(h->top), top_ph) *
          store(&(h->bucks), bucks_ph) *
          dll(top_ph, 0, l) *
          PtrArray::full(bucks_ph, 211, lh) *
          store_map(store_sll, b) *
          store_map(store_name, m_node)
  */
  unsigned int ind;
  struct blist *buc;
  ind = hash_string(key) % 211; /*@ 0 <= ind && ind < 211 */
  buc = malloc_blist();

  buc->key = key;
  buc->val = val;
  buc->up = 0;
  buc->down = h->top;

  if (h->top != 0){
    /*@ exists top_ph l,
        top_ph != 0 &&
        store(&(h->top), top_ph) *
        dll(top_ph, 0, l)
        which implies
        exists top_down l_tail,
          l == cons(top_ph, l_tail) &&
          store(&(h->top), top_ph) *
          store(&(top_ph->down), top_down) *
          store(&(top_ph->up), 0) *
          dll(top_down, top_ph, l_tail)
    */
    h->top->up = buc;
  }
  h->top = buc;

  buc->next = h->bucks[ind];
  h->bucks[ind] = buc;
}

unsigned int hashtbl_find(struct hashtbl *h, char *key, int *valid)
/*@
  With m1 m2 k
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          has_int_permission(valid)
  Ensure store_hash_skeleton(h, m1) *
         store_map(store_uint, m2) *
         store_string(key, k) *
         ((exists p v, store_int(valid, 1) && m1(k) == Some(p) &&
                       m2(p) == Some(v) && __return == v) ||
          (store_int(valid, 0) && m1(k) == None && __return == 0))
*/
{
  unsigned int ind;
  struct blist **i;
  /*@ store_hash_skeleton(h, m1)
      which implies
      exists m_node top_ph bucks_ph l lh b,
        node_value_map(m_node, m1) &&
        store(&(h->top), top_ph) *
        store(&(h->bucks), bucks_ph) *
        dll(top_ph, 0, l) *
        contain_all_addrs(m_node, l) *
        repr_all_heads(lh, b) *
        contain_all_correct_addrs(m_node, b) *
        bucket_cells_nonnull(bucks_ph) *
        PtrArray::full(bucks_ph, 211, lh) *
        store_map(store_sll, b) *
        store_map(store_name, m_node)
  */
  ind = hash_string(key) % 211;/*@ 0 <= ind && ind < 211 */

  /*@ Inv Assert exists m_node l1 l2 top_ph bucks_ph l lh b,
        h == h@pre && key == key@pre && valid == valid@pre &&
        0 <= ind && ind < 211 &&
        ind == hash_string_k(k) % 211 &&
        map_composable(m1, m2) &&
        node_value_map(m_node, m1) &&
        store(&(h->top), top_ph) *
        store(&(h->bucks), bucks_ph) *
        dll(top_ph, 0, l) *
        PtrArray::missing_i(bucks_ph, ind, 0, 211, lh) *
        store_map_missing_i(store_sll, b, ind) *
        store_map(store_name, m_node) *
        (b(ind) == Some(pair(Znth(ind, lh, 0), app(l1, l2)))) *
        (Znth(0, app(l1, l2), 0) == Znth(ind, lh, 0)) *
        sllbseg (&(h->bucks[ind]), i, l1) *
        sll(*i, l2) *
        contain_all_addrs(m_node, l) *
        repr_all_heads(lh, b) *
        contain_all_correct_addrs(m_node, b) *
        not_key(k, l1, m_node) &&
        bucket_cells_nonnull(bucks_ph) &&
        i != 0 &&
        store_map(store_uint, m2) *
        store_string(key, k) *
        has_int_permission(valid)
  */
  for (i = &h->bucks[ind]; *i != 0; i = &(*i)->next){
    /*@ Assert
          exists m_node l1 l2 top_ph bucks_ph l lh b kp vp p_next k_cur l_tail,
            h == h@pre && key == key@pre && valid == valid@pre &&
            0 <= ind && ind < 211 &&
            ind == hash_string_k(k) % 211 &&
            map_composable(m1, m2) &&
            node_value_map(m_node, m1) &&
            l2 == cons(*i, l_tail) &&
            m_node(k_cur) == Some(*i) &&
            store(&(h->top), top_ph) *
            store(&(h->bucks), bucks_ph) *
            dll(top_ph, 0, l) *
            PtrArray::missing_i(bucks_ph, ind, 0, 211, lh) *
            store_map_missing_i(store_sll, b, ind) *
            (b(ind) == Some(pair(Znth(ind, lh, 0), app(l1, l2)))) *
            (Znth(0, app(l1, l2), 0) == Znth(ind, lh, 0)) *
             ((l1 == nil && i == &(h->bucks[ind]) && sllbseg(&(h->bucks[ind]), i, l1)) ||
             (l1 != nil && exists h_val t_l1, l1 == cons(h_val, t_l1) &&
              h_val == Znth(ind, lh, 0) &&
              store(&(h->bucks[ind]), h_val) *
              sllbseg(&(h_val->next), i, t_l1))) *
            contain_all_addrs(m_node, l) *
            repr_all_heads(lh, b) *
            contain_all_correct_addrs(m_node, b) *
            not_key(k, l1, m_node) &&
            bucket_cells_nonnull(bucks_ph) &&
            i != 0 &&
            &((*i)->next) != 0 &&
            m2(&((*i)->val)) == Some(vp) &&
            store_map_missing_i(store_uint, m2, &((*i)->val)) *
            store_string(key, k) *
            has_int_permission(valid) *
            store(&(*i)->key, kp) *
            store(&(*i)->val, vp) *
            store(&(*i)->next, p_next) *
            store_string(kp, k_cur) *
            store_map_missing_i(store_name, m_node, k_cur) *
            sll(p_next, l_tail)
    */
    if (string_equal(key, (*i)->key)) {
      struct blist *b = *i;

      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;

      *valid = 1;
      return b->val;
    }
  }
  *valid = 0;
  return 0;
}

unsigned int *hashtbl_findref(struct hashtbl *h, char *key)
/*@
  With m k
  Require store_hash_skeleton(h, m) *
          store_string(key, k)
  Ensure store_hash_skeleton(h, m) *
         store_string(key, k) *
         ((exists p, m(k) == Some(&(p->val)) && __return == &p->val) ||
          (m(k) == None && __return == (void *) 0))
*/
{
  unsigned int ind;
  struct blist **i;
  /*@ h == h@pre &&
      store_hash_skeleton(h, m)
      which implies
        h == h@pre &&
        exists m_node l lh h_bucks top b0, 
        node_value_map(m_node, m) &&
        contain_all_addrs(m_node, l) && 
        repr_all_heads(lh, b0) && 
        contain_all_correct_addrs(m_node, b0) && 
        bucket_cells_nonnull(h_bucks) &&
        store(&(h->top), top) *
        dll(top, (void*) 0, l) * 
        store(&(h->bucks), h_bucks) *
        PtrArray::full(h_bucks, 211, lh) * 
        store_map(store_sll, b0)*
        store_map(store_name, m_node)
  */
  ind = hash_string(key) % 211;
  i = &h->bucks[ind];
  /*@ Inv Assert
      exists m_node l l0 l_prev l_res lh top b0,
      h == h@pre &&
      ind == hash_string_k(k) % 211 &&
      node_value_map(m_node, m) &&
      contain_all_addrs(m_node, l) && 
      repr_all_heads(lh, b0) && 
      contain_all_correct_addrs(m_node, b0) && 
      bucket_cells_nonnull(h->bucks) &&
      0 <= ind && ind < 211 &&
      b0(ind) == Some(pair(Znth (ind, lh, 0),l0)) &&
      l0 == app(l_prev, l_res) &&
      not_key(k, l_prev, m_node) &&
      key == key@pre &&
      i != 0 &&
      sllbseg(&(h->bucks[ind]), i, l_prev) *
      sll ((*i), l_res) *
      store_map_missing_i(store_sll, b0, ind)*
      store(&(h->top), top) *
      dll(top, (void*) 0, l) * 
      PtrArray::missing_i( h->bucks, ind, 0, 211, lh) *
      store_string(key, k) *
      store_map(store_name, m_node)
  */
  for (; *i != (void *) 0; i = &(*i)->next){
      /*@ exists m_node l_res l_prev,
        (*i) != 0 && 
        i != 0 &&
        (exists k_list_current,
          m_node(k_list_current) == Some((*i))) &&
        store_map(store_name, m_node) *
        sllbseg(&(h->bucks[ind]), i, l_prev) *
        sll((*i), l_res)
    which implies
        exists k_list_current l_resres ,
          (*i) != 0 &&
          i != 0 &&
          m_node (k_list_current) == Some ((*i)) &&
          l_res == cons((*i), l_resres) &&
          &((*i)->next) != 0 &&
          sllbseg(&(h->bucks[ind]), i, l_prev) *
          sll(((*i)->next), l_resres) *
          store_string((*i)->key, k_list_current) *
          store_map_missing_i(store_name, m_node, k_list_current)
    */
    if (string_equal(key, (*i)->key)) {
      struct blist *b = *i;
      /*@ b == (*i) by local */
      // LRU
      *i = b->next;
      /*@ exists l_prev,
        (*i) == b->next &&
        i != 0 &&
        &(b->next) != 0 &&
        sllbseg(&(h->bucks[ind]), i, l_prev)
      which implies
        (l_prev == nil &&
         (&(h->bucks[ind]) == i) &&
         i != 0 &&
         &(b->next) != 0 &&
         store_ptr(&(h->bucks[ind]), b->next)) ||
        (exists head l_prevres,
        (*i) == b->next &&
        i != 0 &&
        &(b->next) != 0 &&
        l_prev == cons(head, l_prevres) &&
        store_ptr(&(h->bucks[ind]), head) *
        sllbseg(&(head->next), i, l_prevres))
      */
      b->next = h->bucks[ind];
      h->bucks[ind] = b;
      return &b->val;
    }
  }
  return (void *) 0;
  
}

unsigned int hashtbl_remove(struct hashtbl *h, char *key, int *removed)
/*@
  With m1 m2 k
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          has_int_permission(removed)
  Ensure store_hash_skeleton(h, KP::remove_map(m1, k)) *
         store_string(key, k) *
         ((exists p v key0 p_up p_down,
              m1(k) == Some(&(p -> val)) &&
              m2(&(p -> val)) == Some(v) && __return == v &&
              store_int(removed, 1) *
              store_map(store_uint, PV::remove_map(m2, &(p -> val))) *
              store_ptr(&(p -> key), key0) * 
              store_string(key0, k) *
              store_ptr(&(p -> up), p_up) *
              store_ptr(&(p -> down), p_down) *
              store_uint(&(p -> val), v)) ||
          ( m1(k) == None && __return == 0 &&
             store_int(removed, 0) *
             store_map(store_uint, m2)))
*/
{
  unsigned int ind;
  struct blist **it;
  /*@ store_hash_skeleton(h, m1)
      which implies
        exists m1_node l lh h_bucks top b, 
        node_value_map(m1_node, m1) &&
        contain_all_addrs(m1_node, l) && 
        repr_all_heads(lh, b) && 
        contain_all_correct_addrs(m1_node, b) && 
        bucket_cells_nonnull(h_bucks) &&
        store(&(h->top), top) *
        dll(top, (void*) 0, l) * 
        store(&(h->bucks), h_bucks) *
        PtrArray::full(h_bucks, 211, lh) * 
        store_map(store_sll, b)*
        store_map(store_name, m1_node)
  */
  ind = hash_string(key) % 211;
  /*@ Inv Assert
      exists m1_node l_prev l_res l0 buck dl_up dl_down dl_prev lh bucket_map itv top,
      map_composable(m1, m2) &&
       node_value_map(m1_node, m1) &&
       not_key(k, l_prev, m1_node) &&
       NoDup(l_res) &&
       ind == hash_string_k(k) % 211 &&
      0 <= ind && ind < 211 &&
      bucket_map(ind) == Some(pair(buck, l0)) &&
      l0 == app(l_prev, l_res) &&
      contain_all_addrs(m1_node, app(dl_up, dl_down)) && 
      repr_all_heads(lh, bucket_map) && 
      contain_all_correct_addrs(m1_node, bucket_map) && 
      bucket_cells_nonnull(h@pre->bucks) &&
      (h == h@pre) &&
      (key == key@pre) &&
      (removed == removed@pre) &&
      it != 0 &&
      store(it, itv) *
      store_map_missing_i(store_sll, bucket_map, ind) *
      sllbseg(&(h@pre->bucks[ind]), it, l_prev) *
      sll(itv, l_res) *
      store_string(key, k) *
      PtrArray::missing_i(h@pre->bucks, ind, 0, 211, lh) *
      store_map(store_name, m1_node) *
      store(&(h@pre->top), top) *
      (itv == 0 => l_res == nil && dl_down == nil) &&
      (top == itv => dl_prev == 0 && dl_up == nil) &&
      (dl_up != nil => top != 0) &&
      dllseg(top, itv, (void*) 0, dl_prev, dl_up) *
      dll(itv, dl_prev, dl_down) *
      has_int_permission(removed) *
      store_map(store_uint, m2)
  */
  for (it = &h->bucks[ind]; *it != (void *) 0; it = &(*it)->next) {
    struct blist *b = *it;
    /*@ exists m1_node l_prev l_res dl_down dl_prev bucket_map,
        b != 0 &&
        it != 0 &&
        map_composable(m1, m2) &&
        removed == removed@pre &&
        node_value_map(m1_node, m1) &&
        not_key(k, l_prev, m1_node) &&
        NoDup(l_res) &&
        current_bucket_suffix(m1_node, bucket_map, ind, l_prev, l_res) &&
        bucket_cells_nonnull(h@pre->bucks) &&
        store(it, b) *
        store_map_missing_i(store_sll, bucket_map, ind) *
        sllbseg(&(h@pre->bucks[ind]), it, l_prev) *
        store_map(store_name, m1_node) *
        dll(b, dl_prev, dl_down) *
        store_map(store_uint, m2) *
        sll(b, l_res)
      which implies
        exists k_list l_resres dl_downres val b_key b_next b_down,
          b != 0 &&
          it != 0 &&
          l_res == cons(b, l_resres) &&
          dl_down == cons(b, dl_downres) &&
          map_composable(m1, m2) &&
          removed == removed@pre &&
          node_value_map(m1_node, m1) &&
          not_key(k, l_prev, m1_node) &&
          NoDup(l_res) &&
          m1_node(k_list) == Some(b) &&
          m2(&(b->val)) == Some(val) &&
          bucket_cells_nonnull(h@pre->bucks) &&
          &(b->next) != 0 &&
          store(it, b) *
          store_map_missing_i(store_sll, bucket_map, ind) *
          sllbseg(&(h@pre->bucks[ind]), it, l_prev) *
          store(&(b->next), b_next) *
          sll(b_next, l_resres) *
          store(&(b->key), b_key) *
          store_string(b_key, k_list) *
          store(&(b->val), val) *
          store_map_missing_i(store_uint, m2, &(b->val)) *
          store(&(b->down), b_down) *
          store(&(b->up), dl_prev) *
          dll(b_down, b, dl_downres) *
          store_map_missing_i(store_name, m1_node, k_list)
    */
    if (string_equal(key, b->key)) {
      if (h->top == b)
        h->top = b->down;
      if (b->up != (void *) 0)
        /*@ exists dl_up dl_up_tail dl_prev top top_next,
              dl_prev != 0 &&
              top != 0 &&
              dl_up == cons(top, dl_up_tail) &&
              store(&(top->down), top_next) *
              store(&(top->up), (void*) 0) *
              dllseg(top_next, b, top, dl_prev, dl_up_tail)
            which implies
              exists dl_up_prefix dl_prev_prev,
                dl_up == app(dl_up_prefix, cons(dl_prev, nil)) &&
                dllseg(top, dl_prev, (void*) 0, dl_prev_prev, dl_up_prefix) *
                store(&(dl_prev->down), b) *
                store(&(dl_prev->up), dl_prev_prev)
        */
        b->up->down = b->down;
      if (b->down != (void *) 0)
        /*@ exists b_down dl_downres,
              b_down != 0 &&
              dll(b_down, b, dl_downres)
            which implies
              exists b_down_down dl_down_tail,
                dl_downres == cons(b_down, dl_down_tail) &&
                store(&(b_down->down), b_down_down) *
                store(&(b_down->up), b) *
                dll(b_down_down, b_down, dl_down_tail)
        */
        b->down->up = b->up;

      *it = b->next;
      unsigned int res = b->val;
      free_blist(b);
      *removed = 1;
      return res;
    }
  }
  *removed = 0;
  return 0;
}

void hashtbl_free_blist(struct blist *bl)
/*@
  With l m1 m2 ks
  Require key_list_for_addrs(m1, l, ks) &&
          sll(bl, l) *
          store_map(store_name, m1) *
          store_map(store_uint, m2) 
  Ensure (store_map(store_name, KP::remove_keys(m1, ks)) *
          store_map(store_uint, m2)
          )
*/
{
  if (bl != (void *) 0) {
    /*@ key_list_for_addrs(m1, l, ks) &&
        sll(bl, l) * store_map(store_name, m1) && bl != (void *) 0
        which implies
        exists l1 k1 ks1 bl_key bl_next,
        l == cons(bl, l1) &&
        ks == cons(k1, ks1) &&
        key_list_for_addrs(KP::remove_map(m1, k1), l1, ks1) &&
        m1(k1) == Some(bl) &&
        store_ptr(&(bl->next), bl_next) *
        sll(bl_next, l1) *
        store_ptr(&(bl->key), bl_key) *
        store_string(bl_key, k1) *
        store_map(store_name, KP::remove_map(m1, k1))
    */
    hashtbl_free_blist(bl->next);
    free_string(bl -> key);
    free_blist(bl);
  }
}

void hashtbl_clear(struct hashtbl *h)
/*@
  With m1 m2
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2)
   Ensure exists m1_node l m_rem list_head,
         node_value_map(m1_node, m1) &&
         remaining_after_bucket_index(m1_node, m_rem, 211) &&
         store(&h->bucks, 0) * 
         store(&h->top, 0) *
         dll(list_head, (void*) 0, l) *
          store_map(store_name, m_rem) *
        store_map(store_uint, m2)
*/ 
{
  /*@ store_hash_skeleton(h, m1)
      which implies
        exists m1_node lh h_bucks b l top, 
        node_value_map(m1_node, m1) &&
        contain_all_addrs(m1_node, l) && 
        repr_all_heads(lh, b) && 
        contain_all_correct_addrs(m1_node, b) && 
        bucket_cells_nonnull(h_bucks) &&
        store(&(h->top), top) *
        dll(top, (void*) 0, l) * 
        store(&(h->bucks), h_bucks) *
        PtrArray::full(h_bucks, 211, lh) * 
        store_map(store_sll, b)*
        store_map(store_name, m1_node)
  */
  int i = 0;
  /*@ Inv Assert
      exists m1_node m_rem li buck_i lh b l ks_i top,
      map_composable(m1, m2) &&
      node_value_map(m1_node, m1) &&
      contain_all_correct_addrs(m1_node, b) &&
      repr_all_heads(lh, b) &&
      remaining_after_bucket_index(m1_node, m_rem, i) &&
      store(&h@pre->top, top) *
      store(&h, h@pre) *
      dll(top, (void*) 0, l) *
      ((i >= 0 && i < 211 &&
      key_list_for_addrs(m_rem, li, ks_i) &&
      current_bucket_key_list(m_rem, b, i, li, ks_i) &&
      PtrArray::missing_i(h@pre->bucks, i, 0, 211, lh) *
      store_map_missing_first_i_Z(store_sll, b, i) *
      store_map(store_name, m_rem) *
      store_map(store_uint, m2) *
      store(&h@pre->bucks[i], buck_i) *
      sll(buck_i, li)) || 
      (i >= 211 && 
      store_map(store_name, m_rem) *
      store_map(store_uint, m2) *
      PtrArray::full(h@pre->bucks, 211, lh)))
  */
  for (i = 0; i < 211 && i >= 0; i++) {
    hashtbl_free_blist(h->bucks[i]);
    h->bucks[i] = (void *) 0;
  }

  free_blist_array(h->bucks);
  h->bucks = (void *) 0;
  h->top = (void *) 0;
}

void free_hashtbl(struct hashtbl *h)
/*@
  With m1 m2
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2)
  Ensure emp
*/
{
  hashtbl_clear(h);
  free_hashtbl_struct(h);
}
