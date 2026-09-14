


const int NBUCK = 211;

struct blist {
  char *key;
  unsigned int val;
  /* for elements with the same hash */
  struct blist *next;
  /* for traversing the whole table */
  struct blist *down;
  struct blist *up;
};

struct hashtbl {
  struct blist **bucks;
  struct blist *top;
};

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
               (repr_all_heads: list Z -> (Z -> option (Z * list Z)) -> Prop)
               (contain_all_correct_addrs: (list Z -> option Z) -> (Z -> option (Z * list Z)) -> Prop)
               (store_hash_skeleton: Z -> (list Z -> option Z) -> Assertion)
               (map_compose: (list Z -> option Z) -> (Z -> option Z) -> (Z -> option Z) -> Prop)
               (map_composable: (list Z -> option Z) -> (Z -> option Z) -> Prop)
               (empty_map: {A} {B} -> A -> option B)
               (KP::insert_map: (list Z -> option Z) -> list Z -> Z -> (list Z -> option Z))
               (KP::remove_map: (list Z -> option Z) -> list Z -> (list Z -> option Z))
               (PV::insert_map: (Z -> option Z) -> Z -> Z -> (Z -> option Z))
               (PV::remove_map: (Z -> option Z) -> Z -> (Z -> option Z))
               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)
               (store_hashtbl: Z -> (list Z -> option Z) -> Assertion)
               (hash_string_k: list Z -> Z)
               (pair: {A} {B} -> A -> B -> A * B)
               (not_key: list Z -> list Z -> (list Z -> option Z) -> Prop)
 */

 /* Please note, if a function f has type (X * Y -> Z), you should write
    f(pair(x,y)) in QCP instead of f(x,y). For a function with type
    (X -> Y -> Z), you write f(x, y) */

/*@ Import Coq Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib */

/*@ include strategies "hashtbl.strategies" */

unsigned int *hashtbl_findref(struct hashtbl *h, char * key)
/*@
  With m k
  Require store_hash_skeleton(h, m) *
          store_string(key, k)
  Ensure store_hash_skeleton(h, m) *
         store_string(key, k) *
         ((exists p, m(k) == Some(p) && __return == p) ||
          (m(k) == None && __return == (void *) 0))
*/;

/* do not free anything */
unsigned int hashtbl_remove(struct hashtbl *h, char * key, int *removed)
/*@
  With m1 m2 k
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          has_int_permission(removed)
  Ensure store_hash_skeleton(h, KP::remove_map(m1, k)) *
         store_string(key, k) *
         ((exists p v key0,
             m1(k) == Some(&(p -> val)) &&
             m2(&(p -> val)) == Some(v) && __return == v &&
             store_int(removed, 1) *
             store_map(store_uint, PV::remove_map(m2, p)) *
             store_ptr(&(p -> key), key0) * store_string(key0, k) *
             has_ptr_permission(&(p -> up)) *
             has_ptr_permission(&(p -> down)) *
             has_ptr_permission(&(p -> next)) *
             store_uint(&(p -> val), v)) ||
          (m1(k) == None && __return == 0 &&
           store_int(removed, 0) * store_map(store_uint, m2)))
*/;
void free_hashtbl(struct hashtbl *h)
/*@
  With m1 m2
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2)
  Ensure emp
*/;

void free_string(char *key);
void free_blist_array(struct blist **i);
void free_blist(struct blist *b);
void free_hashtbl_struct(struct hashtbl *h);
unsigned int hash_string(char *key);
int string_equal(char *k1, char *k2);
