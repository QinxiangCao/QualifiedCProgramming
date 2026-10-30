#include "hash_table.h"

void entails_emp_unfold()
/*@ With A
    Require entails_emp(A) && A
    Ensure emp
 */
{}

void ht_specs_get_hash_spec(ht_hash_fn hash, ht_equal_fn equal, ht_free_fn key_free, ht_free_fn value_free)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion) (key_hash : K -> Z) (key_eq : K -> K -> Prop)
    Require ht_specs(storeK, storeV, key_hash, key_eq, hash, equal, key_free, value_free)
    Ensure (hash |= unsigned int (void *arg)
        With key_k
        Require storeK(arg, key_k)
        Ensure __return == key_hash(key_k) &&
                0 <= key_hash(key_k) &&
                key_hash(key_k) <= UINT_MAX &&
                storeK(arg, key_k))
 */
{}

void ht_specs_get_equal_spec(ht_hash_fn hash, ht_equal_fn equal, ht_free_fn key_free, ht_free_fn value_free)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion) (key_hash : K -> Z) (key_eq : K -> K -> Prop)
    Require ht_specs(storeK, storeV, key_hash, key_eq, hash, equal, key_free, value_free)
    Ensure (equal |= unsigned int (void *lhs, void *rhs)
        With lhs_k rhs_k
        Require storeK(lhs, lhs_k) * storeK(rhs, rhs_k)
        Ensure ((key_eq(lhs_k, rhs_k) && __return == 1 && emp) ||
                (! key_eq(lhs_k, rhs_k) && __return == 0 && emp)) *
               storeK(lhs, lhs_k) * storeK(rhs, rhs_k))
 */
{}

void ht_free_spec_unfold(ht_free_fn free_fn)
/*@ With {A} (storeA : Z -> A -> Assertion)
    Require ht_free_spec(storeA, free_fn)
    Ensure free_fn == 0 && (forall x a, entails_emp(storeA(x, a))) ||
           free_fn != 0 && store_exclusive(storeA) &&
           (free_fn |= void (void *arg) With a Require storeA(arg, a) Ensure emp)
 */
;

void ht_specs_get_key_free_spec(ht_hash_fn hash, ht_equal_fn equal, ht_free_fn key_free, ht_free_fn value_free)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion) (key_hash : K -> Z) (key_eq : K -> K -> Prop)
    Require ht_specs(storeK, storeV, key_hash, key_eq, hash, equal, key_free, value_free)
    Ensure key_free == 0 && (forall x k, entails_emp(storeK(x, k))) ||
           key_free != 0 && store_exclusive(storeK) &&
           (key_free |= void (void *arg) With k Require storeK(arg, k) Ensure emp)
 */
{}
void ht_specs_get_value_free_spec(ht_hash_fn hash, ht_equal_fn equal, ht_free_fn key_free, ht_free_fn value_free)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion) (key_hash : K -> Z) (key_eq : K -> K -> Prop)
    Require ht_specs(storeK, storeV, key_hash, key_eq, hash, equal, key_free, value_free)
    Ensure value_free == 0 && (forall x v, entails_emp(storeV(x, v))) ||
           value_free != 0 && store_exclusive(storeV) &&
           (value_free |= void (void *arg) With v Require storeV(arg, v) Ensure emp)
 */
{}

void ht_store_map_unfold(struct hashtbl *h)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion)
          key_eq key_hash m
    Require ht_store_map(storeK, storeV, key_eq, key_hash, h, m)
    Ensure exists hash equal key_free value_free cap bucks ptrs buckets,
           0 < cap &&
           Zlength(ptrs) == cap &&
           Zlength(buckets) == cap &&
           key_eq_equiv(key_eq) &&
           key_eq_hash_compatible(key_eq, key_hash) &&
           buckets_abs(key_eq, buckets, m) &&
           buckets_hash(key_hash, cap, buckets) &&
           buckets_unique(key_eq, buckets) &&
           ht_specs(storeK, storeV, key_hash, key_eq, hash, equal, key_free, value_free) &&
           store(&(h->hash), hash) *
           store(&(h->equal), equal) *
           store(&(h->key_free), key_free) *
           store(&(h->value_free), value_free) *
           store(&(h->capacity), cap) *
           store(&(h->bucks), bucks) *
           PtrArray::full(bucks, cap, ptrs) *
           ht_bucket_chains(storeK, storeV, ptrs, buckets)
 */
{}

void ht_bucket_chains_split_Znth(uint idx)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion)
          (ptrs : list Z) (buckets : list (list (K * V)))
    Require 0 <= idx && idx < Zlength(ptrs) &&
            Zlength(ptrs) == Zlength(buckets) &&
            ht_bucket_chains(storeK, storeV, ptrs, buckets)
    Ensure ht_bucket_chains_except(storeK, storeV, idx, ptrs, buckets) *
           ht_chain(storeK, storeV, ptrs[idx], buckets[idx])
 */
{}

void ht_chain_nonnull_unfold(struct ht_node *node)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion)
          (bucket : list (K * V))
    Require node != 0 &&
            ht_chain(storeK, storeV, node, bucket)
    Ensure exists cur_key cur_val cur_next cur_k cur_v rest_tail,
            bucket == cons(pair(cur_k, cur_v), rest_tail) &&
            store(&(node->key), cur_key) *
            store(&(node->val), cur_val) *
            store(&(node->next), cur_next) *
            storeK(cur_key, cur_k) *
            storeV(cur_val, cur_v) *
            ht_chain(storeK, storeV, cur_next, rest_tail)
 */
{}

uint ht_ptr_equal(void *lhs, void *rhs) {
  if (lhs == rhs)
    return 1;
  return 0;
}

uint ht_int_hash(void *key) {
  // simple hash from 64-bit to 32-bit
  return (uint)key ^ ((unsigned long long)key >> 32);
}

void ht_init(struct hashtbl *h, uint capacity, ht_hash_fn hash,
             ht_equal_fn equal, ht_free_fn key_free, ht_free_fn value_free) {
  h->hash = hash;
  h->equal = equal;
  h->key_free = key_free;
  h->value_free = value_free;
  h->capacity = capacity;
  h->bucks = ht_alloc_buckets(capacity);
}

void ht_add(struct hashtbl *h, void *key, void *val) {
  ht_store_map_unfold(h) /*@ where {K = K, V = V} */;
  //@ Given buckets
  //@ Given ptrs
  //@ Given cap
  ht_specs_get_hash_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;

  uint index = h->hash(key) % h->capacity;
  //@ index == key_hash(k) % cap && 0 <= index && index < h->capacity

  ht_bucket_chains_split_Znth(index) /*@ where {K = K, V = V} */;
  /*@ ht_chain(storeK, storeV, ptrs[index], buckets[index])
    which implies
    ht_chain_seg(storeK, storeV, ptrs[index], ptrs[index], nil) *
    ht_chain(storeK, storeV, ptrs[index], buckets[index])
  */

  /*@ Inv exists l1 l2,
    index == key_hash(k) % cap &&
    app(l1, l2) == buckets[index] &&
    key_eq_equiv(key_eq) &&
    (forall (pk: K) (pv: V), In(pair(pk, pv), l1) => ! key_eq(pk, k)) &&
    ht_chain_seg(storeK, storeV, ptrs[index], node, l1) *
    ht_chain(storeK, storeV, node, l2)
  */
  for (struct ht_node *node = h->bucks[index]; node != 0; node = node->next) {
    ht_specs_get_equal_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;
    ht_chain_nonnull_unfold(node) /*@ where {K = K, V = V} */;
    if (h->equal(node->key, key)) {
      ht_specs_get_key_free_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;
      if (node->key != key && h->key_free != 0) {
        h->key_free(node->key);
      }
      ht_specs_get_value_free_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;
      if (node->val != val && h->value_free != 0) {
        h->value_free(node->val);
      }
      node->key = key;
      node->val = val;
      return;
    }
  }
  struct ht_node *node = ht_alloc_node();
  struct ht_node *old_head = h->bucks[index];
  node->key = key;
  node->val = val;
  node->next = old_head;
  h->bucks[index] = node;
}

void *ht_find(struct hashtbl *h, void *key, int *valid) {
  ht_store_map_unfold(h) /*@ where {K = K, V = V} */;
  //@ Given buckets
  //@ Given ptrs
  //@ Given cap
  ht_specs_get_hash_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;

  uint index = h->hash(key) % h->capacity;
  //@ index == key_hash(k) % cap && 0 <= index && index < h->capacity

  ht_bucket_chains_split_Znth(index) /*@ where {K = K, V = V} */;
  /*@ ht_chain(storeK, storeV, ptrs[index], buckets[index])
    which implies
    ht_chain_seg(storeK, storeV, ptrs[index], ptrs[index], nil) *
    ht_chain(storeK, storeV, ptrs[index], buckets[index])
  */

  /*@ Inv exists l1 l2,
    index == key_hash(k) % cap &&
    app(l1, l2) == buckets[index] &&
    key_eq_equiv(key_eq) &&
    (forall (pk: K) (pv: V), In(pair(pk, pv), l1) => ! key_eq(k, pk)) &&
    ht_chain_seg(storeK, storeV, ptrs[index], node, l1) *
    ht_chain(storeK, storeV, node, l2)
  */
  for (struct ht_node *node = h->bucks[index]; node != 0; node = node->next) {
    ht_specs_get_equal_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;
    ht_chain_nonnull_unfold(node) /*@ where {K = K, V = V} */;
    if (h->equal(node->key, key)) {
      *valid = 1;
      return node->val;
    }
  }
  *valid = 0;
  return 0;
}

void *ht_remove(struct hashtbl *h, void *key, int *removed) {
  ht_store_map_unfold(h) /*@ where {K = K, V = V} */;
  //@ Given hash
  //@ Given equal
  //@ Given key_free
  //@ Given value_free
  //@ Given bucks
  //@ Given ptrs
  //@ Given buckets
  //@ Given cap
  ht_specs_get_hash_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;

  uint index = h->hash(key) % h->capacity;
  //@ index == key_hash(k) % cap && 0 <= index && index < cap

  ht_bucket_chains_split_Znth(index) /*@ where {K = K, V = V} */;
  struct ht_node **node_ref = &h->bucks[index];

  /*@ Inv Assert exists pre rest node,
        h == h@pre &&
        key == key@pre &&
        removed == removed@pre &&
        0 < cap &&
        Zlength(ptrs) == cap &&
        Zlength(buckets) == cap &&
        key_eq_hash_compatible(key_eq, key_hash) &&
        buckets_abs(key_eq, buckets, m) &&
        buckets_hash(key_hash, cap, buckets) &&
        buckets_unique(key_eq, buckets) &&
        0 <= key_hash(k) &&
        index == key_hash(k) % cap &&
        0 <= index && index < cap &&
        Znth(index, buckets, nil) == app(pre, rest) &&
        key_eq_equiv(key_eq) &&
        (forall (pk: K) (pv: V), In(pair(pk, pv), pre) => ! key_eq(k, pk)) &&
        ht_specs(storeK, storeV, key_hash, key_eq,
          hash, equal, key_free, value_free) &&
        store(&(h->hash), hash) *
        store(&(h->equal), equal) *
        store(&(h->key_free), key_free) *
        store(&(h->value_free), value_free) *
        store(&(h->capacity), cap) *
        store(&(h->bucks), bucks) *
        PtrArray::missing_i(bucks, index, 0, cap, ptrs) *
        store(node_ref, node) *
        ht_bucket_chains_except(storeK, storeV, index, ptrs, buckets) *
        ht_chain_bseg(storeK, storeV,
          bucks + index * sizeof(struct ht_node *), node_ref, pre) *
        ht_chain(storeK, storeV, node, rest) *
        storeK(key, k) *
        has_permission(removed)
  */
  while (*node_ref != 0) {
    struct ht_node *node = *node_ref;
    ht_specs_get_equal_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;
    ht_chain_nonnull_unfold(node) /*@ where {K = K, V = V} */;
    if (h->equal(key, node->key)) {
      void *result = node->val;
      *node_ref = node->next;

      ht_specs_get_key_free_spec(h->hash, h->equal, h->key_free, h->value_free) /*@ where {K = K, V = V} */;
      if (node->key != key && h->key_free != 0) {
        h->key_free(node->key);
      }
      ht_free_node(node);
      *removed = 1;
      return result;
    }
    node_ref = &node->next;
  }

  *removed = 0;
  return 0;
}
