/*
 * Minimal hash table in the same shape as compiler/hashtbl.c:
 * a bucket array whose entries are singly-linked collision chains.
 *
 * The real table also keeps down/up/top links for insertion-order traversal.
 * This example intentionally leaves those fields out.
 */
#pragma once
#include "hash_table_def.h"

typedef unsigned int uint;

typedef uint (*ht_hash_fn)(void *);
typedef uint (*ht_equal_fn)(void *, void *);
typedef void (*ht_free_fn)(void *);

struct ht_node {
  void *key;
  void *val;
  struct ht_node *next;
};

struct hashtbl {
  ht_hash_fn hash;
  ht_equal_fn equal;
  ht_free_fn key_free;
  ht_free_fn value_free;
  uint capacity;
  struct ht_node **bucks;
};

struct ht_node **ht_alloc_buckets(uint capacity)
/*@ Require 0 < capacity && emp
    Ensure __return != 0 &&
           PtrArray::full(__return, capacity, zeros(capacity))
 */
;

struct ht_node *ht_alloc_node()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(__return)
 */
;

void ht_free_node(struct ht_node *node)
/*@ With key val next
    Require store(&(node->key), key) *
            store(&(node->val), val) *
            store(&(node->next), next)
    Ensure emp
 */
;

uint ht_ptr_equal(void *lhs, void *rhs)
/*@ Require emp
    Ensure (lhs == rhs && __return == 1 && emp) ||
           (lhs != rhs && __return == 0 && emp)
 */;

uint ht_int_hash(void *key)
/*@ Require key <= INT64_MAX && key >= INT64_MIN && emp
    Ensure __return == (unsigned_last_nbits(key, 32) ^ (unsigned_last_nbits(key, 64) >> 32)) && emp
 */;

void ht_init(struct hashtbl *h, uint capacity, ht_hash_fn hash,
             ht_equal_fn equal, ht_free_fn key_free, ht_free_fn value_free)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion)
          (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    Require h != 0 && 0 < capacity &&
            key_eq_equiv(key_eq) &&
            key_eq_hash_compatible(key_eq, key_hash) &&
            ht_hash_spec(storeK, key_hash, hash) &&
            ht_equal_spec(storeK, key_eq, equal) &&
            ht_free_spec(storeK, key_free) &&
            ht_free_spec(storeV, value_free) &&
            undef_data_at(h)
    Ensure ht_store_map(storeK, storeV, key_eq, key_hash, h, empty_mapping{K,V})
 */;

void ht_add(struct hashtbl *h, void *key, void *val)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion)
          (key_eq : K -> K -> Prop) (key_hash : K -> Z)
          (m : mapping K V)
          (k : K) (v : V)
    Require h != 0 &&
            ht_store_map(storeK, storeV, key_eq, key_hash, h, m) *
            storeK(key, k) * storeV(val, v)
    Ensure exists new_m,
            map_insert(key_eq, k, v, m, new_m) &&
            ht_store_map(storeK, storeV, key_eq, key_hash, h, new_m)
 */;

void *ht_find(struct hashtbl *h, void *key, int *valid)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion)
          (key_eq : K -> K -> Prop) (key_hash : K -> Z)
          (m : mapping K V) (k : K)
    Require h != 0 && valid != 0 &&
            ht_store_map(storeK, storeV, key_eq, key_hash, h, m) *
            storeK(key, k) *
            has_permission(valid)
    Ensure
      (exists v, map_get(k, m, Some(v)) && storeV(__return, v) * store(valid, 1) * storeK(key, k) *
        ht_store_map_value_hole(storeK, storeV, key_eq, key_hash, h, m, k, __return))
      ||
      (map_get(k, m, None) && __return == 0 && store(valid, 0) * storeK(key, k) *
        ht_store_map(storeK, storeV, key_eq, key_hash, h, m))
 */;

void *ht_remove(struct hashtbl *h, void *key, int *removed)
/*@ With {K V} (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion)
          (key_eq : K -> K -> Prop) (key_hash : K -> Z)
          (m : mapping K V) (k : K)
    Require h != 0 && removed != 0 &&
            ht_store_map(storeK, storeV, key_eq, key_hash, h, m) *
            storeK(key, k) *
            has_permission(removed)
    Ensure
      (exists v new_m,
        map_get(k, m, Some(v)) &&
        map_remove(key_eq, k, m, new_m) &&
        storeV(__return, v) * store(removed, 1) * storeK(key, k) *
        ht_store_map(storeK, storeV, key_eq, key_hash, h, new_m))
      ||
      (map_get(k, m, None) && __return == 0 &&
        store(removed, 0) * storeK(key, k) *
        ht_store_map(storeK, storeV, key_eq, key_hash, h, m))
 */;
