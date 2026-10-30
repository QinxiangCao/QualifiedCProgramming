#pragma once

/*@ Import Coq From SimpleC.EE.Applications_human.hash_table Require Import hash_table_lib */
/*@ Extern Coq (mapping :: * => * => *) */
/*@ Extern Coq
  (ht_hash_spec : {K} -> (Z -> K -> Assertion) -> (K -> Z) -> Z -> FpSpec)
  (ht_equal_spec : {K} -> (Z -> K -> Assertion) -> (K -> K -> Prop) -> Z -> FpSpec)
  (ht_free_spec : {A} -> (Z -> A -> Assertion) -> Z -> FpSpec)
  (ht_specs : {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) ->
    (K -> Z) -> (K -> K -> Prop) -> Z -> Z -> Z -> Z -> FpSpec)
  (key_eq_hash_compatible : {K} -> (K -> K -> Prop) -> (K -> Z) -> Prop)
  (key_eq_equiv : {K} -> (K -> K -> Prop) -> Prop)
  (store_exclusive : {A} -> (Z -> A -> Assertion) -> Prop)
  (ht_chain_seg : {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> Z -> Z -> list (K * V) -> Assertion)
  (ht_chain : {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> Z -> list (K * V) -> Assertion)
  (ht_chain_bseg : {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> Z -> Z -> list (K * V) -> Assertion)
  (ht_chain_node_ref_hole :
    {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> (K -> K -> Prop) ->
    K -> Z -> Z -> Z -> list (K * V) -> Assertion)
  (ht_bucket_chains : {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> list Z -> list (list (K * V)) -> Assertion)
  (ht_bucket_chains_except : {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> Z -> list Z -> list (list (K * V)) -> Assertion)
  (buckets_hash : {K V} -> (K -> Z) -> Z -> list (list (K * V)) -> Prop)
  (ht_table : {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> Z -> Z -> Z -> Z -> Z -> list (list (K * V)) -> Assertion)
  (ht_insert : {K V} -> Z -> K -> V -> list (list (K * V)) -> list (list (K * V)))
  (buckets_abs : {K V} -> (K -> K -> Prop) -> list (list (K * V)) -> mapping K V -> Prop)
  (buckets_unique : {K V} -> (K -> K -> Prop) -> list (list (K * V)) -> Prop)
  (ht_store_map :
    {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> (K -> K -> Prop) -> (K -> Z) ->
    Z -> mapping K V -> Assertion)
  (ht_store_map_value_hole :
    {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> (K -> K -> Prop) -> (K -> Z) ->
    Z -> mapping K V -> K -> Z -> Assertion)
  (ht_store_map_node_ref_hole :
    {K V} -> (Z -> K -> Assertion) -> (Z -> V -> Assertion) -> (K -> K -> Prop) -> (K -> Z) ->
    Z -> mapping K V -> K -> Z -> Z -> Assertion)
  (empty_mapping : {K V} -> mapping K V)
  (map_empty : {K V} -> mapping K V -> Prop)
  (map_insert : {K V} -> (K -> K -> Prop) -> K -> V -> mapping K V -> mapping K V -> Prop)
  (map_remove : {K V} -> (K -> K -> Prop) -> K -> mapping K V -> mapping K V -> Prop)
  (map_get : {K V} -> K -> mapping K V -> option V -> Prop)
  (In : {A} -> A -> list A -> Prop)
  (pair : {A B} -> A -> B -> A * B)
  (Znth: {A} -> Z -> list A -> A -> A)
  (replace_Znth: {A} -> Z -> A -> list A -> list A)
  (zeros : Z -> list Z)
  (entails_emp : Assertion -> Prop)
 */
