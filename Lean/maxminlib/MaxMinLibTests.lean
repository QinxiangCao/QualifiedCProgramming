import Lean.Elab.Tactic.Omega
import MaxMinLib.Interface

open AUXLib
open MaxMinLib
open scoped MaxMinLib.MaxMinNotation

#check TotalOrder
#check TotalOrder.le_refl
#check TotalOrder.le_trans
#check TotalOrder.le_antisym
#check TotalOrder.le_total
#check AUXLib.Morphisms_Prop.and_iff_morphism
#check AUXLib.Morphisms_Prop.or_iff_morphism
#check AUXLib.Morphisms_Prop.ex_iff_morphism
#check AUXLib.Morphisms_Prop.all_iff_morphism
#check le_total_cases
#check le_max
#check le_min
#check max_r
#check max_l
#check max_comm
#check max_assoc
#check min_r
#check min_l

#check max_object_of_subset
#check max_value_of_subset
#check max_value_of_subset_with_default
#check max_object_sound
#check max_object_legal
#check max_default_ge_default
#check max_object_of_subset_congr
#check max_value_of_subset_congr
#check max_value_of_subset_with_default_congr
#check max_unique
#check max_default_unique
#check max_le
#check max_default_le
#check max_eq
#check max_default_eq
#check max_eq_forward'
#check max_eq_forward
#check max_default_eq_forward'
#check max_default_eq_forward
#check max_mono_incr_bind'
#check max_mono_incr_bind
#check max_object_union_left
#check max_object_union1
#check max_object_union_right
#check max_object_union2
#check max_object_union
#check max_union'
#check max_union
#check max_default_union'
#check max_default_union
#check max_object_1
#check max_empty
#check max_1'
#check max_1
#check max_singleton
#check max_default_1
#check max_union_1_right'
#check max_union_1_right
#check max_default_union_1_right'
#check max_default_union_1_right
#check max_default_default_inv
#check max_default_default'
#check max_default_default

#check min_object_of_subset
#check min_value_of_subset
#check min_value_of_subset_with_default
#check min_object_sound
#check min_object_legal
#check min_default_le_default
#check min_object_of_subset_congr
#check min_value_of_subset_congr
#check min_value_of_subset_with_default_congr
#check min_unique
#check min_default_unique
#check min_le
#check min_default_le
#check min_eq
#check min_default_eq
#check min_eq_forward'
#check min_eq_forward
#check min_default_eq_forward'
#check min_default_eq_forward
#check min_mono_incr_bind'
#check min_mono_incr_bind
#check min_object_union_left
#check min_object_union1
#check min_object_union_right
#check min_object_union2
#check min_object_union
#check min_union'
#check min_union
#check min_default_union'
#check min_default_union
#check min_object_1
#check min_empty
#check min_1'
#check min_1
#check min_singleton
#check min_default_1
#check min_union_1_right'
#check min_union_1_right
#check min_default_union_1_right'
#check min_default_union_1_right
#check min_default_default_inv
#check min_default_default'
#check min_default_default

#check max_mono_decr_bind'
#check max_mono_decr_bind
#check min_mono_decr_bind'
#check min_mono_decr_bind
#check min_exists_union_l
#check min_exists_union_r

#check Z_le_total
#check max_n_in_range
#check min_n_in_range
#check Zle_TotalOrder
#check Nat_le_total
#check min_nonempty_exists
#check min_union_iff
#check NatLe_TotalOrder
#check Nat_op_le
#check Nat_op_plus
#check Nat_op_min
#check Nat_op_le_refl
#check Nat_op_le_trans
#check Nat_op_le_antisym
#check Nat_op_le_total
#check Nat_op_le_TotalOrder
#check Z_op_le
#check Z_op_plus
#check Z_op_min
#check Z_op_le_refl
#check Z_op_le_trans
#check Z_op_le_antisym
#check Z_op_le_total
#check Z_op_le_TotalOrder
#check Z_op_plus_mono
#check Z_op_none_le_iff
#check Z_op_le_ge_cases
#check Z_op_plus_O_r
#check Z_op_plus_O_l
#check Z_op_plus_none_r
#check Z_op_plus_comm
#check Z_op_plus_assoc
#check Z_op_min_none_r
#check Z_op_min_le_l
#check Z_op_le_none_r
#check Z_op_le_min_l
#check Z_op_le_min_r
#check Z_op_le_min_imply
#check Z_op_le_min_le_l
#check Z_op_le_min_le_r
#check Z_op_finite_min

#check (inferInstance : TotalOrder (fun x y : Int => x <= y))
#check (inferInstance : TotalOrder (fun x y : Nat => x <= y))
#check (inferInstance : TotalOrder Nat_op_le)
#check (inferInstance : TotalOrder Z_op_le)

#check (inferInstance :
  Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
    (max_object_of_subset (T := Int) (A := Nat) (fun x y : Int => x <= y)))
#check (inferInstance :
  Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
    (max_value_of_subset (T := Int) (A := Nat) (fun x y : Int => x <= y)))
#check (inferInstance :
  Proper (Sets.equiv ==> Eq ==> Eq ==> Eq ==> Iff)
    (max_value_of_subset_with_default (T := Int) (A := Nat) (fun x y : Int => x <= y)))
#check (inferInstance :
  Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
    (min_object_of_subset (T := Int) (A := Nat) (fun x y : Int => x <= y)))
#check (inferInstance :
  Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
    (min_value_of_subset (T := Int) (A := Nat) (fun x y : Int => x <= y)))
#check (inferInstance :
  Proper (Sets.equiv ==> Eq ==> Eq ==> Eq ==> Iff)
    (min_value_of_subset_with_default (T := Int) (A := Nat) (fun x y : Int => x <= y)))

example (R : Int -> Int -> Prop) (P : Nat -> Prop) (f : Nat -> Int) :
    max_value_of_subset R P f 0 =
      (exists a, max_object_of_subset R P f a /\ f a = 0) := rfl

example : le_max (fun x y : Int => x <= y) (3 : Int) 5 = 5 :=
  max_r (fun x y : Int => x <= y) (3 : Int) 5 (by omega)

example : le_max (fun x y : Int => x <= y) (7 : Int) (-2) = 7 :=
  max_l (fun x y : Int => x <= y) (7 : Int) (-2) (by omega)

example : le_min (fun x y : Int => x <= y) (3 : Int) 5 = 3 :=
  min_r (fun x y : Int => x <= y) (3 : Int) 5 (by omega)

example : max_value_of_subset_with_default (fun x y : Int => x <= y)
    (Sets.empty : Nat -> Prop) (fun n : Nat => (n : Int)) 7 7 := by
  apply max_default_default
  intro a h
  exact h

example : min_value_of_subset_with_default (fun x y : Int => x <= y)
    (Sets.empty : Nat -> Prop) (fun n : Nat => (n : Int)) 7 7 := by
  apply min_default_default
  intro a h
  exact h

example : Nat_op_min (some 5) (some 2) = some 2 := rfl
example : Nat_op_min none (some 3) = some 3 := rfl
example : Nat_op_plus (some 2) none = none := rfl

example : Z_op_min (some 5) (some 2) = some 2 := rfl
example : Z_op_min none (some 3) = some 3 := rfl
example : Z_op_plus (some 2) none = none := rfl
example : Z_op_le (some 3) none := trivial
example : Not (Z_op_le none (some 3)) := by
  simp [Z_op_le]

example :
    Z_op_le (Z_op_min (some 5) (some 2)) (some 5) :=
  Z_op_le_min_le_l (some 5) (some 2)

example :
    exists b, min_value_of_subset Nat.le
      (fun x : Nat => x = 2 \/ x = 5) (fun x : Nat => x) b := by
  apply min_nonempty_exists
  exact ⟨2, Or.inl rfl⟩

example :
    exists m, min_object_of_subset Z_op_le
      (fun x : Int => x = 3 \/ x = 1 \/ x = 2)
      (fun x : Int => some x) m := by
  apply Z_op_finite_min (fun x : Int => some x)
    (fun x : Int => x = 3 \/ x = 1 \/ x = 2) [3, 1, 2] 1
  · simp
  · simp
  · intro y hy
    rcases hy with rfl | rfl | rfl <;> simp

example (le : Int -> Int -> Prop) :
    (5 is-the-max-of x in-which x satisfies True) =
      max_value_of_subset le (fun _ : Int => True) (fun x : Int => x) 5 := by
  rfl

example (le : Int -> Int -> Prop) :
    (5 is-the-max-of x in-which x satisfies True with-default 0) =
      max_value_of_subset_with_default le
        (fun _ : Int => True) (fun x : Int => x) 0 5 := by
  rfl

example (le : Int -> Int -> Prop) :
    (the-min-of x in-which x satisfies True) =
      min_value_of_subset le (fun _ : Int => True) (fun x : Int => x) := by
  rfl

#print axioms MaxMinLib.max_default_union
#print axioms MaxMinLib.min_default_union
#print axioms MaxMinLib.Z_op_finite_min
