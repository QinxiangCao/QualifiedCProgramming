import AUXLib.Idents
import AUXLib.VMap
import Lean.Util.CollectAxioms

open AUXLib

#check positive
#check xH
#check xO
#check xI
#check ident
#check ident_eq_dec
#check ident_eqb
#check ident_eqb_refl
#check ident_eqb_eq
#check var
#check func
#check var_eqb
#check func_eqb
#check var_dec
#check func_dec
#check var_eqb_eq
#check var_eqb_neq
#check func_eqb_eq
#check func_eqb_neq
#check var_eqb_refl
#check func_eqb_refl

#check vmap_update
#check vmap_update_list
#check vmap_update_congr0
#check vmap_update_list_congr0
#check vmap_update_eq
#check vmap_update_neq
#check vmap_update_same
#check vmap_update_perm
#check vmap_update_perm_list
#check vmap_update_congr
#check vmap_update_list_congr
#check vmap_update_list_notin
#check vmap_update_list_same
#check vmap_update_list_app
#check vmap_update_list_app_skip1
#check vmap_update_list_app_skip2
#check vmap_update_list_in
#check vmap_update_update_list_in
#check vmap_repair_eq
#check vmap_repair_eq'

example (n m : Nat) (h : Nat.succ n = Nat.succ m) : n = m := by
  inv h
  rfl

example (x : var) (h : x ∈ ([] : List var)) : False := by
  inv h

private abbrev k1 : var := xH
private abbrev k2 : var := xO xH
private abbrev k3 : var := xI xH

example : ident_eqb k1 k1 = true := by native_decide
example : ident_eqb k1 k2 = false := by native_decide

example : (vmap_update (fun _ : var => 0) k1 7) k1 = 7 := by native_decide
example : (vmap_update (fun _ : var => 0) k1 7) k2 = 0 := by native_decide

-- The source recursion updates the tail first, so the earlier duplicate wins.
example : (vmap_update_list (fun _ : var => 0) [k1, k1] [7, 9]) k1 = 7 := by
  native_decide

-- A length mismatch ignores the unmatched suffix on either side.
example : (vmap_update_list (fun _ : var => 0) [k1, k2] [7]) k2 = 0 := by
  native_decide
example : (vmap_update_list (fun _ : var => 0) [k1] [7, 9]) k1 = 7 := by
  native_decide

example : f_eq
    (vmap_update (vmap_update (fun _ : var => 0) k1 7) k2 9)
    (vmap_update (vmap_update (fun _ : var => 0) k2 9) k1 7) := by
  exact vmap_update_perm _ _ _ _ _ (by decide)

example (x y : var) : True := by
  var_destruct x y
  · subst y
    trivial
  · trivial

example {A : Type} (J J' : var -> A) (h : f_eq J J') (v : A) :
    f_eq (vmap_update J k1 v) (vmap_update J' k1 v) := by
  apply vmap_update_congr0.proper
  · exact h
  · rfl
  · rfl

#print axioms AUXLib.ident_eqb_eq
#print axioms AUXLib.vmap_update_perm_list
#print axioms AUXLib.vmap_update_update_list_in
