import SimpleC.SL.Mem
import SimpleC.SL.CNotation

open AUXLib
open SimpleC.SL.Mem

-- Public definitions and source declarations.
#check addr
#check addr_eqb
#check addr_dec
#check addr_eqb_eq
#check addr_eqb_neq
#check addr_eqb_refl
#check byte
#check byte_eqb
#check mem_var
#check Noperm
#check Noninit
#check value
#check mem_var_eqb
#check mem
#check empty_mem
#check single_byte_mem
#check single_Noninit_mem
#check mem_byte_update
#check mem_noninit_update
#check mem_remove
#check mem_update_list
#check Z_seq_nat
#check Z_seq
#check mem_update_N
#check mem_empty
#check mem_single
#check mem_join
#check mem_join_congr
#check mem_incl
#check disjoint
#check merge
#check minus
#check sub

-- All 65 Coq lemmas.
#check empty_mem_empty
#check mem_empty_IS_empty_mem
#check single_mem_single
#check mem_join_comm
#check mem_join_assoc1
#check mem_join_assoc2
#check mem_join_emp1
#check mem_join_emp2
#check mem_join_eq_inv1
#check mem_join_eq_inv2
#check mem_join_None1
#check mem_join_None2
#check mem_join_None3
#check mem_join_Some1
#check mem_join_Some2
#check mem_join_Some3
#check mem_join_Some4
#check mem_join_Some6
#check mem_join_Some5
#check mem_join_update1
#check mem_join_update2
#check mem_join_update_None1
#check mem_join_update_list
#check mem_join_update_range
#check mem_join_incl_l
#check mem_join_incl_r
#check mem_update_N_in
#check mem_update_N_notin
#check single_mem_get_eq
#check single_mem_get_neq
#check mem_join_emp
#check mem_empty_IS_empty_mem'
#check mem_join_emp_l
#check mem_join_emp_r
#check mem_join_eq
#check mem_join_eq_l
#check mem_join_eq_r
#check mem_join_Some_eq_l
#check mem_join_Some_eq_r
#check mem_join_None
#check mem_update_eq
#check mem_update_neq
#check mem_update_single_eq
#check mem_update_unfold
#check mem_join_mem_update_l
#check mem_join_mem_update_l'
#check mem_join_single_mem_update_l
#check mem_join_single_mem_remove_l
#check mem_remove_eq
#check mem_remove_neq
#check mem_remove_unfold
#check mem_join_mem_remove_l
#check mem_get_single_mem_sub
#check disjoint_comm
#check disjoint_merge_mem_join
#check sub_minus_mem_join
#check mem_join_sub_l
#check sub_merge_sub
#check mem_join_disjoint_l_ex
#check mem_join_disjoint
#check disjoint_mem_join_l
#check disjoint_mem_join_r
#check mem_join_eqmerge
#check mem_join_merge_assoc_l
#check mem_join_merge_assoc_r

example : Reflexive (@f_eq Int Int) := inferInstance
example : Symmetric (@f_eq Int Int) := inferInstance
example : Transitive (@f_eq Int Int) := inferInstance
example : AUXLib.Equivalence (@f_eq Int Int) := inferInstance
example : Proper (f_eq ==> f_eq ==> f_eq ==> Iff) mem_join := inferInstance

example : addr_eqb (3 : addr) 3 = true := by decide
example : addr_eqb (3 : addr) 4 = false := by decide
example : mem_var_eqb (value 7) (value 7) = true := by simp [mem_var_eqb, byte_eqb]
example : mem_var_eqb Noninit Noperm = false := by rfl
example : single_byte_mem 2 9 2 = value 9 := by simp [single_byte_mem, addr_eqb]
example : single_byte_mem 2 9 3 = Noperm := by simp [single_byte_mem, addr_eqb]
example : mem_byte_update (single_byte_mem 2 9) 3 8 2 = value 9 := by
  simp [mem_byte_update, single_byte_mem, addr_eqb]
example : mem_remove (single_byte_mem 2 9) 2 2 = Noperm := by simp [mem_remove, addr_eqb]

-- The Coq source intentionally clears every non-target cell here.
example : mem_noninit_update (single_byte_mem 10 7) 0 10 = Noperm := by
  simp [mem_noninit_update, addr_eqb]

-- Tail-first recursion means the first duplicate address wins.
example : mem_update_list empty_mem [0, 0] [some 1, some 2] 0 = value 1 := by
  simp [mem_update_list, mem_byte_update, addr_eqb]
-- Unmatched list suffixes are ignored.
example : mem_update_list empty_mem [0, 1] [some 7] 1 = Noperm := by
  simp [mem_update_list, mem_byte_update, empty_mem, addr_eqb]
example : mem_update_list empty_mem [0] [some 7, some 8] 0 = value 7 := by
  simp [mem_update_list, mem_byte_update, addr_eqb]
example : mem_update_N empty_mem 0 9 (-3) = empty_mem := by rfl

-- The five legal pointwise join forms.
example : mem_join empty_mem empty_mem empty_mem := mem_join_emp
example : mem_join empty_mem (single_Noninit_mem 0) (single_Noninit_mem 0) :=
  mem_join_emp1 _
example : mem_join (single_Noninit_mem 0) empty_mem (single_Noninit_mem 0) :=
  mem_join_emp2 _
example : mem_join empty_mem (single_byte_mem 0 1) (single_byte_mem 0 1) :=
  mem_join_emp1 _
example : mem_join (single_byte_mem 0 1) empty_mem (single_byte_mem 0 1) :=
  mem_join_emp2 _

-- Every pair in which both sides own the same cell is illegal.
example (out : mem) :
    Not (mem_join (single_Noninit_mem 0) (single_Noninit_mem 0) out) := by
  intro h
  simpa [single_Noninit_mem, addr_eqb] using h 0

example (out : mem) :
    Not (mem_join (single_Noninit_mem 0) (single_byte_mem 0 1) out) := by
  intro h
  simpa [single_Noninit_mem, single_byte_mem, addr_eqb] using h 0

example (out : mem) :
    Not (mem_join (single_byte_mem 0 1) (single_Noninit_mem 0) out) := by
  intro h
  simpa [single_Noninit_mem, single_byte_mem, addr_eqb] using h 0

example (out : mem) :
    Not (mem_join (single_byte_mem 0 1) (single_byte_mem 0 2) out) := by
  intro h
  simpa [single_byte_mem, addr_eqb] using h 0

example (x y : addr) : x = y \/ Not (x = y) := by
  addr_destruct x y <;> simp_all

example (x y : addr) : x + 1 = y \/ Not (x + 1 = y) := by
  addr_destruct (x + 1) y <;> simp_all

example (P Q R : Prop) (h : P /\ (Q \/ R)) : (P /\ Q) \/ (P /\ R) := by
  my_destruct h <;> simp_all

example (P : Nat -> Prop) (h : Exists P) : Exists P := by
  my_destruct h
  exact ⟨_, ‹P _›⟩

example (P : Int -> Prop) (Q : Prop) (h : (Exists fun x => P x /\ Q) \/ False) :
    Exists fun x => P x /\ Q := by
  my_destruct h
  exact ⟨_, ‹P _›, ‹Q›⟩

example (m : mem) (h : mem_empty m) : m = empty_mem := by
  solve_empmem
  rfl

example (m out : mem) (h : mem_join m empty_mem out) : out = m := by
  solve_empmem
  rfl

example (m out : mem) (h : mem_join empty_mem m out) : out = m := by
  solve_empmem
  rfl

example (m : mem) (h : mem_join m empty_mem empty_mem) : m = empty_mem := by
  solve_empmem
  rfl

example (m : mem) (h : mem_join empty_mem m empty_mem) : m = empty_mem := by
  solve_empmem
  rfl

example (m : mem) (h : mem_join m empty_mem m) : True := by
  solve_empmem
  fail_if_success clear h
  trivial

example (m : mem) (h : mem_empty m) : True := by
  solve_empmem
  fail_if_success clear h
  trivial

example : mem_join empty_mem empty_mem empty_mem := by
  solve_empmem

example (m : mem) : mem_join m empty_mem m := by
  solve_empmem

example (m : mem) : mem_join empty_mem m m := by
  solve_empmem

example : mem_empty empty_mem := by
  solve_empmem

-- The source tactic is a successful no-op outside its memory-specific shapes.
example (P : Prop) (h : P) : P := by
  solve_empmem
  exact h

example (x : Nat) : x = x := by
  solve_empmem
  rfl

example (m : mem) (x : Nat) (h : mem_empty m) : x = x := by
  solve_empmem
  rfl

example (m : mem) : m = m := by
  solve_empmem
  rfl

example (m n : mem) (h : mem_empty m) : n = n := by
  solve_empmem
  rfl

example (m : mem) (h : mem_empty m) : m = m := by
  solve_empmem
  rfl

#print axioms AUXLib.functional_extensionality
#print axioms AUXLib.propositional_extensionality
#print axioms mem_join_assoc1

namespace CNotationTests

open SimpleC.SL.CNotation
open scoped SimpleC

#check fun (p : SimpleC.SL.CNotation.addr) (q : rvalue_expr) =>
  p = &((q + 1) ->ₛ "pstPrev")

#check fun (p : SimpleC.SL.CNotation.addr) (q : rvalue_expr) =>
  p = &(q ->ₛ "pstPrev")

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &((p # struct "LOS_DL_LIST") ->ₛ "pstPrev")

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &(p # struct "LOS_DL_LIST" ->ₛ "pstPrev")

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &(p # "LOS_DL_LIST" ->ₛ "pstPrev")

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &(p # "LOS_TaskCB" ->ₛ "readWriteCnt"[0 + 1])

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &(((p + 1)) # "LOS_TaskCB" ->ₛ "readWriteCnt"[0 + 1])

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &("g_TaskCB")

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &("g_TaskCB") + sizeof("TaskCB") * 1

#check fun (p : SimpleC.SL.CNotation.addr) =>
  p = &("g_X") + sizeof(INT) * 1

#check fun (p : SimpleC.SL.CNotation.addr) (_n : Int) =>
  p = &((p # "LOS_DL_LIST" + 1) ->ₛ "pstPrev")

#check fun (p : SimpleC.SL.CNotation.addr) (_n : Int) =>
  p = &((p # "LOS_DL_LIST" + (1)) ->ₛ "pstPrev")

example (p : SimpleC.SL.CNotation.addr) :
    &(&(p # "TaskCB" ->ₛ "pend_list") ->ₛ "pstPrev") =
      &(p # "TaskCB" ->ₛ "pend_list" .ₛ "pstPrev") := by
  csimpl
  rfl

example (q : SimpleC.SL.CNotation.addr) :
    &(q # "TaskCB" ->ₛ "pend_list" .ₛ "pstPrev") =
      &(&(q # "TaskCB" ->ₛ "pend_list") ->ₛ "pstPrev") := by
  csimpl
  rfl

example (p : SimpleC.SL.CNotation.addr) :
    let q := p + 10 * sizeof("TaskCB")
    &(q # "TaskCB" ->ₛ "pend_list") =
      &((p # "TaskCB" + 10) ->ₛ "pend_list") := by
  dsimp
  csimpl
  rfl

example (p : SimpleC.SL.CNotation.addr) :
    let q := p + sizeof("TaskCB") * 10
    &(q # "TaskCB" ->ₛ "pend_list") =
      &((p # "TaskCB" + 10) ->ₛ "pend_list") := by
  dsimp
  csimpl
  rfl

example (p q : SimpleC.SL.CNotation.addr)
    (h : &(q # "TaskCB" ->ₛ "pend_list") =
      &((p # "TaskCB" + 10) ->ₛ "pend_list")) :
    q = p + sizeof("TaskCB") * 10 := by
  have h' := addr_of_arrow_field_inv _ _ _ h
  cases h'

example :
    let q := eval_addr_expr (RE_addr_of ("x" : lvalue_expr))
    &(q # "LOS_TaskCB" ->ₛ "pend_list") =
      &(&("x") ->ₛ "pend_list") := by
  dsimp
  csimpl
  rfl

end CNotationTests
