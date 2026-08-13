import SimpleC.SL.CNotation

open AUXLib
open SimpleC.SL.CNotation

-- Definitions, inductives, constructors, coercion helper, and source parameters.
#check NULL
#check SimpleC.SL.CNotation.addr
#check front_end_type
#check FET_struct
#check FET_union
#check FET_enum
#check FET_alias
#check FET_int
#check FET_char
#check FET_int64
#check FET_short
#check FET_uint
#check FET_uchar
#check FET_uint64
#check FET_ushort
#check FET_ptr
#check rvalue_expr
#check lvalue_expr
#check RE_const
#check RE_add_pi
#check RE_sub_pi
#check RE_addr_of
#check LE_var
#check LE_arrow_field
#check LE_array_subst
#check LE_dot_field
#check eval_addr_expr
#check sizeof_front_end_type
#check struct_or_union
#check Struct
#check Union
#check composite_definition
#check Composite
#check get_lvalue_expr

-- All 38 source assumptions: four Parameters, 28 Axioms, and six Admitted theorems.
#check sizeof_int
#check sizeof_char
#check sizeof_int64
#check sizeof_short
#check sizeof_uint
#check sizeof_uchar
#check sizeof_uint64
#check sizeof_ushort
#check sizeof_ptr
#check rvalue_expr_equiv
#check lvalue_expr_equiv
#check rvalue_expr_equiv_refl
#check lvalue_expr_equiv_refl
#check rvalue_expr_equiv_sym
#check lvalue_expr_equiv_sym
#check rvalue_expr_equiv_trans
#check lvalue_expr_equiv_trans
#check LE_arrow_field_congr
#check LE_array_subst_congr
#check LE_dot_field_congr
#check RE_add_pi_congr
#check RE_sub_pi_congr
#check RE_addr_of_congr
#check eval_addr_expr_congr
#check eval_addr
#check addr_of_array_subst
#check addr_of_array_subst'
#check const_array_pi
#check const_array_pi'
#check addr_of_arrow_field
#check addr_of_arrow_field_inv
#check addr_of_LE_var_not_zero
#check RE_add_pi_inv_l
#check RE_add_pi_inv_r
#check RE_sub_pi_inv_l
#check RE_sub_pi_inv_r

-- The two proved Equivalence declarations and all seven Proper registrations.
#check rvalue_expr_equiv_equiv
#check lvalue_expr_equiv_equiv

example : AUXLib.Equivalence rvalue_expr_equiv := inferInstance
example : AUXLib.Equivalence lvalue_expr_equiv := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_arrow_field := inferInstance
example : Proper (lvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_array_subst := inferInstance
example : Proper (lvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_dot_field := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq ==> rvalue_expr_equiv) RE_add_pi := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq ==> rvalue_expr_equiv) RE_sub_pi := inferInstance
example : Proper (lvalue_expr_equiv ==> rvalue_expr_equiv) RE_addr_of := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq) eval_addr_expr := inferInstance

#print axioms rvalue_expr_equiv_equiv
#print axioms lvalue_expr_equiv_equiv
