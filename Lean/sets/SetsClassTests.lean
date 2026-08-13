import SetsClass.SetsClass

open scoped SetsNotation

#check Sets.SETS
#check Sets.full
#check Sets.empty
#check Sets.complement
#check Sets.intersect
#check Sets.union
#check Sets.indexed_intersect
#check Sets.indexed_union
#check Sets.general_intersect
#check Sets.general_union
#check Sets.equiv
#check Sets.included
#check Sets.singleton
#check SETS_Properties
#check SETS_Classical_Properties
#check SetsEle.PRE_SETS_ELE
#check SetsEle.SETS_ELE
#check PRE_SETS_ELE_Properties
#check SETS_ELE_Properties
#check Rels.RELS
#check Rels.RELS_ID
#check Rels.concat
#check lift_PRE_RELS
#check lift_PRE_RELS_ID
#check ACCUM_Assoc
#check ACCUM_LeftId
#check ACCUM_RightId
#check ListConn.list_ACC
#check ListConn.list_ACC_Nil
#check ListConn.list_ACC_LeftId
#check ListConn.list_ACC_RightId
#check ListConn.list_ACC_Assoc
#check clos_refl_trans
#check Sets_union_comm
#check Sets_union_assoc
#check Sets_intersect_union_distr_r
#check Sets_union_intersect_distr_r
#check Sets_complement_union
#check Sets_complement_self_union

example {A : Type} (P Q : A -> Prop) :
    P ∩ Q ≃ₛ Q ∩ P := Sets_intersect_comm P Q

example {A : Type} (P Q R : A -> Prop) :
    (P ∩ Q) ∪ R ≃ₛ (P ∪ R) ∩ (Q ∪ R) :=
  Sets_union_intersect_distr_r P Q R

example {A : Type} (P : A -> Prop) :
    (⋂ P) ↔ forall x, P x := Iff.rfl

example {A : Type} (P : A -> Prop) :
    (⋃ P) ↔ exists x, P x := Iff.rfl

example {A : Type} (P : (A -> Prop) -> Prop) :
    Sets.general_union P ≃ₛ fun a => exists X, P X /\ X a := by
  sets_unfold
  simp

example {A : Type} (P : A -> Prop) (a : A) : SetsEle.In a P <-> P a := Iff.rfl

example {A : Type} (P : A -> Prop) :
    Sets.complement P ∪ P ≃ₛ (Sets.full : A -> Prop) :=
  Sets_complement_self_union P

example {A : Type} (P Q : A -> Prop)
    (h : Sets.equiv (Sets.union P Q) P) : forall x, P x ∨ Q x ↔ P x := by
  sets_unfold at h
  exact h

example {A : Type} (P Q : A -> Prop) :
    Sets.equiv (Sets.complement (Sets.union P Q))
      (fun x => Not (P x) ∧ Not (Q x)) := by
  sets_unfold
  intro x
  exact not_or

example {A : Type} (a x : A) : Sets.singleton a x → a = x := by
  sets_unfold
  exact id

example {A : Type} (a x : A) (h : Sets.singleton a x) : a = x := by
  sets_unfold at h
  exact h

example (P : Prop) (hP : P) : P := by
  sets_unfold
  exact hP

example {A : Type} (a x : A) (hTarget : Sets.singleton a x)
    (hOther : Sets.equiv (Sets.empty : Prop) Sets.empty) :
    a = x ∧ Sets.equiv (Sets.empty : Prop) Sets.empty := by
  sets_unfold at hTarget
  exact ⟨hTarget, hOther⟩

example {A : Type} (xs ys : List A) :
    @Rels.app (List A) (List A) (List A) (ListConn.list_ACC A) xs ys = xs ++ ys := rfl

example {A : Type} :
    @Rels.nil (List A) (ListConn.list_ACC_Nil A) = [] := rfl

example {A : Type} : ACCUM_Assoc
    (List A) (List A) (List A) (List A) (List A) (List A) := inferInstance

example {A : Type} : ACCUM_LeftId (List A) (List A) := inferInstance

example {A : Type} : ACCUM_RightId (List A) (List A) := inferInstance

#print axioms Sets_complement_self_union
