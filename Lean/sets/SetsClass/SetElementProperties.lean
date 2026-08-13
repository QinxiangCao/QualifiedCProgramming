import AUXLib.Morphisms
import SetsClass.SetElement
import SetsClass.SetsDomain

universe u

open AUXLib

class PRE_SETS_ELE_Properties
    (S RES E : Type u)
    [SetsEle.PRE_SETS_ELE S RES E] [Sets.SETS S] [Sets.SETS RES] : Prop where
  In_aux_mono :
    Proper (Eq ==> @Sets.included S _ ==> @Sets.included RES _)
      (@SetsEle.In_aux S RES E _)

class SETS_ELE_Properties
    (S E : Type u) [SetsEle.SETS_ELE S E] [Sets.SETS S] : Prop where
  Sets_In_mono :
    Proper (Eq ==> @Sets.included S _ ==> ImplRel) (@SetsEle.In S E _)

instance Prop_PRE_SETS_ELE_Properties (A S : Type u)
    [Sets.SETS S] : PRE_SETS_ELE_Properties (A -> S) S A where
  In_aux_mono := ⟨by
    intro a a' haa X Y hXY
    subst a'
    exact hXY a⟩

instance lift_PRE_SETS_ELE_Properties
    {A S RES E : Type u}
    [base : SetsEle.PRE_SETS_ELE S (A -> RES) E]
    [Sets.SETS RES] [Sets.SETS S]
    [hbase : PRE_SETS_ELE_Properties S (A -> RES) E] :
    PRE_SETS_ELE_Properties S RES (E × A) where
  In_aux_mono := ⟨by
    intro ea ea' hea X Y hXY
    subst ea'
    exact hbase.In_aux_mono.proper ea.1 ea.1 rfl X Y hXY ea.2⟩

instance Derived_SETS_ELE_Properties
    {S E : Type}
    [base : SetsEle.PRE_SETS_ELE S Prop E] [Sets.SETS S]
    [hbase : PRE_SETS_ELE_Properties S Prop E] :
    SETS_ELE_Properties S E where
  Sets_In_mono := ⟨by
    intro e e' he X Y hXY
    subst e'
    exact hbase.In_aux_mono.proper e e rfl X Y hXY⟩

instance Sets_In_congr
    {S E : Type u} [se : SetsEle.SETS_ELE S E] [Sets.SETS S]
    [SETS_Properties S] [hIn : SETS_ELE_Properties S E] :
    Proper (Eq ==> @Sets.equiv S _ ==> Iff) (@SetsEle.In S E se) where
  proper e e' he X Y hXY := by
    subst e'
    rcases (Sets_equiv_Sets_included X Y).mp hXY with ⟨hForward, hBackward⟩
    constructor
    · exact hIn.Sets_In_mono.proper e e rfl X Y hForward
    · exact hIn.Sets_In_mono.proper e e rfl Y X hBackward
