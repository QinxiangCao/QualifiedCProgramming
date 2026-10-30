Require Import SetsClass.SetsClass.
Import SetsNotation.
Import SetProd.

Local Open Scope sets.

Ltac sets_unfold_fast_term T :=
  let T1 := eval cbv beta iota zeta delta
    [ Sets.full Sets.empty Sets.prop_inj Sets.complement Sets.intersect Sets.union
      Sets.indexed_intersect Sets.indexed_union Sets.equiv Sets.included
      Sets.general_intersect Sets.general_union Sets.Taux Sets.Qaux Sets.Paux
      Sets.conj_aux Sets.imply_aux Sets.forall_aux Sets.exists_aux
      Sets.lift_full Sets.lift_empty Sets.lift_prop_inj Sets.lift_complement
      Sets.lift_intersect Sets.lift_union Sets.lift_indexed_intersect Sets.lift_indexed_union
      Sets.lift_equiv Sets.lift_included Sets.lift_Taux Sets.lift_Qaux Sets.lift_Paux
      Sets.lift_conj_aux Sets.lift_imply_aux Sets.lift_forall_aux Sets.lift_exists_aux
      Sets.test1 Sets.lift1 Sets.filter1
      SetsEle.In SetsEle.In_aux SetsEle.lift_In_aux
      Rels.concat Rels.concat_aux Rels.id Rels.id_aux Rels.test
      Rels.app Rels.nil
      Prop_PRE_RELS lift_PRE_RELS Derived_RELS
      Prop_PRE_RELS_ID lift_PRE_RELS_ID Derived_RELS_ID Derived_RELS_TEST
      ListConn.list_ACC ListConn.list_ACC_Nil
      NatFuncConn.natfunc_ACC NatFuncConn.natfunc_ACC_Nil
      NatFuncConn.natfunc_app
      StreamConn.stream_ACC StreamConn.stream_ACC_Nil
      StreamConn.stream_app
      Prop_SETS lift_SETS Prop_PRE_SETS_ELE lift_PRE_SETS_ELE Derived_SETS_ELE
      prod liftL liftR Prop_SETS_PROD lift_SETS_PROD ] in T in
  constr:(T1).

Ltac sets_unfold_fast_term_with_singleton T :=
  let T0 := eval unfold Sets.singleton in T in
  sets_unfold_fast_term T0.

Ltac sets_unfold_fast :=
  match goal with
  | |- ?T =>
      let T' := sets_unfold_fast_term_with_singleton T in
      change T';
      cbv beta iota
  end.

Ltac sets_unfold_fast_in H :=
  match type of H with
  | ?T =>
      let T' := sets_unfold_fast_term_with_singleton T in
      change T' in H;
      cbv beta iota in H
  end.

Tactic Notation "sets_unfold" := sets_unfold_fast.
Tactic Notation "sets_unfold" "in" constr(H) := sets_unfold_fast_in H.
