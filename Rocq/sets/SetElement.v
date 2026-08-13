Module SetsEle.

Class PRE_SETS_ELE (S RES E: Type): Type := {
  In_aux: E -> S -> RES;
  set_transfer_aux: (E -> RES) -> S;
}.

Class SETS_ELE (S E: Type): Type := {
  In: E -> S -> Prop;
  set_transfer: S -> S;
}.

Definition lift_In_aux
           {A S RES E}
           {_SETS: PRE_SETS_ELE S (A -> RES) E}:
  (E * A) -> S -> RES :=
  fun a X => In_aux
               (match a with (a1, a2) => a1 end)
               X
               (match a with (a1, a2) => a2 end).

Definition lift_set_transfer_aux
           {A S RES E}
           {_SETS: PRE_SETS_ELE S (A -> RES) E}:
  (E * A -> RES) -> S :=
  fun F => set_transfer_aux (fun a1 a2 => F (a1, a2)).

End SetsEle.

#[export] Instance Prop_PRE_SETS_ELE (A S: Type): SetsEle.PRE_SETS_ELE (A -> S) S A :=
  {|
    SetsEle.In_aux := fun a X => X a;
    SetsEle.set_transfer_aux := fun F => F
  |}.

#[export] Instance lift_PRE_SETS_ELE
           {A S RES E: Type}
           (_SETS: SetsEle.PRE_SETS_ELE S (A -> RES) E):
  SetsEle.PRE_SETS_ELE S RES (E * A) :=
  {|
    SetsEle.In_aux := SetsEle.lift_In_aux;
    SetsEle.set_transfer_aux := SetsEle.lift_set_transfer_aux;
  |}.

#[export] Instance Derived_SETS_ELE
           {S E: Type}
           (_SETS: SetsEle.PRE_SETS_ELE S Prop E):
  SetsEle.SETS_ELE S E :=
  {|
    SetsEle.In :=
      SetsEle.In_aux;
    SetsEle.set_transfer :=
      fun X => SetsEle.set_transfer_aux (fun a => SetsEle.In_aux a X);
  |}.

Ltac SETS_ELE_unfold1 _SETS_ELE :=
  match _SETS_ELE with
  | lift_PRE_SETS_ELE _ =>
      let p := eval unfold lift_PRE_SETS_ELE at 1 in _SETS_ELE in
      constr:(p)
  | Prop_PRE_SETS_ELE _ _ =>
      let p := eval unfold Prop_PRE_SETS_ELE in _SETS_ELE in
      constr:(p)
  | Derived_SETS_ELE _ =>
      let p := eval unfold Derived_SETS_ELE in _SETS_ELE in
      constr:(p)
  | @SetsEle.Build_PRE_SETS_ELE _ _ _ _ _ =>
      constr:(_SETS_ELE)
  | @SetsEle.Build_SETS_ELE _ _ _ _ =>
      constr:(_SETS_ELE)
  end.

Ltac test_SETS_ELE_unit _SETS_ELE :=
  match _SETS_ELE with
  | lift_PRE_SETS_ELE _ =>
      constr:(tt)
  | Prop_PRE_SETS_ELE _ _ =>
      constr:(tt)
  | Derived_SETS_ELE _ =>
      constr:(tt)
  | @SetsEle.Build_PRE_SETS_ELE _ _ _ _ _ =>
      constr:(tt)
  | @SetsEle.Build_SETS_ELE _ _ _ _ =>
      constr:(tt)
  end.
  
Ltac SETS_ELE_In_simplify T :=
  match T with
  | @SetsEle.In ?S ?E ?_SETS_ELE =>
      let _ := test_SETS_ELE_unit _SETS_ELE in
      let op1 := eval cbv delta [SetsEle.In] in @SetsEle.In in
      let SETS1 := SETS_ELE_unfold1 _SETS_ELE in
      let T1 := eval cbv beta zeta iota in (op1 S E SETS1) in
      constr:(T1)
  | @SetsEle.In_aux ?S ?RES ?E ?_SETS_ELE =>
      let _ := test_SETS_ELE_unit _SETS_ELE in
      let op1 := eval cbv delta [SetsEle.In_aux] in @SetsEle.In_aux in
      let SETS1 := SETS_ELE_unfold1 _SETS_ELE in
      let T1 := eval cbv beta zeta iota in (op1 S RES E SETS1) in
      let T2 := eval cbv beta delta [SetsEle.lift_In_aux] in T1 in
      constr:(T2)
  end.

Ltac SETS_ELE_In_simplify_rec T :=
  match T with
  | context G [@SetsEle.In ?S ?E ?_SETS_ELE] =>
      let S := SETS_ELE_In_simplify (@SetsEle.In S E _SETS_ELE) in
      let T1 := context G [S] in
      let T2 := SETS_ELE_In_simplify_rec T1 in
      constr:(T2)
  | context G [@SetsEle.In_aux ?S ?RES ?E ?_SETS_ELE] =>
      let S := SETS_ELE_In_simplify (@SetsEle.In_aux S RES E _SETS_ELE) in
      let T1 := context G [S] in
      let T2 := SETS_ELE_In_simplify_rec T1 in
      constr:(T2)
  | _ => constr:(T)
  end.

Ltac unfold_In_in_goal_tac :=
  match goal with
  | |- ?T =>
         let P := SETS_ELE_In_simplify_rec T in
         change P;
         cbv beta iota
  end.

Ltac unfold_In_in_hypo_tac H :=
  match type of H with
  | ?T =>
         let P := SETS_ELE_In_simplify_rec T in
         change P in H;
         cbv beta iota in H
  end.

Ltac SETS_ELE_transfer_aux_simplify T :=
  match T with
  | ?op ?S ?RES ?E ?_SETS_ELE =>
    let _ := test_SETS_ELE_unit _SETS_ELE in
    let op1 := eval cbv delta
              [SetsEle.set_transfer_aux] in op in
    let SETS1 := SETS_ELE_unfold1 _SETS_ELE in
    let T1 := eval cbv beta zeta iota in (op1 S RES E SETS1) in
    let T2 := eval cbv beta delta
              [SetsEle.lift_set_transfer_aux] in T1 in
    constr:(T2)
  end.

Ltac SETS_ELE_transfer_aux_simplify_rec T :=
  match T with
  | context G [@SetsEle.set_transfer_aux ?S ?RES ?E ?_SETS_ELE] =>
      let S := SETS_ELE_transfer_aux_simplify
                 (@SetsEle.set_transfer_aux S RES E _SETS_ELE) in
      let T1 := context G [S] in
      let T2 := SETS_ELE_transfer_aux_simplify_rec T1 in
      constr:(T2)
  | _ => constr:(T)
  end.

Ltac SETS_ELE_transfer_simplify_func T :=
  let tr := SETS_ELE_transfer_aux_simplify_rec
              (fun X: T => @SetsEle.set_transfer_aux T Prop _ _
                              (fun a => @SetsEle.In T _ _ a X)) in
  let F := eval cbv beta in tr in
  constr:(F).

Ltac SETS_ELE_transfer_simplify X :=
  match type of X with
  | ?T => let F := SETS_ELE_transfer_simplify_func T in
          let X0 := eval cbv beta in (F X) in
          constr:(X0)
  end.

Arguments SetsEle.In: simpl never.
