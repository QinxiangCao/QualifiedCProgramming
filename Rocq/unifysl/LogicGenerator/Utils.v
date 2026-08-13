Require Import Coq.Lists.List.
Open Scope list_scope.

Tactic Notation "when" constr(b) ":" tactic3(t) :=
  let bb := eval compute in b in 
  match bb with
  | true => t
  | false => idtac
  end.

Inductive Name := BuildName T (x : T).
Arguments BuildName [T].

Module NameListNotations.
Notation "[ ]" := (@nil Name).
Notation "[ x ]" := (cons (BuildName x) nil).
Notation "[ x ; y ; .. ; z ]" :=
  (cons (BuildName x) (cons (BuildName y) .. (cons (BuildName z) nil) ..)).
End NameListNotations.

Ltac in_name_list n l :=
  match l with
  | nil => constr:(false)
  | cons (BuildName n) _ => constr:(true)
  | cons _ ?l' => in_name_list n l'
  end.
  
Tactic Notation "dolist" tactic0(f) constr(names) :=
  let rec dolist' ns :=
      match ns with
      | nil => idtac
      | ?x :: ?ns' => f x; dolist' ns'
      end
  in dolist' ltac:(eval hnf in names).

Local Ltac print_when f p :=
  match p with
  | (?b, ?names) => when b: dolist f names
  end.

Tactic Notation "dolist_when" tactic0(f) constr(tbl) :=
  dolist (print_when f) tbl.

Ltac remove_arg x :=
  match x with
  | ?y ?z => remove_arg y
  | _ => x
  end.

Ltac map_fst_tac x :=
  match x with
  | nil => constr:(@nil Name)
  | cons (BuildName (pair ?A ?B)) ?y =>
    let res := map_fst_tac y in
    constr:(cons (BuildName A) res)
  end.

Notation "'map_fst' l" := ltac:(let l' := eval hnf in l in
                                let x := map_fst_tac l' in exact x) (only parsing, at level 99).
    
Ltac map_snd_tac x :=
  match x with
  | nil => constr:(@nil Name)
  | cons (BuildName (pair ?A ?B)) ?y =>
    let res := map_snd_tac y in
    constr:(cons (BuildName B) res)
  end.

Notation "'map_snd' l" := ltac:(let l' := eval hnf in l in
                                let x := map_snd_tac l' in exact x) (only parsing, at level 99).
    
Ltac inj_with_hint_tac x l1 l2 :=
  match l1 with
  | cons x _ =>
    match l2 with
    | cons ?a _ => a
    | _ => fail 1000 "inj_with_hint fails since two arguments are not with the same length, or l2 is not fully computed." x l1 l2
    end
  | cons _ ?l1' =>
    match l2 with
    | cons _ ?l2' => inj_with_hint_tac x l1' l2'
    | _ => fail 2 "inj_with_hint fails since two arguments are not with the same length, or l2 is not fully computed." x l1 l2
    end
  | nil => fail 1 "inj_with_hint fails since it finds nothing" x
  | _ => fail 1000 "inj_with_hint fails since l1 is not fully computed."
  end.

Ltac map_with_hint_tac l1 l2 l :=
  match l with
  | nil => match type of l2 with
           | list ?T => constr:(@nil T)
           end
  | cons ?x ?l0 => let a := inj_with_hint_tac x l1 l2 in
                   let l' := map_with_hint_tac l1 l2 l0 in
                   constr:(cons a l')
  end.

Notation "'map_with_hint' '(' l1 ',' l2 ')' l" :=
  ltac:(let l1' := eval hnf in l1 in
        let l2' := eval hnf in l2 in
        let l' := eval hnf in l in
        let res := map_with_hint_tac l1' l2' l' in
        exact res)
  (only parsing, at level 99).

Inductive ___Flag :=.

Ltac if_instance x tac1 tac2 :=
  let z :=
  match type of x with
  | ?T => let res := eval cbv zeta in ltac:(assert(T -> T) by (intro; typeclasses eauto); exact ___Flag) in
          constr:(res)
  | _ => let res := tac2 tt in res
  end
  in
  match z with
  | ___Flag => let res := tac1 tt in res
  | _ => z
  end.

Ltac noninstance_arg_list_rec i t res0 :=
  match t with
  | ?t0 ?x => 
    let tac1 TT := res0 in
    let tac2 TT := noninstance_arg_list_rec i t0 (cons (BuildName (pair i x)) res0) in
    if_instance x tac1 tac2
  | _ => res0
  end.

Ltac noninstance_arg_lists_tac li lt res :=
  match li with
  | nil => res
  | cons (BuildName ?i) ?li0 =>
    match lt with
    | cons (BuildName ?t) ?lt0 =>
      let res := noninstance_arg_list_rec i t res in
      noninstance_arg_lists_tac li0 lt0 res
    end
  end.

Ltac instance_arg_list_rec i t res0 :=
  match t with
  | ?t0 ?x => 
    let tac1 TT := instance_arg_list_rec i t0 (cons (BuildName (pair i x)) res0) in
    let tac2 TT := res0 in
    if_instance x tac1 tac2
  | _ => res0
  end.

Ltac instance_arg_lists_tac li lt res :=
  match li with
  | nil => res
  | cons (BuildName ?i) ?li0 =>
    match lt with
    | cons (BuildName ?t) ?lt0 =>
      let res := instance_arg_list_rec i t res in
      instance_arg_lists_tac li0 lt0 res
    end
  end.

Notation "'noninstance_arg_lists' l" :=
  (ltac:(let li := eval hnf in (fst l) in
         let lt := eval hnf in (snd l) in
         let res := noninstance_arg_lists_tac li lt (@nil Name) in
         exact res))
  (only parsing, at level 99).

Notation "'instance_arg_lists' l" :=
  (ltac:(let li := eval hnf in (fst l) in
         let lt := eval hnf in (snd l) in
         let res := instance_arg_lists_tac li lt (@nil Name) in
         exact res))
  (only parsing, at level 99).

Notation "'nat_ident_list' l" :=
  (ltac:(let l' := eval compute in
         ((fix f (n: nat): list nat :=
            match n with
            | O => nil
            | S n0 => cons O (map S (f n0))
            end) (length l)) in
             exact l'))
  (only parsing, at level 99).

Ltac nodup_nat_ident_list_rec l l_already res n :=
  match l with
  | nil => res
  | cons (BuildName ?a) ?l0 =>
    let test_element := in_name_list a l_already in
    match test_element with
    | true =>
        let rank := inj_with_hint_tac (BuildName a) l_already res in
        nodup_nat_ident_list_rec l0 (cons (BuildName a) l_already) (cons rank res) n
    | false =>
        nodup_nat_ident_list_rec l0 (cons (BuildName a) l_already) (cons n res) (S n)
    end
  end.

Notation "'nodup_nat_ident_list' l" :=
  (ltac:(let l' := eval hnf in l in
         let res := nodup_nat_ident_list_rec l' (@nil Name) (@nil nat) O in
         let res0 := eval compute in (rev res) in    
         exact res0))
  (only parsing, at level 99).

