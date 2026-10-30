Ltac prep_from H :=
  let T := type of H in
  match T with
  | ?P -> ?Q =>
      let Htmp := fresh "Htmp" in
      assert P as Htmp;
      [ idtac | specialize (H Htmp); clear Htmp ]
  end.

Require Import Coq.Unicode.Utf8.
From Ltac2 Require Ltac2.

(** * N-ary tactics

The following helpers are copied from Iris [iris/proofmode/base.v]:
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/proofmode/base.v

Ltac1 has no primitives for traversing its list values, such as those parsed by
[ident_list] and [simple_intropattern_list]. These helpers use Ltac2 internally
to call an Ltac1 tactic on each element, in forward or reverse order.

Keep the implementation in an Ltac definition and use notation only as a wrapper:
<<
Ltac _iTactic xs := ltac1_list_iter ltac:(fun x => intro x) xs.
Tactic Notation "iTactic" "(" ne_ident_list(xs) ")" := _iTactic xs.
>>
To reuse an already parsed list, call [_iTactic xs] directly. Writing
[iTactic (xs)] in another notation would parse [xs] as a list element instead.

[with_ltac1_nil] supplies an empty Ltac1 list to a callback, for example:
<<
Ltac _iTactic0 := with_ltac1_nil ltac:(fun xs => _iTactic xs).
>>

The Iris-derived helpers below are distributed under the BSD-3-Clause license.
Copyright: Iris developers and contributors

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors
      may be used to endorse or promote products derived from this software
      without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)
Ltac2 of_ltac1_list l := Option.get (Ltac1.to_list l).
Ltac ltac1_list_iter tac l :=
  let go := ltac2:(tac l |- List.iter (ltac1:(tac x |- tac x) tac)
                                    (of_ltac1_list l)) in
  go tac l.
Ltac ltac1_list_rev_iter tac l :=
  let go := ltac2:(tac l |- List.iter (ltac1:(tac x |- tac x) tac)
                                    (List.rev (of_ltac1_list l))) in
  go tac l.
Ltac with_ltac1_nil tac :=
  let go := ltac2:(tac |- ltac1:(tac l |- tac l) tac (Ltac1.of_list [])) in
  go tac.


(** The following tactics are from stdpp:
https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/stdpp/tactics.v
*)

(** Tactics for splitting conjunctions:

- [split_and] : split the goal if is syntactically of the shape [_ ∧ _]
- [split_and?] : split the goal repeatedly (perhaps zero times) while it is
  of the shape [_ ∧ _].
- [split_and!] : works similarly, but at least one split should succeed. In
  order to do so, it will head normalize the goal first to possibly expose a
  conjunction.

Note that [split_and] differs from [split] by only splitting conjunctions. The
[split] tactic splits any inductive with one constructor.


- [destruct_and? H] : destruct assumption [H] repeatedly (perhaps zero times)
  while it is of the shape [_ ∧ _].
- [destruct_and! H] : works similarly, but at least one destruct should succeed.
  In order to do so, it will head normalize the goal first to possibly expose a
  conjunction.
- [destruct_and?] iterates [destruct_or? H] on every matching assumption [H].
- [destruct_and!] works similarly, but at least one destruct should succeed.
*)
Tactic Notation "split_and" :=
  match goal with
  | |- _ ∧ _ => split
  (* | |- Is_true (_ && _) => apply andb_True; split *)
  end.
Tactic Notation "split_and" "?" := repeat split_and.
Tactic Notation "split_and" "!" := hnf; split_and; split_and?.

Ltac destruct_and_go H :=
  try lazymatch type of H with
  | True => clear H
  | _ ∧ _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [ H1 H2 ];
    destruct_and_go H1; destruct_and_go H2
  (* | Is_true (bool_decide _) =>
    apply (bool_decide_unpack _) in H;
    destruct_and_go H
  | Is_true (_ && _) =>
    apply andb_True in H;
    destruct_and_go H *)
  end.

Tactic Notation "destruct_and" "?" ident(H) :=
  destruct_and_go H.
Tactic Notation "destruct_and" "!" ident(H) :=
  hnf in H; progress (destruct_and? H).

Tactic Notation "destruct_and" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_and? H) end.
Tactic Notation "destruct_and" "!" :=
  progress destruct_and?.

(** Tactics for splitting disjunctions in an assumption:

- [destruct_or? H] : destruct the assumption [H] repeatedly (perhaps zero times)
  while it is of the shape [_ ∨ _].
- [destruct_or! H] : works similarly, but at least one destruct should succeed.
  In order to do so, it will head normalize the goal first to possibly
  expose a disjunction.
- [destruct_or?] iterates [destruct_or? H] on every matching assumption [H].
- [destruct_or!] works similarly, but at least one destruct should succeed.
*)
Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ ∨ _ => destruct H as [H|H]
  (* | Is_true (bool_decide _) => apply (bool_decide_unpack _) in H
  | Is_true (_ || _) => apply orb_True in H; destruct H as [H|H] *)
  end.
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.


(** The tactic [case_match] destructs an arbitrary match in the conclusion or
assumptions, and generates a corresponding equality. This tactic is best used
together with the [repeat] tactical. *)
Tactic Notation "case_match" "eqn" ":" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.
Ltac case_match :=
  let H := fresh in case_match eqn:H.
