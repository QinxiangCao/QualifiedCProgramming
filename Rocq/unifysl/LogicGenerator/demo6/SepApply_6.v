(*************************************************************************

This file include the sep_apply tactic VST/floyd/seplog_tactics. In 2020,
Qinxiang Cao adds connections of this normalized tactic to UnifySL libray.
Here is VST.msl's LICENSE information.

Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
All rights reserved.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS "AS IS" AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR THE CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

***************************************************************************)

Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses.
Require Import export_lib_6.
Import EXPO.
Import EXPO_TRANSPARENTS.
Local Open Scope expo_transparent_scope.
Local Declare Scope syntax.
Local Open Scope syntax.

Module SepApplyNotation.
Notation "|--  x" := ((provable) x) (only parsing, at level 71, no associativity) : syntax.
Notation "x --> y" := ((impp) x y) (only parsing, at level 55, right associativity) : syntax.
Notation "x * y" := ((sepcon) x y) (only parsing, at level 40, left associativity) : syntax.
End SepApplyNotation.
Import SepApplyNotation.

Existing Instances logic_equiv_impp_proper
                   logic_equiv_sepcon_proper
                   provable_proper_equiv
                   logic_equiv_refl_instance.

Ltac cancel_tac EVAR :=
  apply provables_emp_sepcon_unfold;
  rewrite <- !logic_equiv_sepcon_assoc;
  apply provables_emp_sepcon_unfold;
  repeat
    lazymatch goal with
    | |- |-- (?u1 * _) * _ --> ?u2 * _ =>
      (unify u1 u2;
      apply provables_sepcon_impp_unfold;
      repeat apply provables_sepcon_assoc) + simple apply provables_sepcon_sepcon_unfold
    | _ =>
      simple apply provables_sepcon_sepcon_unfold
    end;
  unfold EVAR; apply provable_sepcon_emp_derives.
  
Ltac apply_find_core X :=
 match X with
 | ?U -> ?V => match type of U with Prop => apply_find_core V end
 | provable (impp _ _) => constr:(X)
 | @eq (expr) ?A ?B => constr:(provable (impp A B))
 end.

Ltac head_of_type_of H :=
 match type of H with ?A => apply_find_core A end.

Ltac sep_apply_aux2 H' := 
     match head_of_type_of H' with provable (impp ?C ?D) =>
      let frame := fresh "frame" in evar (frame: (expr));
       apply provables_impp_trans with (C * frame);
             [ solve [cancel_tac frame]
             | eapply provables_impp_trans;
                [ apply provable_sepcon_mono;
                  [ clear frame; apply H'
                  | try subst frame; apply provable_impp_refl]
                | subst frame; rewrite provable_sepcon_emp_logic_equiv
                ]
             ]
     end.

Ltac sep_apply_aux1 H := sep_apply_aux2 H.

Ltac sep_apply_aux0 H := sep_apply_aux1 H.

(* NOTE: this is originally "adjust2_sep_apply".
   But we do not need to handle pure facts now.
   Thus it is a simplified version here. *)
Ltac adjust_sep_apply H :=
 match type of H with
 | @eq (expr) _ _ => constr:(provable_impp_refl' _ _ H)
 | _ => H
 end.

Ltac sep_apply_in_entailment H :=
  match goal with
  | |- provable (impp _ _) =>
     let H' := adjust_sep_apply H in
         sep_apply_aux0 H'
  | _ => fail 0 "The proof goal is not an SL entailment"
  end.

Ltac my_unshelve_evar name T cb evar_tac :=
  let x := fresh name
  in
  unshelve evar (x:T); revgoals;
  [
    let x' := eval unfold x in x
    in
    clear x; cb x'
  |
    evar_tac x
  ].

Ltac HO_sep_apply_in_entailment originalH evar_tac prop_tac :=
  let rec sep_apply_in_entailment_rec H :=
    lazymatch type of H with
    | forall x:?T, _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T);
           [ | sep_apply_in_entailment_rec (H H'); clear H'];
           [ prop_tac | .. ]
      | _ => my_unshelve_evar x T
        ltac:(fun x => sep_apply_in_entailment_rec (H x))
        evar_tac
      end
    | ?T -> _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T);
           [ | sep_apply_in_entailment_rec (H H'); clear H'];
           [ prop_tac | .. ]
      | _ => let x := fresh "arg" in
        my_unshelve_evar x T
          ltac:(fun x => sep_apply_in_entailment_rec (H x))
          evar_tac
      end
    | provable (impp ?A ?B) => sep_apply_in_entailment H
    | ?A = ?B => sep_apply_in_entailment H
    | _ => fail 0 originalH "is not an SL entailment or equivalence"
    end
  in
  sep_apply_in_entailment_rec originalH.

Ltac sep_apply_evar_tac x := fail 0 "Unable to find an instance for the variable" x.
Ltac default_sep_apply_prop_tac := first [reflexivity | assumption | idtac].
Ltac sep_apply_prop_tac := default_sep_apply_prop_tac.

Ltac sep_apply H :=
  HO_sep_apply_in_entailment H sep_apply_evar_tac sep_apply_prop_tac.

