(*************************************************************************

This file include the normalize tactic VST/msl/log_normalize. In 2020,
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

Module Type ASSUM.

Parameter __PARA__: Type.
  
Parameter expr: forall `{__PARA__}, Type.

Section ASSUM.

Context {p: __PARA__}.

Local Notation "'expr'" := (@expr p).

Parameter provable: expr -> Prop.
Parameter sepcon: expr -> expr -> expr.
Parameter andp: expr -> expr -> expr.
Parameter impp: expr -> expr -> expr.
Parameter iffp: expr -> expr -> expr.
Parameter coq_prop: Prop -> expr.

Local Declare Scope syntax.
Local Open Scope syntax.
Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "'!!' e" := (coq_prop e) (at level 25) : syntax.
Notation "x && y" := (andp x y) (at level 40, left associativity) : syntax.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.

Axiom provable_coq_prop_andp_sepcon1: forall P Q R,
  |-- !! P && Q * R <--> !! P && (Q * R).

Axiom provable_coq_prop_sepcon_andp1: forall P Q R,
 |-- Q * (R && !! P) <--> !! P && (Q * R).

Axiom provable_coq_prop_sepcon_andp2: forall P Q R,
  |-- Q * (!! P && R) <--> !! P && (Q * R).

Axiom provable_coq_prop_andp_sepcon2: forall P Q R,
  |-- Q && !! P * R <--> !! P && (Q * R).

Axiom provable_andp_assoc: forall (x y z: expr),
  |-- x && y && z <--> x && (y && z).

Axiom provables_coq_prop_elim: forall (P: Prop) x,
  (P -> |-- x) -> |-- !! P --> x.

Axiom provables_coq_prop_andp_derives: forall (P: Prop) Q R,
  (P -> |-- Q --> R) -> |-- !! P && Q --> R.

Axiom provables_andp_coq_prop_derives: forall (P: Prop) Q R,
  (P -> |-- Q --> R) -> |-- Q && !! P --> R.

Axiom provables_coq_prop_andp: forall (P: Prop) Q,
  P -> |-- !! P && Q <--> Q.

Axiom provables_andp_coq_prop: forall (P: Prop) Q,
  P -> |-- Q && !! P <--> Q.

End ASSUM.
End ASSUM.

Module ExportTactic (T: ASSUM).

Import T.

Local Declare Scope syntax.
Local Open Scope syntax.
Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "'!!' e" := (coq_prop e) (at level 25) : syntax.
Notation "x && y" := (andp x y) (at level 40, left associativity) : syntax.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.

Ltac normalize1 :=
         match goal with
            | |- _ => contradiction
            | |- context [(!! ?P && ?Q) * ?R] => rewrite (provable_coq_prop_andp_sepcon1 P Q R)
            | |- context [?Q * (!! ?P && ?R)] => rewrite (provable_coq_prop_sepcon_andp2 P Q R)
            | |- context [(?Q && !! ?P) * ?R] => rewrite (provable_coq_prop_andp_sepcon2 P Q R)
            | |- context [?Q * (?R && !! ?P)] => rewrite (provable_coq_prop_sepcon_andp2 P Q R)
            | |- provable (impp ?A _) =>
                   match A with
                   | context [ ((!! ?P) && ?Q) && ?R ] => rewrite (provable_andp_assoc (!!P) Q R)
(*                   | context [ ?Q && (!! ?P && ?R)] =>
                                         match Q with !! _ => fail 2 | _ => rewrite (provable_andp_assoc' (!!P) Q R) end*)
                   end
            |  |- ?ZZ -> _ =>
                   match type of ZZ with
                   | Prop =>
                       let H := fresh in
                       ((assert (H:ZZ) by auto; clear H; intros _) || intro H)
                   | _ => intros _
                   end
            | |- |-- !! _ --> _ => apply provables_coq_prop_elim
            | |- |-- !! _ && _ --> _ => apply provables_coq_prop_andp_derives
            | |- |-- _ && !! _ --> _ => apply provables_andp_coq_prop_derives
            end.

Ltac normalize1_in Hx :=
             match type of Hx with
                | context [ !! ?P && ?Q ] =>
                                    rewrite (provables_coq_prop_andp P Q) in Hx by auto with typeclass_instances
                | context [ ?Q && !! ?P ] =>
                                    rewrite (provables_andp_coq_prop P Q) in Hx by auto with typeclass_instances
                | context [(!! ?P && ?Q) * ?R] => rewrite (provable_coq_prop_andp_sepcon1 P Q R) in Hx
                | context [?Q * (!! ?P && ?R)] => rewrite (provable_coq_prop_sepcon_andp2 P Q R) in Hx
                | context [(?Q && !! ?P) * ?R] => rewrite (provable_coq_prop_andp_sepcon2 P Q R) in Hx
                | context [?Q * (?R && !! ?P)] => rewrite (provable_coq_prop_sepcon_andp2 P Q R) in Hx
                | _ => progress  (autorewrite with norm in Hx); auto with typeclass_instances
                end.

Ltac normalize := repeat normalize1.

Tactic Notation "normalize" "in" hyp(H) := repeat (normalize1_in H).

End ExportTactic.

