import Unifysl.Lib.Bijection

namespace Unifysl

def Countable (A : Type u) : Type u := injection A Nat

def injection_Countable {A : Type u} {B : Type v} (R : injection A B)
    (CB : Countable B) : Countable A :=
  injection_trans R CB

def bijection_Countable {A : Type u} {B : Type v} (R : bijection A B)
    (CB : Countable B) : Countable A :=
  injection_Countable (bijection_injection R) CB

def sum_Countable {A : Type u} {B : Type v} (CA : Countable A)
    (CB : Countable B) : Countable (Sum A B) :=
  injection_trans (sum_injection CA CB) (bijection_injection nat2_nat_bijection)

def prod_Countable {A : Type u} {B : Type v} (CA : Countable A)
    (CB : Countable B) : Countable (Prod A B) :=
  injection_trans (prod_injection CA CB) (bijection_injection natnat_nat_bijection)

def nCountable_Countable {A : Nat -> Type u}
    (CA : forall n, Countable (A n)) : Countable (Sigma A) :=
  injection_trans (sigT_injection Nat A Nat CA) (bijection_injection natnat_nat_bijection)

def unit_Countable : Countable Unit :=
  FBuild_injection Unit Nat (fun _ => 0) (by
    intro a1 a2 _
    cases a1
    cases a2
    rfl)

syntax "solve_Countable" : tactic

macro_rules
  | `(tactic| solve_Countable) =>
      `(tactic|
        first
        | apply sum_Countable <;> solve_Countable
        | apply prod_Countable <;> solve_Countable
        | apply nCountable_Countable
          intro
          solve_Countable
        | apply unit_Countable
        | try assumption)

end Unifysl
