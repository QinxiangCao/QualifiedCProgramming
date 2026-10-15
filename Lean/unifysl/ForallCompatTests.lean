import Unifysl.Lib.Coqlib

namespace ForallCompatTests

example {P : α -> Prop} {xs : List α} (h : List.Forall P xs) : True := by
  cases h with
  | nil => trivial
  | cons hx hxs => trivial

example {P : α -> Prop} {xs : List α} (h : List.Forall P xs) :
    forall x, x ∈ xs -> P x := by
  induction h with
  | nil =>
      intro x hx
      cases hx
  | cons hx hxs ih =>
      intro x hmem
      cases hmem with
      | head => exact hx
      | tail _ htail => exact ih x htail

#check List.Forall.rec
#check List.Forall.casesOn

end ForallCompatTests
