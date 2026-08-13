import SetsClass.SetsDomain
import SetsClass.SetElementProperties
import SetsClass.RelsDomain

namespace SetsNotation

scoped notation "∅" => Sets.empty
scoped infixl:70 " ∩ " => Sets.intersect
scoped infixl:65 " ∪ " => Sets.union
scoped notation "⋂" xs:70 => Sets.indexed_intersect xs
scoped notation "⋃" xs:70 => Sets.indexed_union xs
scoped infix:50 " ≃ₛ " => Sets.equiv
scoped infix:50 " ⊆ " => Sets.included

end SetsNotation
