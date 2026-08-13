Require Export SetsClass.SetElement.
Require Export SetsClass.SetsDomain.
Require Export SetsClass.SetElementProperties.
Require Export SetsClass.SetProd.
Require Export SetsClass.RelsDomain.

Module SetsNotation.

Declare Scope sets_scope.
Delimit Scope sets_scope with sets.

Notation "[ ]":= Sets.empty (format "[ ]"): sets_scope.
Notation "∅":= Sets.empty (at level 5, no associativity): sets_scope.
Notation "[ x ]":= (Sets.singleton x) : sets_scope.
Notation "x ∩ y" := (Sets.intersect x y)(at level 13, left associativity): sets_scope.
Notation "x ∪ y" := (Sets.union x y)(at level 14, left associativity): sets_scope.
Notation "⋃ x" := (Sets.indexed_union x)(at level 10, no associativity): sets_scope.
Notation "⋂ x" := (Sets.indexed_intersect x)(at level 10, no associativity): sets_scope.
Notation "⨆ x" := (Sets.general_union x)(at level 10, no associativity): sets_scope.
Notation "⨅ x" := (Sets.general_intersect x)(at level 10, no associativity): sets_scope.
Notation "x == y" := (Sets.equiv x y) (at level 70, no associativity): sets_scope.
Notation "x ⊆ y" := (Sets.included x y) (at level 70, no associativity): sets_scope.
Notation "x ∈ y" := (SetsEle.In x y) (at level 70, no associativity): sets_scope.
Notation "⌜ x ⌝" := (Sets.prop_inj x) (at level 40, no associativity): sets_scope.
Notation "X ∘ Y" := (Rels.concat X Y) (right associativity, at level 12): sets_scope.

Notation "x × y" := (prod x y)
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (prod x (@Sets.full y _))
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (prod (@Sets.full x _) y)
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (prod (@Sets.full x _) (@Sets.full y _))
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (ltac:(any_prod x y))
  (left associativity, only parsing, at level 11): sets_scope.

End SetsNotation.
