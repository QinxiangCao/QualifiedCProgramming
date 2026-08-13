(** This library aims to express abstract maps using Coq function type. *)
(** Inspired by `Maps` from Software Foundation Volumn 1, 
    https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html
*)
Require Export Coq.Classes.EquivDec.

Section total_map.
Context {K V: Type} `{EqDec K eq}.

Definition t_empty (v: V): K -> V := fun _ => v.

Definition t_set (m: K -> V) (k: K) (v: V): K -> V :=
  fun k' => if k == k' then v else m k'.

End total_map.

Declare Scope map_scope.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity) : map_scope.

Notation "x '!->' v ';' m" := (t_set m x v)
  (at level 100, v at next level, right associativity) : map_scope.
