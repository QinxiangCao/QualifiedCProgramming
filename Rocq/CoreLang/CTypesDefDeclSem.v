Require Import Coq.Structures.Equalities.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import SimpleC.Common.CTypes.
Require Import SimpleC.CoreLang.CTypes.

Inductive StructUnionEnum_State: Type :=
  | Declared_struct
  | Declared_union
  | Declared_enum
  | Defined_struct (m: list FieldDecl)
  | Defined_union (m: list FieldDecl)
  | Defined_enum (m: list Enumerator)
.

Record Stack (T: Type): Type := {
  stack_top: T;
  rest_of_stack: list T;
}.

Notation "x '.(stack_top)'" := (stack_top _ x)
  (at level 1).

Notation "x '.(rest_of_stack)'" := (rest_of_stack _ x)
  (at level 1).

Fixpoint get_from_list
           {A B: Type}
           (f: A -> option B)
           (l: list A):
  option (B * nat) :=
  match l with
  | nil => None
  | cons a l0 =>
      match f a with
      | Some b => Some (b, length l0)
      | None => get_from_list f l0
      end
  end.

Definition get_from_stack
             {A B: Type}
             (f: A -> option B)
             (s: Stack A):
  option (B * nat) :=
  match f s.(stack_top) with
  | Some b => Some (b, length s.(rest_of_stack))
  | None => get_from_list f s.(rest_of_stack)
  end.

Definition map_stack {A B: Type} (f: A -> B) (s: Stack A): Stack B :=
  {|
    stack_top := f (s.(stack_top));
    rest_of_stack := map f (s.(rest_of_stack));
  |}.

Definition stack_size {A: Type} (s: Stack A): nat :=
  S (length s.(rest_of_stack)).

Definition current_level {A: Type} (s: Stack A): nat :=
  length s.(rest_of_stack).

Notation "x '.(size)'" := (stack_size x)
  (at level 1).

Notation "x '.(lvl)'" := (current_level x)
  (at level 1).

Definition TypeEnv: Type :=
  Stack 
    ( (TypeName -> option StructUnionEnum_State) *
    (string -> option SimpleCtype) ).

Definition struct_union_enum_env (t_env: TypeEnv):
  Stack  (TypeName -> option StructUnionEnum_State) :=
  map_stack fst t_env.

Definition alias_env (t_env: TypeEnv):
  Stack  (string -> option SimpleCtype) :=
  map_stack snd t_env.

Notation "x '.(struct_union_enum_env)'" := (struct_union_enum_env x)
  (at level 1).

Notation "x '.(alias_env)'" := (alias_env x)
  (at level 1).

Definition get_SUE_state (t_env: TypeEnv) (s: string):
  option (StructUnionEnum_State * nat) :=
  get_from_stack (fun f => f (CTN_named s)) t_env.(struct_union_enum_env).

Definition get_alias_state (t_env: TypeEnv) (s: string):
  option (SimpleCtype * nat) :=
  get_from_stack (fun f => f s) t_env.(alias_env).

Definition get_top_SUE_state (t_env: TypeEnv) (s: string):
  option StructUnionEnum_State :=
  t_env.(struct_union_enum_env).(stack_top) (CTN_named s).

Definition get_top_alias_state (t_env: TypeEnv) (s: string):
  option SimpleCtype :=
  t_env.(alias_env).(stack_top) s.

