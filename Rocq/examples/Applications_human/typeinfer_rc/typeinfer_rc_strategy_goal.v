From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc.
Local Open Scope sac.

Definition typeinfer_rc_strategy46 :=
  forall (M : RcState),
    TT &&
    emp **
    ((store_world_missing M (@nil TypeFieldKey)))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (N : RcState),
      TT &&
      (“ (N = M) ”) &&
      emp -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy43 :=
  forall (p : Z) (tr : TypeTree) (M : RcState),
    TT &&
    (“ (store_type M p tr) ”) &&
    emp **
    ((store_world M))
    |--
    (
    TT &&
    (“ (store_type M p tr) ”) &&
    emp **
    ((store_world M))
    ) ** (
    ALL (out : TypeTree) (N : RcState),
      TT &&
      (“ (N = M) ”) &&
      (“ (out = tr) ”) &&
      emp -*
      TT &&
      (“ (store_type N p out) ”) &&
      emp
      ).

Definition typeinfer_rc_strategy0 :=
  forall (M : RcState),
    TT &&
    emp **
    ((store_world M))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_world_missing M (@nil TypeFieldKey)))
    ).

Definition typeinfer_rc_strategy4 :=
  forall (p : Z) (n : TypeNode) (M : RcState),
    TT &&
    (“ (node_at M p n) ”) &&
    emp
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    emp
    ) ** (
    ALL (m : TypeNode),
      TT &&
      (“ (n = m) ”) &&
      emp -*
      TT &&
      (“ (node_at M p m) ”) &&
      emp
      ).

Definition typeinfer_rc_strategy100 :=
  forall (s : TypeFieldSlot) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p s L) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy101 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (s : TypeFieldSlot) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    emp -*
    TT &&
    (“ (field_lookup p s L) ”) &&
    emp
    ).

Definition typeinfer_rc_strategy102 :=
  forall (L : (@list TypeFieldKey)) (k : TypeFieldKey),
    TT &&
    (“ (field_fresh k L) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy47 :=
  forall (v : Z) (n : TypeNode) (L : (@list TypeFieldKey)) (M : RcState) (p : Z) (q : Z),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    (“ (q = p) ”) &&
    (“ (v = (node_tag n)) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L))) **
    ((poly_store FET_int &( ((q)) # "atype" ->ₛ "t") v))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (N : RcState),
      TT &&
      emp **
      ((store_world N)) -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy48 :=
  forall (n : TypeNode) (q : Z) (p : Z) (M : RcState) (L : (@list TypeFieldKey)) (v : Z),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ (q = p) ”) &&
    (“ (v = (node_a n)) ”) &&
    (“ ((node_tag n) = 1) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L))) **
    ((poly_store FET_ptr &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from") v))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (N : RcState),
      TT &&
      emp **
      ((store_world N)) -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy49 :=
  forall (n : TypeNode) (q : Z) (p : Z) (M : RcState) (L : (@list TypeFieldKey)) (v : Z),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ (q = p) ”) &&
    (“ (v = (node_b n)) ”) &&
    (“ ((node_tag n) = 1) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload1)) L))) **
    ((poly_store FET_ptr &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to") v))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (N : RcState),
      TT &&
      emp **
      ((store_world N)) -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy50 :=
  forall (n : TypeNode) (q : Z) (p : Z) (M : RcState) (L : (@list TypeFieldKey)) (v : Z),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ (q = p) ”) &&
    (“ (v = (node_a n)) ”) &&
    (“ ((node_tag n) = 2) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L))) **
    ((poly_store FET_ptr &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn") v))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (N : RcState),
      TT &&
      emp **
      ((store_world N)) -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy51 :=
  forall (n : TypeNode) (q : Z) (p : Z) (M : RcState) (L : (@list TypeFieldKey)) (v : Z),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ (q = p) ”) &&
    (“ (v = (node_b n)) ”) &&
    (“ ((node_tag n) = 2) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload1)) L))) **
    ((poly_store FET_ptr &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand") v))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (N : RcState),
      TT &&
      emp **
      ((store_world N)) -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy52 :=
  forall (n : TypeNode) (q : Z) (p : Z) (M : RcState) (L : (@list TypeFieldKey)) (v : Z),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ (q = p) ”) &&
    (“ (v = (node_a n)) ”) &&
    (“ ((node_tag n) = 0) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L))) **
    ((poly_store FET_int &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name") v))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (N : RcState),
      TT &&
      emp **
      ((store_world N)) -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy6 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState) (n : TypeNode),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L))) **
    ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") (node_tag n)))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_world_missing M L))
    ).

Definition typeinfer_rc_strategy17 :=
  forall (v : Z) (name : Z) (M : RcState) (unused : Z) (p : Z),
    TT &&
    (“ (node_at M p (Node 3 name unused)) ”) &&
    (“ (v = name) ”) &&
    emp **
    ((store_world_missing M (payload_keys p (Node 3 name unused)))) **
    ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v))
    |--
    (
    TT &&
    (“ (node_at M p (Node 3 name unused)) ”) &&
    emp
    ) ** (
    ALL (N : RcState),
      TT &&
      (“ (N = M) ”) &&
      emp -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy36 :=
  forall (p : Z) (tr : TypeTree) (M : RcState) (N : RcState),
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (store_type M p tr) ”) &&
    emp **
    ((store_world N))
    |--
    (
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (store_type M p tr) ”) &&
    (“ (store_type N p tr) ”) &&
    emp **
    ((store_world N))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy37 :=
  forall (p : Z) (n : TypeNode) (M : RcState) (N : RcState),
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (node_at M p n) ”) &&
    emp **
    ((store_world N))
    |--
    (
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (node_at M p n) ”) &&
    (“ (node_at N p n) ”) &&
    emp **
    ((store_world N))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy38 :=
  forall (p : Z) (tr : TypeTree) (M : RcState) (N : RcState) (L : (@list TypeFieldKey)),
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (store_type M p tr) ”) &&
    emp **
    ((store_world_missing N L))
    |--
    (
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (store_type M p tr) ”) &&
    (“ (store_type N p tr) ”) &&
    emp **
    ((store_world_missing N L))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy39 :=
  forall (p : Z) (n : TypeNode) (M : RcState) (N : RcState) (L : (@list TypeFieldKey)),
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (node_at M p n) ”) &&
    emp **
    ((store_world_missing N L))
    |--
    (
    TT &&
    (“ (rc_preserves M N) ”) &&
    (“ (node_at M p n) ”) &&
    (“ (node_at N p n) ”) &&
    emp **
    ((store_world_missing N L))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy42 :=
  forall (x : Z) (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    (“ (x = (node_tag n)) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L))) **
    ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") x))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z) (q : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy73 :=
  forall (s : TypeFieldSlot) (p : Z),
    TT &&
    (“ (field_lookup p s (@nil TypeFieldKey)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p s) (@nil TypeFieldKey)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy74 :=
  forall (p : Z) (q : Z) (L : (@list TypeFieldKey)) (t : TypeFieldSlot) (s : TypeFieldSlot),
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (p <> q) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (p <> q) ”) &&
    (“ (field_lookup p s L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy75 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    (“ (field_lookup p (RefCount) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy76 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    (“ (field_lookup p (RefCount) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy77 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    (“ (field_lookup p (RefCount) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy78 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    (“ (field_lookup p (Tag) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy79 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    (“ (field_lookup p (Tag) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy80 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    (“ (field_lookup p (Tag) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy81 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy82 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy83 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy84 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    (“ (field_lookup p (Payload1) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy85 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    (“ (field_lookup p (Payload1) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy86 :=
  forall (q : Z) (L : (@list TypeFieldKey)) (p : Z),
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    (“ (field_lookup p (Payload1) L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy87 :=
  forall (p : Z) (q : Z) (t : TypeFieldSlot) (s : TypeFieldSlot) (L : (@list TypeFieldKey)),
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (field_fresh (field_key p s) L) ”) &&
    (“ (p <> q) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p s) L) ”) &&
    (“ (p <> q) ”) &&
    (“ (field_fresh (field_key p s) (@cons TypeFieldKey (field_key q t) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy88 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    (“ (field_fresh (field_key p (RefCount)) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy89 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    (“ (field_fresh (field_key p (RefCount)) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy90 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (RefCount) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    (“ (field_fresh (field_key p (RefCount)) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy91 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    (“ (field_fresh (field_key p (Tag)) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy92 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    (“ (field_fresh (field_key p (Tag)) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy93 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Tag) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    (“ (field_fresh (field_key p (Tag)) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy94 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ (field_fresh (field_key p (Payload0)) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy95 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ (field_fresh (field_key p (Payload0)) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy96 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Payload0) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ (field_fresh (field_key p (Payload0)) (@cons TypeFieldKey (field_key q (Payload1)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy97 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ (field_fresh (field_key p (Payload1)) (@cons TypeFieldKey (field_key q (RefCount)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy98 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ (field_fresh (field_key p (Payload1)) (@cons TypeFieldKey (field_key q (Tag)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy99 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (q : Z),
    TT &&
    (“ (field_lookup p (Payload1) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ (field_fresh (field_key p (Payload1)) (@cons TypeFieldKey (field_key q (Payload0)) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy103 :=
  forall (q : Z) (p : Z) (L : (@list TypeFieldKey)) (t : TypeFieldSlot) (s : TypeFieldSlot),
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (q <> p) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (q <> p) ”) &&
    (“ (field_lookup p s L) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy104 :=
  forall (q : Z) (p : Z) (t : TypeFieldSlot) (s : TypeFieldSlot) (L : (@list TypeFieldKey)),
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (field_fresh (field_key p s) L) ”) &&
    (“ (q <> p) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_fresh (field_key p s) L) ”) &&
    (“ (q <> p) ”) &&
    (“ (field_fresh (field_key p s) (@cons TypeFieldKey (field_key q t) L)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition typeinfer_rc_strategy34 :=
  forall (ty : front_end_type) (a : Z) (b : Z) (x : (front_end_type_value ty)),
    TT &&
    (“ (a = b) ”) &&
    emp **
    ((poly_store ty a x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (v : (front_end_type_value ty)),
      TT &&
      (“ (v = x) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store ty b v))
      ).

Definition typeinfer_rc_strategy35 :=
  forall (ty : front_end_type) (a : Z) (b : Z) (x : (front_end_type_value ty)),
    TT &&
    (“ (a = b) ”) &&
    emp **
    ((poly_store ty a x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store ty b))
    ).

Definition typeinfer_rc_strategy7 :=
  forall (M : RcState),
    TT &&
    emp **
    ((store_world M))
    |--
    (
    TT &&
    emp **
    ((store_world_missing M (@nil TypeFieldKey)))
    ) ** (
    ALL (ty : front_end_type) (v : (front_end_type_value ty)) (a : Z),
      TT &&
      emp **
      ((poly_store ty a v)) -*
      TT &&
      emp **
      ((poly_store ty a v))
      ).

Definition typeinfer_rc_strategy8 :=
  forall (M : RcState),
    TT &&
    emp **
    ((store_world M))
    |--
    (
    TT &&
    emp **
    ((store_world_missing M (@nil TypeFieldKey)))
    ) ** (
    ALL (ty : front_end_type) (a : Z),
      TT &&
      emp **
      ((poly_undef_store ty a)) -*
      TT &&
      emp **
      ((poly_undef_store ty a))
      ).

Definition typeinfer_rc_strategy72 :=
  forall (p : Z) (n : TypeNode) (M : RcState) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L))) **
    ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") (node_tag n)))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_lookup p (Tag) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L))) **
    ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") (node_tag n)))
    ) ** (
    ALL (v : Z) (q : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((q)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy41 :=
  forall (n : TypeNode) (p : Z) (tr : TypeTree) (M : RcState),
    TT &&
    (“ (store_type M p tr) ”) &&
    (“ (node_at M p n) ”) &&
    (“ (rc_valid M) ”) &&
    (“ ((node_tag n) = 3) ”) &&
    emp **
    ((store_world_missing M (@nil TypeFieldKey)))
    |--
    (
    TT &&
    (“ (store_type M p tr) ”) &&
    (“ (node_at M p n) ”) &&
    (“ (rc_valid M) ”) &&
    (“ (tr = (TVar (node_a n))) ”) &&
    (“ (n = (Node 3 (node_a n) 0)) ”) &&
    (“ (node_at M p (Node 3 (node_a n) 0)) ”) &&
    (“ (0 <= (node_a n)) ”) &&
    (“ ((node_a n) < 100) ”) &&
    emp **
    ((store_world_missing M (payload_keys p (Node 3 (node_a n) 0))))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_a n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy44 :=
  forall (n : TypeNode) (M : RcState) (tr : TypeTree) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (store_type M p tr) ”) &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 1) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    EX (a : TypeTree) (b : TypeTree),
      (
      TT &&
      (“ (store_type M p tr) ”) &&
      (“ (node_at M p n) ”) &&
      (“ (field_fresh (field_key p (Payload0)) L) ”) &&
      (“ (tr = (TArrow a b)) ”) &&
      (“ (store_type M (node_a n) a) ”) &&
      (“ (store_type M (node_b n) b) ”) &&
      emp **
      ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = (node_a n)) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from") v))
        ).

Definition typeinfer_rc_strategy45 :=
  forall (n : TypeNode) (M : RcState) (tr : TypeTree) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (store_type M p tr) ”) &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 2) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    EX (a : TypeTree) (b : TypeTree),
      (
      TT &&
      (“ (store_type M p tr) ”) &&
      (“ (node_at M p n) ”) &&
      (“ (field_fresh (field_key p (Payload0)) L) ”) &&
      (“ (tr = (TApply a b)) ”) &&
      (“ (store_type M (node_a n) a) ”) &&
      (“ (store_type M (node_b n) b) ”) &&
      emp **
      ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = (node_a n)) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn") v))
        ).

Definition typeinfer_rc_strategy33 :=
  forall (p : Z) (unused : Z) (name : Z) (M : RcState),
    TT &&
    (“ (node_at M p (Node 3 name unused)) ”) &&
    emp **
    ((store_world_missing M (@nil TypeFieldKey)))
    |--
    (
    TT &&
    (“ (node_at M p (Node 3 name unused)) ”) &&
    emp **
    ((store_world_missing M (payload_keys p (Node 3 name unused))))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = name) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy20 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 3) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_a n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy21 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 3) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name")))
    ).

Definition typeinfer_rc_strategy22 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 0) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_a n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy23 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 0) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name")))
    ).

Definition typeinfer_rc_strategy24 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 1) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_a n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from") v))
      ).

Definition typeinfer_rc_strategy25 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 1) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from")))
    ).

Definition typeinfer_rc_strategy26 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ ((node_tag n) = 1) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload1)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_b n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to") v))
      ).

Definition typeinfer_rc_strategy27 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ ((node_tag n) = 1) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload1)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to")))
    ).

Definition typeinfer_rc_strategy28 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 2) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_a n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn") v))
      ).

Definition typeinfer_rc_strategy29 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 2) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn")))
    ).

Definition typeinfer_rc_strategy30 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ ((node_tag n) = 2) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload1)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_b n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand") v))
      ).

Definition typeinfer_rc_strategy31 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    (“ ((node_tag n) = 2) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Payload1)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload1)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand")))
    ).

Definition typeinfer_rc_strategy5 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState) (n : TypeNode),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_tag n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") v))
      ).

Definition typeinfer_rc_strategy9 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState) (n : TypeNode),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (RefCount)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (rc_count M p)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "atype" ->ₛ "refcnt") v))
      ).

Definition typeinfer_rc_strategy10 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState) (n : TypeNode),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (RefCount)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "refcnt")))
    ).

Definition typeinfer_rc_strategy13 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState) (n : TypeNode),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "t")))
    ).

Definition typeinfer_rc_strategy53 :=
  forall (n : TypeNode) (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (rc_valid M) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) <> 1) ”) &&
    (“ ((node_tag n) <> 2) ”) &&
    (“ ((node_tag n) <> 3) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (node_at M p n) ”) &&
    (“ (rc_valid M) ”) &&
    (“ (field_fresh (field_key p (Payload0)) L) ”) &&
    (“ ((node_tag n) = 0) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p (Payload0)) L)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (node_a n)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy40 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState) (tr : TypeTree),
    TT &&
    (“ (store_type M p tr) ”) &&
    (“ (field_fresh (field_key p (Tag)) L) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    EX (n : TypeNode),
      (
      TT &&
      (“ (store_type M p tr) ”) &&
      (“ (field_fresh (field_key p (Tag)) L) ”) &&
      (“ (node_at M p n) ”) &&
      (“ (0 <= (node_tag n)) ”) &&
      (“ ((node_tag n) <= 3) ”) &&
      emp **
      ((store_world_missing M (@cons TypeFieldKey (field_key p (Tag)) L)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = (node_tag n)) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") v))
        ).

Definition typeinfer_rc_strategy11 :=
  forall (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (rc_valid M) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    (“ (0 < (rc_count M p)) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    EX (n : TypeNode),
      (
      TT &&
      (“ (rc_valid M) ”) &&
      (“ (field_fresh (field_key p (RefCount)) L) ”) &&
      (“ (node_at M p n) ”) &&
      emp **
      ((store_world_missing M (@cons TypeFieldKey (field_key p (RefCount)) L)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = (rc_count M p)) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "atype" ->ₛ "refcnt") v))
        ).

Definition typeinfer_rc_strategy12 :=
  forall (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (rc_valid M) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    (“ (0 < (rc_count M p)) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    EX (n : TypeNode),
      (
      TT &&
      (“ (rc_valid M) ”) &&
      (“ (field_fresh (field_key p (RefCount)) L) ”) &&
      (“ (node_at M p n) ”) &&
      emp **
      ((store_world_missing M (@cons TypeFieldKey (field_key p (RefCount)) L)))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp **
      ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "refcnt")))
      ).

Definition typeinfer_rc_strategy14 :=
  forall (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (rc_valid M) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    (“ (0 < (rc_reserved M p)) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    EX (n : TypeNode),
      (
      TT &&
      (“ (rc_valid M) ”) &&
      (“ (field_fresh (field_key p (RefCount)) L) ”) &&
      (“ (node_at M p n) ”) &&
      emp **
      ((store_world_missing M (@cons TypeFieldKey (field_key p (RefCount)) L)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = (rc_count M p)) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "atype" ->ₛ "refcnt") v))
        ).

Definition typeinfer_rc_strategy15 :=
  forall (M : RcState) (p : Z) (L : (@list TypeFieldKey)),
    TT &&
    (“ (rc_valid M) ”) &&
    (“ (field_fresh (field_key p (RefCount)) L) ”) &&
    (“ (0 < (rc_reserved M p)) ”) &&
    emp **
    ((store_world_missing M L))
    |--
    EX (n : TypeNode),
      (
      TT &&
      (“ (rc_valid M) ”) &&
      (“ (field_fresh (field_key p (RefCount)) L) ”) &&
      (“ (node_at M p n) ”) &&
      emp **
      ((store_world_missing M (@cons TypeFieldKey (field_key p (RefCount)) L)))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp **
      ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "refcnt")))
      ).

Definition typeinfer_rc_strategy54 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (RefCount) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "atype" ->ₛ "refcnt") v)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "atype" ->ₛ "refcnt") v))
      ).

Definition typeinfer_rc_strategy55 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (RefCount) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "refcnt"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "refcnt")))
    ).

Definition typeinfer_rc_strategy56 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Tag) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") v)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "atype" ->ₛ "t") v))
      ).

Definition typeinfer_rc_strategy57 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Tag) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "t"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "atype" ->ₛ "t")))
    ).

Definition typeinfer_rc_strategy58 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy59 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "VAR"))) # "anonymous struct 3" ->ₛ "name")))
    ).

Definition typeinfer_rc_strategy60 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name") v)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name") v))
      ).

Definition typeinfer_rc_strategy61 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ATOM"))) # "anonymous struct 4" ->ₛ "name")))
    ).

Definition typeinfer_rc_strategy62 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from") v)) -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from") v))
      ).

Definition typeinfer_rc_strategy63 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "from")))
    ).

Definition typeinfer_rc_strategy64 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload1) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to") v)) -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to") v))
      ).

Definition typeinfer_rc_strategy65 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload1) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "ARROW"))) # "anonymous struct 1" ->ₛ "to")))
    ).

Definition typeinfer_rc_strategy66 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn") v)) -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn") v))
      ).

Definition typeinfer_rc_strategy67 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload0) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "tfn")))
    ).

Definition typeinfer_rc_strategy68 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload1) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand") v)) -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand") v))
      ).

Definition typeinfer_rc_strategy69 :=
  forall (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M L))
    |--
    (
    TT &&
    (“ (field_lookup p (Payload1) L) ”) &&
    emp **
    ((store_world_missing M L))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand"))) -*
    TT &&
    emp **
    ((poly_undef_store FET_ptr &( ((&( ((&( ((p)) # "atype" ->ₛ "d"))) # "anonymous union 1" ->ₛ "APP"))) # "anonymous struct 2" ->ₛ "rand")))
    ).

Definition typeinfer_rc_strategy70 :=
  forall (s : TypeFieldSlot) (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p s) L)))
    |--
    (
    TT &&
    (“ (field_lookup p s L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p s) L)))
    ) ** (
    ALL (N : RcState),
      TT &&
      emp **
      ((store_world N)) -*
      TT &&
      emp **
      ((store_world N))
      ).

Definition typeinfer_rc_strategy71 :=
  forall (s : TypeFieldSlot) (L : (@list TypeFieldKey)) (p : Z) (M : RcState),
    TT &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p s) L)))
    |--
    (
    TT &&
    (“ (field_lookup p s L) ”) &&
    emp **
    ((store_world_missing M (@cons TypeFieldKey (field_key p s) L)))
    ) ** (
    ALL (N : RcState) (K : (@list TypeFieldKey)),
      TT &&
      emp **
      ((store_world_missing N K)) -*
      TT &&
      emp **
      ((store_world_missing N K))
      ).

Definition typeinfer_rc_strategy105 :=
  forall (p : Z) (q : Z) (L : (@list TypeFieldKey)) (t : TypeFieldSlot) (s : TypeFieldSlot),
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (p <> q) ”) &&
    emp
    |--
    (
    TT &&
    (“ (field_lookup p s (@cons TypeFieldKey (field_key q t) L)) ”) &&
    (“ (p <> q) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type typeinfer_rc_Strategy_Correct.

  Axiom typeinfer_rc_strategy46_correctness : typeinfer_rc_strategy46.
  Axiom typeinfer_rc_strategy43_correctness : typeinfer_rc_strategy43.
  Axiom typeinfer_rc_strategy0_correctness : typeinfer_rc_strategy0.
  Axiom typeinfer_rc_strategy4_correctness : typeinfer_rc_strategy4.
  Axiom typeinfer_rc_strategy100_correctness : typeinfer_rc_strategy100.
  Axiom typeinfer_rc_strategy101_correctness : typeinfer_rc_strategy101.
  Axiom typeinfer_rc_strategy102_correctness : typeinfer_rc_strategy102.
  Axiom typeinfer_rc_strategy47_correctness : typeinfer_rc_strategy47.
  Axiom typeinfer_rc_strategy48_correctness : typeinfer_rc_strategy48.
  Axiom typeinfer_rc_strategy49_correctness : typeinfer_rc_strategy49.
  Axiom typeinfer_rc_strategy50_correctness : typeinfer_rc_strategy50.
  Axiom typeinfer_rc_strategy51_correctness : typeinfer_rc_strategy51.
  Axiom typeinfer_rc_strategy52_correctness : typeinfer_rc_strategy52.
  Axiom typeinfer_rc_strategy6_correctness : typeinfer_rc_strategy6.
  Axiom typeinfer_rc_strategy17_correctness : typeinfer_rc_strategy17.
  Axiom typeinfer_rc_strategy36_correctness : typeinfer_rc_strategy36.
  Axiom typeinfer_rc_strategy37_correctness : typeinfer_rc_strategy37.
  Axiom typeinfer_rc_strategy38_correctness : typeinfer_rc_strategy38.
  Axiom typeinfer_rc_strategy39_correctness : typeinfer_rc_strategy39.
  Axiom typeinfer_rc_strategy42_correctness : typeinfer_rc_strategy42.
  Axiom typeinfer_rc_strategy73_correctness : typeinfer_rc_strategy73.
  Axiom typeinfer_rc_strategy74_correctness : typeinfer_rc_strategy74.
  Axiom typeinfer_rc_strategy75_correctness : typeinfer_rc_strategy75.
  Axiom typeinfer_rc_strategy76_correctness : typeinfer_rc_strategy76.
  Axiom typeinfer_rc_strategy77_correctness : typeinfer_rc_strategy77.
  Axiom typeinfer_rc_strategy78_correctness : typeinfer_rc_strategy78.
  Axiom typeinfer_rc_strategy79_correctness : typeinfer_rc_strategy79.
  Axiom typeinfer_rc_strategy80_correctness : typeinfer_rc_strategy80.
  Axiom typeinfer_rc_strategy81_correctness : typeinfer_rc_strategy81.
  Axiom typeinfer_rc_strategy82_correctness : typeinfer_rc_strategy82.
  Axiom typeinfer_rc_strategy83_correctness : typeinfer_rc_strategy83.
  Axiom typeinfer_rc_strategy84_correctness : typeinfer_rc_strategy84.
  Axiom typeinfer_rc_strategy85_correctness : typeinfer_rc_strategy85.
  Axiom typeinfer_rc_strategy86_correctness : typeinfer_rc_strategy86.
  Axiom typeinfer_rc_strategy87_correctness : typeinfer_rc_strategy87.
  Axiom typeinfer_rc_strategy88_correctness : typeinfer_rc_strategy88.
  Axiom typeinfer_rc_strategy89_correctness : typeinfer_rc_strategy89.
  Axiom typeinfer_rc_strategy90_correctness : typeinfer_rc_strategy90.
  Axiom typeinfer_rc_strategy91_correctness : typeinfer_rc_strategy91.
  Axiom typeinfer_rc_strategy92_correctness : typeinfer_rc_strategy92.
  Axiom typeinfer_rc_strategy93_correctness : typeinfer_rc_strategy93.
  Axiom typeinfer_rc_strategy94_correctness : typeinfer_rc_strategy94.
  Axiom typeinfer_rc_strategy95_correctness : typeinfer_rc_strategy95.
  Axiom typeinfer_rc_strategy96_correctness : typeinfer_rc_strategy96.
  Axiom typeinfer_rc_strategy97_correctness : typeinfer_rc_strategy97.
  Axiom typeinfer_rc_strategy98_correctness : typeinfer_rc_strategy98.
  Axiom typeinfer_rc_strategy99_correctness : typeinfer_rc_strategy99.
  Axiom typeinfer_rc_strategy103_correctness : typeinfer_rc_strategy103.
  Axiom typeinfer_rc_strategy104_correctness : typeinfer_rc_strategy104.
  Axiom typeinfer_rc_strategy34_correctness : typeinfer_rc_strategy34.
  Axiom typeinfer_rc_strategy35_correctness : typeinfer_rc_strategy35.
  Axiom typeinfer_rc_strategy7_correctness : typeinfer_rc_strategy7.
  Axiom typeinfer_rc_strategy8_correctness : typeinfer_rc_strategy8.
  Axiom typeinfer_rc_strategy72_correctness : typeinfer_rc_strategy72.
  Axiom typeinfer_rc_strategy41_correctness : typeinfer_rc_strategy41.
  Axiom typeinfer_rc_strategy44_correctness : typeinfer_rc_strategy44.
  Axiom typeinfer_rc_strategy45_correctness : typeinfer_rc_strategy45.
  Axiom typeinfer_rc_strategy33_correctness : typeinfer_rc_strategy33.
  Axiom typeinfer_rc_strategy20_correctness : typeinfer_rc_strategy20.
  Axiom typeinfer_rc_strategy21_correctness : typeinfer_rc_strategy21.
  Axiom typeinfer_rc_strategy22_correctness : typeinfer_rc_strategy22.
  Axiom typeinfer_rc_strategy23_correctness : typeinfer_rc_strategy23.
  Axiom typeinfer_rc_strategy24_correctness : typeinfer_rc_strategy24.
  Axiom typeinfer_rc_strategy25_correctness : typeinfer_rc_strategy25.
  Axiom typeinfer_rc_strategy26_correctness : typeinfer_rc_strategy26.
  Axiom typeinfer_rc_strategy27_correctness : typeinfer_rc_strategy27.
  Axiom typeinfer_rc_strategy28_correctness : typeinfer_rc_strategy28.
  Axiom typeinfer_rc_strategy29_correctness : typeinfer_rc_strategy29.
  Axiom typeinfer_rc_strategy30_correctness : typeinfer_rc_strategy30.
  Axiom typeinfer_rc_strategy31_correctness : typeinfer_rc_strategy31.
  Axiom typeinfer_rc_strategy5_correctness : typeinfer_rc_strategy5.
  Axiom typeinfer_rc_strategy9_correctness : typeinfer_rc_strategy9.
  Axiom typeinfer_rc_strategy10_correctness : typeinfer_rc_strategy10.
  Axiom typeinfer_rc_strategy13_correctness : typeinfer_rc_strategy13.
  Axiom typeinfer_rc_strategy53_correctness : typeinfer_rc_strategy53.
  Axiom typeinfer_rc_strategy40_correctness : typeinfer_rc_strategy40.
  Axiom typeinfer_rc_strategy11_correctness : typeinfer_rc_strategy11.
  Axiom typeinfer_rc_strategy12_correctness : typeinfer_rc_strategy12.
  Axiom typeinfer_rc_strategy14_correctness : typeinfer_rc_strategy14.
  Axiom typeinfer_rc_strategy15_correctness : typeinfer_rc_strategy15.
  Axiom typeinfer_rc_strategy54_correctness : typeinfer_rc_strategy54.
  Axiom typeinfer_rc_strategy55_correctness : typeinfer_rc_strategy55.
  Axiom typeinfer_rc_strategy56_correctness : typeinfer_rc_strategy56.
  Axiom typeinfer_rc_strategy57_correctness : typeinfer_rc_strategy57.
  Axiom typeinfer_rc_strategy58_correctness : typeinfer_rc_strategy58.
  Axiom typeinfer_rc_strategy59_correctness : typeinfer_rc_strategy59.
  Axiom typeinfer_rc_strategy60_correctness : typeinfer_rc_strategy60.
  Axiom typeinfer_rc_strategy61_correctness : typeinfer_rc_strategy61.
  Axiom typeinfer_rc_strategy62_correctness : typeinfer_rc_strategy62.
  Axiom typeinfer_rc_strategy63_correctness : typeinfer_rc_strategy63.
  Axiom typeinfer_rc_strategy64_correctness : typeinfer_rc_strategy64.
  Axiom typeinfer_rc_strategy65_correctness : typeinfer_rc_strategy65.
  Axiom typeinfer_rc_strategy66_correctness : typeinfer_rc_strategy66.
  Axiom typeinfer_rc_strategy67_correctness : typeinfer_rc_strategy67.
  Axiom typeinfer_rc_strategy68_correctness : typeinfer_rc_strategy68.
  Axiom typeinfer_rc_strategy69_correctness : typeinfer_rc_strategy69.
  Axiom typeinfer_rc_strategy70_correctness : typeinfer_rc_strategy70.
  Axiom typeinfer_rc_strategy71_correctness : typeinfer_rc_strategy71.
  Axiom typeinfer_rc_strategy105_correctness : typeinfer_rc_strategy105.

End typeinfer_rc_Strategy_Correct.
