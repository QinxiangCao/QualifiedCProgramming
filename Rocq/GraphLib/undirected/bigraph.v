Require Import GraphLib.graph_basic.

Class BiGraph (G V E: Type) (g: G) {pg: Graph G V E} {undirected: UndirectedGraph G V E g} := {
  left_out: G -> V -> Prop;
  right_out: G -> V -> Prop;
  bi_consist: forall x, vvalid g x -> left_out g x \/ right_out g x;
  only_two_edges: forall x y e, step_aux g e x y -> 
    (left_out g x /\ right_out g y) \/ (right_out g x /\ left_out g y);
}.
