From SumLib Require Import Sum.

(** * 图相关指标集 *)

(** ** 注册的 Instance *)

(*
  未来可能加入的 GraphLib 相关 instance。

  Instance 是：

    finite_graph_vertices

  指标集是：

    fun v : V => vvalid g v

  enum:

    nodup vertex_eq_dec
      (filter (fun v => if prop_dec (vvalid g v) then true else false)
              (listV g))

  Instance 是：

    finite_graph_vertices'

  指标集是：

    fun v : V => vvalid g v /\ P v

  enum:

    nodup vertex_eq_dec
      (filter
         (fun v => if prop_dec (vvalid g v /\ P v) then true else false)
         (listV g))

  Instance 是：

    finite_graph_out_neighbors

  指标集是：

    fun v : V => exists e : E, step_aux g e u v

  enum:

    nodup vertex_eq_dec
      (filter
         (fun v =>
            if prop_dec (exists e : E, step_aux g e u v)
            then true else false)
         (listV g))

  Instance 是：

    finite_graph_out_neighbors'

  指标集是：

    fun v : V => (exists e : E, step_aux g e u v) /\ P v

  enum:

    nodup vertex_eq_dec
      (filter
         (fun v =>
            if prop_dec ((exists e : E, step_aux g e u v) /\ P v)
            then true else false)
         (listV g))
*)

(** ** 内部辅助引理 *)

(** ** 公开求和性质 *)
