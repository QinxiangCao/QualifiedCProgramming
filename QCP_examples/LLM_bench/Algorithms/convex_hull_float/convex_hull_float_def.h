struct PointF {
  float x;
  float y;
};

/*@ Extern Coq Record PointF {
      pointf_x : fp32;
      pointf_y : fp32;
    } */

/*@ Extern Coq (pointf_mk : fp32 -> fp32 -> PointF)
               (fp32_of_bits : Z -> fp32)
               (bits_of_fp32 : fp32 -> Z)
               (pointf_get_x : PointF -> fp32)
               (pointf_get_y : PointF -> fp32)
               (default_pointf : PointF)
               (store_pointf : Z -> PointF -> Assertion)
               (store_pointf_x_bits : Z -> Z -> Assertion)
               (store_pointf_y_bits : Z -> Z -> Assertion)
               (undef_pointf : Z -> Assertion)
               (pointf_cmp_xy : PointF -> PointF -> Z)
               (pointf_cross : PointF -> PointF -> PointF -> fp32)
               (pointf_cross_finite : PointF -> PointF -> PointF -> Prop)
               (pointf_swap : list PointF -> Z -> Z -> list PointF)
               (PointFArray::full : Z -> Z -> list PointF -> Assertion)
               (PointFArray::missing_i : Z -> Z -> Z -> Z -> list PointF -> Assertion)
               (PointFArray::seg : Z -> Z -> Z -> list PointF -> Assertion)
               (PointFArray::undef_full : Z -> Z -> Assertion)
               (PointFArray::undef_seg : Z -> Z -> Z -> Assertion)
               (Znth : {A} -> Z -> list A -> A -> A)
               (replace_Znth : {A} -> Z -> A -> list A -> list A)
 */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.convex_hull_float.convex_hull_float_lib */
/*@ include strategies "pointf_array.strategies" */
