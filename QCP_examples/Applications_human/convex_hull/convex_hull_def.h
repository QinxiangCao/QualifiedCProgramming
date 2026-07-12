struct Point {
    int x;
    int y;
};

/*@ Extern Coq Record Point {
  x : Z;
  y : Z;
} */

/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (rev : {A} -> list A -> list A)
               (Zlength: {A} -> list A -> Z)
*/

/*@ Extern Coq (point_mk : Z -> Z -> Point)
               (point_x : Point -> Z)
               (point_y : Point -> Z)
               (store_point : Z -> Point -> Assertion)
               (undef_point : Z -> Assertion)
               (point_cmp_xy : Point -> Point -> Z)
               (point_cmp_polar : Point -> Point -> Point -> Z)
               (point_cross : Point -> Point -> Point -> Z)
               (point_dot : Point -> Point -> Point -> Z)
               (point_swap : list Point -> Z -> Z -> list Point)
               (sublist : {A} -> Z -> Z -> list A -> list A)
               (PointArray::full : Z -> Z -> list Point -> Assertion)
               (PointArray::missing_i: Z -> Z -> Z -> Z -> list Point -> Assertion)
               (PointArray::seg: Z -> Z -> Z -> list Point -> Assertion)
               (PointArray::undef_full : Z -> Z -> Assertion)
               (PointArray::undef_seg: Z -> Z -> Z -> Assertion)
               (PointArray::undef_missing_i: Z -> Z -> Z -> Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
*/

/*@ Import Coq Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib */
/*@ include strategies "point_array.strategies" */
