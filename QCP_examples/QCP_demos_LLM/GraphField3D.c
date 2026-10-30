#include "array3_def.h"

struct GraphBox {
    int graph[2][3][4];
};

void touch_plane(int plane[][4], int rows_count, int cols_count)
/*@ With plane_rows
    Require rows_count == 3 && cols_count == 4 &&
            Zlength(plane_rows) == 3 &&
            IntArray2::full(plane, 3, 4, plane_rows)
    Ensure IntArray2::full(plane, 3, 4, plane_rows)
*/
{
    /*@ Inv Assert
        0 <= i && i <= 3 &&
        plane == plane@pre &&
        rows_count == rows_count@pre && cols_count == cols_count@pre &&
        rows_count@pre == 3 && cols_count@pre == 4 &&
        Zlength(plane_rows) == 3 &&
        IntArray2::full(plane@pre, 3, 4, plane_rows)
    */
    for (int i = 0; i < 3; ++i) {
        /*@ Inv Assert
            0 <= j && j <= 4 &&
            plane == plane@pre &&
            rows_count == rows_count@pre && cols_count == cols_count@pre &&
            rows_count@pre == 3 && cols_count@pre == 4 &&
            Zlength(plane_rows) == 3 &&
            0 <= i && i < 3 &&
            IntArray2::full(plane@pre, 3, 4, plane_rows)
        */
        for (int j = 0; j < 4; ++j) {
            int value = plane[i][j];
        }
    }
}

void touch_graph_direct(struct GraphBox *box)
/*@ With cubes
    Require Zlength(cubes) == 2 &&
            IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
    Ensure IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
*/
{
    /*@ Inv Assert
        0 <= i && i <= 2 &&
        box == box@pre &&
        Zlength(cubes) == 2 &&
        IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
    */
    for (int i = 0; i < 2; ++i) {
        /*@ Inv Assert
            0 <= j && j <= 3 &&
            0 <= i && i < 2 &&
            box == box@pre &&
            Zlength(cubes) == 2 &&
            IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
        */
        for (int j = 0; j < 3; ++j) {
            /*@ Inv Assert
                0 <= k && k <= 4 &&
                0 <= i && i < 2 &&
                0 <= j && j < 3 &&
                box == box@pre &&
                Zlength(cubes) == 2 &&
                IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
            */
            for (int k = 0; k < 4; ++k) {
                int value = box->graph[i][j][k];
            }
        }
    }
}

void touch_graph_plane(struct GraphBox *box, int layer)
/*@ With cubes
    Require 0 <= layer && layer < 2 &&
            Zlength(cubes) == 2 &&
            IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
    Ensure IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
*/
{
    int (*plane)[4];
    plane = box->graph[layer];
    touch_plane(plane, 3, 4);
}
