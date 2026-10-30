/*
Contiguous 2D integer matrix version of max_fill.
The matrix is stored as one flat block in row-major order.
*/

#include "array2_def.h"

int max_fill_array2(int* grid, int grid_rows, int grid_cols, int capacity)
/*@ With rows
    Require 0 <= grid_rows && grid_rows <= 100 &&
            0 <= grid_cols && grid_cols <= 100 &&
            1 <= capacity && capacity <= 10 &&
            Zlength(rows) == grid_rows &&
            (forall (i: Z), (0 <= i && i < grid_rows) => (Zlength(rows[i]) == grid_cols)) &&
            (forall (i: Z) (j: Z), (0 <= i && i < grid_rows && 0 <= j && j < grid_cols) => (0 <= rows[i][j] && rows[i][j] <= 1)) &&
            IntArray2::full(grid, grid_rows, grid_cols, rows)
    Ensure IntArray2::full(grid, grid_rows, grid_cols, rows)
*/
{
    int out=0;
    /*@ Inv Assert
        0 <= i && i <= grid_rows@pre &&
        0 <= grid_rows@pre && grid_rows@pre <= 100 &&
        0 <= grid_cols@pre && grid_cols@pre <= 100 &&
        1 <= capacity@pre && capacity@pre <= 10 &&
        grid_rows == grid_rows@pre && grid_cols == grid_cols@pre &&
        grid == grid@pre &&
        capacity == capacity@pre &&
        Zlength(rows) == grid_rows@pre &&
        (forall (r: Z), (0 <= r && r < grid_rows@pre) => (Zlength(rows[r]) == grid_cols@pre)) &&
        (forall (r: Z) (c: Z), (0 <= r && r < grid_rows@pre && 0 <= c && c < grid_cols@pre) => (0 <= rows[r][c] && rows[r][c] <= 1)) &&
        0 <= out && out <= i * grid_cols@pre &&
        IntArray2::full(grid@pre, grid_rows@pre, grid_cols@pre, rows)
    */
    for (int i=0;i<grid_rows;i++)
    {
        int sum=0;
        /*@ Inv Assert
            0 <= j && j <= grid_cols@pre &&
            0 <= grid_rows@pre && grid_rows@pre <= 100 &&
            0 <= grid_cols@pre && grid_cols@pre <= 100 &&
            1 <= capacity@pre && capacity@pre <= 10 &&
            grid_rows == grid_rows@pre && grid_cols == grid_cols@pre &&
            grid == grid@pre &&
            capacity == capacity@pre &&
            Zlength(rows) == grid_rows@pre &&
            (forall (r: Z), (0 <= r && r < grid_rows@pre) => (Zlength(rows[r]) == grid_cols@pre)) &&
            (forall (r: Z) (c: Z), (0 <= r && r < grid_rows@pre && 0 <= c && c < grid_cols@pre) => (0 <= rows[r][c] && rows[r][c] <= 1)) &&
            Zlength(Znth(i, rows, nil)) == grid_cols@pre &&
            0 <= i && i < grid_rows@pre &&
            0 <= sum && sum <= j &&
            0 <= out && out <= i * grid_cols@pre &&
            IntArray2::full(grid@pre, grid_rows@pre, grid_cols@pre, rows)
        */
        for (int j=0;j<grid_cols;j++)
            sum+=*(grid + i * grid_cols + j);
        if (sum>0)  out+=(sum-1)/capacity+1;
    }
    return out;
}
