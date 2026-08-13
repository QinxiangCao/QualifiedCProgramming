#include "array3_def.h"

struct GraphBox {
    int graph[2][3][4];
};

void touch_graph_one_read(struct GraphBox *box)
/*@ With cubes
    Require Zlength(cubes) == 2 &&
            IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
    Ensure IntArray3::full(field_addr(box, GraphBox, graph), 2, 3, 4, cubes)
*/
{
    int value = box->graph[0][0][0];
}
