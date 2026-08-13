/* QCP V2.0.5 symexec does not preserve the preprocessor conditional stack
   across an #include boundary, so a nested #include inside an #ifndef guard is
   reported as an unterminated #if. Keep includes above the guard. */
#include "CDCL_qcp_compat.h"

#ifndef QCPSAT_QCP_H
#define QCPSAT_QCP_H 1

/* The struct tags are named (rather than anonymous) so that the generated Coq
   spells each field access `p # "var_data" ->ₛ "value"` instead of
   `p # "anonymous struct 1" ->ₛ "value"`.  Tagging changes no C semantics: the
   tag lives in its own namespace and the typedef name is unchanged. */
typedef struct var_data{
    int *value;                    //存储变量当前的赋值 -1表示未赋值
    int *ancient;                  //记录变量的前继子句，决策变量和未赋值变量为-1
    int *dl;                       //记录变量的决策等级，未赋值变量决策等级为-1
} var_data;

typedef struct clause_data{
    int* state;                    //clause的状态，0：sat，1：unsat，2：unit，-n：others(n个未赋值变量)
    int* lit_state;                //赋值为true的literal数量
    int* unassign_num;             //未赋值的literal数量
    int** value;                   //clause包含的literal，0表示不包含，1表示包含x，-1表示包含非x
} clause_data;

typedef struct sat_data{
    int v_size;
    int cl_size;
    int cl_maxsize;
    int cur_dl;
    var_data *v_data;
    clause_data* cl_data;
}   sat_data;

int* clause_resolution(int *wi, int *wj, sat_data* s);

int* clause_learning(int wi, sat_data* s);

int conflict_analysis(int* clause, sat_data* s);

int bcp(sat_data *s);   //返回值>=0为冲突子句的编号，-1为正常运行

void backtrack(int back_dl, sat_data *s);

int decide(sat_data* s);  //返回新决策变量的编号，-1表示没有新的变量可以决策

int cdcl_solver(sat_data* s);

void qcpsat_fill_ints(int *a, int n, int value);

sat_data* initCDCL_TEST(int n, int m);

void free_vdata(var_data *v_data);

void freeCDCL(sat_data* s);
#endif
