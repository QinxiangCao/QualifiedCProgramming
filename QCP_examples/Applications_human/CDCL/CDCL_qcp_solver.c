/* Generation group: solver. Native builds use CDCL_qcp.c. */
#define QCP_SPLIT_UNIT 1
#define QCP_SPLIT_qcpsat_fill_ints 1
#define QCP_SPLIT_clause_resolution 1
#define QCP_SPLIT_clause_learning 1
#define QCP_SPLIT_conflict_analysis 1
#define QCP_SPLIT_decide 1
#define QCP_SPLIT_cdcl_solver 1
#include "CDCL_qcp.c"
