/* See CDCL_qcp.h: includes stay above the guard for QCP V2.0.5 symexec. */
#include "CDCL_qcp_def.h"

#ifndef QCPSAT_QCP_COMPAT_H
#define QCPSAT_QCP_COMPAT_H

typedef int bool;
#define true 1
#define false 0

#define QCPSAT_FATAL_BCP_NO_VARIABLE 1
#define QCPSAT_FATAL_BCP_UNIT_COUNT 2
#define QCPSAT_FATAL_BCP_UNSAT_CLAUSE 3

int *qcpsat_alloc_row(int n)
/*@ Require 0 < n && n < INT_MAX && emp
    Ensure __return != 0 && IntArray::undef_full(__return, n)
*/
;

void qcpsat_free_row(int *row, int n)
/*@ With l
    Require 0 <= n && n < INT_MAX && IntArray::full(row, n, l)
    Ensure emp
*/
;

void qcpsat_fatal(int site)
/*@ Require 0 == 1 && emp
    Ensure emp
*/
;

#endif
