
float float_identity(float x)
/*@ Require emp
    Ensure __return == x && emp
  */
{
  return x;
}

float float_one_from_int()
/*@ Require emp
    Ensure __return == fp32(1.0) && emp */
{
  return 1;
}

float int_to_float(int x)
/*@ Require emp && x >= 0 && x <= 16777216
    Ensure __return == Z_to_fp32(x) && emp
  */
{
  return x;
}

float float_one()
/*@ Require emp
    Ensure __return == fp32(1.0) && emp */
{
  return 1.0f;
}

double double_identity(double x)
/*@ Require emp
    Ensure __return == x && emp
  */
{
  return x;
}

float float_literals()
/*@ Require emp
    Ensure emp
  */
{
  float f;
  f = 0.0f;
  f = -0.0f;
  f = 1.0f;
  f = 1e-3f;
  f = 1.5e+2f;
  f = .5f;
  f = 2E+1F;
  return f;
}

double double_literals()
/*@ Require emp
    Ensure emp
  */
{
  double d;
  d = 0.0;
  d = -0.0;
  d = 1.0;
  d = 1e-3;
  d = 1.5e+2;
  d = .5;
  d = 2E+1;
  return d;
}

float float_literal_addition()
/*@ Require emp
    Ensure emp
  */
{
  float f;
  f = 1.0f + 2.0f;
  f = 1e-3f + 1.5e+2f;
  f = .5f + 2E+1F;
  return f;
}

double double_literal_addition()
/*@ Require emp
    Ensure emp
  */
{
  double d;
  d = 1.0 + 2.0;
  d = 1e-3 + 1.5e+2;
  d = .5 + 2E+1;
  return d;
}

float float_add_literal(float x)
/*@ Require emp && fp32_isFinite(x) && x < FLT_MAX - fp32(1.0)
    Ensure __return == fp32_add(x, fp32(1.0)) && emp
  */
{
  return x + 1.0f;
}

float float_add_int_literal(float x)
/*@ Require emp && fp32_isFinite(x) && x < FLT_MAX - fp32(1.0)
    Ensure __return == fp32_add(x, fp32(1.0)) && emp
  */
{
  return x + 1;
}

double double_add_literal(double x)
/*@ Require emp && fp64_isFinite(x) && x < DBL_MAX - fp64(1.0)
    Ensure __return == fp64_add(x, fp64(1.0)) && emp
  */
{
  return x + 1.0;
}

float float_literal_arithmetic()
/*@ Require emp
    Ensure emp
  */
{
  float f;
  f = 1.2f * 3.4f;
  f = 4.5f / 0.2f;
  f = (1.0f + 2.0f) * (3.0f - 4.0f) / 5.0f;
  return f;
}

double double_literal_arithmetic()
/*@ Require emp
    Ensure emp
  */
{
  double d;
  d = 1.2 * 3.4;
  d = 4.5 / 0.2;
  d = (1.0 + 2.0) * (3.0 - 4.0) / 5.0;
  return d;
}

float float_neg(float x)
/*@ Require emp && fp32_isFinite(x)
    Ensure __return == fp32_neg(x) && emp
  */
{
  return -x;
}

double double_neg(double x)
/*@ Require emp && fp64_isFinite(x)
    Ensure __return == fp64_neg(x) && emp
  */
{
  return -x;
}

float float_sub(float x, float y)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(y) &&
              fp32_isFinite(fp32_sub(x, y))
    Ensure __return == fp32_sub(x, y) && emp
  */
{
  return x - y;
}

double double_sub(double x, double y)
/*@ Require emp && fp64_isFinite(x) && fp64_isFinite(y) &&
              fp64_isFinite(fp64_sub(x, y))
    Ensure __return == fp64_sub(x, y) && emp
  */
{
  return x - y;
}

float float_mul(float x, float y)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(y) &&
              fp32_isFinite(fp32_mul(x, y))
    Ensure __return == fp32_mul(x, y) && emp
  */
{
  return x * y;
}

double double_mul(double x, double y)
/*@ Require emp && fp64_isFinite(x) && fp64_isFinite(y) &&
              fp64_isFinite(fp64_mul(x, y))
    Ensure __return == fp64_mul(x, y) && emp
  */
{
  return x * y;
}

float float_div(float x, float y)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(y) &&
              fp32_ne(y, fp32(0.0)) &&
              fp32_isFinite(fp32_div(x, y))
    Ensure __return == fp32_div(x, y) && emp
  */
{
  return x / y;
}

double double_div(double x, double y)
/*@ Require emp && fp64_isFinite(x) && fp64_isFinite(y) &&
              fp64_ne(y, fp64(0.0)) &&
              fp64_isFinite(fp64_div(x, y))
    Ensure __return == fp64_div(x, y) && emp
  */
{
  return x / y;
}

float float_mixed_expression(float x, float y)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(y) &&
              fp32_isFinite(fp32_mul(fp32_add(x, y), fp32_sub(x, y)))
    Ensure __return == fp32_mul(fp32_add(x, y), fp32_sub(x, y)) && emp
  */
{
  return (x + y) * (x - y);
}

double double_mixed_expression(double x, double y)
/*@ Require emp && fp64_isFinite(x) && fp64_isFinite(y) &&
            fp64_isFinite(fp64_add(x, y)) &&
            fp64_isFinite(fp64_sub(x, y)) &&
            fp64_isFinite(fp64_mul(fp64_add(x, y), fp64_sub(x, y)))
    Ensure __return == fp64_mul(fp64_add(x, y), fp64_sub(x, y)) && emp
  */
{
  return (x + y) * (x - y);
}

float float_add_sub_chain(float x, float y, float z)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(y) && fp32_isFinite(z) &&
              fp32_isFinite(fp32_add(x, y)) &&
              fp32_isFinite(fp32_sub(fp32_add(x, y), z))
    Ensure __return == fp32_sub(fp32_add(x, y), z) && emp
  */
{
  return (x + y) - z;
}

double double_mul_add_chain(double x, double y, double z)
/*@ Require emp && fp64_isFinite(x) && fp64_isFinite(y) && fp64_isFinite(z) &&
              fp64_isFinite(fp64_mul(x, y)) &&
              fp64_isFinite(fp64_add(fp64_mul(x, y), z))
    Ensure __return == fp64_add(fp64_mul(x, y), z) && emp
  */
{
  return x * y + z;
}

float float_literal_mul_exact()
/*@ Require emp
    Ensure __return == fp32(3.0) && emp
  */
{
  return 1.5f * 2.0f;
}

double double_literal_div_exact()
/*@ Require emp
    Ensure __return == fp64(3.0) && emp
  */
{
  return 7.5 / 2.5;
}

int float_sub_self_zero_branch(float x)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(fp32_sub(x, x))
    Ensure __return == 1 && emp
  */
{
  if (x - x == 0.0f) {
    return 1;
  }
  return 0;
}

int double_div_self_one_branch(double x)
/*@ Require emp && fp64_isFinite(x) && fp64_ne(x, fp64(0.0)) &&
              fp64_isFinite(fp64_div(x, x))
    Ensure __return == 1 && emp
  */
{
  if (x / x == 1.0) {
    return 1;
  }
  return 0;
}

int float_neg_involution_branch(float x)
/*@ Require emp && fp32_isFinite(x) &&
              fp32_isFinite(fp32_neg(x)) &&
              fp32_isFinite(fp32_neg(fp32_neg(x)))
    Ensure __return == 1 && emp
  */
{
  if (-(-x) == x) {
    return 1;
  }
  return 0;
}

int float_lt_branch(float x, float y)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(y)
    Ensure fp32_lt(x, y) && __return == 1 && emp ||
           fp32_ge(x, y) && __return == 0 && emp
  */
{
  if (x < y) {
    return 1;
  }
  return 0;
}

int float_ne_branch(float x, float y)
/*@ Require emp && fp32_isFinite(x) && fp32_isFinite(y)
    Ensure fp32_ne(x, y) && __return == 1 && emp ||
           fp32_eq(x, y) && __return == 0 && emp
  */
{
  if (x != y) {
    return 1;
  }
  return 0;
}

int double_eq_branch(double x, double y)
/*@ Require emp && fp64_isFinite(x) && fp64_isFinite(y)
    Ensure fp64_eq(x, y) && __return == 1 && emp ||
           fp64_ne(x, y) && __return == 0 && emp
  */
{
  if (x == y) {
    return 1;
  }
  return 0;
}

int double_ge_branch(double x, double y)
/*@ Require emp && fp64_isFinite(x) && fp64_isFinite(y)
    Ensure fp64_ge(x, y) && __return == 1 && emp ||
           fp64_lt(x, y) && __return == 0 && emp
  */
{
  if (x >= y) {
    return 1;
  }
  return 0;
}
