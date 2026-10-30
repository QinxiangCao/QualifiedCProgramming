#define NEG (-(1LL << 60))
void test()
/*@ Require emp Ensure emp */
{
  long long x = NEG;
}