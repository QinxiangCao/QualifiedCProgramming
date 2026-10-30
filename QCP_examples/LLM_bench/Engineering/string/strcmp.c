#include "string.h"

int strcmp(char *s1, char *s2)
/*@ default */
{
  int i = 0;
  /*@ Inv Assert
      valid_string(str1) && valid_string(str2) &&
      string_length(str1) < INT_MAX && string_length(str2) < INT_MAX &&
      0 <= i && i <= string_length(str1) && i <= string_length(str2) &&
      s1 == s1@pre && s2 == s2@pre &&
      (forall (k: Z), (0 <= k && k < i) =>
        Znth(k, c_string(str1), 0) == Znth(k, c_string(str2), 0)) &&
      store_string(s1@pre, str1) * store_string(s2@pre, str2)
  */
  while (s1[i] != 0 && s1[i] == s2[i]) {
    i++;
  }
  return s1[i] - s2[i];
}

int strncmp(char *s1, char *s2, int n)
/*@ default */
{
  int i = 0;
  /*@ Inv Assert
      valid_string(str1) && valid_string(str2) &&
      0 <= n@pre && n@pre < INT_MAX &&
      string_length(str1) < INT_MAX && string_length(str2) < INT_MAX &&
      0 <= i && i <= n@pre &&
      i <= string_length(str1) && i <= string_length(str2) &&
      s1 == s1@pre && s2 == s2@pre && n == n@pre &&
      (forall (k: Z), (0 <= k && k < i) =>
        Znth(k, c_string(str1), 0) == Znth(k, c_string(str2), 0)) &&
      store_string(s1@pre, str1) * store_string(s2@pre, str2)
  */
  while (i < n && s1[i] != 0 && s1[i] == s2[i]) {
    i++;
  }
  if (i == n) {
    return 0;
  }
  return s1[i] - s2[i];
}
