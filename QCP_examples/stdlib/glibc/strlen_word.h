#ifndef QCP_STRLEN_WORD_H
#define QCP_STRLEN_WORD_H

/* Object-bounded implementation; see strlen_word_spec.h for the two contracts. */
unsigned long long strlen_word(const unsigned char *s);
unsigned long long sl_load_word(const unsigned long long *p);
unsigned long long sl_first_zero(unsigned long long w, unsigned long long start);

#endif
