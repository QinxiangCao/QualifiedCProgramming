# FME / GE over GMP

## File layout

```text
QCP_examples/Applications_human/fme_ge_gmp/
  gmp/                         GMP C cases, headers, and strategies
  fme/                         FME C case, header, and strategies
  ge/                          GE C cases, header, and strategies

Rocq/examples/Applications_human/fme_ge_gmp/
  Makefile                     scoped generation and compilation entry point
  gmp/                         GMP libraries and generated case files
  fme/                         FME library and generated case files
  ge/                          GE libraries and generated case files
```

For each C case, QCP generates:

```text
<case>_goal.v
<case>_proof_auto.v
<case>_proof_manual.v
<case>_goal_check.v
```

Only proof bodies in `<case>_proof_manual.v` are filled after generation.

## Makefile commands

Run commands from the formal directory:

```sh
cd Rocq/examples/Applications_human/fme_ge_gmp

# Generate one case.
make qcp-case-gmp-mpz_add
make qcp-case-fme-fme_gmp
make qcp-case-ge-mod_norm_gmp

# Compile one case and its prerequisites.
make -j8 case-gmp-mpz_add
make -j8 case-fme-fme_gmp
make -j8 case-ge-mod_norm_gmp

# Generate or compile a layer.
make -j8 generate-gmp
make -j8 generate-fme
make -j8 generate-ge
make -j8 gmp-artifacts
make -j8 fme-artifacts
make -j8 ge-artifacts

# Compile all currently generated files.
make -j8 all
```
