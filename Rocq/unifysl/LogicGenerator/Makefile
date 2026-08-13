COQBIN=
-include ../CONFIGURE
unifysl_dir := ..
coq_exe		:= $(COQBIN)coqc
coq_flags	:= -R $(unifysl_dir) Logic
src         := Generate.v
src2        := GenerateBeta.v
dst         := Generated.v
dst2        := Generated2.v

.PHONY: all clean

all: $(dst)

Config.vo: Config.v
	@$(coq_exe) $(coq_flags) Config.v

GeneratedGenerate.v: Config.vo
	@$(coq_exe) $(coq_flags) GenerateGenerate.v > GeneratedGenerate.v

GeneratedGenerate.vo: GeneratedGenerate.v
	@$(coq_exe) $(coq_flags) GeneratedGenerate.v

$(dst): $(src) Config.vo GeneratedGenerate.vo
	@$(coq_exe) $(coq_flags) $(src) > $@

$(dst2): $(src) Config.vo GeneratedGenerate.vo
	@$(coq_exe) $(coq_flags) $(src2) > $@

clean:
	@rm -rf *.vo *.glob .*.aux $(dst) 2>/dev/null
