COQMAKEFILE=CoqMakefile

.PHONY: all
all: $(COQMAKEFILE)
	@$(MAKE) -f $< $@

$(COQMAKEFILE): _CoqProject
	coq_makefile -f $^ -o $@

_CoqProject: ;

%: $(COQMAKEFILE)
	@$(MAKE) -f $< $@
