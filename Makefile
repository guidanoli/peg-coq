COQC=coqc -Q . Peg
RM=rm -f

.PHONY: all
all:
	$(COQC) Tactics.v
	$(COQC) Strong.v
	$(COQC) Suffix.v
	$(COQC) Pigeonhole.v
	$(COQC) Pattern.v
	$(COQC) Grammar.v
	$(COQC) Match.v
	$(COQC) Coherent.v
	$(COQC) Verifyrule.v
	$(COQC) Nullable.v
	$(COQC) Checkloops.v
	$(COQC) Verifygrammar.v

.PHONY:
clean:
	$(RM) *.glob *.vo *.vok *.vos
