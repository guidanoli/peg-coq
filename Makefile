COQC=coqc -Q . Peg
RM=rm -f

.PHONY: all
all:
	$(COQC) Strong.v
	$(COQC) Suffix.v
	$(COQC) Pigeonhole.v
	$(COQC) PEG.v

.PHONY:
clean:
	$(RM) *.glob *.vo *.vok *.vos
