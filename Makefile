COQC=coqc -Q . Peg

all:
	$(COQC) Strong.v
	$(COQC) Suffix.v
	$(COQC) Pigeonhole.v
	$(COQC) PEG.v
	$(COQC) Smallstep.v
