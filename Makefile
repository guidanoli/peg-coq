COQC=coqc -Q . Peg

all:
	$(COQC) Strong.v
	$(COQC) Suffix.v
	$(COQC) PEG.v
	$(COQC) Smallstep.v
