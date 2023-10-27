COQC=coqc -Q . Peg

all:
	$(COQC) Strong.v
	$(COQC) PEG.v
	$(COQC) Smallstep.v
