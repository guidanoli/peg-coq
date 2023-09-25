COQC=coqc -Q . Peg

all:
	$(COQC) PEG.v
	$(COQC) Smallstep.v
