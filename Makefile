COQC=coqc -Q . Peg

all:
	$(COQC) Nth.v
	$(COQC) BigstepInd.v
