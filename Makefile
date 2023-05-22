COQC=coqc -Q . Peg

all:
	$(COQC) Smallstep.v
	$(COQC) Bigstep.v
	$(COQC) Nth.v
	$(COQC) BigstepInd.v
	$(COQC) WellFormed.v
	$(COQC) WellFormed2.v
