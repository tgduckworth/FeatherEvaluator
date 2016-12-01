all:
	coqc AdditionalTactics.v Atom.v Metatheory.v FJ_Definitions.v FJ_Facts.v FJ_Properties.v FJ_Example.v	

clean:
	rm *.vo *.glob
