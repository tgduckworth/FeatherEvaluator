all:
	coqc AdditionalTactics.v Atom.v Metatheory.v FJ_Definitions.v FJ_Facts.v FJ_Properties.v FJ_Example.v FEV_Properties.v FEV_Example.v
	rm *.glob
	@echo "Compiling finished.."

clean:
	rm *.vo
