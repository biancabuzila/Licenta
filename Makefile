include ./Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

all: cnfformula utils formula main multi strings

cnfformula: out ./CnfFormula.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'CnfFormula' ./CnfFormula.fst --record_hints
	$(OCAMLOPT) out/CnfFormula.ml -o cnfformula.exe
	./cnfformula.exe

utils: out ./Utils.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Utils' ./Utils.fst --record_hints
	$(OCAMLOPT) out/Utils.ml -o utils.exe
	./utils.exe

formula: out ./FormulaT.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'FormulaT' ./FormulaT.fst --record_hints
	$(OCAMLOPT) out/FormulaT.ml -o formula.exe
	./formula.exe

main: out ./Main.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Main' ./Main.fst --record_hints
	$(OCAMLOPT) out/Main.ml -o main.exe
	./main.exe

multi:
	$(MAKE) -C multifile

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
