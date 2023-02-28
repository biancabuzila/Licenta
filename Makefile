include ./Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

all: cnfformula multi strings

cnfformula: out ./CnfFormula.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'CnfFormula' ./CnfFormula.fst --record_hints
	$(OCAMLOPT) out/CnfFormula.ml -o cnfformula.exe
	./cnfformula.exe

multi:
	$(MAKE) -C multifile

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
