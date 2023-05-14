include ./Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

# OUT_DIR   = out
# CACHE_DIR = cache
# ROOTS     = Main.fst

# FSTAR_FLAGS = $(OTHERFLAGS) --cmi --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) \
#   --cache_checked_modules --already_cached 'Prims FStar'

# FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

# .PHONY: all main clean

# all:
# 	rm -f .depend && $(MAKE) .depend
# 	+$(MAKE) main

# # 1. Extract .ml files
# # - generate the F* dependency graph of $(ROOTS) with `fstar --dep full`
# # - verify every F* file in parallel to generate .checked files
# # - extract each .checked file into a .ml file in parallel
# .depend:
# 	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

# include .depend

# $(CACHE_DIR)/%.checked: | .depend
# 	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
# 	touch $@

# # 2. Compile all .ml files to .cmx and link them to get an executable
# $(OUT_DIR):
# 	mkdir -p $@

# $(OUT_DIR)/%.ml: | .depend
# 	$(FSTAR) --codegen OCaml \
# 	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
# 	  $(notdir $(subst .checked,,$<)) && \
# 	touch $@

# %.cmx:
# 	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

# $(OUT_DIR)/main.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
# 	$(OCAMLOPT) -I $(OUT_DIR) -o $(OUT_DIR)/main.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

# main: $(OUT_DIR)/main.exe
# 	$(OUT_DIR)/main.exe

# clean:
# 	rm -rf $(OUT_DIR) $(CACHE_DIR)






cnf: out ./Cnf.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Cnf' ./Cnf.fst --record_hints 
	$(OCAMLOPT) out/Cnf.ml -o cnf.exe
	./cnf.exe

utils: out ./Utils.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Utils' ./Utils.fst --record_hints
	$(OCAMLOPT) out/Utils.ml -o utils.exe
	./utils.exe

formula: out ./FormulaT.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'FormulaT' ./FormulaT.fst --record_hints
	$(OCAMLOPT) out/FormulaT.ml -o formula.exe
	./formula.exe

cnfformula: out ./CnfFormula.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'CnfFormula' ./CnfFormula.fst --record_hints
	$(OCAMLOPT) out/CnfFormula.ml -o cnfformula.exe
	./cnfformula.exe

tseitincore: out ./TseitinCore.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'TseitinCore' ./TseitinCore.fst --record_hints
	$(OCAMLOPT) out/TseitinCore.ml -o tseitincore.exe
	./tseitincore.exe

tseitin: out ./Tseitin.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Tseitin' ./Tseitin.fst --record_hints
	$(OCAMLOPT) out/Tseitin.ml -o tseitin.exe
	./tseitin.exe

tseitinproofs: out ./TseitinProofs.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'TseitinProofs' ./TseitinProofs.fst --record_hints
	$(OCAMLOPT) out/TseitinProofs.ml -o tseitinproofs.exe
	./tseitinproofs.exe

main: out ./Main.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Main' ./Main.fst --record_hints
	$(OCAMLOPT) out/Main.ml -o main.exe
	./main.exe