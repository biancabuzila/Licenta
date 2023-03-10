include ./Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

OUT_DIR   = out
CACHE_DIR = cache
ROOTS     = Main.fst

FSTAR_FLAGS = $(OTHERFLAGS) --cmi --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) \
  --cache_checked_modules --already_cached 'Prims FStar'

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

.PHONY: all main clean

all:
	rm -f .depend && $(MAKE) .depend
	+$(MAKE) main

# 1. Extract .ml files
# - generate the F* dependency graph of $(ROOTS) with `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .ml file in parallel
.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

# 2. Compile all .ml files to .cmx and link them to get an executable
$(OUT_DIR):
	mkdir -p $@

$(OUT_DIR)/%.ml: | .depend
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

%.cmx:
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/main.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
	$(OCAMLOPT) -I $(OUT_DIR) -o $(OUT_DIR)/main.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

main: $(OUT_DIR)/main.exe
	$(OUT_DIR)/main.exe

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR)
