.PHONY: all run lake


OUT_DIR = ../../client/public
LEAN_SYSROOT ?= /home/alex/Projects/lean4/build/release/stage1
LEAN_LIBDIR := $(LEAN_SYSROOT)/lib/lean

all: $(OUT_DIR)/server.js

# Link C binary against Lake package dynamic library

lake:
	lake --dir=lib build

$(OUT_DIR):
	mkdir -p $@

ifneq ($(OS),Windows_NT)
# Add shared library paths to loader path (no Windows equivalent)
LINK_FLAGS=-Wl,-rpath,$(LEAN_LIBDIR) -Wl,-rpath,$(PWD)/lib/build/lib
endif

$(OUT_DIR)/server.js: main.c lake | $(OUT_DIR)
# Add library paths for Lake package and for Lean itself
	emcc -o $@ $< -I $(LEAN_SYSROOT)/include -L $(LEAN_LIBDIR) lib/build/ir/RFFI.c -lInit -lLean -lleancpp -lleanrt $(LINK_FLAGS) \
	  -sFORCE_FILESYSTEM -lnodefs.js -s EXIT_RUNTIME=0 -s MAIN_MODULE=1 -s LINKABLE=1 -s EXPORT_ALL=1 -s ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto



# Alternatively, we can copy all shared lib dependencies to the current directory
# in order to avoid path set up and obtain a more portable executable

# ifeq ($(OS),Windows_NT)
# SHLIB_PREFIX :=
# SHLIB_EXT := dll
# LEAN_SHLIB := $(LEAN_SYSROOT)/bin/libleanshared.$(SHLIB_EXT)
# else
# SHLIB_PREFIX := lib
# # Add current directory to loader path (default on Windows)
# ifeq ($(shell uname -s),Darwin)
# LINK_FLAGS_LOCAL := -Wl,-rpath,@executable_path
# SHLIB_EXT := dylib
# else
# LINK_FLAGS_LOCAL := -Wl,-rpath,'$${ORIGIN}'
# SHLIB_EXT := so
# endif
# LEAN_SHLIB=$(LEAN_LIBDIR)/libleanshared.$(SHLIB_EXT)
# endif

# $(OUT_DIR)/main-local: main.c lake | $(OUT_DIR)
# 	cp -f $(LEAN_SHLIB) lib/build/lib/$(SHLIB_PREFIX)RFFI.$(SHLIB_EXT) $(OUT_DIR)
# 	cc -o $@ $< -I $(LEAN_SYSROOT)/include -L $(OUT_DIR) -lRFFI -lleanshared $(LINK_FLAGS_LOCAL)

# run-local: $(OUT_DIR)/main-local
# 	$(OUT_DIR)/main-local
