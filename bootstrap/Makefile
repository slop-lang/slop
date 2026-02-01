# Bootstrap Makefile for SLOP Native Toolchain
#
# This Makefile builds the SLOP compiler tools from pre-generated C files.
# No existing SLOP installation is required - just a C compiler.
#
# Structure:
#   runtime/     - Shared runtime header
#   parser/      - All parser .h and .c files
#   checker/     - All checker .h and .c files
#   transpiler/  - Transpiler module .h and .c files (used by compiler)
#   compiler/    - All compiler .h and .c files (merged checker + transpiler)
#   tester/      - All tester .h and .c files
#
# Usage:
#   make           - Build all tools
#   make parser    - Build only the parser
#   make clean     - Remove built binaries
#   make release   - Build optimized release binaries

# Configuration
CC ?= cc
CFLAGS ?= -O2 -Wall -Wno-unused-function -Wno-unused-variable -Wno-return-type -Wno-pointer-sign
CFLAGS += -DSLOP_DEBUG

# Directories
BIN_DIR = bin
RUNTIME_DIR = runtime

# Platform detection
UNAME_S := $(shell uname -s)
UNAME_M := $(shell uname -m)

ifeq ($(UNAME_S),Linux)
    PLATFORM = linux
endif
ifeq ($(UNAME_S),Darwin)
    PLATFORM = macos
endif

ifeq ($(UNAME_M),x86_64)
    ARCH = x64
endif
ifeq ($(UNAME_M),aarch64)
    ARCH = arm64
endif
ifeq ($(UNAME_M),arm64)
    ARCH = arm64
endif

# Source files for each tool
PARSER_SRCS := $(wildcard parser/*.c)
CHECKER_SRCS := $(wildcard checker/*.c)
TRANSPILER_SRCS := $(wildcard transpiler/*.c)
COMPILER_SRCS := $(wildcard compiler/*.c)
TESTER_SRCS := $(wildcard tester/*.c)

# Targets
.PHONY: all clean parser checker compiler tester release info

all: parser checker compiler tester

info:
	@echo "Platform: $(PLATFORM)-$(ARCH)"
	@echo "CC: $(CC)"
	@echo "CFLAGS: $(CFLAGS)"
	@echo ""
	@echo "Parser sources: $(PARSER_SRCS)"
	@echo "Checker sources: $(CHECKER_SRCS)"
	@echo "Transpiler sources: $(TRANSPILER_SRCS)"
	@echo "Compiler sources: $(COMPILER_SRCS)"
	@echo "Tester sources: $(TESTER_SRCS)"

$(BIN_DIR):
	mkdir -p $(BIN_DIR)

parser: $(BIN_DIR)
	@echo "Building parser..."
	$(CC) $(CFLAGS) -I$(RUNTIME_DIR) -Iparser -o $(BIN_DIR)/slop-parser $(PARSER_SRCS)
	@echo "  -> $(BIN_DIR)/slop-parser"

checker: $(BIN_DIR)
	@echo "Building checker..."
	$(CC) $(CFLAGS) -I$(RUNTIME_DIR) -Ichecker -o $(BIN_DIR)/slop-checker $(CHECKER_SRCS)
	@echo "  -> $(BIN_DIR)/slop-checker"

compiler: $(BIN_DIR)
	@echo "Building compiler..."
	$(CC) $(CFLAGS) -I$(RUNTIME_DIR) -Icompiler -o $(BIN_DIR)/slop-compiler $(COMPILER_SRCS)
	@echo "  -> $(BIN_DIR)/slop-compiler"

tester: $(BIN_DIR)
	@echo "Building tester..."
	$(CC) $(CFLAGS) -I$(RUNTIME_DIR) -Itester -o $(BIN_DIR)/slop-tester $(TESTER_SRCS)
	@echo "  -> $(BIN_DIR)/slop-tester"

clean:
	rm -rf $(BIN_DIR)

# Release target - builds optimized binaries without debug
release: CFLAGS = -O3 -Wall -Wno-unused-function -Wno-unused-variable -Wno-return-type -Wno-pointer-sign -DNDEBUG
release: clean all
	@echo ""
	@echo "Release binaries built in $(BIN_DIR)/"
	@ls -la $(BIN_DIR)/
