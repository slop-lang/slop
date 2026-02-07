# SLOP Project Makefile
#
# Usage:
#   make help          Show available targets
#   make build-native  Build the native toolchain
#   make test          Run Python test suite
#   make test-native   Run native SLOP test suite

CC ?= cc
CFLAGS ?= -O2 -Wall -Wextra
DEBUG_CFLAGS ?= -g -DSLOP_DEBUG -Wall -Wextra
RUNTIME = runtime

.PHONY: help build-native test test-native test-all clean clean-native bootstrap bootstrap-update

help:
	@echo "SLOP Build System"
	@echo ""
	@echo "Targets:"
	@echo "  build-native       Build native toolchain (parser, checker, compiler, tester)"
	@echo "  test               Run Python test suite (uv run pytest)"
	@echo "  test-native        Run native SLOP test suite"
	@echo "  test-all           Run both test suites"
	@echo "  clean              Remove build artifacts"
	@echo "  clean-native       Remove native binaries only"
	@echo "  bootstrap          Build toolchain from bootstrap C files"
	@echo "  bootstrap-update   Regenerate bootstrap C files from SLOP source"
	@echo ""
	@echo "Native binaries are installed to bin/"

# Build the native toolchain
build-native:
	./scripts/build_native.sh

# Run Python test suite
test:
	uv run pytest

# Run native SLOP test suite
test-native:
	./scripts/run_native_tests.sh

# Run both test suites
test-all: test test-native

# Compile C directly
%.o: %.c
	$(CC) $(CFLAGS) -I$(RUNTIME) -c $< -o $@

%-debug.o: %.c
	$(CC) $(DEBUG_CFLAGS) -I$(RUNTIME) -c $< -o $@

# Remove build artifacts
clean:
	rm -f *.o *.c.filled build/*
	rm -rf __pycache__ .pytest_cache
	find . -name "*.pyc" -delete
	rm -f bin/slop-*

# Remove native binaries only
clean-native:
	rm -f bin/slop-*
	@echo "Native binaries cleaned"

# Build from bootstrap C files
bootstrap:
	cd bootstrap && make

# Regenerate bootstrap C files
bootstrap-update:
	./bootstrap/update_bootstrap.sh
