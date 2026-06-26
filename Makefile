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

.PHONY: help install build-native selfhost check-sync test test-native test-all clean clean-native bootstrap bootstrap-update

help:
	@echo "SLOP Build System"
	@echo ""
	@echo "Targets:"
	@echo "  install            Build bootstrap toolchain and install it to bin/"
	@echo "  build-native       Rebuild native toolchain from SLOP source into bin/ (needs install first)"
	@echo "  selfhost           Cold-start + two-stage self-host rebuild (set SLOP_OPT=3 for release)"
	@echo "  check-sync         Verify committed bootstrap C matches current SLOP source"
	@echo "  test               Run Python test suite (uv run pytest)"
	@echo "  test-native        Run native SLOP test suite"
	@echo "  test-all           Run both test suites"
	@echo "  clean              Remove build artifacts"
	@echo "  clean-native       Remove native binaries only"
	@echo "  bootstrap          Build toolchain from bootstrap C files into bootstrap/bin/"
	@echo "  bootstrap-update   Regenerate bootstrap C files from SLOP source"
	@echo ""
	@echo "Fresh checkout: run 'make install' (cold-start from the C bootstrap),"
	@echo "then optionally 'make build-native' to self-host from current SLOP source."
	@echo "Native binaries are installed to bin/"

# Build the native toolchain
build-native:
	./scripts/build_native.sh

# Two-stage self-host rebuild from current SLOP source (cold-start + 2 passes).
selfhost:
	./scripts/selfhost.sh

# Fail if the committed bootstrap C has drifted from current SLOP source.
check-sync:
	./scripts/check_bootstrap_sync.sh

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

# Install the bootstrap-built binaries where the toolchain can find them.
# This is the cold-start step: bootstrap/bin/ -> bin/ (the CLI's search path).
install: bootstrap
	mkdir -p bin
	cp bootstrap/bin/slop-* bin/
	@echo "Installed native binaries to bin/"

# Regenerate bootstrap C files
bootstrap-update:
	./bootstrap/update_bootstrap.sh
