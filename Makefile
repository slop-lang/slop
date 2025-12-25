# SLOP Project Makefile
# 
# Usage:
#   make parse FILE=examples/rate-limiter.slop
#   make transpile FILE=examples/rate-limiter.slop
#   make build FILE=examples/rate-limiter.slop

PYTHON ?= python3
CC ?= cc
CFLAGS ?= -O2 -Wall -Wextra
DEBUG_CFLAGS ?= -g -DSLOP_DEBUG -Wall -Wextra

TOOLING = tooling/src
RUNTIME = runtime

.PHONY: help parse transpile check fill build clean test

help:
	@echo "SLOP Build System"
	@echo ""
	@echo "Usage: make <target> FILE=<path/to/file.slop>"
	@echo ""
	@echo "Targets:"
	@echo "  parse      Parse and display AST"
	@echo "  holes      Show holes in file"
	@echo "  transpile  Convert to C"
	@echo "  check      Validate file"
	@echo "  fill       Fill holes with LLM"
	@echo "  build      Full pipeline to binary"
	@echo "  clean      Remove build artifacts"
	@echo "  test       Run tests"

parse:
	$(PYTHON) $(TOOLING)/slop_cli.py parse $(FILE)

holes:
	$(PYTHON) $(TOOLING)/slop_cli.py parse $(FILE) --holes

transpile:
	$(PYTHON) $(TOOLING)/slop_cli.py transpile $(FILE) -o $(basename $(FILE)).c

check:
	$(PYTHON) $(TOOLING)/slop_cli.py check $(FILE)

fill:
	$(PYTHON) $(TOOLING)/slop_cli.py fill $(FILE) -o $(FILE).filled

build:
	$(PYTHON) $(TOOLING)/slop_cli.py build $(FILE)

build-debug:
	$(PYTHON) $(TOOLING)/slop_cli.py build $(FILE) --debug

# Compile C directly
%.o: %.c
	$(CC) $(CFLAGS) -I$(RUNTIME) -c $< -o $@

%-debug.o: %.c
	$(CC) $(DEBUG_CFLAGS) -I$(RUNTIME) -c $< -o $@

clean:
	rm -f *.o *.c.filled build/*

test:
	@echo "Running parser tests..."
	$(PYTHON) $(TOOLING)/parser.py
	@echo ""
	@echo "Running transpiler tests..."
	$(PYTHON) $(TOOLING)/transpiler.py
	@echo ""
	@echo "Running schema converter tests..."
	$(PYTHON) $(TOOLING)/schema_converter.py
	@echo ""
	@echo "All tests passed!"

# Example targets
example-rate-limiter:
	$(PYTHON) $(TOOLING)/slop_cli.py transpile examples/rate-limiter.slop -o build/rate_limiter.c
	$(CC) $(CFLAGS) -I$(RUNTIME) -DRATE_LIMITER_TEST build/rate_limiter.c -o build/rate_limiter

example-run: example-rate-limiter
	./build/rate_limiter
