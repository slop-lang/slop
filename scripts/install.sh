#!/bin/bash
# SLOP Installation Script for Unix (Linux/macOS)
#
# Usage:
#   ./install.sh              # Install to /usr/local (may require sudo)
#   PREFIX=~/.local ./install.sh  # Install to ~/.local
#
set -e

PREFIX="${PREFIX:-/usr/local}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "Installing SLOP to $PREFIX..."

# Create directories
mkdir -p "$PREFIX/bin"
mkdir -p "$PREFIX/lib/slop"
mkdir -p "$PREFIX/share/slop"

# Copy binaries
echo "  Installing binaries..."
cp "$SCRIPT_DIR/bin/"* "$PREFIX/bin/"
chmod +x "$PREFIX/bin/slop-"*

# Copy libraries
echo "  Installing libraries..."
cp -r "$SCRIPT_DIR/lib/"* "$PREFIX/lib/slop/"

# Copy specs and examples
echo "  Installing specs and examples..."
cp -r "$SCRIPT_DIR/spec/"* "$PREFIX/share/slop/"
cp -r "$SCRIPT_DIR/examples" "$PREFIX/share/slop/"

echo ""
echo "SLOP installed successfully!"
echo ""
echo "  Commands:"
echo "    slop              Python CLI (parse, transpile, build, fill)"
echo "    slop-parser       Native parser"
echo "    slop-checker      Native type checker"
echo "    slop-compiler     Native compiler (type check + transpile)"
echo "    slop-tester       Native test runner"
echo ""
echo "  Locations:"
echo "    Binaries:  $PREFIX/bin/"
echo "    Libraries: $PREFIX/lib/slop/"
echo "    Specs:     $PREFIX/share/slop/"
echo ""

# Check if PREFIX/bin is in PATH
if [[ ":$PATH:" != *":$PREFIX/bin:"* ]]; then
    echo "Note: $PREFIX/bin is not in your PATH."
    echo "Add it with: export PATH=\"\$PATH:$PREFIX/bin\""
    echo ""
fi

# Check Python availability
if ! command -v python3 &> /dev/null; then
    echo "Warning: python3 not found. The 'slop' command requires Python 3.11+."
    echo ""
fi

echo "Try: slop --help"
