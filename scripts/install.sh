#!/bin/bash
# SLOP Installation Script for Unix (Linux/macOS)
#
# Usage:
#   ./install.sh              # Install to /usr/local (may require sudo)
#   PREFIX=~/.local ./install.sh  # Install to ~/.local
#
# The distribution is installed whole in $PREFIX/lib/slop, which is the
# SLOP_HOME the `slop` command uses: bin/ (the native tools and the slop
# wrapper), lib/std, lib/runtime, lib/python, spec/ and examples/. $PREFIX/bin
# gets the commands: links to the native tools, and a launcher for slop.
#
set -e

PREFIX="${PREFIX:-/usr/local}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SLOP_DIR="$PREFIX/lib/slop"

echo "Installing SLOP to $PREFIX..."

# macOS tags downloaded files with a com.apple.quarantine flag; Gatekeeper then
# blocks each unsigned binary on first run ("developer cannot be verified").
# Clear it for the extracted package (scoped to this directory) so the installed
# tools run without a per-binary prompt.
if [ "$(uname)" = "Darwin" ]; then
    echo "  Clearing macOS quarantine flag..."
    xattr -dr com.apple.quarantine "$SCRIPT_DIR" 2>/dev/null || true
fi

# Replace any earlier install. $PREFIX/lib/slop holds only SLOP; an install
# from before 0.4.2 left python/, runtime/ and std/ there, which nothing uses.
echo "  Installing the distribution to $SLOP_DIR..."
rm -rf "$SLOP_DIR"
mkdir -p "$SLOP_DIR" "$PREFIX/bin"
cp -R "$SCRIPT_DIR/bin" "$SCRIPT_DIR/lib" "$SCRIPT_DIR/spec" "$SCRIPT_DIR/examples" "$SLOP_DIR/"
chmod +x "$SLOP_DIR/bin/"*

# The commands. The slop wrapper finds the rest of the install relative to
# itself, so $PREFIX/bin/slop runs it where it is rather than linking it.
echo "  Installing commands to $PREFIX/bin..."
for tool in "$SLOP_DIR/bin/slop-"*; do
    ln -sf "$tool" "$PREFIX/bin/$(basename "$tool")"
done
cat > "$PREFIX/bin/slop" << LAUNCHER
#!/bin/bash
exec "$SLOP_DIR/bin/slop" "\$@"
LAUNCHER
chmod +x "$PREFIX/bin/slop"

echo ""
echo "SLOP installed successfully!"
echo ""
echo "  Commands:"
echo "    slop              Python CLI (check, build, test, verify, format, doc, ref)"
echo "    slop mcp          MCP server for coding agents (claude mcp add slop -- slop mcp)"
echo "    slop-parser       Native parser"
echo "    slop-checker      Native type checker"
echo "    slop-compiler     Native compiler (type check + transpile)"
echo "    slop-tester       Native test runner"
echo ""
echo "  Locations:"
echo "    Commands:      $PREFIX/bin/"
echo "    Distribution:  $SLOP_DIR/ (the standard library, specs and examples)"
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
elif ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))'; then
    echo "Warning: the 'slop' command requires Python 3.11+, and python3 is $(python3 --version 2>&1)."
    echo ""
fi

echo "Try: slop --help"
