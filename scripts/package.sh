#!/bin/bash
# SLOP Distribution Packaging Script for Unix (Linux/macOS)
#
# Usage:
#   RELEASE_VERSION=v0.1.0 ./package.sh linux-x64 tar.gz
#   RELEASE_VERSION=v0.1.0 ./package.sh macos-arm64 tar.gz
#
set -e

PLATFORM="${1:?Usage: package.sh <platform> <format>}"
FORMAT="${2:-tar.gz}"
VERSION="${RELEASE_VERSION:-dev}"
DIST_NAME="slop-${VERSION}-${PLATFORM}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "Packaging SLOP ${VERSION} for ${PLATFORM}..."
echo ""

# Create distribution directory structure
mkdir -p "dist/${DIST_NAME}/bin"
mkdir -p "dist/${DIST_NAME}/lib/std"
mkdir -p "dist/${DIST_NAME}/lib/runtime"
mkdir -p "dist/${DIST_NAME}/lib/python/slop"
mkdir -p "dist/${DIST_NAME}/spec"
mkdir -p "dist/${DIST_NAME}/examples"

# Copy binaries
echo "  Copying binaries..."
cp "$ROOT_DIR/bootstrap/bin/"* "dist/${DIST_NAME}/bin/"
chmod +x "dist/${DIST_NAME}/bin/"*

# Copy standard library
echo "  Copying standard library..."
cp -r "$ROOT_DIR/lib/std/"* "dist/${DIST_NAME}/lib/std/"

# Copy runtime header
echo "  Copying runtime..."
cp "$ROOT_DIR/bootstrap/runtime/slop_runtime.h" "dist/${DIST_NAME}/lib/runtime/"

# Copy Python tools (as a proper package)
echo "  Copying Python tools..."
cp -r "$ROOT_DIR/src/slop/"* "dist/${DIST_NAME}/lib/python/slop/"

# Create slop wrapper script for Python CLI
echo "  Creating slop wrapper..."
cat > "dist/${DIST_NAME}/bin/slop" << 'WRAPPER'
#!/bin/bash
# SLOP Python CLI wrapper
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SLOP_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
export PYTHONPATH="$SLOP_ROOT/lib/python:$PYTHONPATH"
exec python3 -m slop.cli "$@"
WRAPPER
chmod +x "dist/${DIST_NAME}/bin/slop"

# Copy specs
echo "  Copying specs..."
cp "$ROOT_DIR/spec/"*.md "dist/${DIST_NAME}/spec/"

# Copy examples
echo "  Copying examples..."
cp -r "$ROOT_DIR/examples/"* "dist/${DIST_NAME}/examples/"

# Copy docs and installer
echo "  Copying docs..."
cp "$ROOT_DIR/LICENSE" "dist/${DIST_NAME}/" 2>/dev/null || echo "    (LICENSE not found, skipping)"
cp "$ROOT_DIR/README.md" "dist/${DIST_NAME}/" 2>/dev/null || echo "    (README.md not found, skipping)"

# Copy Unix installer
cp "$SCRIPT_DIR/install.sh" "dist/${DIST_NAME}/"
chmod +x "dist/${DIST_NAME}/install.sh"

# Create archive
echo ""
echo "  Creating archive..."
cd dist
if [ "$FORMAT" = "tar.gz" ]; then
    tar -czvf "${DIST_NAME}.tar.gz" "${DIST_NAME}"
    echo ""
    echo "Created: dist/${DIST_NAME}.tar.gz"
elif [ "$FORMAT" = "zip" ]; then
    zip -r "${DIST_NAME}.zip" "${DIST_NAME}"
    echo ""
    echo "Created: dist/${DIST_NAME}.zip"
else
    echo "Unknown format: $FORMAT"
    exit 1
fi

# Show contents
echo ""
echo "Package contents:"
ls -la "${DIST_NAME}/"
