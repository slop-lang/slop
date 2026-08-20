#!/bin/sh

## Bump the SLOP version everywhere it is mirrored.
##
## VERSION is the source of truth; this script keeps the following in sync:
##   - VERSION
##   - pyproject.toml         (Python package version)
##   - src/slop/__init__.py   (`slop --version`)
##   - lib/compiler/*/main.slop  (each native tool's --version string)
##
## After running, regenerate the bootstrap C and rebuild so the native binaries
## report the new version:  make bootstrap-update && make selfhost
##
## Usage: scripts/bump_version.sh 0.1.1

set -e

NEW="${1:?usage: bump_version.sh <version, e.g. 0.1.1>}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OLD="$(cat "$ROOT/VERSION")"

echo "Synchronizing version $OLD -> $NEW"

printf '%s\n' "$NEW" > "$ROOT/VERSION"
perl -pi -e "s/^version = \"[^\"]*\"/version = \"$NEW\"/" "$ROOT/pyproject.toml"
perl -pi -e "s/^__version__ = \"[^\"]*\"/__version__ = \"$NEW\"/" "$ROOT/src/slop/__init__.py"
for tool in parser checker compiler tester; do
    # Match the version after "slop-<tool> " without anchoring on the closing
    # quote, since some mains print a trailing escape (e.g. "slop-tester 0.1.0\n").
    perl -pi -e "s/slop-$tool [0-9]+\.[0-9]+\.[0-9]+/slop-$tool $NEW/g" "$ROOT/lib/compiler/$tool/main.slop"
done

grep -Fq "version = \"$NEW\"" "$ROOT/pyproject.toml"
grep -Fq "__version__ = \"$NEW\"" "$ROOT/src/slop/__init__.py"
for tool in parser checker compiler tester; do
    grep -Fq "slop-$tool $NEW" "$ROOT/lib/compiler/$tool/main.slop"
done

echo "Source bumped. Now run:  make bootstrap-update && make selfhost"
echo "(regenerates bootstrap C and rebuilds so the native binaries report $NEW)"
