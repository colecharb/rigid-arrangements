#!/bin/bash
# usage: explore/caseb/build.sh [outdir]
# Concatenates the case-(b) sources (imports live in Lattice.lean, which comes first) and
# compiles them, as explore/offlattice/catalogue/build.sh does.  Run from the repository root.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
OUT="${1:-$HERE/out}"
mkdir -p "$OUT"
cat "$HERE/Lattice.lean" "$HERE/Body.lean" "$HERE/Corners.lean" "$HERE/Rhombus.lean" "$HERE/Interval.lean" \
    "$HERE/Chain.lean" "$HERE/Main.lean" > "$OUT/caseb.lean"
cd "$REPO"
lake env lean --root="$OUT" -c "$OUT/caseb.c" "$OUT/caseb.lean"
lake env leanc -O3 "$OUT/caseb.c" -o "$OUT/caseb" 2>&1 | grep -v warning | head -20 || true
echo "built $OUT/caseb"
