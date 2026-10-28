#!/bin/bash
# usage: build.sh out files...  (concatenates the files and compiles them)
set -e
export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
OUT=$1; shift
cd /tmp/claude-0/offlat/catalogue
cat "$@" > $OUT.lean
lean --root=/tmp/claude-0/offlat/catalogue -c $OUT.c $OUT.lean
leanc -O3 $OUT.c -o $OUT 2>&1 | grep -v warning | head -20
