#!/usr/bin/env bash
# Elaborate the library against the Mathlib installation on LEAN_PATH.
# (No Lake build is needed: `lean` picks up /opt/mathlib through LEAN_PATH.)
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$LEAN_PATH:$PWD"
mods="Basic Hermitian Spectral Subconstituent PerronFrobenius CollatzWielandt Cayley DistanceRegular Hamming Thin TwoThin DistanceMatrix AssociationScheme Schemes2 RFL LateChapters"
for m in $mods; do
  echo "== Terwilliger.$m"
  lean -o "Terwilliger/$m.olean" "Terwilliger/$m.lean"
done
echo "== Terwilliger"
lean Terwilliger.lean
echo "OK"
