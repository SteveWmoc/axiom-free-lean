#!/usr/bin/env bash
set -euo pipefail

mkdir -p results

for audit in \
  Audit/CoreProbe.lean \
  Audit/RepresentativeProbe.lean \
  Audit/ZeroBenchmarks.lean \
  Audit/AxiomPaths.lean \
  Audit/AxiomCensus.lean
do
  result="results/$(basename "${audit}" .lean).txt"
  echo "writing ${result}"
  lake env lean "${audit}" | tee "${result}"
done

./scripts/check-data.py
