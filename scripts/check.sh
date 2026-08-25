#!/usr/bin/env bash
set -euo pipefail

lake build

for audit in \
  Audit/CoreProbe.lean \
  Audit/RepresentativeProbe.lean \
  Audit/ZeroBenchmarks.lean \
  Audit/AxiomPaths.lean \
  Audit/AxiomCensus.lean
do
  echo "checking ${audit}"
  lake env lean "${audit}" >/dev/null
done

./scripts/check-data.py
