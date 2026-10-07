#!/bin/bash
set -euo pipefail
export PATH="/home/dfredriksen_quantyra_org/.elan/bin:$PATH"
cd /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness
LOG=/home/dfredriksen_quantyra_org/compile-overlap.log
{
  echo "START $(date -Is)"
  echo "LEAN $(lean --version)"
  sha256sum lean/PvNP/RealizableHardness/ActualThreeSatOverlap.lean
  sha256sum lean/PvNP/RealizableHardness/ActualThreeSatOverlapChecks.lean
  lake build --old PvNP.RealizableHardness.ActualThreeSatOverlapChecks
  echo "LAKE_EXIT $?"
  echo "END $(date -Is)"
} >"$LOG" 2>&1
echo DONE >>"$LOG"
