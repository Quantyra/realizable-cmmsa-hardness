#!/bin/bash
set -euo pipefail
export PATH="/home/dfredriksen_quantyra_org/.elan/bin:$PATH"
cd /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness
LOG=/home/dfredriksen_quantyra_org/compile-halfwidth.log
{
  echo "START $(date -Is)"
  echo "LEAN $(lean --version)"
  sha256sum lean/PvNP/RealizableHardness/ActualThreeSatHalfWidth.lean
  sha256sum lean/PvNP/RealizableHardness/ActualThreeSatHalfWidthChecks.lean
  lake build --old PvNP.RealizableHardness.ActualThreeSatHalfWidthChecks
  echo "LAKE_EXIT $?"
  echo "END $(date -Is)"
} >"$LOG" 2>&1
echo DONE >>"$LOG"
