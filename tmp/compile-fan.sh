#!/bin/bash
set -euo pipefail
export PATH="/home/dfredriksen_quantyra_org/.elan/bin:$PATH"
cd /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness
LOG=/home/dfredriksen_quantyra_org/compile-fan.log
{
  echo "START $(date -Is)"
  echo "LEAN $(lean --version)"
  sha256sum lean/PvNP/RealizableHardness/ActualThreeSatGrassmannFan.lean
  sha256sum lean/PvNP/RealizableHardness/ActualThreeSatGrassmannFanChecks.lean
  lake build --old PvNP.RealizableHardness.ActualThreeSatGrassmannFanChecks
  echo "LAKE_EXIT $?"
  echo "END $(date -Is)"
} >"$LOG" 2>&1
echo DONE >>"$LOG"
