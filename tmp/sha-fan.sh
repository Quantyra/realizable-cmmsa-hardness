#!/bin/bash
set -euo pipefail
cd /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness
echo START_LINE
head -n 6 /home/dfredriksen_quantyra_org/compile-fan.log
echo SHA_MAIN
sha256sum lean/PvNP/RealizableHardness/ActualThreeSatGrassmannFan.lean
echo SHA_CHECKS
sha256sum lean/PvNP/RealizableHardness/ActualThreeSatGrassmannFanChecks.lean
echo END_LINE
tail -n 5 /home/dfredriksen_quantyra_org/compile-fan.log
