#!/bin/bash
set -euo pipefail
cd /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness
echo START_LINE
head -n 6 /home/dfredriksen_quantyra_org/compile-overlap.log
echo SHA_MAIN
sha256sum lean/PvNP/RealizableHardness/ActualThreeSatOverlap.lean
echo SHA_CHECKS
sha256sum lean/PvNP/RealizableHardness/ActualThreeSatOverlapChecks.lean
echo END_LINE
tail -n 5 /home/dfredriksen_quantyra_org/compile-overlap.log
