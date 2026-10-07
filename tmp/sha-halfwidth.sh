#!/bin/bash
set -euo pipefail
cd /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness
echo START_LINE
head -n 5 /home/dfredriksen_quantyra_org/compile-halfwidth.log
echo SHA_MAIN
sha256sum lean/PvNP/RealizableHardness/ActualThreeSatHalfWidth.lean
echo SHA_CHECKS
sha256sum lean/PvNP/RealizableHardness/ActualThreeSatHalfWidthChecks.lean
echo AXIOM_TAIL
tail -n 40 /home/dfredriksen_quantyra_org/compile-halfwidth.log
