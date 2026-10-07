#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/compile-overlap.sh /tmp/ActualThreeSatOverlap.lean /tmp/ActualThreeSatOverlapChecks.lean
REPO=/home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness
cp /tmp/ActualThreeSatOverlap.lean "$REPO/"
cp /tmp/ActualThreeSatOverlapChecks.lean "$REPO/"
chmod +x /tmp/compile-overlap.sh
nohup /tmp/compile-overlap.sh >/dev/null 2>&1 &
echo STARTED
