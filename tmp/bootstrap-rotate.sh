#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/compile-rotate.sh /tmp/ActualThreeSatRotate.lean /tmp/ActualThreeSatRotateChecks.lean
REPO=/home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness
cp /tmp/ActualThreeSatRotate.lean "$REPO/"
cp /tmp/ActualThreeSatRotateChecks.lean "$REPO/"
chmod +x /tmp/compile-rotate.sh
nohup /tmp/compile-rotate.sh >/dev/null 2>&1 &
echo STARTED
