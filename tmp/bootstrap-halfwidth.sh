#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/compile-halfwidth.sh /tmp/ActualThreeSatHalfWidth.lean /tmp/ActualThreeSatHalfWidthChecks.lean
REPO=/home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness
cp /tmp/ActualThreeSatHalfWidth.lean "$REPO/"
cp /tmp/ActualThreeSatHalfWidthChecks.lean "$REPO/"
chmod +x /tmp/compile-halfwidth.sh
nohup /tmp/compile-halfwidth.sh >/dev/null 2>&1 &
echo STARTED
