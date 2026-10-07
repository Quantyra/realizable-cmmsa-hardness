#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/compile-fan.sh /tmp/ActualThreeSatGrassmannFan.lean /tmp/ActualThreeSatGrassmannFanChecks.lean
REPO=/home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness
cp /tmp/ActualThreeSatGrassmannFan.lean "$REPO/"
cp /tmp/ActualThreeSatGrassmannFanChecks.lean "$REPO/"
chmod +x /tmp/compile-fan.sh
nohup /tmp/compile-fan.sh >/dev/null 2>&1 &
echo STARTED
