#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/ActualThreeSatGrassmannFan.lean /tmp/compile-fan.sh
cp /tmp/ActualThreeSatGrassmannFan.lean /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness/
rm -f /home/dfredriksen_quantyra_org/compile-fan.log
chmod +x /tmp/compile-fan.sh
nohup /tmp/compile-fan.sh >/dev/null 2>&1 &
echo RESTARTED
