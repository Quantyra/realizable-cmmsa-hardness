#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/ActualThreeSatOverlap.lean /tmp/compile-overlap.sh
cp /tmp/ActualThreeSatOverlap.lean /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness/
rm -f /home/dfredriksen_quantyra_org/compile-overlap.log
chmod +x /tmp/compile-overlap.sh
nohup /tmp/compile-overlap.sh >/dev/null 2>&1 &
echo RESTARTED
