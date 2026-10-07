#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/ActualThreeSatRotate.lean /tmp/compile-rotate.sh
cp /tmp/ActualThreeSatRotate.lean /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness/
rm -f /home/dfredriksen_quantyra_org/compile-rotate.log
chmod +x /tmp/compile-rotate.sh
nohup /tmp/compile-rotate.sh >/dev/null 2>&1 &
echo RESTARTED
