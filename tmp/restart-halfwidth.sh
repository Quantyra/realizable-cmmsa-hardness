#!/bin/bash
set -euo pipefail
sed -i 's/\r$//' /tmp/ActualThreeSatHalfWidth.lean /tmp/compile-halfwidth.sh
cp /tmp/ActualThreeSatHalfWidth.lean /home/dfredriksen_quantyra_org/realizable-cmmsa-hardness/lean/PvNP/RealizableHardness/
rm -f /home/dfredriksen_quantyra_org/compile-halfwidth.log
chmod +x /tmp/compile-halfwidth.sh
nohup /tmp/compile-halfwidth.sh >/dev/null 2>&1 &
echo RESTARTED
