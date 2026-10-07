#!/usr/bin/env bash
set -euo pipefail
BASE=/home/dfredriksen_quantyra_org
RUN="$BASE/cmmsa_tagged_ordered_cb9b4bf_exact"
RECEIPT="$BASE/cmmsa_tagged_ordered_cb9b4bf_receipt"
EXITFILE="$BASE/cmmsa_tagged_ordered_cb9b4bf_replay.exit"
trap 'rc=$?; printf "%s\n" "$rc" > "$EXITFILE"' EXIT
cmp "$RUN/lake-manifest.json" "$BASE/cmmsa-phasea-build-185df9d/lake-manifest.json"
export PATH="$BASE/.elan/bin:$PATH"
cd "$RUN"
lake build PvNP.RealizableHardness.ActualTaggedConcreteStarLawChecks > "$RECEIPT/build-two.log" 2>&1
sha256sum lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLaw.lean lean/PvNP/RealizableHardness/ActualTaggedOrderedQuestionSourceBridge.lean lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLawChecks.lean > "$RECEIPT/source-after.sha256"
cmp "$RECEIPT/source-before.sha256" "$RECEIPT/source-after.sha256"
if grep -En 'sorry|admit|native_decide|^axiom|trace_state' lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLaw.lean lean/PvNP/RealizableHardness/ActualTaggedOrderedQuestionSourceBridge.lean lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLawChecks.lean > "$RECEIPT/forbidden-scan.txt"; then
  exit 3
fi
printf 'SOURCE_COMMIT=cb9b4bf\nBUILD_ONE=0\nBUILD_TWO=0\n' > "$RECEIPT/OUTCOME.txt"
cd "$BASE"
tar -czf cmmsa_tagged_ordered_cb9b4bf_receipt.tar.gz cmmsa_tagged_ordered_cb9b4bf_receipt
sha256sum cmmsa_tagged_ordered_cb9b4bf_receipt.tar.gz > "$RECEIPT/archive.sha256"
