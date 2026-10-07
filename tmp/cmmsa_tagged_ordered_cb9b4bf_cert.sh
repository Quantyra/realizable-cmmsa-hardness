#!/usr/bin/env bash
set -euo pipefail
BASE=/home/dfredriksen_quantyra_org
RUN="$BASE/cmmsa_tagged_ordered_cb9b4bf_exact"
ARCHIVE="$BASE/cmmsa_tagged_ordered_cb9b4bf.tar"
RECEIPT="$BASE/cmmsa_tagged_ordered_cb9b4bf_receipt"
EXITFILE="$BASE/cmmsa_tagged_ordered_cb9b4bf.exit"
trap 'rc=$?; printf "%s\n" "$rc" > "$EXITFILE"' EXIT
mkdir -p "$RUN" "$RECEIPT"
printf '%s  %s\n' f5a446aa68b9c794c658eb46c103caede3af0a1373da2a4481314fbc8752ec8c "$ARCHIVE" | sha256sum -c - > "$RECEIPT/archive-verify.txt"
tar -xf "$ARCHIVE" -C "$RUN"
cmp "$RUN/lake-manifest.json" "$BASE/cmmsa-tagged-build-b5c87492933a/lake-manifest.json"
mkdir -p "$RUN/.lake"
ln -s "$BASE/cmmsa-tagged-build-b5c87492933a/.lake/packages" "$RUN/.lake/packages"
export PATH="$BASE/.elan/bin:$PATH"
cd "$RUN"
lake --version > "$RECEIPT/toolchain.txt"
lean --version >> "$RECEIPT/toolchain.txt"
sha256sum lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLaw.lean lean/PvNP/RealizableHardness/ActualTaggedOrderedQuestionSourceBridge.lean lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLawChecks.lean > "$RECEIPT/source-before.sha256"
lake build PvNP.RealizableHardness.ActualTaggedConcreteStarLawChecks > "$RECEIPT/build-one.log" 2>&1
lake clean > "$RECEIPT/clean.log" 2>&1
lake build PvNP.RealizableHardness.ActualTaggedConcreteStarLawChecks > "$RECEIPT/build-two.log" 2>&1
sha256sum lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLaw.lean lean/PvNP/RealizableHardness/ActualTaggedOrderedQuestionSourceBridge.lean lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLawChecks.lean > "$RECEIPT/source-after.sha256"
cmp "$RECEIPT/source-before.sha256" "$RECEIPT/source-after.sha256"
if grep -En 'sorry|admit|native_decide|^axiom|trace_state' lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLaw.lean lean/PvNP/RealizableHardness/ActualTaggedOrderedQuestionSourceBridge.lean lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLawChecks.lean > "$RECEIPT/forbidden-scan.txt"; then
  exit 3
fi
printf 'SOURCE_COMMIT=cb9b4bf\nEXIT=0\n' > "$RECEIPT/OUTCOME.txt"
cd "$BASE"
tar -czf cmmsa_tagged_ordered_cb9b4bf_receipt.tar.gz cmmsa_tagged_ordered_cb9b4bf_receipt
sha256sum cmmsa_tagged_ordered_cb9b4bf_receipt.tar.gz > "$RECEIPT/archive.sha256"
