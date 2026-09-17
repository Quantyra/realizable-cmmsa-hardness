# Actual runOptionGuardTag_eq complexity-theory review

**Verdict: GO-WITH-NOTES**

This file is historical evidence for the earlier guard-only snapshot. It is superseded for current-snapshot closeout by the 2026-09-17 guard-plus-truncation reviews. Its hashes and verdict below are intentionally preserved.

Reviewed source base: `c6dfbb4`. Main SHA-256: `2500a41289666dfbe384642c17f61104a5013834e3a564b878af2d1591dd1e57`. Checks SHA-256: `7432999fac70c80ae77fbfc6b832be3441b175c1781bef4a982b69dd1aa5441b`.

Cloud-targeted build: 2461/2461. Full Lake build: 3961/3961. Printed axioms for the exposed guard theorems are limited to `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, or new axioms were found.

The increment is a genuine packed length-guard FP/semantics agreement, not a claim that the un-packed executor is in FP. `runOptionGuardTag_eq` clarifies the guard contract; it does not run `checkedBits` or establish a full selected-pipeline map. The next interface is the outer policy/truncation layer, followed by the checked executor.

Not credited by this review: `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, or P-vs-NP. The increment remains bounded and is not route-final.
