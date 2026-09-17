# Actual runOptionGuardTag_eq proof-adversarial review

**Verdict: GO-WITH-NOTES**

This file is historical evidence for the earlier guard-only snapshot. It is superseded for current-snapshot closeout by the 2026-09-17 guard-plus-truncation reviews. Its hashes and verdict below are intentionally preserved.

Reviewed source base: `c6dfbb4`. Main SHA-256: `2500a41289666dfbe384642c17f61104a5013834e3a564b878af2d1591dd1e57`. Checks SHA-256: `7432999fac70c80ae77fbfc6b832be3441b175c1781bef4a982b69dd1aa5441b`.

The cloud-targeted build is green (2461/2461); the full Lake build is green (3961/3961). The exposed guard theorems use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, `native_decide`, or new axioms were found.

This review accepts the bounded `runOptionGuardTag_eq` agreement increment: the packed guard is related to the intended decode/length-guard semantics. It does not treat the agreement lemma as execution of `checkedBits`, `accepted`, or an output tree. The proof has no identified defect, but Checks do not provide a concrete nonempty successful instance; that remains a coverage note rather than a proof failure.

The accepted boundary is the packed guard contract only. It does not establish `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, or P-vs-NP. This review does not authorize route-final closeout.
