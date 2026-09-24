# ActualStarJointKernel proof-adversarial review

**Verdict: GO-WITH-NOTES**

Reviewed source base: `d6e59e2eca47031a31b0795587b4df2cea9540ba`. Main SHA-256: `f02b9c19a7145c07eefa78693e24ca4eade747303e75300ebdc54563bd12d40f`. Checks SHA-256: `38cd8e0488cae0bb8c5892fce6dba6cb26a6f14bfca8b70c913be595ed42f761`.

R8 GCP evidence at `artifacts/gcp_actual_star_joint_kernel_r8_20260924T170258Z` records a pass for dependency, direct, combined, and replay builds. Direct and replay logs and `.olean` hashes agree, the shortcut scan passes, and the exposed theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The bounded proof increment uses the full direct sum of quotient increments. It does not weaken joint directness to pairwise intersection conditions. The accepted conclusions are the injectivity characterization and the nonzero-kernel witness characterization in `ActualStarJointKernel`.

Note: the driver replay-diff status handling should be made more robust in a future harness. The actual R8 replay diff is empty and marked stable, so this is a harness-maintenance note rather than a defect in the accepted source or run.
