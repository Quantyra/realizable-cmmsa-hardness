# Tagged MZ threshold force, 2026-09-28

Source commit: `7a6a104` (parent `f71ac52`). The checked source files are
`ActualTaggedFixedUDensityForce.lean` (SHA-256 `ffc1a93e4a1faebca783d21da946a6d8f4eefbdb5c7c72150149a32f22b574cb`)
and `ActualTaggedFixedUDensityForceChecks.lean` (SHA-256 `69e4ee2e6b622a46744bff44fef6db491e932f69957bbb1e943b33fcc631daa0`).
The remote file hashes matched the local hashes after upload.
After both jobs ended, a VM process check showed no active Lake build.
The hidden-console stop command's local observer timed out, but a subsequent
instance description returned **TERMINATED**.

On GCP instance `quantyra-lean-builder-01`, project
`quantyra-lean-cert-20260915`, zone `us-central1-a`, the exact source was
built with `lake build PvNP.RealizableHardness.ActualTaggedFixedUDensityForceChecks`.
The final direct run and fresh `.lake/build` replay both exited 0 and
completed 3,255 jobs. Logs beside this receipt contain no `error:` lines.
The new theorem axiom reports list only `propext`, `Classical.choice`, and
`Quot.sound`; the scoped source scan found no `sorry`, `admit`, `unsafe`,
`native_decide`, or axiom declaration.

The first theorem gives the exact fixed-table implication
`physical ≥ α`, `2^-J + 16S ≤ α` ⇒ one predraw canonical table and
eligible-`U` mass at least `8S` at conditional density at least `8S`.
The second charges an explicit factor-two preceding loss: if
`physical ≥ 2^-(q+1)`, `q+6 ≤ p ≤ J`, and `S=2^-p`, the same conclusion
follows. The third specializes the exponent gap to manuscript parameters
`q=2(1−ξ)hm`, `p=2(1−1000ρ)hm`, `ξ=4000ρ`, under the explicit integral
exponent and sufficiently-large-`h` conditions. The theorem retains
`physical ≥ 2^-(q+1)` as a hypothesis. It does not derive that tagged
ordered physical score from a composed score above `2^-q`; the manuscript's
initial-vertex/clique-resampling transfer and prior losses remain to be
formalized. It does not prove the MZ decoder, outer NO contradiction,
Theorem 1, or Corollary 2.
