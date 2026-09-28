# Fixed-U canonical density force

- Source base: `c4cec25955f35e3947e4c6ae21c8468315dc209e`.
- Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`. All local `gcloud.cmd` commands ran with `subprocess.CREATE_NO_WINDOW`.
- Isolated exact-source tree: `/tmp/cmmsa-fixed-u-density-r1`, using the pinned shared package cache. The initial upload tunnel closed before a build launched; a retry succeeded. Main build r1 exposed source errors, repaired before the terminal builds.
- Terminal main build: `/tmp/cmmsa-fixed-u-density-r2.exit=0`, 3254 jobs. Terminal Checks build: PID `3232`, `/tmp/cmmsa-fixed-u-density-r3.exit=0`, 3255 jobs. Full logs: `/tmp/cmmsa-fixed-u-density-r2.log` and `/tmp/cmmsa-fixed-u-density-r3.log`.
- Local and remote SHA-256 matched: main `db843d7aa9f5e08f689cb44c96ab203b9c78d22e4f669d79f4cc50175bda8eea`; Checks `db1ac6431413a4e97c617fbf9c95c76973ca4600c20f16b21359400fd5296902`.
- `#print axioms` for the conditional bound, exact mean, and force theorem gives only `propext`, `Classical.choice`, `Quot.sound`.
- After both builds, `gcloud compute instances stop` succeeded and fresh status was `TERMINATED`.

`conditionalCanonicalDensity` is the canonical acceptance probability conditional on a fixed eligible `U`, with uniform transverse stored `K` and independent uniform leaves in that `K` fiber. `ordered_canonical_eq_uniformU_mean` identifies the ordered-source canonical mass exactly with the uniform eligible-`U` mean of this quantity. For every fixed center table `C` and arbitrary raw vertex table `T`, `ordered_physical_forces_high_density_U` chooses one full-domain table `T'` before the draw. Under its explicit collision guards and a physical lower bound `α ≥ 2^-J`, the uniform mass of eligible `U` having conditional canonical density at least `(α - 2^-J)/2` is at least `(α - 2^-J)/2`.

This reduces the logical NO-soundness gap by providing the correct fixed-table high-density first-question input to the MZ local decoder. It does not prove that the density threshold meets MZ Theorem 4.2's hypothesis, construct the MZ decoder, prove the manuscript initial-vertex/resampled-`U'` source marginal, bound the outer repeated-game value, or certify Theorem 1. The quantitative NO exponent is unchanged.
