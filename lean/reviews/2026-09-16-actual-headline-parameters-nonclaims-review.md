# Actual headline σ_L / γ_L parameters: non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `605b07e8d192f13772bdeac9ab16e3772b491d5a`. Gate logs name `605b07e`, not `bba6dbb`. Main `ActualHeadlineParameters.lean` SHA-256 `29767BDCE518085DB0590A260293003083858169FCC30D49A299217D913FC20C`. Checks SHA-256 `1000E3BD838BF74C7C3EE923F5816E45421169C471FBC7BE49C3A556EE949B48`. Evidence `research/evidence/2026-09-16-actual-headline-parameters-fresh-run/`. Independently rehashed local sources at `605b07e`, certify commit `8ce8e2a`, `HEAD`, and the working tree match the freeze and the gate. Certification commit `8ce8e2a` did not change the Lean sources.

Accepted, manuscript parameter family and conditional specialization only:

- `log2nat`, `qOf`, `mOf`, `hOf`, `ROf`, `GammaOf`, `sigmaL`, and `gammaL` instantiate the freeze’s `σ_L` / `γ_L` arithmetic: largest admissible `m` (else `0`), `q = Nat.sqrt m`, `b_m = Nat.max m 1`, `h = b_m * floor(log2(((L-1)/(q(m+1)))) / (2 b_m))`, `R = 2^(2h)`, `Gamma = 2 (3/4)^q`, `sigmaL = (R/4)/2`, `gammaL = 2 Gamma`.
- `mOf_spec` / `mOf_maximal` are the zero-or-admissible and maximality facts for that `m`. `mOf_unbounded` is `∀ M, ∃ L0, ∀ L ≥ L0, M ≤ mOf L`.
- `sigmaL_ge_one_eventual`, `gammaL_pos_lt_one_eventual`, and `gammaL_small_eventual` are eventual domain facts. They do not hold at `L = 0` or at the `L = 2^20` fixture.
- `hOf_le_log2` is `2 * hOf L (mOf L) ≤ log2nat L`. `sigmaL_le_ROf` is `sigmaL L ≤ ROf L`. There is no `log(sigma_L)/log L → 1` theorem and no `∨ True` disjunct.
- `adviceLeaf`, `sigmaLearn`, and `gammaLearn` are the Corollary 2 parameter maps (`a - 2 log2(a+1) - cU`, `floor(49/100 · sigmaL(·))`, `5 · gammaL(·)`). They are definitions, not HN transfer and not learning hardness.
- `theorem1_headline` is `theorem1_realizable_cmmsa` at `sigmaL` / `gammaL`. It still requires `1 ≤ sigmaL L`, `0 < gammaL L < 1`, and the two hypothesized `Preserves (1/6)` maps. It is not inhabited.

The module header denies constructing SAT-to-source or source-to-CMMSA `Preserves (1/6)` maps, inhabiting the headline theorem with identity, and proving unconditional Theorem 1, Corollary 2 NP-hardness, or P vs NP. Checks `#check` / `#print axioms` every public theorem, reduce `mOf` / `sigmaL` / `gammaL` at `0` and `2^20`, prove `mOf 0 = 0`, `sigmaL 0 = 0`, `gammaL 0 = 4`, and invoke `hOf_le_log2` / `sigmaL_le_ROf` at those points. Checks do **not** inhabit `theorem1_headline`, including not using identity as `hSrcCmmsa`. Main does not import `*Checks.lean`. `#print axioms` of every public theorem is empty or `propext` / `Classical.choice` / `Quot.sound` only. Forbidden-scan is clean. README, `INTEGRITY-CLAIMS.md`, `CHANGELOG.md`, and `CITATION.cff` are unchanged by this increment.

Notes, not blocking:

- Module/commit titles that say "actual headline" / "prove actual headline sigma_L gamma_L parameters" are catalog labels. They are not unconditional manuscript Theorem 1, Corollary 2 NP-hardness, constructed `1/6` maps, publication, or `P` versus `NP`.
- `#eval` at `L = 2^20` yields `mOf = 0`, `sigmaL = 32768`, `gammaL = 4`. That fixture typechecks and reduces; it is not a witness of `256 ≤ mOf L` or of `0 < gammaL L < 1`, and it does not discharge `theorem1_headline`.
- `gammaL 0 = 4` and `sigmaL 0 = 0` are the honest small-`L` values. The CMMSA hypotheses `1 ≤ sigmaL` and `gammaL < 1` remain eventual.
- `hOf_le_log2` plus `sigmaL_le_ROf` is an upper bound `log R ≤ log2 L`, not nearlinear tightness. Do not cite it as `log(sigma_L)/log L → 1`.
- `sigmaLearn` / `gammaLearn` do not prove Corollary 2. No SAT-to-regularized-3-Lin or source-to-encoded-CMMSA `Preserves (1/6)` map is constructed.

Forbidden claims absent. Unconditional Theorem 1, Corollary 2 NP-hardness, constructed SAT-to-CMMSA maps, P vs NP, and publication remain out of scope. Next: construct the two `Preserves (1/6)` maps. Do not inhabit `theorem1_headline` with identity, and do not skip those maps.
