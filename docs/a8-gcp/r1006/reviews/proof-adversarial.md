# S3132 r1006 proof-adversarial route review

Date: 2026-10-04 America/Los_Angeles. Model: GPT-6.1 Sol. Mode: read-only; no Lean, Lake, elan, GCP, source edits, commits, or pushes.

## Verdict

**GO-WITH-NOTES.** The earlier `MANUSCRIPT GAP` diagnosis was too strong. The manuscript's T2/A1 argument supports the required inequality for arbitrary supported complex input. What is missing is a formal composition lemma, not a new hypothesis or manuscript redesign.

## Corrections and verified argument

- Let `k = rank X`, `K = ker X`, `u = dim P`, and `v = dim K - dim Q0`. The graph-lift fiber has cardinality
  `N = 2^(k*u) * 2^(k*v) = 2^(k*(u+v))`.
  The prior note incorrectly substituted `k` for `dim K` in the second term. `a7_t2_complement_card_le` contains the correct dimensions.
- An output-pair share has an output-shift average over `S : Hom(E,K)` in addition to the ambient `T` average. Its inner actual carrier is `Hom(E/P,Q0)`. The actual energy has the same normalized denominator under the canonical carrier identifications.
- The zero share is `||g||_2^4`, not `||g||_4^4`. All nonzero pairs, including the one-sided classes, belong to the positive sum.
- T2 plus selector uniqueness identifies the whole output derivative on the common carrier as a sum over actual graph lifts. A1 moves each summand to the corresponding actual derivative at translated base `T + Delta(S)`.
- For energies `e_alpha = E_N |G_alpha(N)|^2`, Cauchy--Schwarz on the common carrier followed by scalar Cauchy--Schwarz gives
  `(E_N |sum_alpha G_alpha|^2)^2 <= N^3 * sum_alpha e_alpha^2`.
  This controls all cross terms for arbitrary complex coefficients. Termwise equality is false and is not needed.
- Averaging over `T,S` removes `Delta(S)` because translation of the full ambient `T` group is bijective. Supportedness and `a6Order t <= D` force pairs with `u+v > D-a6Order t` to vanish. For remaining pairs,
  `N^3 = 2^(3*k*(u+v)) <= 2^(3*k*(D-a6Order t)) <= 2^(6*D*k)`.
- Summing shares counts each actual pair once because its output pair is recovered canonically. The downstream A9 partition/count remains valid inside the supported window.

No existing declaration proves this full averaged bridge. Coordinate helpers transport an already specified integrand; they do not replace this composition.

## Exactly one next action

Formalize the averaged per-output-pair inequality using `typedW6OutputEnergy`, the corrected graph count, both base averages, and the `N^3` norm loss. This is an S3132 manuscript-facing increment, not helper increment 3.

