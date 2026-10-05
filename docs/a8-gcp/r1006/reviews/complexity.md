# S3132 r1006 complexity-theory route review

Date: 2026-10-04 America/Los_Angeles. Model: GPT-6.1 Sol. Mode: read-only; no Lean, Lake, elan, GCP, source edits, commits, or pushes.

## Verdict

**GO-WITH-NOTES.** The averaged output-`Q` bound is the correct intermediate obligation behind manuscript A8. T2/A1 can establish it for arbitrary supported complex inputs and every output-pair class. Existing APIs supply the components; the integrated Lean bridge remains outstanding.

## Findings

- `X : H -> U = V/C` is a frequency; the output function lives on `Hom(E,K)` for `E = U/range X` and `K = ker X`. For final `(A',B')`, the induced frequency has rank `k`, and its output carrier is canonically `Hom(E/P,Q0)`.
- The graph fiber has exact size `N = 2^(k*u) * 2^(k*v)`, with `u = dim P` and `v = dim K - dim Q0`. The earlier note's exponent and domain-side construction require correction: the section image in `H/Q0` must be pulled back to `H` to obtain `B'`.
- Selector uniqueness does not imply squared-energy additivity. After the T2 whole-function identity, the norm estimate gives `||sum h_gamma||_2^4 <= N^3 * sum ||h_gamma||_2^4`; no orthogonality hypothesis is required.
- Nonzero output derivatives have `u+v <= D-t`, so `N^3 <= 2^(3*k*(D-t)) <= 2^(6*D*k)`. Clearing the W6 weight is downstream accounting, not the proof of this transport bound.
- Every pair share includes its own output-base average, and uniform ambient-base translation removes the embedded shift by finite Fubini. The zero pair contributes `||g||_2^4`; both one-sided positive classes must remain. At `k=0`, graph fibers are singletons.
- No new assumption or mechanism is required. Complementary vanishing outside the supported window and the existing A9 coarse count remain downstream steps. The work remains S3132 and does not trigger a literature review.

## Exactly one next action

Complete one integrated S3132 proof of `a8_output_q_le_actual_predecessor_sum`, incorporating corrected dimensions, both base averages, and the `N^3` norm loss.

