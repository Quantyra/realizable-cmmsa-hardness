# Late-τ copied-row padding boundary

`ActualLateTauPadding.exists_late_tau_padding` connects the manuscript's late
choice of positive rational `τ` to the existing tagged-copy collision theorem.
For every fixed actual occurrence-allocation instance with `m>0`, every fixed
`J`, and every later `τ>0`, it chooses `T≥4` and
`copies=1+T·J·(J−1)·157`. In the **uniform ordered copied-row draw**, the
illegitimate mass `a` obeys `a≤τ/100` and `a≤1/4`, and legitimate mass is
exactly `1−a`. This is the manuscript §7 conditioning budget, with its actual
copied-row `GoodOrderedQuestion` event.

The theorem composes proved results in `ActualTaggedQuestionRetainedMass`;
the source optimum preservation is separately proved by
`Finite3LinOptimum.taggedCopy_value`. It does not prove Equation (21) for the
full verifier. The MZ positive-error outer YES theorem, including the encoded
bounded-occurrence 3-Lin reduction with an absolute NO gap for each fixed
positive `ε₁`, remains an **external source contract**. The finite tagged-copy
calculation neither proves that hardness theorem nor builds its encoding.
The remaining typed obligations are:

1. Prove the **full verifier/resampled marginal bridge**: identify the full
   post-padding verifier draw's original-question marginal with this uniform
   ordered copied-row draw, and establish the joint
   `eventMass μ (legitimate ∩ bad i) ≤ J·ε₁` for every one of the `m+1`
   original and clique-resampled blocks. This is currently unproved. It feeds
   `ActualLateTauYesComposition.conditioned_yes_failure_le` directly.
2. Define a source row-incidence degree and prove
   `degree ((taggedCopy S K), (k,v)) = degree (S,v)` for each copied variable.
   The finite `taggedCopy` definition makes this plausible, but the attempted
   Lean proof timed out and was reverted. No degree result is claimed here.
3. Define an encoded copy constructor and prove its output represents the
   finite `taggedCopy` source, has size linear in `K` times input size, and is
   computable in polynomial time for fixed `J,T`. The present finite semantic
   structure has no encoding/runtime theorem.

This padding increment reduces the **legitimate-conditioning premise** of the
YES bound for the copied ordered-question marginal. It does not change the
numeric NO-soundness gap or close Theorem 1.

## Three-lens bounded review

| Lens | Bounded padding result | Equation (21) / core Theorem 1 |
| --- | --- | --- |
| Proof-adversarial | GO-WITH-NOTES | NO-GO: full joint verifier and resampled block laws remain unproved. |
| Complexity theory | GO-WITH-NOTES | NO-GO: encoded reduction/runtime and degree preservation remain unproved. |
| Non-claims boundary | GO-WITH-NOTES | NO-GO: MZ positive-error outer YES is external and the full marginal bridge is unproved. |

`ActualLateTauPaddingChecks` built green (3388 jobs); `#print axioms`
reported only standard Lean axioms. These reviews certify the bounded
copied-row mass statement, not a completed YES reduction or Theorem 1.
