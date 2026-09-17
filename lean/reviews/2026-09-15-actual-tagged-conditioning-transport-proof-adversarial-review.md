# Proof-adversarial review: actual tagged conditioning transport

Date: 2026-09-15  
Verdict: **GO-WITH-NOTES**

## Frozen review target

- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedConditioningTransport.lean`
  - expected SHA-256: `4C4D97A764ADD32F54806830B42460169DBFF69A5FFBCD3D5AD5E2DECE06C284`
  - independently observed SHA-256: `4C4D97A764ADD32F54806830B42460169DBFF69A5FFBCD3D5AD5E2DECE06C284`
- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedConditioningTransportChecks.lean`
  - expected SHA-256: `1ECD3F99C5E3C31B9910588ADC344B2FC0570B2815DE14628223C0A1DD0AF61E`
  - independently observed SHA-256: `1ECD3F99C5E3C31B9910588ADC344B2FC0570B2815DE14628223C0A1DD0AF61E`
- Certification directory: `research/evidence/2026-09-15-actual-tagged-conditioning-transport-fresh-run/`
  - expected artifact-manifest SHA-256: `8AB7CDBE388B62A358EF06AD052FEE35CA98B6E8EA539145A7938DD03F4D9BD9`
  - independently observed artifact-manifest SHA-256: `8AB7CDBE388B62A358EF06AD052FEE35CA98B6E8EA539145A7938DD03F4D9BD9`
  - all 24 manifest entries were independently rehashed and matched their recorded sizes and SHA-256 values.

## Findings

1. **The conditional-mean identity is sound.** `actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass` expands the good mean to `S / |G|`, the gated uniform mean to `S / |U|`, and good mass to `|G| / |U|`. It proves both denominators nonzero from `hm : 0 < m`, positivity of `actualPaddingCopies`, and the imported positive-good-cardinality theorem, then closes the field identity. There is no hidden zero-denominator convention in the proof.

2. **The `4/3` conditioning bound uses the correct hypotheses.** The imported retained-mass theorem gives `1 / goodMass <= 4/3` under exactly `hT : 4 <= T` and `hm : 0 < m`. The cast from `Rat` to `Real` preserves this inequality. For nonnegative `f`, the gated uniform mean is nonnegative and is at most the full uniform mean pointwise. Multiplying the reciprocal-mass bound by the gated mean therefore gives

   `goodMean <= (4/3) * uniformMean`.

   The theorem introduces only the necessary score assumption `hf : forall u, 0 <= f u`; it does not assume normalization, boundedness, independence, uniformity after projection, or the desired result.

3. **The factor-two corollary is sound.** `actualTaggedGoodMean_le_two_mul_uniformMean_of_nonneg` invokes the stronger `4/3` theorem, independently establishes nonnegativity of the full uniform mean, and uses `4/3 <= 2`. It matches the manuscript's factor-two conditioning allowance at lines 1129-1134 and the generic failure-probability conditioning step at lines 1148-1155.

4. **No weakening or illicit proof mechanism was found.** `set_option autoImplicit false` prevents undeclared implicit assumptions. Direct source inspection and the certification scan found no `sorry`, `admit`, `native_decide`, explicit `axiom`, or `unsafe` proof device. The five `#print axioms` reports list only `propext`, `Classical.choice`, and `Quot.sound`, the ordinary Lean/Mathlib classical quotient profile. No new or user-defined axiom appears.

5. **The certification receipt is coherent and appropriately scoped.** Main and Checks both report exit code 0. The certified objects independently rehash to
   - main: `78082F14478AE65D23D22A99877EABD6EC1F9BB23C569373F41D7FF2A252E26C`
   - Checks: `72AF400B84A10F7E230DED81F53F46E89D79840F57CCFD8E212E179D50746243`.

   The target contained neither object before compilation, sources remained stable, and the build used Lean `4.34.0-rc2` with one thread. This is a target-fresh main-and-Checks build against a copied, hashed dependency tree. It is not a full rebuild of every dependency from source, as the receipt itself states.

6. **Fixture coverage is adequate for this bridge.** Checks expose both definitions and all three theorems, print their axiom profiles, exercise the quotient identity with a zero score at `J = 0`, exercise both inequalities with the one score at `J = 0`, and exercise both branches of a symbolic nonnegative equality-indicator score at `J = 2`, `T = 4`. The fixtures supplement the general theorem signatures; they are not being used as evidence in place of the universal proofs. A separate nontrivial-`J` fixture for the quotient identity would be optional and would not materially increase assurance.

## Manuscript and dependency boundary

This increment formalizes the generic finite-space conditioning calculation needed by the manuscript: conditioning a nonnegative score on legitimate ordered tagged questions costs at most `4/3`, hence at most `2`. It supports the numerical claims at manuscript lines 1129-1134 and the first sentence of lines 1154-1155.

It does **not** establish the manuscript's remaining claims at lines 1148-1164:

- that the relevant bad mass is at most `tau/100` rather than only `1/4`;
- that ordered tagged tuples push forward uniformly to the intended legitimate subset/subspace distribution;
- that each clique-resampled `U'_i` is uniform on legitimate `U`;
- the equivalence-class stationarity and equal-transverse-extension assertion;
- that the concrete failure indicator/score has the required unconditioned expectation;
- the `(m+1)J` union bound or the final `tau/75` arithmetic;
- actual-star acceptance, the randomized reduction, or the headline hardness theorem.

The next consumer should therefore be the ordered-tuple-to-subset transport theorem with its exact constant-fibre statement, followed by the concrete clique/star stationarity bridge. No claim of conditioned base uniformity follows from the theorem reviewed here.

## Disposition

**GO-WITH-NOTES.** Accept these three theorems as the canonical conditioning-multiplier obligation. The proofs are kernel-checked, assumption-preserving, and mathematically correct. Keep the integration boundaries above explicit in the obligation ledger so this result is not mistaken for the sampler-marginal or full completeness argument.
