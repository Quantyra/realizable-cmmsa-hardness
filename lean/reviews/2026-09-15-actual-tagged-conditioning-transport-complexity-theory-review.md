# Actual tagged conditioning transport: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for the S3138 conditioning bridge  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment correctly proves the finite conditional-expectation identity and the manuscript's constant-factor conditioning inequality on the actual tagged **ordered-tuple** carrier. For every nonnegative real score `f`, a nonempty actual source (`0 < m`), and `T >= 4`, it proves

```text
E_uniform-good[f]
  = E_uniform[1_G f] / Pr_uniform[G]
  <= (4/3) E_uniform[f]
  <= 2 E_uniform[f].
```

Here the ambient sample space is exactly

```text
Fin J -> Fin (actualPaddingCopies J T) x I.RowId,
```

sampled uniformly with replacement, and `G` is `GoodOrderedQuestion` for the support of the tagged copy of the actual occurrence source. Thus the result closes the numerical conditioning-multiplier obligation used in the manuscript at lines 1129-1134 and 1154-1155 whenever the failure score is defined on this same ordered tagged space.

It does not yet identify this law with the manuscript's uniform legitimate query-set law, prove the clique-resampled marginals, or instantiate the concrete star failure score. Those are force-bearing downstream bridges. The result is therefore acceptable as a completed local obligation, while S3138 and the headline route remain active.

## Frozen artifacts and independent evidence check

| Artifact | Independently observed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedConditioningTransport.lean` | `4C4D97A764ADD32F54806830B42460169DBFF69A5FFBCD3D5AD5E2DECE06C284` | Matches the assigned frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedConditioningTransportChecks.lean` | `1ECD3F99C5E3C31B9910588ADC344B2FC0570B2815DE14628223C0A1DD0AF61E` | Matches the assigned frozen Checks source. |
| `research/evidence/2026-09-15-actual-tagged-conditioning-transport-fresh-run/artifact-hashes.txt` | `8AB7CDBE388B62A358EF06AD052FEE35CA98B6E8EA539145A7938DD03F4D9BD9` | Matches the assigned certification-manifest payload hash. |
| `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md` | `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240` | Manuscript version compared, especially lines 1123-1174. |

All 24 entries in `artifact-hashes.txt` were independently rehashed and matched their recorded lengths and hashes. The receipt records source stability, absent preexisting target objects, and direct Lean exit codes `0/0` for main and Checks. The fresh object hashes are `78082F14478AE65D23D22A99877EABD6EC1F9BB23C569373F41D7FF2A252E26C` and `72AF400B84A10F7E230DED81F53F46E89D79840F57CCFD8E212E179D50746243`. This is a target-fresh main-and-Checks build against a copied and hashed dependency target; it is not a from-source rebuild of the entire dependency graph.

The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and explicit user axioms. The printed axiom profile contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact mathematical content

`actualTaggedUniformMean` is the normalized sum over the full ordered tagged carrier. `actualTaggedGoodMean` is the normalized sum over its good finset. The quotient theorem proves the elementary but necessary equality

```text
sum_G f / |G| = (sum_U (if G then f else 0) / |U|) / (|G| / |U|).
```

Its denominator obligations are real rather than artifacts of totalized division: positivity of the tagged carrier follows from `0 < m` and positive padding copies, and positivity of the good set follows from the previously certified lower bound `Pr[G] >= 3/4`.

The `4/3` theorem then combines three valid facts:

- `1 / Pr[G] <= 4/3`;
- the gated mean is nonnegative for nonnegative `f`;
- pointwise `1_G f <= f`, hence the gated uniform mean is at most the full uniform mean.

No independence, boundedness, or Boolean-valued premise is silently used. Consequently the theorem applies to failure indicators, acceptance scores, and sums of nonnegative local failure indicators. The factor-two theorem is a direct weaker corollary because the uniform mean is nonnegative and `4/3 <= 2`.

The Checks file exposes both definitions and all three theorem signatures, prints their axiom profiles, and exercises zero/one scores at `J = 0` plus a nonconstant nonnegative equality-indicator score at `J = 2`, `T = 4`. The universal proofs, rather than the fixtures, supply the substantive coverage.

## Match to the manuscript conditioning step

The manuscript uses `a` for the discarded illegitimate mass and claims that conditioning multiplies a failure probability by at most `1/(1-a)`, with a factor-two allowance. On the Lean carrier,

```text
a = actualTaggedBadMass I K J,
Pr[G] = actualTaggedGoodMass I K J = 1 - a.
```

The preceding retained-mass module proves this complement identity and `Pr[G] >= 3/4`. The reviewed quotient theorem realizes division by `Pr[G]`, and the reviewed score inequality gives the stronger multiplier `4/3`. This exactly discharges the arithmetic and finite-expectation part of the manuscript step for a score on ordered tagged tuples.

The match stops at that interface. The manuscript's star sampler is described in terms of legitimate query objects and then uniform representatives from leaf equivalence classes. The current Lean score domain is an ordered function space. Although `GoodOrderedQuestion` includes injectivity and the support-side legitimacy predicate, the reviewed module does not prove that forgetting order has constant `J!` fibres or that goodness is permutation invariant. Those facts are needed to transport uniform conditioned ordered tuples to uniform legitimate tagged subsets.

Conditioning also does not make the projection to uncopied base-row tuples uniform. Different base tuples can admit different numbers of good tag assignments because their position-conflict graphs can differ. Any downstream argument that calls this projected distribution uniform would be incorrect. The sound route keeps the tagged carrier through the score comparison, or proves a separate weighted pushforward theorem appropriate to the actual consumer.

## Remaining route to the source, star, and headline theorem

The immediate next obligation is an ordered-to-subset transport theorem. It should prove permutation invariance of `GoodOrderedQuestion`, the exact `J!` fibre cardinality for each legitimate tagged `J`-subset, and equality between the pushforward of the conditioned ordered law and the uniform legitimate-subset law. This is the direct consumer of the reviewed result.

The next high-risk obligation is the actual clique/star kernel. It must define the concrete finite state spaces and equivalence relation, prove that uniform resampling within an equivalence class preserves the required legitimate-query marginal, and justify the equal-count claims for transverse extensions. The current theorem supplies no stationarity or coupling property.

Completeness then needs a concrete nonnegative failure score, its unconditioned expectation from the actual source error, the `(m+1)J` union bound, and the final arithmetic

```text
(m+1) J epsilon_1 / (1-a) <= tau/75 < tau.
```

The padding route also still needs the positive-`tau` choice of `T` proving `1/T <= tau/100`, rather than only the `T >= 4` quarter bound. The quantifier order must match the manuscript: the fixed PCP parameters precede the desired positive constant `tau`, and then `T` and the constant copy count are chosen independently of input length.

After those semantic bridges, the route still requires the actual-star acceptance theorem, encoded source and sampler implementation with polynomial size and runtime, the headline randomized-reduction assembly, quantitative lemmas consumed by that skeleton, the learning corollary, and manuscript reconciliation. None of those conclusions follows from this local conditioning theorem.

## Claim boundary and disposition

The defensible claim is:

> Lean verifies that uniform conditioning on good ordered questions in the padded actual tagged source sends every nonnegative real score to at most `4/3`, and therefore at most `2`, times its unconditioned uniform mean.

Do not strengthen this to uniformity after projection to base tuples, uniformity on legitimate subsets before the constant-fibre bridge is proved, clique-resampling stationarity, the `tau/100` padding choice, actual-star completeness or soundness, a polynomial-time randomized reduction, the headline hardness theorem, P versus NP, novelty, or publication readiness.

**GO-WITH-NOTES.** Accept the quotient identity and the `4/3` and factor-two inequalities as the canonical completed conditioning-multiplier obligation. Keep ordered-to-subset transport, concrete clique/star stationarity, score instantiation, and final reduction assembly open in the dependency ledger.
