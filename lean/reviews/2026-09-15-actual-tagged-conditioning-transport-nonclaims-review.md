# Actual tagged conditioning transport: non-claims-boundary review

2026-09-15. Top-level read-only review of the frozen `ActualTaggedConditioningTransport` main and Checks modules, their target-fresh certification evidence, and the corresponding manuscript implications. No Lean source, certification artifact, commit, push, release, or public claim was changed. This review file is the only artifact written by this lens.

## Verdict

**GO-WITH-NOTES.** The frozen increment proves an exact quotient identity and two valid upper bounds for real-valued nonnegative scores on the full finite space of ordered independently tagged row tuples. Under `4 <= T` and `0 < m`, the uniform mean over good tuples is at most `4/3` times, and hence at most twice, the uniform mean over all tagged tuples.

This is a genuine finite conditioning-score inequality. For an indicator score it specializes mathematically to the usual event bound under conditioning on the good set. It does not identify the score with a manuscript failure event, prove the unconditioned manuscript failure estimate, preserve uniformity of the base-row projection after conditioning, transport the ordered law to unordered questions, prove clique-resampling stationarity or actual-star acceptance, instantiate source hardness, assemble a randomized reduction, establish NP-hardness, or imply `P = NP` or `P != NP`.

## Frozen artifacts and certification scope

| Artifact | SHA-256 | Review result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedConditioningTransport.lean` | `4C4D97A764ADD32F54806830B42460169DBFF69A5FFBCD3D5AD5E2DECE06C284` | Matches the routed freeze and certification source snapshots. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedConditioningTransportChecks.lean` | `1ECD3F99C5E3C31B9910588ADC344B2FC0570B2815DE14628223C0A1DD0AF61E` | Matches the routed freeze and certification source snapshots. |
| `research/evidence/2026-09-15-actual-tagged-conditioning-transport-fresh-run/artifact-hashes.txt` | `8AB7CDBE388B62A358EF06AD052FEE35CA98B6E8EA539145A7938DD03F4D9BD9` | Matches `artifact-hashes-manifest.sha256`. |

The evidence reports stable before/after source hashes and exit code `0` for both main and Checks. The fresh objects have SHA-256 values `78082F14478AE65D23D22A99877EABD6EC1F9BB23C569373F41D7FF2A252E26C` and `72AF400B84A10F7E230DED81F53F46E89D79840F57CCFD8E212E179D50746243`. The forbidden scan found no `sorry`, `admit`, `native_decide`, or explicit source-level `axiom`. The five printed axiom profiles contain only `propext`, `Classical.choice`, and `Quot.sound`, with no project-specific axiom.

The certification directly compiled the two frozen modules with Lean `4.34.0-rc2` into a new target, seeded from the certified retained-mass target while excluding preexisting conditioning-transport objects. This is target-fresh main-and-Checks evidence against the recorded immutable dependency seed. It is not a full source rebuild of every transitive dependency.

The canonical manuscript inspected for claim comparison is `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`.

## Exact theorem boundary

The module defines

```text
actualTaggedUniformMean I K J f
```

as the real sum of `f` over the full function space

```text
Fin J -> Fin K × I.RowId
```

divided by that space's cardinality. It defines

```text
actualTaggedGoodMean I K J f
```

as the real sum over `actualTaggedGoodQuestions I K J` divided by the good set's cardinality.

For `K = actualPaddingCopies J T`, `4 <= T`, and `0 < m`, the imported retained-mass theorems ensure both denominators used in the proof are positive. Under those premises, the increment proves:

1. `actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass`: the good-set mean equals the full-space mean of the score gated to good tuples, divided by good mass.
2. `actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg`: for every pointwise nonnegative real score `f`, the good-set mean is at most `4/3` times its full-space mean.
3. `actualTaggedGoodMean_le_two_mul_uniformMean_of_nonneg`: the manuscript-facing weaker factor-two consequence.

The inequality does not require `f <= 1`; it is valid for every nonnegative real score. Consequently it can later be applied to an indicator, failure probability represented as a nonnegative score, or a bounded loss once the corresponding score and law are connected to this exact tagged-tuple space.

The definitions themselves accept arbitrary `K`, `J`, and `m`. Because real division is totalized, `actualTaggedGoodMean` is syntactically defined even when the good set is empty. It should be called a conditional mean only at theorem sites that establish positive good cardinality, as this increment does under `4 <= T` and `0 < m`.

## Conditioning versus distribution transport

The factor-two theorem formalizes the normalization loss in manuscript lines 1130--1132 and the abstract inequality behind line 1154, but only for the full ordered tagged-tuple law and an arbitrary nonnegative score already expressed on that law. It does not prove every distributional statement in lines 1148--1164.

In particular, the conditioned base-row projection need not be uniform merely because the unconditioned tagged tuple is uniform. Goodness depends on the selected rows and tags, so different base tuples can have different numbers of good tag lifts. The current theorem avoids asserting otherwise: for a base-dependent score, it bounds its conditioned good mean by its unconditioned tagged mean times `4/3`. A separate compiled equal-fibre or product-law theorem must identify that unconditioned tagged mean with the intended uniform base-row mean before the manuscript failure bound can consume it.

Similarly, `actualTaggedGoodQuestions` is a set of ordered functions. Nothing in this increment proves that forgetting order yields the manuscript's legitimate unordered question law, that every target question has the same `J!` fibre, or that the quotient map preserves the required mean. Those facts belong in the planned ordered-to-subset transport bridge.

The module also contains no clique equivalence relation, clique-resampling kernel, stationary measure, transverse-extension count, or star experiment. It therefore does not prove the manuscript assertion at lines 1155--1158 that each clique-resampled `U'_i` has the required uniform legitimate marginal. That is a separate, higher-risk consumer after ordered-to-subset transport.

## Manuscript implications

The strongest manuscript-compatible statement supported now is:

> On the semantic actual-source space of ordered independently tagged row tuples, with `K = 1 + T * 157 J(J-1)`, `T >= 4`, and a nonempty original row list, Lean proves that restricting a nonnegative real score to legitimate tuples increases its uniform mean by at most a factor `4/3`, and therefore by less than the manuscript's allowed factor two.

This wording must retain “ordered independently tagged row tuples,” the nonnegative-score scope, and the stated parameter premises. It should not be shortened to “conditioning preserves uniformity” or “the conditioned sampler is uniform,” because neither statement is proved.

The manuscript's completeness calculation at lines 1137--1164 still requires a separate choice of `T` from positive `tau` proving bad mass at most `tau/100` as well as `1/4`; a connection from each original-equation failure score to the unconditioned uniform tagged mean; the law of every resampled `U'_i`; and the union-bound assembly over all `(m+1)J` queried equations. The present factor bound supplies one algebraic input to that chain and does not discharge the chain.

The soundness sentence at lines 1129--1132 may use the factor-two corollary only after the relevant decoded-success or failure score has been represented on this same finite law and all preceding source/star distribution bridges are proved. This module alone does not certify modified-PCP soundness.

## Names and checks

The names `actualTaggedUniformMean` and `actualTaggedGoodMean` accurately identify the domain as actual-source tagged tuples, but “good mean” should be documented as a finite good-set average rather than a constructed probabilistic sampler. `actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass` accurately exposes the normalization identity. The two inequality names explicitly state the nonnegativity condition and their constants, so they do not overclaim uniformity, stationarity, or source hardness.

The Checks module confirms the exact signatures and axiom profiles and includes zero- and one-score examples at `J = 0`, plus a nonconstant nonnegative score at `J = 2`, `T = 4`. These are useful elaboration fixtures for the quotient and both inequalities. They do not verify a conditioned base-row marginal, an ordered-to-subset fibre law, clique stationarity, an actual-star sampler, or any reduction-level property.

## Remaining dependency path

The next direct consumer should be the ordered-to-subset transport theorem, with the exact constant-fibre law and mean transfer stated over the manuscript's legitimate question representation. The remaining claim-facing path is:

```text
conditioned nonnegative-score bound on ordered tagged tuples  [this increment]
  -> unconditioned tagged/base score identification
  -> ordered-to-subset constant-fibre transport
  -> concrete clique equivalence and resampling stationarity
  -> actual-star marginal and acceptance theorem
  -> positive-tau parameter choice and completeness union bound
  -> source-hardness instantiation
  -> encoded polynomial-time randomized-reduction assembly
  -> fixed-parameter NP-hardness theorem
  -> learning corollary and manuscript reconciliation
```

The encoded source producer, its size/runtime proof, and exact source-value connection also remain obligations in the source-preserving padding story. A semantic finite mean does not by itself provide an executable rejection sampler or a polynomial runtime theorem.

## Prohibited claim promotion

Do not describe this increment as proving conditioned base uniformity, the unordered legitimate-question law, clique-resampling stationarity, actual-star acceptance, the complete actual-source bridge, source hardness, the randomized reduction, NP-hardness of the manuscript target, manuscript correctness, novelty, publication readiness, `P = NP`, or `P != NP`.

It is accurate to record the ordered tagged-tuple conditioning-score inequality as completed, with the frozen hashes, target-fresh build receipt, and three-lens review table. The route and headline claims must remain open.

