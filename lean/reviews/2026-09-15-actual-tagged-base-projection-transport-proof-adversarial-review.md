# Proof-adversarial review: actual tagged base-projection transport

Date: 2026-09-15  
Verdict: **GO-WITH-NOTES**

## Frozen review target

- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedBaseProjectionTransport.lean`
  - expected SHA-256: `A90C2EFB35D40A278F80E873720B8C8181D2CC05F08EBB1A1AED8BBA2584A2E0`
  - independently observed SHA-256: `A90C2EFB35D40A278F80E873720B8C8181D2CC05F08EBB1A1AED8BBA2584A2E0`
- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedBaseProjectionTransportChecks.lean`
  - expected SHA-256: `795FF7E76726BAB026203245C4FA91272B3D7095D6F1C974F47D7BE7106184B4`
  - independently observed SHA-256: `795FF7E76726BAB026203245C4FA91272B3D7095D6F1C974F47D7BE7106184B4`
- Certification directory: `research/evidence/2026-09-15-actual-tagged-base-projection-transport-fresh-run/`
  - expected artifact-manifest SHA-256: `5651FFAA82FD899C148AF63228C1478EF176FDBC4DDA97EEAAA78650F4779D71`
  - independently observed artifact-manifest SHA-256: `5651FFAA82FD899C148AF63228C1478EF176FDBC4DDA97EEAAA78650F4779D71`
  - all 25 manifest entries were independently rehashed and matched their recorded sizes and SHA-256 values.

## Findings

1. **The tagged-to-base uniform-mean identity is mathematically sound.** `taggedTupleEquiv` is a bijection from an ordered tagged tuple `u : Fin J -> Fin K x I.RowId` to the pair consisting of its tag assignment and base-row assignment. Under this equivalence, `g (baseProjection u)` depends only on the second coordinate. `Fintype.sum_equiv`, followed by the product-sum identity, therefore gives

   `sum_u g (baseProjection u) = card (Fin J -> Fin K) * sum_q g q`.

   `taggedTuple_card` gives the matching denominator factorization. The proof cancels exactly the tag-assignment cardinality; it does not assume the desired equality or smuggle in a distributional hypothesis.

2. **The cancellation hypothesis is sufficient and handles the edge cases correctly.** `hK : 0 < K` constructs a tag assignment and proves `0 < card (Fin J -> Fin K)`, so cancellation in `Real` is valid. This remains true at `J = 0`, where the function type has one element. No positivity assumption on `rowCount` is needed for the first theorem: if the base function space is empty, Lean's zero-division convention makes both sides zero after cancellation of the nonzero tag factor. Conversely, allowing `K = 0` with `J > 0` would make the tagged domain empty while the base domain can remain nonempty, so the stated `K > 0` guard is substantively appropriate.

3. **The conditioned base-projection bound composes the right compiled bridges.** `actualTaggedGoodMean_baseProjection_le_four_thirds` applies the already certified nonnegative-score conditioning theorem to `f u = g (baseProjection u)`, discharging pointwise nonnegativity from `hg`, and rewrites its unconditioned tagged mean with the exact identity above. Its assumptions are exactly `hT : 4 <= T`, `hrows : 0 < rowCount`, and nonnegativity of `g`. It adds no normalization, boundedness, independence, stationarity, or uniformity-after-conditioning assumption.

4. **No weakening or forbidden proof mechanism was found.** `set_option autoImplicit false` blocks undeclared implicit variables. Direct source inspection found no `sorry`, `admit`, `native_decide`, explicit `axiom`, or `unsafe` declaration in either frozen source. Both `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`, the standard Lean/Mathlib classical quotient profile. No new or user-defined axiom appears.

5. **The certification receipt is coherent and appropriately scoped.** Main and Checks both report exit code 0, with frozen sources unchanged before and after compilation. The target contained neither reviewed object before compilation. The certified objects independently rehash to:
   - main: `0C30FA64D1B31F490152AB13A824630B9E877E239578E976EA951409ABE9E379`;
   - Checks: `1D1FBD1606FB7DEAFA5CED671FB55C02582837BD5653DDA3BDC48D111953BD59`.

   The run used Lean `4.34.0-rc2`, one thread, and a fresh target seeded with hashed dependency objects while explicitly excluding both target objects. This is a target-fresh main-and-Checks certification, not a rebuild of all dependencies from source. The only compiler messages are two nonsemantic linter warnings about an unused simp argument and an unnecessarily broad sequencing combinator.

6. **The fixtures cover the relevant structural branches.** Checks expose and print the axiom profiles of both public theorems. The `J = 0` fixture exercises the empty-coordinate function space. The two-row fixture proves both branches of a nonconstant equality-indicator score and instantiates the conditioned theorem at `J = 2`, `T = 4`, with nonnegativity proved branchwise. These fixtures support the universal proofs rather than replacing them. They do not compute an independent numerical tagged mean, but that would be redundant with the general bijection and sum proof.

## Manuscript and dependency boundary

This increment formalizes the first distributional transport needed in manuscript lines 1137-1164: before conditioning, forgetting independently uniform copy tags sends the uniform ordered tagged-tuple mean exactly to the uniform ordered base-row mean. Combined with the retained-mass conditioning bridge, it proves that the good tagged mean of any nonnegative base score is at most `4/3` times its uniform ordered base mean. This rigorously supports the conditioning-cost portion of lines 1148-1155 for the initial ordered tagged question.

It does **not** prove the rest of lines 1148-1164:

- that bad mass is at most the manuscript's `tau/100` branch rather than the formalized `1/4` branch;
- that conditioning preserves a uniform base projection (it generally does not, and the theorem correctly supplies only an inequality);
- a pushforward from ordered tuples to unordered subsets or subspaces, including the required constant `J!` fibre law;
- that clique resampling preserves the uniform legitimate-question measure;
- the equivalence-class stationarity or equal-transverse-extension assertion;
- that the concrete equation-failure score has unconditioned mean at most `J * epsilon_1`;
- the `(m+1)J` union bound, `tau/75` arithmetic, actual-star acceptance, randomized reduction, or headline hardness theorem.

The immediate consumer should be an ordered-tuple-to-subset transport theorem that states and proves the precise constant-fibre condition. The next high-risk obligation after that remains the concrete clique/star transition kernel and its stationarity proof.

## Disposition

**GO-WITH-NOTES.** Accept both theorems as the canonical tagged-to-base ordered-mean transport obligation. Their statements are assumption-preserving, their proofs are kernel-checked and algebraically correct, and the certification artifacts are internally consistent. Keep the boundary above explicit in the obligation ledger: this result bounds the conditioned base score, but it does not establish conditioned base uniformity, unordered-question uniformity, or clique-resampling stationarity.
