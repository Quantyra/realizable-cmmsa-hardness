# Complexity review: SourceSize Spectral47 application successor candidates

**This is not final acceptance and not an overall GO.** I used no tools, wrote no files, ran no Lean or Lake, and used no subagents. I recomputed no hashes; every hash and status below is copied from the packet. Both new candidate files are uncompiled, and reading their source is not kernel evidence.

The scope is narrow. It covers the two new candidate bodies and how they actually compose with their consumers. It does not cover all 343 sources or the whole manuscript.

## Verdicts

| Question | Verdict |
|---|---|
| **Does the math follow?** | **Yes.** Each new theorem is the existing native-qualified original consumer with its `hSpectral` premise filled in. The filling is `(spectral47_contract_iff cutoff).mp (spectral47_exact_contract_inhabitant cutoff)`, using the same `sourceHeightCutoff` the selector and analytic floor use. Every other premise and the whole conclusion are copied unchanged. If the Full101 inhabitant is valid, both conclusions hold as stated. |
| **Is the consumer composition right?** | **Yes, statically.** Both theorems go only through the SourceSize-lane consumers (`Instance N rows`). HC46 is supplied inside those consumers by `original_HC46_exact`, and no legacy `Instance N m` material theorem is used. |
| **Will it compile as written?** | **Probably not.** One finding, F1, is HIGH: three identifiers are split across a line break right after a namespace dot, which is very likely a parse error. The candidates also depend on Full101, which is still uncompiled. |
| **Native readiness** | **Not ready.** |
| **Manuscript readiness** | **Not ready.** The exact eigenvalue and G/Φ laws, the scalar steps after the right-hand side, the source/runtime work, R14 HIGH, and the publication gates all remain open. |

## 1. Coverage

**Freshly reviewed in full:**
- `ActualSelectedComplementSourceSizeSpectralApplication.lean` (5BF441CD…)
- `ActualSelectedComplementSourceSizeSpectralApplicationChecks.lean` (448189FE…)
- The static-derivation JSON
- The captured contract bridge (022E14E6…, which is also Full100 native)

**Reused by identity, not re-reviewed (41 bodies).** These are the 33 bodies from packet 7F2CAE47… plus the 8 from the crosswalk round. I re-consulted only the declarations this composition depends on:
- The SourceSize `selected_actual_material_moment_bound_original` (22DE415F…) and the dyadic `…_original_at_dyadic_exponent` (AF3E380A…). Both source hashes match Full100 native identities.
- The SourceSize and legacy `Spectral47ExactContract` definitions.
- `spectral47_exact_contract_inhabitant` (2F8A6758…, Full101 frozen, never launched).

I make no claim of fresh coverage of all 41 bodies, of all 340 sources, or of all 327 native-closure sources.

## 2. Signature and argument-order check

| Item | Original consumer | Candidate | Result |
|---|---|---|---|
| Implicit arguments | `{N rows m L samplerA}`, plus `k` in the dyadic theorem | Same | ✓ The source-row count stays independent of the fixed leaf arity m. |
| Explicit argument order (material) | `I copies U A C T f base sourceHeightCutoff hsel hA r hrd e he hfail hSpectral a ha` | Same order, with `hSpectral` removed from the signature and supplied in the proof | ✓ |
| Explicit argument order (dyadic) | `… hfail hSpectral a ha hkDyadic hkm` | `… hfail ⟨discharged⟩ a ha hkDyadic hkm` | ✓ |
| Shared I/copies/U/A/C/T/f | One lane through mass, centre, failed-zoom and moment | Passed through unchanged | ✓ |
| Selector, height and cutoff | `hsel` with `max (analyticSourceHeightFloor base sourceHeightCutoff j) (j+2)` | Same, and the inhabitant is instantiated at the **same** `sourceHeightCutoff` | ✓ |
| Parity, ρ, split, dimension | Discharged inside the original via `selected_spectral_parameters` and `h² < J` | Not touched | ✓ (that body was not supplied) |
| Failed-zoom guard | `hrd`, `e`, `he`, and `hfail` on `selectedCoordinateLeafTable I copies U A T` | Same | ✓ |
| Positive-parameter guards | `hA : 1 ≤ samplerA`, `a > 0` | Same | ✓ |
| Dyadic guards | `∃ q, k = 2^q`, `4m ≤ k`; fixed window `4m ≤ k < 8m` in the material theorem | Same | ✓ |
| Conclusion | Both conjuncts, including the `let … fc := …;` form in the dyadic theorem | Same text | ✓ by inspection |
| Bridge direction | The inhabitant's type is the legacy contract (it opens the legacy namespace) | `.mp` takes legacy to SourceSize | ✓ (`Iff.rfl`, so it is definitionally equal either way) |
| How names resolve | The original opens the SourceSize namespace | The candidate opens SourceSize; legacy is imported but not opened | ✓ No legacy material, dimension-bound or selected* constants enter the statement. |

**Unchanged premises are still carried, not discharged:** `hsel`, `hA`, `r`/`hrd`, `e`/`he`, `hfail`, `a`/`ha`, and the dyadic guards.

## 3. Findings

| ID | Severity | Evidence | Disposition and action |
|---|---|---|---|
| **F1** | **HIGH (elaboration; probably blocks compilation)** | Three identifiers are broken across a line right after a namespace dot: in the main file, `…ActualFiniteAppendSpectral47ExactInhabitant.⏎ spectral47_exact_contract_inhabitant` (twice); in the Checks file, `…SourceSizeAnalyticMoment.⏎ Spectral47ExactContract` and `…ExactInhabitant.⏎ spectral47_exact_contract_inhabitant`. Lean 4 only extends an identifier across a `.` when an identifier character immediately follows it. Otherwise the `.` becomes a separate token, and both the projection and dot-identifier parsers reject whitespace after it. None of the supplied native-qualified sources splits an identifier this way. | **Expected parse error.** Only a native run can confirm this. **Action:** after Full101 compiles unchanged, issue a separately hashed successor that keeps each full name on one line (or uses `open … in`). Re-derive the static type identity for that successor. Do not edit the frozen Full101 bytes. |
| F2 | MEDIUM (native dependency) | The inhabitant comes from frozen, unlaunched Full101. Its own risks are still open: instance and filter consistency, `cast`/`HEq`, unused-binder warnings. | The candidates cannot be compiled before Full101. Compile Full101 as captured first. |
| F3 | LOW (elaboration) | The original SourceSize file also opens `ActualBinaryMatrixHC46OriginalExactInhabitant`, whose body was not supplied; the candidate does not. Both files declare `attribute [local instance] Classical.propDecidable`, so the `if centerMatchBit …` decidability instances should elaborate the same way. | The match is exact only if that unopened namespace shadows no name used in the statement. A kernel `exact` check will settle it. |
| F4 | LOW (evidence tier) | The static derivation's `exact_type_reconstruction: true` and its type hashes come from text reconstruction, not from compiler output. The two type hashes differ by design because `hSpectral` was removed. | Treat as planning-tier evidence. Optionally add a check that the candidate's type equals the original type with `hSpectral` instantiated. |
| F5 | LOW (claims) | The Checks file `#print axioms` on both consumers. This covers the inhabitant and `original_HC46_exact` transitively. The `example` confirms the bridge output has the SourceSize contract type. | Good design. Require the profile `{propext, Classical.choice, Quot.sound}` with no `sorryAx`, and zero owned warnings. |
| F6 | MEDIUM (scope) | The conclusions still contain `selected_actual_analytic_rhs`, which includes the HC46 constant `2^(500 i² k)` and the high-level sum with the weaker `+3·2^(i−n)` factor. The fixed-window theorem forces `k < 8m`, but the manuscript's `P ≥ mT` may be larger; only the dyadic variant fits. | This is not a numeric NO and not the manuscript's inverse contradiction. Those scalar steps remain to be formalized. |
| F7 | INFO (claims boundary) | Discharging `hSpectral` relies only on the weaker inequality contract. | It is not native evidence for the exact eigenvalue, 𝒢𝒯 = Φ, the restricted adjoint or exact energy. Do not cite it as such. |

## 4. Complexity lens

- **What the candidates are:** pure proof-term composition. Every result is finite existence and counting under classical choice.
- **What they are not:** they contain no algorithm, sampler, encoded witness, selection, reduction, runtime or learning bound.
- **Parameters:** J = `SamplerParameters.blocks samplerA h` and the dyadic k are fixed-parameter quantities. Encoded size and runtime are not addressed.
- **Still open:** removing the spectral oracle does not settle numeric NO, the source/star/robust8S/pre-draw witnesses, physical sampling, upstream transports, or R14 HIGH.

## 5. Missing load-bearing bodies, and whether earlier reviews cover them

| Body | Covered by earlier exact-body review? |
|---|---|
| Full101 inhabitant chain (11 files) | **Reading coverage: yes.** Prior three-lens reviews read them; mathematics found sufficient. **Native coverage: no.** |
| SourceSize Original application and dyadic consumers | **Yes.** Freshly reviewed in the crosswalk round, with hashes matching Full100 native. |
| Contract bridge | **Yes.** Full100 native, and re-read here. |
| `ActualBinaryMatrixHC46OriginalExactInhabitant` (`original_HC46_exact` body and axiom profile) | **No.** Never supplied in any round. |
| `ActualSelectedComplementSourceSizeAppendMoment` (mass bound, centre identity, `hsmall` discharge) | **No.** Never supplied. |
| `ActualSelectedSpectralParameters` (parity, ρ, split, cutoff facts) | **No.** Never supplied. |
| `ActualComplementCoordinateMassBridge`, `ActualLeafLabelRankImageAlignment`, `MatrixGrassmannIdentity`, `ActualFixedFunctionalStarMoment`, `ActualRankImageRightBasisInvariance`, `ActualFiniteMomentLpBounds` | **No.** Never supplied. |
| `ActualCmmsa*`, `ActualTagged*`, `SamplerParameters`, `ActualStarFixedRhoDimensionGuard`, `ActualMaximalPairLadder`, `ActualOccurrenceAllocation`, `ActualSourceStarLaw`, `MatrixLiftNominalDirectComparison` | **No.** Never supplied. |

None of the "No" rows can be covered by reusing earlier reviews, because none of those bodies was ever supplied.

## Remaining to-do list

1. Renew GCP authentication, then compile frozen Full101 exactly as captured. Collect real diagnostics and axiom profiles before any repair.
2. Fix F1 in a new, separately hashed successor with unbroken identifiers. Recompute its static type derivation. Then compile it and the Checks file natively, requiring the standard three-axiom profile, no `sorryAx` and zero owned warnings.
3. After compilation, trace actual consumption: inhabitant → bridge → both SourceSize consumers → `original_HC46_exact`. Confirm that no legacy material theorem appears in the trace.
4. Supply and review the never-supplied bodies listed in §5.
5. Formalize the scalar steps downstream of `selected_actual_analytic_rhs`: high-level sum ≤ 2^(−rb), the choice of T/P bound to the dyadic k, the selection averaging, the ambient bounds and the λ > 0 contradiction.
6. Separately translate the exact eigenvalue, 𝒢, Φ, the restricted adjoint and exact energy. Pin MZ24 versions and lemma numbering.
7. Keep open: numeric NO; source/star/robust8S/pre-draw witnesses; sampling; encoded selection/reduction/runtime/learning; upstream transports; R14 HIGH; warnings and fresh-checkout custody; novelty, citations and PDF; the provider gate and final QA; publication. **No overall GO.**
