# Non-claims delta review: SourceSize Spectral47 application, v1 → v2

**This is a focused delta review. It is not final acceptance, there is no overall GO, and it does not review the whole manuscript.** I used no tools, wrote nothing, ran no Lean or Lake, and used no subagents. I recomputed no SHA-256 values; every hash is copied from the packet.

Both v2 files and Full101 are still uncompiled. Everything below is read from the text. It can close a syntax or composition finding by reading, but it cannot give native acceptance.

## Coverage

**Freshly reviewed:**
- the complete v1 and v2 main files and Checks files;
- both derivation JSONs;
- both complete original consumers (22DE…, AF3E…);
- the captured bridge (022E…);
- the three prior reports;
- the coverage-v2 custody JSON;
- the MZ24 numbering audit.

**Prior coverage, not reread here:**
- the 11 Full101 inhabitant bodies;
- the earlier full-source reviews;
- the 49 bodies enumerated in the custody audit.

## Delta checks

| Check | Result |
|---|---|
| **The four split identifiers** | All four are joined. Main file: `…ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant`, twice. Checks file: `…SourceSizeAnalyticMoment.Spectral47ExactContract` and `…ExactInhabitant.spectral47_exact_contract_inhabitant`. No other qualified name in v2 ends a line with a dot. The only remaining line breaks are after `=` or between arguments, and the natively compiled consumers already break lines that way. (The prior complexity report counted three; there are four.) |
| **Byte deltas** | Both are consistent with exactly these edits, assuming LF line endings. Main file: +365 = 383 bytes for the new theorem and its blank line, minus 2 × 9 for the two joins (newline plus 8 spaces). Checks: +623 = 637 bytes for five `#print axioms` lines, minus 2 × 7 for the joins (newline plus 6 spaces). This only supports, and does not prove, that nothing else changed. |
| **Material and dyadic statements** | Unchanged in meaning from v1, line for line. Compared with the consumers, each one differs only by the rename and the removed `hSpectral` binder. Implicit order, explicit order, all binders, both let-telescopes, the `∃ k q, k = 2^q ∧ 4m ≤ k ∧ k < 8m` window, the dyadic `;` form, and both conjuncts all match. The v2 derivation's type hashes are the same as v1's, which is what you'd expect since only proof terms changed. |
| **Proof applications** | Unchanged apart from the joins. The argument order is `I copies U A C T f base sourceHeightCutoff hsel hA r hrd e he hfail ⟨bridge.mp inhabitant⟩ a ha`, with `hkDyadic hkm` added in the dyadic theorem. The inhabitant is instantiated at the same `sourceHeightCutoff` that the selector and floor use. |
| **Named inhabitant `sourceSize_spectral47_inhabited`** | Correctly typed by reading. Its stated type is the fully qualified SourceSize `Spectral47ExactContract cutoff`. Its body is `(spectral47_contract_iff cutoff).mp (legacy inhabitant)`, which goes legacy → SourceSize, the right direction. The bridge is `Iff.rfl`. The theorem is a Prop-valued `theorem` inside the candidate namespace and noncomputable section, and I see no name clash. |
| **Direct axiom checks** | All five names resolve by transitive import. The Checks file imports the application, which imports the Full101 inhabitant, the bridge, SourceSizeOriginalApplication (and through it the HC46 inhabitant) and the dyadic consumer. |
| **Rows independent of m** | Retained. `{N rows m L samplerA (k)}` with `Instance N rows`. |
| **Shared actual objects** | Retained. The same I, copies, U, A, C, T and f are threaded through, and Cc, Tc and fc are rebuilt only inside the let-blocks. |
| **Caller guards** | All retained: `hsel` (selector with the analytic floor), `hA`, `r`/`hrd`, `e`/`he`, `hfail` (failed zoom on the same `selectedCoordinateLeafTable`), `a`/`ha`, and in the dyadic theorem `hkDyadic` and `hkm`. |
| **Internal guards** | Still derived inside the consumers. In the AF3E body I can see `hm` (from `hm256`), `hsplit`, `hrhoPos`, `hcReal`, `hsReal`, `hcutFloor` (from `selected_spectral_parameters`), and `hdim` (from `h² < J`). They feed `hEven`, `hRho`, `hc`, `hs`, `hHeight` and `hdim`. The fixed-window path's inner `selected_actual_material_moment_bound` body is prior coverage. |

## Findings and dispositions

| ID | Severity | Finding | Disposition |
|---|---|---|---|
| **F1 / P1 / cx-F1** (split identifiers) | was HIGH | All four joins confirmed, and no residual dotted line breaks. | **Closed statically** (syntax and composition). A native parse is still needed to confirm. |
| F2 (composition) | — | Argument order, bridge direction, conclusions and the SourceSize lane are unchanged. No legacy material consumer is used. | **Remains resolved** (static). |
| F3 / cx-F3 (name resolution) | LOW | The candidate does not open the HC46 inhabitant namespace, although SourceSizeOriginalApplication does. The dyadic consumer has identical statement text, uses the same opens, and compiled natively. Prior coverage said the Full101 imports add no names to opened namespaces. | **Open at LOW**, to be settled by kernel elaboration. |
| F4 / P3 (`Decidable`/`Fintype` instance defeq) | LOW–MEDIUM | Unchanged: the same `Classical.propDecidable` local instance applies. | **Open**; kernel `exact` settles it. |
| F5 / P2 (native dependency on Full101) | MEDIUM–HIGH | v2 still imports the uncompiled Full101 inhabitant, and that inhabitant's A1 risks (decidability/filter, cast/HEq, `field_simp`, unused binders) are still open. | **Open.** |
| F6a / F6b / P6 (axiom attribution) | was LOW–MEDIUM | v2 adds `#print axioms` for: the named SourceSize inhabitant, `spectral47_exact_contract_inhabitant`, `original_HC46_exact`, and both consumers. | **Closed statically.** The actual outputs are still missing. |
| F6c (mechanical type-equality check) | — | Not required. The `exact` term kernel-checks the consumer → candidate direction. Fidelity of the binders rests on the text comparison above plus inspecting the `#check` output. No meta-programming is needed. | **Withdrawn as a requirement.** Residual: compare the elaborated `#check` output against the consumer's type with `hSpectral` instantiated. |
| Direct-check adequacy | — | The checks are adequate. The bridge's axioms are not printed, but it is `Iff.rfl` and native in Full100, so this is optional. `#print axioms` does not show consumption, and it says nothing about warnings. | **Adequate.** The gate: every profile ⊆ {propext, Classical.choice, Quot.sound}, no `sorryAx`, and owned warnings counted separately from the build log. |
| F7 / P4 / cx-F6–F7 (claims boundary) | HIGH | Unchanged. Only HC46 and Spectral47 are discharged. All the guards above remain caller premises. The conclusion is still `2 · selected_actual_analytic_rhs`, with the weaker `+3·2^(i−n)` factor. Only the dyadic theorem fits the manuscript's P ≥ mT. This is not numeric NO, not exact eigenvalue/𝒢/Φ/adjoint evidence, and not source or runtime completion. | **Retained.** |
| F8 / P5 / cx §5 ("never-supplied" bodies) | was MEDIUM | The custody audit gives exact per-lens receipts for all 49 enumerated sources. That covers every body earlier flagged as never supplied: `HC46OriginalExactInhabitant`, `SourceSizeAppendMoment`, `SelectedSpectralParameters`, `LeafLabelRankImageAlignment`, `ComplementCoordinateMassBridge`, `OrdinaryStarWeightedSelection`, `RankImageRightBasisInvariance`, `FiniteMomentLpBounds`, `MatrixGrassmannIdentity`, `Cmmsa*`, `Tagged*`, `StarFixedRhoDimensionGuard`, `SamplerParameters`, `MaximalPairLadder`, `OccurrenceAllocation`, `SourceStarLaw` and `MatrixLiftNominalDirectComparison`. Every referenced receipt appears in `verified_receipts`. | **The never-supplied claim is resolved** for these 49 sources at their stated hashes. Any conditional verdicts from those receipts are inherited unchanged. No fresh rereading is claimed, and I am not asking for duplicate reviews. |
| N1 (custody pointer, new) | LOW | The audit does not list the modules whose constants appear in the candidate's statement or opens: `ActualSelectedComplementSourceSizeAnalyticMoment` (`Spectral47ExactContract`, `selected_actual_material_moment_bound`), legacy `ActualSelectedComplementAnalyticMoment`, `ActualFixedFunctionalAppendOperator`, `ActualFixedFunctionalBinaryMatrixMoment`, `ActualAppendFourierCrossLevelOrthogonality`, `BinaryMatrixFourier` and `GrassmannCounting`. Prior rounds say the SourceSize contract and material bound were consulted, but from this packet I cannot tie these sources' hashes to prior receipts. | **Not a re-review demand.** Supply a hash ↔ receipt pointer, from the 41-body set or the reuse audit A9F55FFD…. Only a source with no matching identity is a real gap. |
| F9 / P7 / cx-F4 (text hashes) | LOW | v2 type hashes are textual, as before. | **Retained.** Kernel elaboration is what decides. |
| N2 (manifest, new) | LOW | The v2 derivation does not record the new public declaration `sourceSize_spectral47_inhabited` (its type or type hash). Its `only_type_change` field describes only the two derivations, so it is now incomplete about additions. | **Record it** in the next manifest. Not blocking. |
| N3 (supersession, new) | INFO | v1 cannot parse as written. | **Retire v1.** Keep it for history, but do not compile or cite it. |
| N4 (docstring, new) | INFO | The module docstring is unchanged and does not mention the named theorem. "Retained exactly" is a static claim, and "native contract bridge" refers to the Full100 bridge, not this candidate. | **Acceptable.** Optionally clarify the wording. |
| F10 (carried-over items) | — | M1 custody is partly addressed by the MZ24 v4 source-counter audit: A.10 level-d basis invariant, A.11 adjoint, A.12 φ, A.13 eigenvalue calculations, A.18 preserve-pseudorandom. That audit is a bounded source audit: the PDF numbering is unconfirmed, nothing was natively verified, and no TeX was executed. The λ product identity with its `i ≤ d` guard, the 𝒢/Φ/adjoint/eigenvalue translations, the duplicate-covariance native evidence and the downstream scalar and decoder steps are untouched. | **Retained**, with M1 version and numbering moved to "source-pinned, PDF unconfirmed". |
| R14 | HIGH | Untouched. | **Retained.** |

## Remaining to-do list

1. Renew GCP authentication. Compile frozen Full101 unchanged first and collect its real diagnostics and axiom profiles.
2. Then compile the exact-energy candidate, the earlier selected-leaf application, and these v2 files with their Checks, each as a separate capture. Confirm that the F1 joins parse and that the F3/F4 elaboration risks go away.
3. Record the actual `#print axioms` outputs for all seven names: the two candidates, the named inhabitant, the Full101 inhabitant, `original_HC46_exact` and the two consumers. Require ⊆ {propext, Classical.choice, Quot.sound}, no `sorryAx`, and zero owned warnings.
4. Inspect the elaborated `#check` types of both candidates against the consumers' types with `hSpectral` instantiated (residual of F6c).
5. Produce the actual consumption trace: Full101 inhabitant → bridge `.mp` → the SourceSize material and dyadic consumers → `original_HC46_exact`, with no legacy material consumer.
6. Add the N1 hash ↔ receipt pointers and the N2 manifest record for `sourceSize_spectral47_inhabited`.
7. Publish the F7 claims boundary in exactly those terms, and cite only the dyadic theorem against the manuscript's P ≥ mT.
8. Keep open:
   - inherited conditional findings from the 49 receipted bodies;
   - F10 (PDF confirmation of the MZ24 numbering; λ identity; 𝒢/Φ/adjoint/eigenvalue; scalar and decoder steps);
   - numeric NO;
   - source, star, robust8S and pre-draw witnesses;
   - sampling, encoded selection/reduction, runtime and learning;
   - upstream transports;
   - R14 HIGH;
   - warnings and fresh-checkout custody replay;
   - novelty, citations and PDF;
   - the provider and final QA gates;
   - publication.
