# Non-claims review: SourceSize material and dyadic Spectral47 discharge candidate

**This is not final acceptance and there is no overall GO.** I used no tools, wrote no files, ran no Lean or Lake, and used no subagents. I did not recompute any SHA-256; every hash and status below is copied from the packet. Both new candidate files are uncompiled. Reading the source closely and reconstructing types by hand is not kernel evidence.

## Verdicts

| Question | Verdict |
|---|---|
| **Does the composition hold mathematically?** | **Yes.** Each candidate theorem takes an existing SourceSize consumer and fills its `hSpectral` premise with the universal inhabitant. Nothing else changes. The mathematics therefore rests entirely on that inhabitant (`spectral47_exact_contract_inhabitant`), which the prior three reviews found sufficient. |
| **Do the signatures match exactly?** | **Yes, by text comparison.** I compared both theorems against the complete original bodies 22DE… and AF3E…. The only differences are the theorem name and the removed `hSpectral` binder. Argument order, every remaining premise, and every conclusion match. This agrees with the static derivation. I did not recompute its type hashes. |
| **Is any legacy material consumer used?** | **No.** Both calls go into the SourceSize lane, which uses `Instance N rows`. The legacy contract appears only as the domain of the native `Iff.rfl` bridge. |
| **Will it elaborate?** | **Probably not as written.** There is a likely parse error (F1): qualified identifiers are split across a line break after a trailing dot. This is mathematically harmless and quick to repair. |
| **Is it native-ready?** | **No.** Both new files are uncompiled. They depend on the frozen Full101 inhabitant chain, which is also uncompiled, and GCP authentication is still pending. |
| **Is it manuscript- or final-ready?** | **No.** The exact eigenvalue/operator work, scalar/source/runtime/upstream debt, R14 HIGH, numeric NO, and the citation/PDF/publication gates all remain open. |

## 1. Coverage

**Freshly reviewed in full:**
- `ActualSelectedComplementSourceSizeSpectralApplication.lean` (5BF441CD…)
- `…SpectralApplicationChecks.lean` (448189FE…)
- the static derivation JSON
- the re-supplied captured bridge (022E14E6…)

**Re-consulted for the crosswalk (reused by identity, not freshly re-reviewed):**
- the complete signatures and proof bodies of `SourceSizeOriginalApplication.selected_actual_material_moment_bound_original` (22DE…) and `ManuscriptDyadicMoment.selected_actual_material_moment_bound_original_at_dyadic_exponent` (AF3E…), including the inner `…_at_dyadic_exponent`
- the SourceSize and legacy `Spectral47ExactContract` definitions
- the SourceSize `selected_actual_material_moment_bound`
- the inhabitant body
- the Full100 native report profiles

**Reused without re-review:** the remaining 41 prior bodies (33 + 8). Prior full-body reviews are reused only to the extent they actually covered those bodies.

**Not claimed:** fresh coverage of all 343 or 340 sources, or of the whole manuscript.

## 2. Findings

| # | Severity | Finding and evidence | Disposition and action |
|---|---|---|---|
| **F1** | **HIGH (elaboration; blocks compile)** | Four qualified names are broken across a newline after a dot, for example `…ActualFiniteAppendSpectral47ExactInhabitant.⏎ spectral47_exact_contract_inhabitant`. Two are in the main file and two are in the Checks file, including `…SourceSizeAnalyticMoment.⏎ Spectral47ExactContract`. In Lean 4 an identifier continues past `.` only when the next character can start an identifier. Projection and dot-ident notation both reject whitespace after the dot. So these are very likely parse errors. Nothing comparable appears in the natively compiled callers. | Put each qualified name on one line, or `open` the namespace and use the short name. This file is a new candidate, not frozen Full101, so repairing it is allowed. After the repair, re-hash both files and redo the static type reconstruction. If you prefer, compile once first to confirm the diagnosis. |
| **F2** | Resolved (composition) | **Argument order.** The original explicit arguments are `I copies U A C T f base sourceHeightCutoff hsel hA r hrd e he hfail hSpectral a ha`. The dyadic version adds `hkDyadic hkm`. The candidate passes exactly this sequence, with the spectral term in the `hSpectral` slot. **Implicit arguments.** The implicits `{N rows m L samplerA (k)}` are fixed by `I`, `U`, `hkDyadic` and the expected type. **Spectral term.** `(spectral47_contract_iff c).mp (inhabitant c)` turns the legacy-typed inhabitant into the SourceSize contract. **Conclusions.** The let-telescopes match, including the fixed window `∃ k q, k=2^q ∧ 4m≤k ∧ k<8m` in the first theorem and the caller-chosen `k` with `;` in the dyadic one. | None. The bridge is technically redundant, since `Iff.rfl` means the two contracts are definitionally equal. Keeping it explicit is still right, because it records which lane is used. |
| **F3** | Resolved (namespace) | The candidate opens the same 12 namespaces as the natively compiled dyadic file, only in a different order. The new imports (the Full101 chain, legacy, the bridge) declare names only inside namespaces the candidate does not open. Unqualified names therefore resolve as they do in a file that has already passed native compilation. | Confirm by compiling. |
| **F4** | LOW–MEDIUM (elaboration) | `exact` needs the candidate's statement to be definitionally equal to the original's. That includes the `Decidable` instance in `if centerMatchBit … then` and the `Fintype` instance in the Grass sums. Both originals and the candidate declare `attribute [local instance] Classical.propDecidable`, so the same instance should be chosen. If it is not, `Classical.propDecidable` does not reduce, and the mismatch would surface as an `exact` failure. | Compile. If it fails, reuse the original statement with `@`-explicit instances, or state the theorem through `type_of%`. |
| **F5** | MEDIUM (native dependency) | The proof is only as sound as the frozen Full101 inhabitant chain (11 modules, uncompiled). That chain also carries unresolved earlier risks: decidability instances, `cast`/`HEq`, `field_simp` closures, and unused-binder warnings in `spectral47_exact_contract_inhabitant`. The HC46 side is natively covered: the Full100 profile of `…SourceSizeOriginalApplication.selected_actual_material_moment_bound_original` is `{Classical.choice, Quot.sound, propext}`, and that profile transitively includes `original_HC46_exact`. | Order of work: compile frozen Full101 exactly as captured, then compile this candidate as a separate capture. Do not edit Full101 to suit this candidate. |
| **F6** | MEDIUM (check coverage) | The Checks file `#check`s both theorems and prints their axioms, which transitively covers the inhabitant. Its SourceSize-shaped `example` has no name, so its axioms cannot be printed. Nothing in the file checks mechanically that each candidate's type equals the original's type with only the spectral premise removed. | Add three things. (a) A named `theorem sourceSize_spectral47_inhabited : SourceSize.Spectral47ExactContract c := …` with `#print axioms`. (b) `#print axioms spectral47_exact_contract_inhabitant`. (c) Equality checks: `example : (type of candidate) = (∀…, original type with hSpectral instantiated)` or an equivalent `Iff`/`rfl` check. The gate must require exactly `{propext, Classical.choice, Quot.sound}` with no `sorryAx`. Count owned warnings separately. |
| **F7** | **HIGH (claims boundary)** | Once compiled, this candidate is the first SourceSize material statement with **both** HC46 and Spectral47 discharged. **Still open premises:** `hsel` (selector/height floor), `hA`, `r` with `hrd`, `e ≥ 0`, `hfail` (failed-zoom on the same coordinate leaf table), `a > 0`, and in the dyadic version `hkDyadic` and `4m ≤ k`. **Conclusion:** star-mass ≤ 2 × `selected_actual_analytic_rhs`, which still contains the weaker `+3·2^(i−n)` high-level factors, plus the center identity. It is not numeric NO. It is not a source or table witness, a runtime, or the manuscript's inverse contradiction. **Window mismatch:** the fixed-window theorem (4m ≤ k < 8m) does not in general reach the manuscript's P ≥ mT; only the dyadic theorem does. **Guards:** the height, parity, ρ, split and ambient guards are still produced inside the consumers (`selected_spectral_parameters`, `hdim`) and still passed to the contract. The inhabitant does not use them, which is legitimate strengthening. | State this in exactly these words. Do not call the theorems "manuscript Spectral47 verified" or "source completion". The exact eigenvalue and the G/Φ/adjoint equalities are not needed by the consumer and remain manuscript debt. Supersede, but do not cite as an application, the earlier legacy wrapper `ActualSelectedComplementSpectral47OriginalApplication`. |
| **F8** | MEDIUM (inventory) | **Load-bearing bodies that were never supplied:** `ActualBinaryMatrixHC46OriginalExactInhabitant`, `…SourceSizeAppendMoment` (mass bound, center identity, `hsmall`), `ActualSelectedSpectralParameters`, `ActualLeafLabelRankImageAlignment`, `MatrixGrassmannIdentity`, `ActualFixedFunctionalStarMoment`, `ActualComplementCoordinateMassBridge`, `ActualOrdinaryStarWeightedSelection`, `ActualTagged*`, `ActualCmmsa*`, `ActualStarFixedRhoDimensionGuard`, `SamplerParameters`, `ActualMaximalPairLadder`, and `ActualRankImageRightBasisInvariance`. **Reuse limits:** reusing earlier exact-body reviews covers composition validity, because that is pure application and needs no definitions. It cannot vouch for what the conclusions *mean*: the selector, the J/blocks identity, the failed-zoom semantics, or the sampler law behind the mass bound. Those bodies were never reviewed; native compilation of them only certifies their stated types. | Supply these bodies for an independent semantic review before claiming anything beyond composition. |
| **F9** | LOW | The static derivation's "exact_type_reconstruction" and the two type hashes come from static text. They are not elaborated `Expr` hashes. | Treat them as planning evidence only. After compiling, compare against the elaborated types (F6c). |
| **F10** | Carried over, unchanged | These items are untouched by this candidate: M1 citation and version custody (MZ24 version and A-numbering), the natural-to-real λ product identity with its `i ≤ d` guard, native translations of G, Φ, adjoint and kernel-eigenvalue, recovered covariance/orbit duplicates still lacking their own native evidence, and the downstream scalar steps (high part ≤ 2^(−rb), T/P, the signal contradiction, robust local decoding). | Keep open. |

**Evidence tiers:**
- **Native (Full100, 327 sources only):** both consumers, the bridge, HC46 coverage via the consumer profiles.
- **Uncompiled:** Full101 (11 recovered modules within the 340-source capture), the exact-energy candidate, the legacy wrapper and its Checks, and both new files.
- **Prose only:** the exact operator laws.
- **Attribution:** the spectral content is MZ Lemma 4.7 / MZ24 A.10–A.13. The exact λ is our own reconstruction. No novelty is claimed.

## Remaining to-do list

1. Fix F1 by joining the split identifiers, re-hash, and redo the static type reconstruction. Optionally confirm by compiling first.
2. Renew GCP authentication. Natively compile frozen Full101 exactly as captured, collecting its real diagnostics and axiom profiles. Only after that, compile this candidate and its Checks as a separate capture.
3. Extend the Checks file as in F6: a named SourceSize inhabitant with axioms printed, axioms for the inhabitant itself, a type-equality check against the originals with `hSpectral` instantiated, and no `sorryAx`.
4. Trace actual consumption, Spectral47 inhabitant → bridge → SourceSize consumers, and record both the original-HC46 and spectral discharges in one trace.
5. Publish the claims boundary in F7: which premises remain, that the conclusion is a bound and not numeric NO, and that the dyadic theorem is the one compatible with the manuscript.
6. Supply and semantically review the bodies listed in F8.
7. Close or explicitly scope the carried-over items in F10: M1 custody, the λ product identity, the G/Φ/adjoint translations, the duplicate-covariance native evidence, and the downstream scalar and decoder steps.
8. Keep open: numeric NO; source, star, robust8S and pre-draw witnesses; sampling; encoded selection, reduction, runtime and learning; upstream transports; R14 HIGH; warnings and fresh-checkout replay; novelty, citations and PDF; the final provider and QA gates; and publication.
