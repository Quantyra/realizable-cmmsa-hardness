# Proof-adversarial delta review, SourceSize Spectral47 application v1 → v2 (not final acceptance)

**Result:** v2 fixes the parse defect I raised as P1, statically. All four split names are now joined correctly, and nothing else in the theorems changed. The new named SourceSize inhabitant and the added direct `#print axioms` checks are correctly typed and adequate. Both v2 files and Full101 are still uncompiled, so none of this is native evidence. There is no overall GO.

I used no tools, writes, Lean/Lake or subagents. I recomputed no SHA-256 values; every hash is copied from the packet. The exact11-body inhabitant proof and the earlier full-source reviews count as prior coverage and were not reread here.

## 1. Delta check, v1 → v2

**Joined names.** All four are now on one line and spelled exactly as in v1:

| Location | Joined name | Result |
|---|---|---|
| Main file, theorem 1 | `PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant` | ✓ |
| Main file, theorem 2 | Same name | ✓ |
| Checks `example`, type | `PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment.Spectral47ExactContract` | ✓ |
| Checks `example`, term | `…ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant` | ✓ |

- **No split names remain.** The other line breaks (for example after `…spectral47_contract_iff`, before `sourceHeightCutoff).mp`) come after a complete name, before its argument. That is ordinary whitespace between a function and its argument.
- **Nothing else changed.** Reading v1 and v2 side by side, the header comment, imports, the 12 `open`s, `autoImplicit`, `noncomputable section`, `Classical.propDecidable`, both signatures, both `let` blocks, both conclusions and the argument order of both `exact` calls are identical.
- **The byte counts agree.** As a plausibility check (not a hash check), I counted bytes by hand, assuming LF line endings and a trailing newline:
  - **Main file:** joining two names removes 2 × 9 = 18 bytes, and the new theorem plus its blank line adds 383. That is +365, which matches 9233 → 9598 exactly.
  - **Checks file:** joining two names removes 2 × 7 = 14 bytes, and the five new `#print axioms` lines add 637. That is +623, which matches 1111 → 1734 exactly.
- **The derivation records the same thing.** Both stated types and their two candidate type hashes are unchanged from v1 to v2, which fits a change to proof terms only.

**Theorem statements unchanged.**
- Rows stay independent of `m`: the implicits are `{N rows m L samplerA (k)}` and the instance is `Instance N rows`.
- The common actual I, copies, U, A, C, T and f are threaded unchanged into one consumer call each.
- All caller guards are retained: `hsel` (with the same `sourceHeightCutoff` used for the inhabitant), `hA`, `r`/`hrd`, `e`/`he`, `hfail` on `selectedCoordinateLeafTable I copies U A T`, and `a`/`ha`.
- In the dyadic theorem, `hkDyadic` and `hkm` are also retained. In the fixed-window theorem, the conclusion still forces `4m ≤ k < 8m`.
- The height, parity/split, ρ and dimension guards are still derived inside the unchanged consumers (via `selected_spectral_parameters` and `h² < J`).
- Both conclusions are unchanged, including the `;` form in the dyadic `let` block.

**Spectral47 term.** In both theorems, `(spectral47_contract_iff sourceHeightCutoff).mp (inhabitant sourceHeightCutoff)` sits in the `hSpectral` slot, as in v1. HC46 is still supplied inside the consumers by `original_HC46_exact`. No legacy material consumer is used.

**Named inhabitant `sourceSize_spectral47_inhabited (cutoff : Real → Nat)`.**
- **Type:** the SourceSize `Spectral47ExactContract cutoff`, written fully qualified.
- **Term:** `.mp` of the bridge, which runs legacy → SourceSize, applied to the Full101 inhabitant. This is the right direction.
- **`theorem` is valid:** the contract appears as a side of an `Iff` in the bridge, so it is a `Prop`.
- **Name resolution:** inside the candidate's namespace, the fully qualified names fall back to root resolution; there are no nested `PvNP.*` namespaces to capture them.

**Direct axiom checks.**
- The Checks file now prints axioms for both new theorems, the named inhabitant, the Full101 inhabitant, `original_HC46_exact`, and both consumers.
- That is enough to attribute every axiom: each new theorem's profile must be a subset of the consumer's profile plus the inhabitant's. The bridge is `Iff.rfl` with a Full100 native profile, so printing it is optional.
- A separate type-equality check is not needed. Elaborating `exact` is itself the kernel check that each stated type is definitionally equal to the consumer's type with `hSpectral` filled in. I withdraw the earlier request for one; no extra meta-programming is required.

## 2. Findings

### New findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| D1 | LOW | The Checks file refers to `PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact`. That full name is inferred from two things: the dyadic file's relative reference `ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact` inside the `PvNP.RealizableHardness.*` namespace, and the module path. The file defining it (6F56EAF2…) is not in this packet. If the name were wrong, only the Checks file would fail, with "unknown constant"; the main file is unaffected. | Open until compiled. The prior receipts for 6F56EAF2… can confirm the namespace. |
| D2 | INFO | The v2 derivation does not record the statement of the new third theorem, and the header comment does not mention it. | Optional: record it in a future static derivation. |
| D3 | INFO | The unnamed `example` duplicates `sourceSize_spectral47_inhabited`. | Harmless; no action. |

### My previous findings

| # | Status | Notes |
|---|---|---|
| P1 (HIGH, parse) | **Closed statically** | All four names joined; see D1 for the one new name to confirm at compile. |
| P2 (HIGH, Full101 native dependency) | Open | Unchanged. |
| P3 (LOW–MED, instance agreement) | Open | Same instance setup as before; the `exact` elaboration will settle it. |
| P4 (MED, claims boundary) | Open | Unchanged: only `hSpectral` is removed; the result is still a bound of 2 · `selected_actual_analytic_rhs`; only the dyadic theorem fits the manuscript's P ≥ mT. |
| P5 (MED, coverage) | **"Never supplied" claim withdrawn** | My statement that these bodies were never supplied was wrong. The custody audit lists prior receipts from all three lenses for every body I named: HC46 inhabitant, AppendMoment, SelectedSpectralParameters, LeafLabelRankImageAlignment, CoordinateMassBridge, CmmsaAdmissibilitySelector, SamplerParameters, StarFixedRhoDimensionGuard. The conditional verdicts from those reviews still apply. |
| P6 (LOW, axiom checks) | **Closed statically** | Native output still required. |
| P7 (LOW, evidence tier) | Open | Text hashes are not elaborated types. |
| P8 (INFO) | Unchanged | No action. |

### Complexity review findings

| # | Status | Notes |
|---|---|---|
| F1 | Closed statically | Same defect as P1. |
| F2 | Open | Full101 native dependency. |
| F3 | Open, LOW | The candidate does not open the HC46 namespace; settled at elaboration. |
| F4 | Open | Evidence tier. |
| F5 | Satisfied and strengthened | v2 adds direct checks for the inhabitant and HC46. |
| F6 | Open | Scope: scalar steps after the right-hand side. |
| F7 | Open | Claims boundary. |
| §5 "No" rows | Resolved as supply claims | Custody audit covers them; conditional verdicts still apply. |

### Non-claims review findings

| # | Status | Notes |
|---|---|---|
| F1 | Closed statically | Same defect as P1. |
| F2, F3 | Still resolved | Composition and namespace, re-confirmed against v2. |
| F4 | Open | Instance agreement. |
| F5 | Open | Full101 native dependency. |
| F6 | Closed statically | (a) and (b) are done. (c) is met by the `exact` elaboration, pending compile. |
| F7 (HIGH, claims boundary) | Open | Unchanged. |
| F8 | Resolved as supply claim | All enumerated bodies map to custody receipts; the semantic conditions still apply. |
| F9 | Open | Text-hash evidence tier. |
| F10 | Carried | Unchanged. |

**Coverage limit, not a demand for new reviews.** The custody audit does not list `ActualSelectedComplementSourceSizeAnalyticMoment`, `ActualFixedFunctionalAppendOperator`, `ActualAppendFourierCrossLevelOrthogonality`, `ActualFixedFunctionalBinaryMatrixMoment`, `BinaryMatrixFourier` or `GrassmannCounting`. No earlier round flagged them as never supplied. They still rest on the earlier 41-body reuse, whose identities are not re-supplied in this packet. I am not asking for duplicate reviews of them.

## 3. Remaining to-do list

1. Renew GCP authentication. Compile frozen Full101 unchanged and collect its real diagnostics and axiom profiles.
2. Compile the v2 main file and Checks file as a separate capture.
   - Confirm that each wrapper's `exact` elaborates (P3/F4) and that the HC46 name resolves (D1).
   - Require `{propext, Classical.choice, Quot.sound}` with no `sorryAx` for all nine `#print axioms` targets. The new theorems' profiles must be a subset of consumer plus inhabitant.
   - Count owned warnings.
3. Run the actual consumption trace: Full101 inhabitant → bridge → both SourceSize consumers, with `original_HC46_exact` inside them, and no legacy material consumer.
4. Keep the claims boundary: only Spectral47 and HC46 are discharged; the other caller premises remain; the result is a bound, not numeric NO; use the dyadic theorem for the manuscript's P.
5. Keep the inherited conditional verdicts from the custody-audited bodies and from the earlier 41-body reuse.
6. Keep the semantic and native debt open:
   - exact eigenvalue, 𝒢, Φ, adjoint, and the λ product identity with its `i ≤ d` guard
   - scalar reductions after the right-hand side, binding P to k, and checking J
   - M1 custody: the MZ24 v4 counter audit is source-level only, without PDF confirmation
   - numeric NO, and the source, star, robust8S and pre-draw witnesses
   - sampling, encoded reduction, runtime and learning
   - upstream transports
   - **R14 HIGH**
   - warnings, fresh-checkout and custody replay
   - novelty, citations, PDF, the provider and QA gates, and publication
